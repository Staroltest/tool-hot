#!/usr/bin/env python3
"""HOT 站点生成器：拉取 RSS -> 去重 -> 链接解析到工具本身 -> 工具收录门
-> 规则打分 -> 生成静态站。

只用 Python 标准库（urllib + xml.etree），不依赖任何外部包，也不依赖
大模型 API 或数据库；数据层就是 data/ 下的 JSON 文件。

流水线（参考 AIHOT 的信息架构：采集 -> 判重 -> 评分 -> 精选 -> 日报，
但全部落成静态文件，供 GitHub Pages 托管、定时任务驱动更新）：
  1. 拉取 sources.json 里的公开 RSS/Atom 与 JSON API（只读标题+摘要+链接，不转载全文）
  2. 按规范化链接去重，与 data/store.json 里的本地历史合并（增量更新；store.json 不推送）；
     链接解析到工具本身（Product Hunt 跟随 /r/p/ 跳转，Reddit 取正文 [link] 外链；
     Ignlab 走 /api/v1/listings，url 字段直接就是工具官网）
  3. 工具站收录门：只收点开就能用的工具网站，文章/新闻/博客/帖子/仓库页/
     目录页一律拦下；再规则打分（时间新鲜度 + 信源分级 + 主题关键词，config.json 可调）
  4. 产出 data/hot.json（热点榜 Top 20）、data/days/（按天分块）与 index.html
  5. 带 --daily 时额外产出 data/daily.json 与 daily.html（当日日报）

可选 LLM 打分：只有同时设置 HOT_LLM_API_KEY、HOT_LLM_BASE_URL、
HOT_LLM_MODEL 三个环境变量时才启用；任何失败都静默回退到规则分，
且绝不把 Key 写进代码、配置或输出文件。
"""

import argparse
import hashlib
import html
import json
import os
import re
import shutil
import sys
import time
import urllib.request
import urllib.error
import urllib.parse
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime

CST = timezone(timedelta(hours=8))
UA = {"User-Agent": "HOTBot/1.0"}

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ANALYTICS = "<!-- Cloudflare Web Analytics --><script type='module' src='https://static.cloudflareinsights.com/beacon.min.js' data-cf-beacon='{\"token\": \"45ad8fc57fc1481caa995c5bcdeb9072\"}'></script><!-- End Cloudflare Web Analytics -->"  # Cloudflare Web Analytics 统计代码
CLARITY = """<script type="text/javascript">(function(c,l,a,r,i,t,y){c[a]=c[a]||function(){(c[a].q=c[a].q||[]).push(arguments)};t=l.createElement(r);t.async=1;t.src="https://www.clarity.ms/tag/"+i;y=l.getElementsByTagName(r)[0];y.parentNode.insertBefore(t,y);})(window, document, "clarity", "script", "zfumqwq0k0");</script>"""


# ---------------------------------------------------------------- 工具函数

def load_json(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def save_json(path, data, compact=False):
    # 写 JSON（原子替换）。compact=True 时写紧凑单行，省体积（分块数据与 hot.json 用）。
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        if compact:
            json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
        else:
            json.dump(data, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def strip_html(text):
    if not text:
        return ""
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def shorten(text, limit=200):
    if len(text) <= limit:
        return text
    return text[:limit].rstrip() + "…"


SENT_END = "。！？.!?"
CLAUSE_END = "，、；：,;:；"
CLOSE_CHARS = "）】」』\"'”’"


def complete_para(text, limit=1500):
    """把一段摘要收成完整的一段话：不超过 limit，以句末标点收尾，不加省略号。
    详情页导读/正文摘要用：不允许截断到半句、末尾挂 …。
    已在限制内且以句末标点结尾的原样返回；否则退到 limit 内最后一个完整句；
    无完整句时退到最后一个分句标点；再无则硬截（仍不加 …）。"""
    text = (text or "").strip()
    if not text:
        return ""
    if text.endswith("…"):
        text = text[:-1].rstrip()
    if not text:
        return ""
    if len(text) <= limit and text[-1] in SENT_END:
        return text
    cut = text[:limit] if len(text) > limit else text
    best = -1
    for i, ch in enumerate(cut):
        if ch not in SENT_END:
            continue
        # ASCII 句点夹在数字之间是版本号/小数（如 4.8），不是句末
        if ch == "." and i > 0 and i + 1 < len(cut) \
                and cut[i - 1].isdigit() and cut[i + 1].isdigit():
            continue
        j = i + 1
        while j < len(cut) and cut[j] in CLOSE_CHARS:
            j += 1
        best = j
    if best > 0:
        return cut[:best].rstrip()
    for i in range(len(cut) - 1, -1, -1):
        if cut[i] in CLAUSE_END:
            return cut[:i + 1].rstrip()
    return cut.rstrip()


def norm_link(link):
    """去 fragment 与 utm_* 追踪参数，供去重用。"""
    link = (link or "").strip().split("#")[0]
    if "?" in link:
        base, qs = link.split("?", 1)
        kept = [p for p in qs.split("&") if p and not p.lower().startswith("utm_")]
        link = base + ("?" + "&".join(kept) if kept else "")
    return link.rstrip("/")


def parse_date(text):
    """RSS 的 RFC 2822 与 Atom 的 ISO 8601 都接受；失败返回 None。"""
    if not text:
        return None
    text = text.strip()
    try:
        dt = parsedate_to_datetime(text)
        if dt is not None:
            return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
    except (TypeError, ValueError):
        pass
    try:
        dt = datetime.fromisoformat(text.replace("Z", "+00:00"))
        return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def fmt_cst(dt):
    return dt.astimezone(CST).strftime("%m月%d日 %H:%M")


def fmt_cst_en(dt):
    """English twin of fmt_cst: 'Nov 14, 15:02' (CST)."""
    return dt.astimezone(CST).strftime("%b %d, %H:%M")


def fmt_gen_en(dt):
    """English generation timestamp: 'November 14, 2026, 15:02' (CST)."""
    return dt.astimezone(CST).strftime("%B %d, %Y, %H:%M")


def local_name(tag):
    return tag.rsplit("}", 1)[-1]


# ---------------------------------------------------------------- 工具站收录门（2026-11-16 起：只收能直接用的工具网站）
# 目标链接必须是点开就能用的工具本身（转换器、格式化、生成器、计算器、
# 编辑器等）；文章、新闻、博客、帖子、仓库页、目录页一律不上榜。
# 标题措辞只是次要信号，一律按目标链接的域名与路径判定；直接链到工具
# 本身的上线公告可以收。

# 域名黑名单：后缀匹配（子域名同样拦截），覆盖文章/博客/新闻/社交/
# 仓库/视频/目录站与短链
BLOCKED_DOMAINS = {
    "dev.to", "medium.com", "hackernoon.com", "smashingmagazine.com",
    "css-tricks.com", "freecodecamp.org", "stackoverflow.blog",
    "github.blog", "techcrunch.com", "theverge.com", "lobste.rs",
    "github.com", "gitlab.com", "reddit.com", "x.com", "twitter.com",
    "youtube.com", "youtu.be", "ycombinator.com", "substack.com",
    "wordpress.com", "cloudflare.com", "producthunt.com",
    "alternativeto.net", "toolify.ai", "betalist.com",
    "theresanaiforthat.com", "futuretools.io", "indiehackers.com",
    # AIToolMix：AI 工具目录站（229 个工具按分类罗列、另有文章/优惠/新闻），
    # 不是能直接用的工具本身（2026-11-22 06:37 CST 轮：热点第 1 条混入）
    "aitoolmix.com",
    # npx.tools：开发者工具索引站（可搜索的 npx 工具目录），所列工具需 npx
    # 本地运行，不是浏览器里能直接用的工具（2026-11-22 06:37 CST 轮：热点第 1 条）
    "npx.tools",
    # financialcrimes.fyi：白领犯罪日报站（Daily broadsheet，报纸版式呈现
    # 新闻内容），标题带 newspaper 但因 Daily Scribe 豁免未被标题门拦住；
    # 不是能直接用的工具（2026-11-22 17:07 CST 轮：热点榜混入新闻站）
    "financialcrimes.fyi",
    # samsara.pauoliver.net：佛学修行讲解文章站（按次第讲授佛陀教法，配经文
    # 与短片），是阅读内容不是工具（2026-11-22 17:07 CST 轮：当日时间线混入）
    "samsara.pauoliver.net",
    # webless.ai：面向企业官网的 AI 客服/搜索服务站（Agents + AI Search），
    # 只能预约演示，没有访客点开能直接用的工具（2026-11-22 归档复查：
    # 11-07 日报里的 Webless Agents；域名后缀匹配，www 子域一并拦）
    "webless.ai",
    # dravyra.com：短剧（short drama）观看指南与剧情介绍站（去哪看、
    # 剧情梗概、演员信息），是阅读型内容站，不是点开就能用的工具
    # （2026-11-25 13:37 CST 轮：热点榜第 3 条混入，实测确认）
    "dravyra.com",
    # artcraftguide.org：ArtCraft 桌面应用的独立指南站（17 个 Craft 应用
    # 的选型指南、文件支持说明、官方下载链接），整站是阅读型指南内容，
    # 所指应用均为 Rust 原生桌面应用、须下载安装，不是浏览器里能直接用
    # 的工具（2026-11-26 13:37 CST 轮：热点榜第 1 条混入，实测确认）
    "artcraftguide.org",
    # minsukim.io：个人 AI 引荐服务落地页（"I introduce people by email"），
    # 全站只有一句话介绍，没有访客点开能直接用的工具，不是工具网站
    # （2026-11-26 19:37 CST 轮：热点榜混入，实测确认）
    "minsukim.io",
    # best-gbagames.com：宝可梦 GBA 游戏与周边内容站（游戏、发售日历、
    # 周边商品、TCG），整站都是游戏内容，纯游戏按游戏口径一律拦
    # （2026-11-25 13:37 CST 轮：热点榜第 2 条混入，实测确认）
    "best-gbagames.com",
    # doomanalysis.com：交互式数据分析长文（P(doom)、2100 年崩溃与丰裕
    # 预测，分地区/成因展示图表），整站是一篇带图表的分析报告，没有访客
    # 能输入并得到结果的工具功能，不是能直接用的工具；标题“Si Won't
    # Save Us”不露文章痕迹，实测确认（2026-11-26 21:07 CST 轮：热点榜
    # 混入，人工核实后封）
    "doomanalysis.com",
    # seekquarry.com：Yioop 开源 PHP 搜索引擎的项目页/下载站（“Download
    # it, start it, and you have a search engine of your own”），须下载安
    # 装才能用，不是浏览器里能直接用的工具；可直接用的演示在 yioop.com，
    # 不在该链接上（2026-11-26 19:37 CST 轮：热点榜第 2 条混入，实测确认）
    "seekquarry.com",
    # perit.ai：卖数据与 RL 任务给 AI 实验室的数据集市（perit.ai/marketplace
    # 是数据集目录、按报价成交），不是点开能用的工具（2026-11-22 归档复查：
    # 11-15 日报与 W46/W47 周报、11 月月报里的 Perit Marketplace）
    "perit.ai",
    # probablystolenguide.com：游戏《Probably Stolen》（像素风赛博朋克
    # 店主模拟）的 Wiki 与攻略站（272 件物品价格、机制指南），整站都是
    # 游戏内容，纯游戏按游戏口径一律拦（2026-11-27 07:37 CST 轮：热点榜
    # 第 1 条混入，实测确认）
    "probablystolenguide.com",
    "facebook.com", "instagram.com", "linkedin.com", "tiktok.com",
    "apps.apple.com", "play.google.com",
    # Steam 商店页：须下载安装的游戏/软件，不是浏览器里能直接用的工具
    # （2026-11-19 20:07 CST 轮：IT Thinks 链到 store.steampowered.com）
    "steampowered.com",
    # rmux.app：原生终端应用（Rust 编写，macOS/Windows/Linux 均须下载安装，
    # 站上写明 macOS 已签名公证、Windows 未签名、Linux 需 Ubuntu 24.04）；
    # 站内浏览器里跑的只是 WASM 样例演示（"Sample sessions only; no shell
    # or server connection"），"Get a feel for it before you install"，
    # 不是能直接用的工具本身。标题 "terminal workspace" 不露安装痕迹，
    # 实测又因 "running in your browser" 豁免放行，故整域封禁
    # （2026-11-22 22:37 CST 轮：热点榜混入，人工核实后封）
    "rmux.app",
    # modelflare.dev：纯 AI API 网关（"One OpenAI-compatible API key for
    # many LLMs"，接 GPT/Claude/Gemini，要拿 key 后用 curl/SDK 调用），
    # 点开不能直接在浏览器里用，按“纯 API 平台不收”口径拦（与此前
    # TokLab、ScraperSocial、PennyCompute 同类处理）；标题“One
    # OpenAI-compatible API key for many LLMs”不露 API 平台痕迹，实测
    # 也无安装信号，人工抽查封禁（2026-11-23 16:07 CST 轮：新到 HN
    # 条目混入当日时间线）
    "modelflare.dev",
    # crux.quest：iPhone/iPad 游戏应用 Crux 的官网，全站都是每日单词、
    # 逻辑、数字、地理等小游戏（如 Borderdraw 画国界线游戏），纯游戏，
    # 按游戏口径一律拦；标题“Show HN: Borderdraw (Web Mini-Game)”
    # 的 mini-game 说法标题门此前未覆盖，标题门已同步加 mini-game
    # 规则（2026-11-23 16:07 CST 轮：新到 HN 条目混入当日时间线）
    "crux.quest",
    # extrabar.app：macOS 菜单栏桌面应用（自定义菜单栏、深链与快捷操作，
    # 须下载安装、付费买断、无免费试用，站上写明支持 macOS 12.4+、配置
    # 存在本机），不是浏览器里能直接用的工具；标题“ExtraBar”不露安装
    # 痕迹，人工抽查发现（2026-11-23 18:19 CST 轮：归档复查发现 11-20
    # 日报里的 ExtraBar，整域封禁）
    "extrabar.app",
    # agent-home.ai：Gal 本地优先智能体运行时（CLI gal / 桌面 galw 均为
    # Go 二进制，须下载安装到本机，内核级沙箱只在本地生效），站上是营销
    # 落地页、浏览器里没有能直接用的工具；标题“local-first agent runtime”
    # 不露安装痕迹，实测放行，人工抽查封禁（2026-11-24 00:37 CST 轮：
    # 热点榜第 1 条混入）
    "agent-home.ai",
    # aitoolfinder.org：AI 工具目录站（按分类罗列 AI 工具、可比较功能与价格），
    # 是目录不是能直接用的工具本身，与此前已封的 aitoolmix.com 同类
    # （2026-11-24 18:37 CST 轮：热点榜第 2 条混入，人工核实后封）
    "aitoolfinder.org",
    # supacheap.eu：付费 GDPR 数据删除服务（买 API key/套餐后由其后台删
    # 544 家数据经纪商的数据，无免费可直接用的功能，站上还提到自家 app），
    # 是售卖页不是点开能用的工具（2026-11-24 18:37 CST 轮：热点榜
    # 第 13 条混入，人工核实后封）
    "supacheap.eu",
    # 1fit.kids：塔什干线下儿童课程目录/地图（按城市列课程、卖家庭会员），
    # 是本地服务目录不是浏览器里能直接用的工具
    # （2026-11-24 18:37 CST 轮：当日时间线混入，人工核实后封）
    "1fit.kids",
    # heroui.pro：付费 React/React Native UI 组件库与模板（按 license 售卖，
    # 须 npm 安装进项目才能用），不是点开能用的工具；标题 "HeroUI Pro 1.0"
    # 不露安装痕迹，实测放行，归档复查封禁（2026-11-24 19:07 CST 轮：
    # 11-13 日报里的 HeroUI Pro，整域封禁）
    "heroui.pro",
    # distribution.dev：开发者广告网络（daily.dev 与 DEV 合办的广告投放
    # 服务，须联系洽谈买广告位），是售卖页不是点开能用的工具
    # （2026-11-24 19:07 CST 轮：归档复查发现 11-17 日报里的 distribution.dev）
    "distribution.dev",
    # extradock.app：macOS 桌面应用（多 Dock 工具，须下载安装、一次性付费
    # €14.99），不是浏览器里能直接用的工具；与已封的 extrabar.app 同类
    # （2026-11-24 19:07 CST 轮：归档复查发现 11-16 日报里的 ExtraDock 5）
    "extradock.app",
    # directorygems.com：目录站研究库（350 个目录站的拆解、基准数据集、
    # 案例研究与周更 teardown），是目录/研究内容站不是能直接用的工具；
    # 标题“DirectoryGems”不露目录痕迹，实测放行，人工核实后封
    # （2026-11-25 02:07 CST 轮：热点榜混入，浏览器实测确认）
    "directorygems.com",
    # clueffygame.com：游戏发现站（按短视频线索找游戏、链官方游玩链接与
    # 攻略），是游戏目录不是能直接用的工具，纯游戏按游戏口径一律拦
    # （2026-11-25 15:07 CST 轮：热点榜第 6 条混入，实测确认）
    "clueffygame.com",
    # krillionhint.com：Krillion 每日潜水游戏（Daily Dive）的答案与提示站
    # （首页 "verified answers and spoiler-free hints for today's Daily
    # Dive"，按提示出分、按名次排名），是纯游戏的配套答案站不是工具；
    # 纯游戏按游戏口径一律拦
    # （2026-11-25 15:37 CST 轮：当日时间线新到，浏览器实测确认）
    "krillionhint.com",
    # toolmarina.com：工具目录站（按分类罗列外部工具、可提交收录），
    # 是目录不是能直接用的工具本身，与已封的 aitoolfinder.org 同类
    # （2026-11-25 15:07 CST 轮：热点榜第 4 条混入，实测确认）
    "toolmarina.com",
    # puraroute.com：住宅代理购买/管理后台（买代理、配连接信息、看用量），
    # 是付费代理服务售卖页不是点开能用的工具
    # （2026-11-25 15:07 CST 轮：热点榜第 16 条混入，实测确认）
    "puraroute.com",
    # soniccaption.com：浏览器扩展（首页 "Add to Chrome / Install
    # Extension"，装进 Chrome/Edge 后给标签页音频加实时字幕），
    # 浏览器扩展按标准一律不收
    # （2026-11-25 15:07 CST 轮：热点榜第 19 条混入，实测确认）
    "soniccaption.com",
    # devglobaljobs.com：全球招聘平台（按国家城市找工作、远程与签证岗、
    # 可免费发帖），是招聘职位目录不是能直接用的工具
    # （2026-11-25 15:07 CST 轮：当日时间线混入，实测确认）
    "devglobaljobs.com",
    # dssub.com：DeepSeek 与多模型 API 套餐售卖/管理站（比价、管理 API
    # key 与用量账单），纯 API 平台落地页，按“纯 API 平台不收”口径拦
    # （2026-11-25 15:07 CST 轮：当日时间线混入，实测确认）
    "dssub.com",
    # vicelet.com：七宗罪测试问卷站（答 21 道题出罪行分数卡），是娱乐
    # 测验不是能直接用的工具
    # （2026-11-25 15:07 CST 轮：当日时间线混入，实测确认）
    "vicelet.com",
    # gettradelatch.com：承包商漏接电话短信回拨服务（须接电话系统、按
    # 服务收费），是业务服务售卖页不是点开能用的工具
    # （2026-11-25 15:07 CST 轮：当日时间线混入，实测确认）
    "gettradelatch.com",
    # allocations.com：SPV 与基金管理收费服务站（Standard SPV 一次性
    # 收费 $9,950 起，Get Started 跳 Calendly 预约洽谈），是雇人代办的
    # 业务服务售卖页不是点开能用的工具；标题 "Allocations Inc" 不露
    # 服务售卖痕迹，实测放行，人工核实后封
    # （2026-11-26 06:07 CST 轮：热点榜第 3 条混入，实测确认）
    "allocations.com",
    # proofable.me：AI 智能体权限与签发凭证层（"Add Proofable to any
    # MCP client or app"、SDK 接入），须接进 MCP 客户端或自家应用才能
    # 用，点开是营销页、浏览器里没有能直接用的工具；按“纯 API 平台
    # 不收”口径拦，与此前已封的 TokLab、modelflare.dev 同类
    # （2026-11-26 06:07 CST 轮：热点榜第 20 条混入，实测确认）
    "proofable.me",
    # puzlio.com：每日解谜/文字/地理小游戏目录站（游戏指南 + 官方答案
    # 汇总，链向原出版商去玩），是游戏目录不是能直接用的工具；纯游戏
    # 按游戏口径一律拦，目录页按标准也不收
    # （2026-11-26 06:07 CST 轮：热点榜第 1 条混入，实测确认）
    "puzlio.com",
    # good-morning-gorgeous.pages.dev：AI 鼓励陪伴聊天机器人（每日鼓励、
    # 倾诉对话、日记），是陪伴娱乐型聊天应用不是任务工具
    # （2026-11-25 15:07 CST 轮：当日时间线混入，实测确认）
    "good-morning-gorgeous.pages.dev",
    "nytimes.com", "theguardian.com", "reuters.com", "washingtonpost.com",
    "cnn.com", "bbc.com", "bbc.co.uk", "economist.com", "ft.com", "wsj.com",
    "theatlantic.com", "newyorker.com", "thehill.com", "cnbc.com",
    "businessinsider.com", "engadget.com", "gizmodo.com", "venturebeat.com",
    "arstechnica.com", "tomshardware.com", "techpowerup.com", "spacenews.com",
    "space.com", "sciencealert.com", "quantamagazine.org", "theweek.com",
    "telegraph.co.uk", "euronews.com", "dw.com", "nltimes.nl", "fortune.com",
    "lithub.com", "harpers.org", "science.org", "newscientist.com",
    "livescience.com", "wired.com", "bloomberg.com", "apnews.com", "npr.org",
    "axios.com", "vox.com", "cnet.com", "zdnet.com", "pcworld.com",
    "mashable.com", "hackaday.com", "ieee.org", "ietf.org",
    "googleblog.com", "openai.com", "anthropic.com",
    "v.redd.it", "i.redd.it", "preview.redd.it",
    "imgur.com",
    "blogspot.com", "ghost.io", "hashnode.dev", "livejournal.com",
    "tumblr.com", "notion.site", "notion.so",
    "docs.google.com", "drive.google.com",
    "arxiv.org", "zenodo.org", "archive.org", "web.archive.org",
    # 论文分享站（2026-11-16 第四轮泄漏：Perfect Numbers Generator 链到
    # academia.edu 的论文页，且该链接 404；论文站不是在线工具）
    "academia.edu", "researchgate.net", "semanticscholar.org",
    "stackexchange.com", "stackoverflow.com",
    "chromewebstore.google.com", "addons.mozilla.org",
    "hub.docker.com", "apps.microsoft.com",
    "snapcraft.io", "flathub.org", "f-droid.org", "testflight.apple.com",
    "npmjs.com", "pypi.org", "crates.io", "rubygems.org",
    "packagist.org", "nuget.org",
    # 抽查确认不是在线工具（2026-11-16）：Mac 桌面应用、研究论文站、电子书售卖页
    "minutenotes.app", "getswiftapi.com", "bestmillionstartups.com",
    # Agency：无法验证为网页工具，摘要显示是给智能体配电脑的本地搭建工具
    "agency.makors.xyz",
    # 抽查确认不是在线工具（2026-11-16 第二轮）：JS 组件库、iPhone 应用、数据买卖市场
    "dynaura.ashutoshswamy.in", "asostudio.app", "perit.ai",
    # 抽查确认不是在线工具（2026-11-16 第三轮）：Mac/安卓桌面应用、自托管智能体、打车应用内功能
    "tacie.app", "pocketdbforsupabase.netlify.app", "defaulttamer.app",
    "freeflow.audio", "uber.com", "screengo.app", "rakazo.com",
    # 抽查确认不是在线工具（2026-11-16 第四轮）：亲子场所目录/攻略站，
    # 主站是行程与指南内容并主推 iPhone 应用，不是能直接用的工具
    "ourplayday.com",
    # 抽查确认不是在线工具（2026-11-16 第五轮，Ignlab 接入首批）：
    # Divi Digital 是迪拜 SEM 代运营公司官网，不是工具；
    # Reels Blocker 与 ChatSweep 是浏览器扩展（落地页）；
    # GamersVPN 是 VPN 客户端下载服务；GrabaRobot 是机器人厂商目录站
    "dividigital.ae", "reelsblocker.biznift.com", "gamersvpn.com",
    "chatgptbulkdelete.net", "grabarobot.com",
    # 2026-11-17 扩源实测封禁（MakerHunt 首批 25 条）：
    # dokira.com 是 B2B 广告平台落地页（须申请接入），不是点开能用的工具；
    # dragontraveler.gg 是游戏 wiki/梯队榜数据库（内容站）；papaya.chat 仅限
    # 等候名单（点开用不了）；website-ai-agent.com 是企业 AI 客服落地页
    # （须购买嵌入），站内无直接可用的工具；jobswithpay.com 是薪资招聘版
    # （职位目录）；soleapp.com.au 是记账移动应用（App Store/Google Play）；
    # flowmails.net 是 AI 代理邮箱 SDK 服务（须 npm 安装接入）；
    # cybermaps.dev 是 WordPress 插件（须安装）；provimedia.de 的 Code
    # Guardian 是须 npm 安装的开发工具；opensoundconnect.app 是 Mac 桌面应用
    "dokira.com", "dragontraveler.gg", "papaya.chat",
    "website-ai-agent.com", "jobswithpay.com", "soleapp.com.au",
    "flowmails.net", "cybermaps.dev", "provimedia.de",
    # 2026-11-22 10:07 PST 轮热点榜自查补封：gtaviwiki.org 是 GTA VI
    # 参考 wiki 站（标题自写 "Reference Site for Grand Theft Auto VI"），
    # 是内容站、不是能直接用的工具；整站就是这一个 wiki，按游戏 wiki
    # dragontraveler.gg 的口径封整个域名
    "gtaviwiki.org",
    # 2026-11-23 21:07 CST 轮热点榜自查补封：zipzax.com 是 AI/在线工具
    # 目录站（首页罗列 475+ 工具、链到站外），不是能直接用的工具本身；
    # 按目录站（aitoolmix.com、theresanaiforthat.com）口径封整个域名
    "zipzax.com",
    # 2026-11-26 08:07 PST 轮：pikkai.com 是 AI 工具目录站（按任务找工具、
    # 对比收藏，首页罗列站外工具），不是能直接用的工具本身；本轮由时间线
    # 升入热点榜才被发现，按目录站口径封整个域名
    "pikkai.com",
    # 2026-11-26 08:07 PST 轮：meminto.com 是付费定制印刷书礼品服务
    # （每周提问、最后印成精装实体书，$99 起售卖页），核心产出是实体书
    # 而非浏览器里能用的工具，按售卖页口径封整个域名
    "meminto.com",
    "opensoundconnect.app",
    # 2026-11-17 扩源实测封禁（Smol Launch 首批 50 条）：
    # talat.app 是桌面转录应用（Download for Mac/Windows）；
    # hiapi.ai 是 OpenAI 兼容 API 平台（须 npm 安装 CLI）；
    # toklab.ai 是统一 AI 模型 API 平台（纯 API，无浏览器工具）；
    # newbornlog.com 是婴儿追踪移动应用（App Store/Google Play）；
    # tapmap.net 是地图社交网络 + 移动应用；publishyoursaas.com 与
    # listmaro.com 是 SaaS 目录站；secretpass.com 是优惠券会员站 + 浏览器
    # 扩展；myzucoins.org 是加密货币钱包项目站（主推下载钱包）；
    # fundraisebase.com 是创业融资数据库/新闻站；importz.fi 是芬兰汽车
    # 进口资讯站（数据库 + 文章）；gpt288.com 是 ChatGPT 订阅代充平台；
    # pluginpeer.com 是 WordPress 插件 QA 社区服务；alook.ai 是须下载的
    # 多智能体协作应用（接 Claude Code/Codex 桌面端）；applylah.com 仅限
    # 等候名单；fast.io 是 AI 数据层 B2B 服务（无直接可用工具）；
    # intakerun.com 是原生邮件客户端（macOS/iPhone/iPad/Android）
    "talat.app", "hiapi.ai", "toklab.ai", "newbornlog.com", "tapmap.net",
    # 2026-11-26 08:07 PST 轮：01router.com 是统一 AI 视频/图片生成 API
    # 平台（一个 API key、调 API 生成，按 toklab.ai 纯 API 平台口径封整个
    # 域名；FAQ 虽提到站内有视频生成器，但本轮链接指向的是 API 营销首页，
    # 点开不能直接用；若日后出现直达生成器的链接可再评估）
    "01router.com",
    # 2026-11-27 05:07 PST 轮：bloque.run 是托管 MCP 网关平台（集中管理
    # MCP 服务器、发 API key 供 AI 客户端调用，Playground 只是平台内测功
    # 能），按 toklab.ai 纯 API 平台口径封整个域名
    "bloque.run",
    # 2026-11-27 21:37 PST 轮：wikivectors.com 是维基百科搜索 API（给 AI
    # 应用调 API 用，需申请 key 接入；站内 Try it 只是 API 试调用演示，
    # 不是浏览器里能直接用的工具），按 toklab.ai 纯 API 平台口径封整个域名
    "wikivectors.com",
    "publishyoursaas.com", "listmaro.com", "secretpass.com",
    "myzucoins.org", "fundraisebase.com", "importz.fi", "gpt288.com",
    "pluginpeer.com", "alook.ai", "applylah.com", "fast.io",
    "intakerun.com",
    # 2026-11-17 扩源实测封禁（DevHunt 首批 129 条，描述自述即非浏览器工具）：
    # rustable.app 是原生数据库客户端；micronotch.app 是 Mac 工具栏应用；
    # trina.app 须装到公司自有服务器；infracanvas.app 须安装 agent；
    # lookbk.dev 是 Claude Code 等的 agent skills 资料库；
    # uniroute.app / kennmarq.com / sully.ai / modellix.ai 是纯 API 平台；
    # strg.com 是 S3 存储服务；haipay.net 是支付基础设施；
    # cadenya.com 是托管运行时；usagerail.com 是 SDK；
    # mailkube.com 是交易邮件 API 服务；foragent.io 是给 AI 代理的电话
    # 号码服务；tenpace.com 的 Review Router 是 GitHub→Slack 路由服务
    "rustable.app", "micronotch.app", "trina.app", "infracanvas.app",
    "lookbk.dev", "uniroute.app", "kennmarq.com", "sully.ai",
    "modellix.ai", "strg.com", "haipay.net", "cadenya.com",
    "usagerail.com", "mailkube.com", "foragent.io", "tenpace.com",
    # 2026-11-17 扩源实测封禁（DevHunt 第二批，人工抽查 103 条在榜条目）：
    # wtfm.sh 是 Claude Code/Codex 插件；cuehq.social 是 MCP 服务器；
    # eased.dev 是 React 动效组件库；raziel.co 是 API + MCP 服务器；
    # skilder.ai 把 Agent Skills/MCP 打包成插件；apilabs.ai 是 Claude Code
    # 插件/技能；lowrouter.ai 是 AI 网关 API；autorouter.com 是 Agent 编排
    # 服务；vidkraken.com 是下载 YouTube 视频的 REST API；sqlly.app 是原生
    # SQL 桌面客户端；caprock.dev 是 macOS 桌面应用；atriumkit.com 是 Chrome
    # 扩展；storesynk.com 是 Shopify-Webflow 集成服务；gnista.sh 监控编码
    # CLI；jilebi.ai 是云 Linux 虚拟机；aplite.ai 是自托管 OpenClaw 实例；
    # terminay.com 是桌面终端；uncensoredlabs.dev 是无审查模型 API；
    # remotejobsrock.com 是远程招聘版；symvibe.com 是编码 CLI 并行运行器；
    # eigenflux.ai 是 Agent 数据基础设施；bench47.com 是 Agent 软件工厂服务；
    # evoforge.cc 是代办任务的 Agent 服务；captapi.com 是社媒数据 API；
    # agentivity.io 是 AI 团队服务；gortex.ai 是决策 API；usetyton.com 是
    # Meta Pixel 代装服务；extraheadroom.com 是 macOS/Windows/Linux 菜单栏
    # 应用；gnsoftlab.com 的 NetIntel 是 Linux 边缘系统监控；mcpexplorer.com
    # 是 MCP 服务器目录；lassocut.com 是去背景 API；logoapi.sh 是 Logo API；
    # avastudio.com 是 Agent 接入服务；bearconnect.io 是 LinkedIn 自动化；
    # ibertechsolutions.co.uk 是网页设计公司页面；canopyapi.co 是亚马逊商品
    # 数据 API；stateofpixel.com 是 CI 视觉回归服务；motokoui.com 是 Next.js
    # SaaS 起手模板；pr-viz.com 是 IDE skill；oreoui.com 是图标素材库；
    # marketmee.app 是营销自动化服务；prodlaunch.xyz 是产品展示目录；
    # borehole.dev 是并购尽调服务；brewless.eu 是 Laravel 部署服务；
    # yt2wav.net 是 YouTube 转音频下载站；slcr.dev 是需求规范文档站；
    # zerotime.dev/thinker.sh 是 npx 安装的 CLI 工具；ac-bridge.com 是接
    # Claude Code 的智能灯桥接服务；kathe.app 是 Mac/Windows 桌面应用；
    # usestring.ai 是纯 API/MCP（/web-access 页只对 AI Agent 说话）；
    # usevoicy.com 是 Mac/Windows/Linux/iPhone/Android 听写应用
    "wtfm.sh", "cuehq.social", "eased.dev", "raziel.co", "skilder.ai",
    "apilabs.ai", "lowrouter.ai", "autorouter.com", "vidkraken.com",
    "sqlly.app", "caprock.dev", "atriumkit.com", "storesynk.com",
    "gnista.sh", "jilebi.ai", "aplite.ai", "terminay.com",
    "uncensoredlabs.dev", "remotejobsrock.com", "symvibe.com",
    "eigenflux.ai", "bench47.com", "evoforge.cc", "captapi.com",
    "agentivity.io", "gortex.ai", "usetyton.com", "extraheadroom.com",
    "gnsoftlab.com", "mcpexplorer.com", "lassocut.com", "logoapi.sh",
    "avastudio.com", "bearconnect.io", "ibertechsolutions.co.uk",
    "canopyapi.co", "stateofpixel.com", "motokoui.com", "pr-viz.com",
    "oreoui.com", "marketmee.app", "prodlaunch.xyz", "borehole.dev",
    "brewless.eu", "yt2wav.net", "slcr.dev", "zerotime.dev",
    "thinker.sh", "ac-bridge.com", "kathe.app", "usestring.ai",
    "usevoicy.com",
    # 2026-11-22 03:07 CST 轮：VoiceVibe 是 Windows/macOS/Linux 桌面
    # 语音助手应用（官网写明 Available for Windows 10+、macOS 14+、
    # Linux X11），须下载安装才能用，不是浏览器里直接用的工具；
    # 标题不露痕迹，标题门拦不住，域名封禁
    "voicevibe.ai",
    # 2026-11-22 19:37 CST 轮：HomeBrain 是家用硬件小盒子（本地 AI、私有云、
    # 密码库都跑在自家设备上），官网写明“Open source, and installable today.
    # Runs on Ubuntu 24.04 or later... even on a Raspberry Pi 5”，且硬件仍
    # 是原型、只能加入等候名单，点开网站本身不能用工具；标题只说“private
    # cloud box, local agent”，标题门与实测都拦不住，域名封禁
    "homebrain.house",
    # 2026-11-22 19:37 CST 轮：osssoftware.org 是开源替代品目录站（“Alternative
    # to: Product Hunt / Notion / Trello …”逐条列产品、链到各产品官网），本身
    # 不是能直接用的工具；Disposable Email Checker 是纯 REST API（文档页只有
    # GET /check 接口说明，无浏览器界面），同纯 API 平台，域名封禁
    "osssoftware.org", "disposable-email-checker.ara-v1.workers.dev",
    # 2026-11-21 08:37 CST 轮：saturnsql.com/context-layer 是付费 SaaS
    # （€29/人/月 Pro 套餐）数据库上下文层产品的营销页，须注册付费并接入
    # 自有数据库、经 MCP 使用，页面本身不是点开能用的工具；同已封的
    # TokLab 等纯 API/MCP 平台，域名封禁
    "saturnsql.com",
    # WhyArc：实测首页是 iPhone 应用落地页（App Store 链接 7 处），不是网页工具
    "whyarc.com",
    # 2026-11-23 04:07 CST 轮：Fission Agents 是统一 AI 模型 API 平台
    # （“View API passes”、$5 一次性 API 通行证、共享 AI 预算），站内无
    # 点开能直接用的浏览器工具；同已封的 TokLab 等纯 API 平台，域名封禁
    "ai.fissionagents.com",
    # 2026-11-24 13:07 CST 轮：Woolly 是本地记忆 API/CLI 工具（“Runs on
    # your machine”“A local API with TypeScript and Python clients”、
    # 须在本地跑 woolly check），官网本身只是营销页，点开不能用工具；
    # 2026-11-17 就已混进当日归档（zh_title 一直为空才被发现）；标题
    # “local mem0-compatible memory API”不露下载痕迹，标题门拦不住，
    # 同已封的 TokLab 等纯 API/本地工具，域名封禁
    "usewoolly.com",
    # 2026-11-24 06:37 CST 轮：AI X Tool（aixtool.xyz）是 AI 工具目录站
    # （“AI Tool Directory”“3,151 tools indexed”），本身不是能直接用
    # 的工具，目录页一律拦，域名封禁
    "aixtool.xyz",
    # 2026-11-25 22:37 CST 轮：OpenEight 是 AI 智能体治理控制面，
    # 核心是 Python SDK + LangChain 集成 + API key，须安装 SDK 接入
    # 自有智能体才能用，官网本身只是营销页，点开不能用工具；
    # Avva 是把个人专业经验发布成 MCP 供他人 AI 查阅的平台，
    # 成品是 MCP 端点、供 AI 调用而非人在浏览器里直接用的工具；
    # 同已封的 TokLab、Hookr 等纯 API/MCP 平台，域名封禁
    "openeight.ai", "avva.chat",
    # 2026-11-25 22:37 CST 轮（同轮抽查补封 4 个）：One Fairway 是浏览
    # 器 3D 高尔夫游戏（onefairwaygolf.com/play），纯游戏一律拦；
    # bouncemarket 是押注小球掉落方向的预测市场游戏（余额/份额/
    # 排行榜），不是工具；LaunchPulse 是付费代投服务（把产品分发到
    # 100+ 目录、买家雷达、营收归因，$29–299），售卖页本身不是点
    # 开能用的工具；Cyber（cyber.askgina.ai）是网络安全事件日报/
    # 资讯聚合（每小时重建的事件登记），新闻类一律拦，域名封禁
    "onefairwaygolf.com", "bouncemarket.minhanhday.com",
    "pulse.statementflow.win", "cyber.askgina.ai",
    # 2026-11-27 15:37 CST 轮：Flatkey 是统一 AI 模型 API 平台
    # （“One API key for multiple AI models”、调 API 生成 + GPU 租赁，
    # Tools 页是“1,000+ AI tools, one key and one balance”的 API 目录，
    # Playground 须注册后在控制台里试模型，首页本身不是点开能用
    # 的工具；同已封的 TokLab、01router 等纯 API 平台，域名封禁）
    "flatkey.ai",
    # 2026-11-28 12:37 CST 轮：SonoJS API 是免费 Fake REST API 平台
    # （"Free fake REST APIs with live JSON"、十个共享演示数据集，
    # 供前端开发调 API 做原型；站内 Playground 只是 API 测试台，
    # 产品本身是 API 端点而非浏览器里直接用的工具；同已封的
    # TokLab、01router、bloque.run、flatkey.ai 等纯 API 平台，域名封禁）
    "sonojs.com",
    # 2026-11-24 06:37 CST 轮：Everything Is Outdated
    # （everythingisoutdated.dev）是标题自带 (Game) 的终端主题纯游戏，
    # 按游戏口径（纯游戏一律拦）封禁；整站即游戏，域名封禁
    "everythingisoutdated.dev",
    # 抽查确认不是在线工具（2026-11-16 第五轮）：原生 iPhone/iPad/Mac 笔记应用，
    # 首页主推原生应用下载，网页版只是附属，不符合“完全在网站上就能用”
    "remindly.com",
    # 抽查确认不是在线工具（2026-11-16 第六轮，ListBulb 接入首批 22 条
    # 逐条审描述后封禁）：AI Rank Inspector 是 Chrome 扩展；
    # Battery Orbit 是 Mac 菜单栏应用；Interview Clozo（clozo.ai）是 Mac
    # 桌面应用；Buildingnow 是播客+邮件订阅，不是工具；BuzzLaunches /
    # PeekLaunch / Launchgp / MegaLaunch 是新品发布与发现目录站；
    # Dotleadlist 是卡车线索售卖服务；FieldForm Templates 是模板文件
    # 下载库；Ibuildinpublic 是 builder 社区；Indish Marketer 是营销
    # 自动化代运营服务；Ecommerce Data API 是付费 REST API，不是能在
    # 浏览器里直接用的工具
    "airankinspector.com", "batteryorbit.app", "clozo.ai",
    "buildingnow.fm", "buzzlaunches.com", "peeklaunch.com",
    "launchgp.io", "megalaun.ch", "dotleadlist.com",
    "fieldformtemplates.com", "ibuildinpublic.com",
    "indishmarketer.com", "ecommercedataapi.com",
    # 抽查确认不是在线工具（2026-11-16 第六轮，ListBulb 抽查实测）：
    # Matikiri 上榜描述写的是“AI 音乐工具、可生成节拍”，但实测官网
    # 是印尼语 K-Pop 音乐流媒体站（首页 0 处 AI/编曲相关内容，链接
    # 全是歌曲页、榜单与曲库），没有能用的工具，属内容站而非工具站
    "matikiri.net",
    # 抽查确认不是在线工具（2026-11-16 午间轮）：Vindle 是 iPhone/iPad
    # 每日猜车游戏，官网主推 TestFlight 内测下载，不是能在浏览器里
    # 直接用的网页工具；标题不露痕迹，标题门拦不住，域名封禁
    "vindle.app",
    # 抽查确认不是在线工具（2026-11-17 凌晨轮实测）：
    # Solipsist 是本地安装的 Markdown 编辑器（curl | sh 安装，在本机
    # 跑 localhost:3000 服务），要下载安装才能用，不是浏览器里直接
    # 用的工具；RightNow AI 是开源模型推理 API 落地页，站上没有能直
    # 接用的工具，只能写代码调 API；Sample 是 Android 音乐播放器，
    # 官网只给 APK 下载（留邮箱发下载链接），手机应用不算在线工具；
    # Dustify 演示本身静音，实际播放必须连接 Spotify Premium，核心
    # 功能不在站内完成，不算“完全在网站上就能用”
    "solipsist.sh", "rightnowai.co", "sample-music-player.netlify.app",
    "dustify.org",
    # 抽查确认不是在线工具（2026-11-18 13:37 轮实测）：Security Zines 的
    # AWS 页是手绘 zine 合集的售卖页（12 卷 $99，单卷 $15），卖的是付费
    # 阅读内容，站上没有能直接用的工具；标题带 "zines" 但标题门未覆盖，
    # 域名封禁
    "securityzines.com",
    # 抽查确认不是在线工具（2026-11-18 16:07 轮实测）：Incredible Agents
    # 是 Mac/Windows 桌面应用（官网 "Download for Mac/Windows"），实测
    # 命中 download_platform 信号，但被 "Agents work in your browser"
    # 触发豁免放行——豁免句说的是桌面智能体在浏览器里操作，别的东西，
    # 不是工具本身在浏览器里用；UI Verify 是视觉回归测试服务，用之
    # 前须把 @uiverify/* 包接进自家测试并跑 CI（站上写 "fetch
    # install.md with curl"），不是点开就能用的工具，探查信号够不着
    # 这种写法；两站域名封禁
    "incredible.one", "uiverify.ai",
    # 抽查确认不是在线工具（2026-11-18 16:07 轮自查补漏）：Beacon MCP 是
    # Chrome 扩展 + 中继服务（官网第一步就是 "Install the extension /
    # Load the Chrome extension"），没有扩展用不了；浏览器扩展不收。
    # 探查信号够不着这种写法（extension_install 要求 install 后紧跟
    # 浏览器名），域名封禁
    "trybeacon.space",
    # 抽查确认不是在线工具（2026-11-18 11:37 PST 轮实测，本轮热点/时间线
    # 泄漏 10 条）：joelriley.com/fun-with-trainers 是个人博客文章（讲单车
    # 训练器 Web Bluetooth 实验，工具本身只是文中链接）；sourcepost.dev
    # 是 AI 代理供应商/服务/API 目录站；kradle.ai 是 Minecraft 多智能体
    # 基准榜单与回放结果页，站上跑不了评测；intrusive.ai 是开源攻击模拟
    # 平台（AGPL，Operator/Interceptor 须自托管安装），站上没有能直接用
    # 的工具；transposeany.com 是 Chrome 扩展落地页（须安装扩展）；
    # yashmouje.com/record 是个人互动散文页（金唱片主题的十二件事，内容
    # 站）；shown.simdijinkins.com 是 Show HN 全量存档/目录站；
    # scififutures.vercel.app 是科幻技术成熟度互动科普页（内容站）；
    # rshekhar.com/voyager 是旅行者 1 号互动拆解页（内容站，非工具）；
    # voxoria.ai 是纯 API/MCP 营销数据平台，定价对比页是参考页（同已封
    # 的 TokLab 等纯 API 平台）
    "joelriley.com", "sourcepost.dev", "kradle.ai", "intrusive.ai",
    "transposeany.com", "yashmouje.com", "shown.simdijinkins.com",
    "scififutures.vercel.app", "rshekhar.com", "voxoria.ai",
    # Tabletop：Google Labs 是实验展示站，labs.google 根地址是目录页；
    # 其实测 tabletop.google/about 是仅限邀请的候补名单落地页，访客无法
    # 直接使用工具（2026-11-16 时间线泄漏：Tabletop 链到 labs.google 根地址）
    "labs.google",
    # 抽查确认不是在线工具（2026-11-16 晚间轮，浏览器实测）：CodeGraphy 是
    # 本地优先的 AST 代码图 + 11 工具 MCP 服务器，首页主推
    # `pip install codegraphy-lite`，浏览器里只有固定示例项目的界面预览，
    # 无法上传/分析自己的代码库；Pro 购买按钮还链到一个无关 Telegram 账号
    "codegraphy.software",
    # 抽查确认不是在线工具（2026-11-16 16:00 轮，浏览器实测本轮 9 条新品，
    # 6 条泄漏）：LingoMic 是 Chrome 扩展 + Windows 桌面应用，核心功能要
    # 安装扩展/客户端；ByteVoice 只有 macOS 桌面应用下载；Notebook to Notes
    # 是 19 美元 macOS 付费应用（.dmg 下载）；StateWeave 是给编码智能体
    # 做沙箱测试的平台，要装 sw CLI 才能用；UI SDK 是供智能体生成 UI 的
    # 行为库/SDK（同第二轮已封的 JS 组件库）；go.cal.com 短链本轮链到
    # Product Hunt 的 Cal.com Companion Apps，即 iOS/Android 原生应用 +
    # 浏览器扩展；apps.shopify.com 是 Shopify 应用商店（同已封的
    # apps.apple.com / play.google.com），时间线里的 AgentWatch 即链此
    "lingomic.com", "bytevoice.app", "notebooktonotes.com",
    "stateweave.net", "ui-sdk.dev", "go.cal.com", "apps.shopify.com",
    # Black Pixel：69 字节 PNG 的 NFT 收购 dossier 销售页（413 ETH 买断、
    # 出价、询价表单与收藏条款），内嵌的解剖演示只能看固定文件、不能处理
    # 自己的数据，不是能直接用的工具（2026-11-16 16:00 轮补位条目实测）
    "black-pixel-1x1.vercel.app",
    # Glifa：macOS 桌面 Markdown 编辑器，需 Apple Silicon 与 macOS 15，
    # 付费下载（2026-11-16 16:00 轮补位条目，Product Hunt 页实测）
    "glifa.app",
    # 抽查确认不是在线工具（2026-11-16 16:00 轮，时间线补翻 7 条时实测）：
    # Papyras 是写手文章站（SEO 指南与评测合集），不是工具；
    # Findy 是 macOS 桌面文件搜索应用（11 美元买断，须装客户端）；
    # Kafkador 是自托管 Kafka 控制台，要 Docker / jar 或装桌面应用；
    # Fluid 是语音模型 API（按分钟计费的 speech-to-speech 模型页）；
    # Blomma 是手机应用（官网主推 Download the app），/orgs 是创始机构
    # 候补名单页，都没有能在浏览器里直接用的工具
    "papyras.com", "getfindy.xyz", "codestreamlab.com",
    "kugelaudio.com", "blomma.com",
    # Intelligent Eyewear：三星 AI 智能眼镜硬件产品页（Warby Parker /
    # Gentle Monster 联名，需配手机蓝牙使用，购买走零售店），不是工具
    # （2026-11-16 16:00 轮，时间线补翻时实测）；samsung.com 是硬件商城，
    # 不托管网页工具
    "samsung.com",
    # 抽查确认不是在线工具（2026-11-16 午后轮，浏览器实测）：Aven App Agent
    # 是给开发者把 AI 助手嵌进自家应用的 SDK，官网只有“选 SDK、注册任务”的
    # 接入指引，浏览器里无法直接使用，不是能直接用的工具
    "avenappagent.com",
    # 抽查确认不是在线工具（2026-11-16 晚间轮，浏览器实测）：Jensen World
    # 链到 mods.factorio.com，是 Factorio 游戏 mod 下载页，需要先装游戏
    # 再下载 mod 才能用，不是“在网站上就能用”的工具；标题门同步加 \bmod\b
    "mods.factorio.com",
    # 抽查确认不是在线工具（2026-11-16 21:00 轮，浏览器实测）：Candela 是
    # macOS 桌面应用（Apple Silicon + macOS 15，官网写“Free to try. Just
    # download it.”和“Move Candela to Applications”），须下载安装才能用，
    # 不是能在浏览器里直接用的工具；标题不露痕迹，标题门拦不住，域名封禁
    "livoni.software",
    # 抽查确认不是在线工具（2026-11-16 22:00 轮，本轮 9 条新品，5 条泄漏）：
    # Prettywhale 链到 VS Code Marketplace 扩展下载页；Offline PDF Desk
    # 链到 Gumroad 商品页（单个 HTML 文件，需下载才能用）
    "marketplace.visualstudio.com", "gumroad.com",
    # 抽查确认不是在线工具（2026-11-19 03:37 轮，浏览器实测）：The Calm
    # Creator Mastermind 链到 davidspinks.com/mastermind，是 400 美元/月的
    # 团体教练 Mastermind 售卖页（申请表 + 报名截止日期），没有能在浏览器
    # 里直接用的工具（2026-11-17 日报泄漏）
    "davidspinks.com",
    # 抽查确认不是在线工具（2026-11-19 03:37 轮，浏览器实测）：ToolJet
    # 首页 tooljet.com 是低代码平台营销页（客户 logo、证言、案例表，结尾
    # "Free to start" 注册引导），站上没有能直接用的工具；产品本身须注册
    # 云端账号或自托管部署，不是点开就能用的工具
    "tooljet.com",
    # 抽查确认不是在线工具（2026-11-19 05:07 轮，curl 实测）：AI Stack Lab
    # 首页是 AI 工具定价数据目录站（Tools/Compare/Best picks/Price changes，
    # 34 个工具的价格与快照），点开是工具清单与比价页，不是工具本身；计算器
    # 只是其中一个子栏目，热点榜链的是根地址目录页，按目录页封禁
    "ai-stack-lab-wherebeing.pages.dev",
    # 抽查确认不是在线工具（2026-11-19 05:07 轮，curl 实测）：Globus 是
    # 每日新闻产品（One edition a day of the stories that matter），iPhone
    # 应用（Designed for iPhone，Free for 7 days 试用），新闻 + 手机应用双重
    # 泄漏，标题里的 (iOS) 也露了痕迹
    "globus.earth",
    # 抽查确认不是在线工具（2026-11-21 01:37 轮，浏览器实测）：RMRFBench
    # 是 AI 智能体删文件基准的排行榜与结果报告站（排行榜、事件报告、方法论
    # 文章），站上跑不了评测、没有能直接用的工具，是报告/内容站；
    # FreeLLM 自称 "comprehensive directory of free LLM API"，是免费大模型
    # API 目录站（534 个模型清单与配置片段），目录页不收，Playground 只是
    # 其中一个子功能，热点榜链的是根地址目录页
    "rmrfbench.com", "freellm.net",
    # 抽查确认不是在线工具（2026-11-19 05:07 轮，curl 实测）：AI Portrait
    # Prompts 是 55 条人像提示词静态合集（Browse 55 tested prompts，复制粘贴
    # 进 ChatGPT/Midjourney/DALL-E），站上没有交互工具，同已封的提示词库
    # promptcrate.pages.dev，属内容站；What Is Localhost 是 localhost 互动
    # 科普指南（A field guide，分章讲解概念），没有能用的工具，同已封的互动
    # 科普页 scififutures / rshekhar.com/voyager，属内容站
    "aiportraitprompts.com", "whatislocalhost.com",
    # 抽查确认不是在线工具（2026-11-16 23:00 轮，浏览器实测本轮 6 条新品，
    # 3 条泄漏）：Codjiva 是 macOS/Windows/Linux 桌面应用（官网“Free, for
    # macOS, Windows and Linux”“Pick the build for your system”），须下载安装；
    # Localhost2137 是本地服务模拟运行时，`pnpm add -g localhost2137` 全局
    # 安装后跑在本机，不在浏览器里用；Flintty 是 Mac 终端应用（Apple Silicon
    # + macOS 13，官网“A Mac app”），须下载安装；三者标题均不露痕迹，标题门
    # 拦不住，域名封禁
    "codjiva.aay.sh", "localhost2137.dev", "flintty.com",
    # 抽查确认不是在线工具（2026-11-16 23:30 轮，浏览器实测本轮 4 条新品，
    # 3 条泄漏）：Mnestiq 是 Python SDK（pip install mnestiq，仪表盘只跑在
    # 本机），须下载安装才能用；InvoiceForge 链到 Codester 代码市集商品页
    # （25 美元 JS 库购买/下载页），不是能直接用的工具；两者标题均不露痕迹
    "mnestiq.com", "codester.com",
    # 抽查确认不是在线工具（2026-11-17 00:30 轮，浏览器实测本轮 9 条新品，
    # 2 条泄漏）：Torsher 是 Jellyfin/*ARR 平替的 Docker 自托管媒体服务，
    # 官网 demo 只是假数据的电视界面展示，真正工具须自己部署 Docker 才能用；
    # CoderBaba 是终端 AI 编程助手，`npm install -g coderbaba` 装到本机跑，
    # 不是能在浏览器里直接用的工具；两者标题均不露痕迹，标题门拦不住，域名封禁
    "torsher.app", "coderbaba.si",
    # 抽查确认不是在线工具（2026-11-17 02:40 CST 轮，浏览器实测本轮 7 条新品，
    # 4 条泄漏）：View（useview.app）是 Mac 桌面应用（Download for Mac，
    # "No browser in a trench coat"），须下载安装；Netrix 是 Windows 桌面
    # SSH/SFTP 客户端（Tauri，下载 .exe 安装包），须下载安装；Qube 是面向
    # 企业的加密会议室 SaaS 服务（卖的是会议服务与安全巡检，不是点开能用的
    # 工具本身）；wheelgap 是 PyPI 缺失 wheels 的 pip 安装索引页（须 pip
    # install 下载安装），不是能在浏览器里直接用的工具；四者标题均不露痕迹
    # 抽查确认不是在线工具（2026-11-17 03:00 CST 轮，浏览器实测）：
    # Lirico 是 Windows 桌面应用（官网“free · Windows 10 & 11”、
    # “Starts with Windows”“More info → Run anyway”），歌词显示在
    # 任务栏里，须下载安装才能用；标题只写“lyrics in your taskbar”，
    # 标题门拦不住，域名封禁；标题门同步加 \btaskbar\b
    "getlirico.pages.dev",
    # 抽查确认不是在线工具（2026-11-17 03:37 CST 轮，浏览器实测本轮 6 条新品，
    # 2 条泄漏）：Chisle 是 Claude Code 插件（npx 安装进编码助手才能用），
    # 不是能在浏览器里直接用的工具，标题门同步加 \bplugin\b；box.simular.ai
    # 是给 AI 智能体配云电脑的 MCP 服务（须注册账号、接 MCP 才能用），官网
    # 只是落地页与接入手册，不是点开能用的工具本身；两者标题均不露痕迹
    # 抽查确认不是在线工具（2026-11-17 05:40 CST 轮，浏览器实测本轮 5 条新到
    # 热点，4 条泄漏）：Compass Post 是 iPhone/Android 手游（官网“Scan with
    # your phone. iPhone opens the App Store, Android opens Google Play”），
    # 网页只有截图和介绍，须下载应用才能玩；Annotations 是 Obsidian 桌面应用的
    # 插件（社区插件页，须装 Obsidian 1.8.7+ 才能用），不是能在浏览器里用的
    # 工具；ShowStartup 是独立产品发布目录站（Browse launches/collections/
    # categories），本身是目录页，不是工具；sourcesli.st 是 Debian ISO 下载
    # 辅助站（标题即 Download Debian，核心是按架构列 ISO 下载按钮与校验和），
    # 成果就是下载文件，是下载页；四者标题均不露痕迹，标题门拦不住，域名封禁
    "compasspost.nodewires.com", "community.obsidian.md",
    "showstartup.com", "sourcesli.st",
    "chisle.jaypokale.me", "box.simular.ai",
    "useview.app", "netrix-console.com", "qube.so",
    # 抽查确认不是在线工具（2026-11-17 07:00 轮，浏览器实测本轮 5 条新品，
    # 3 条泄漏）：Standard Support 是“AI 智能体提交工单的约定”规范文档站，
    # 站上只有规范文本与参考实现说明，没有能直接用的工具；NOS 是 Rust 写的
    # x86-64 hypervisor 操作系统，/en/demo 是演示视频解说页，系统本身须装到
    # 裸机服务器上才能用；Brewlet 是 Kubernetes 运行时管理工具（git clone +
    # make build 装到集群里），不是能在浏览器里直接用的工具；三者标题均不露痕迹
    "standardsupport.dev", "nos-os.tech", "brewlet.sh",
    # 抽查确认不是在线工具（2026-11-17 13:37 CST 轮，浏览器实测本轮 3 条新到
    # 热点泄漏）：Fluxtail 链到 indielaunches.com 的项目页，是新品发布目录站
    # 的条目页，不是工具本身；FocusBlock 链到 Edge 扩展商店页，是浏览器扩展；
    # Blobby 是 Mac/Windows/Linux 桌面应用（官网“Download free”、项目存在
    # 本机文件夹），须下载安装才能用；三者标题均不露痕迹，标题门拦不住，域名封禁
    "indielaunches.com", "microsoftedge.microsoft.com", "useblobby.com",
    "bit.ly", "t.co", "goo.gl", "tinyurl.com", "ow.ly", "is.gd",
    "buff.ly", "cutt.ly", "rebrand.ly", "shorturl.at",
    # 抽查确认不是在线工具（2026-11-17 20:07 CST 轮，浏览器实测本轮 7 条新品，
    # 3 条泄漏）：Main Street Wealth 的 /datasets 是数据授权主题的文章页
    # （页脚自称 article、附 CSV/JSON 下载链接），不是能直接用的工具；
    # Agents in the Wild 的 /mcp-server 是 MCP 服务器接入手册（服务地址与
    # 工具说明），须接 MCP 客户端才能用，站上没有能直接搜的界面；
    # Save North Korea 的 /watch 是朝鲜动态监测仪表盘（导弹发射、朝中社
    # 露面、制裁名单），核心是时事新闻内容，不是工具；三者标题均不露痕迹
    "mainstreetwealth.ai", "agentsinthewild.co", "savenorthkorea.org",
    # 抽查确认不是在线工具（2026-11-17 22:37 CST 轮，补翻 13 条旧日归档
    # Product Hunt 条目时实测）：Cookie Away 是 Chrome 扩展官网（首页自称
    # free open-source Chrome extension，功能是自动拒 cookie 横幅），
    # 浏览器扩展不在收录范围；Degla AI 是无人机自主飞行系统（自然语言
    # 指令派无人机出任务、看演示视频），官网只是硬件产品展示站，不是
    # 浏览器里能用的工具；Nexus（trynexus.io）只有等候名单与预约演示，
    # 点开用不了工具本身；RankSpot 是给智能体用的 SEO/MCP 执行层
    # （mcp.rankspot.ai，接 Claude/ChatGPT 等智能体才能用），站上没有能
    # 直接用的工具；polyroom.ai 首页渲染后只有站名、无任何可用内容，
    # 无法验证为网页工具；五者标题均不露痕迹，标题门拦不住，域名封禁
    "cookieaway.com", "degla.ai", "trynexus.io", "rankspot.ai",
    "polyroom.ai",
    # 抽查确认不是在线工具（2026-11-18 08:07 CST 轮，浏览器实测本轮 2 条新到
    # 热点）：MacAudio 是原生 Mac 菜单栏音量混合器（官网“Native Mac volume
    # mixer … from your Mac's menu bar”），须下载安装才能用，不是浏览器里
    # 直接用的工具；首页是 JS 空壳（静态 HTML 仅 1.6KB），实测探查不到下载
    # 信号；标题“Best volume mixer on Mac?”也不露痕迹，标题门同步加
    # \bon\s+mac\b；域名封禁
    "macaudio.app",
    # 抽查确认不是在线工具（2026-11-17 23:07 CST 轮，浏览器实测本轮 10 条新品，
    # 3 条泄漏）：Flexible Sim 链到 JetBrains Marketplace 插件页，是 JetBrains
    # IDE 插件（须装 IDE 与 Julia/Python/OpenModelica 运行时），不是浏览器里
    # 能直接用的工具；Darkroom Finder 是摄影暗房目录站（按城市/邮编找暗房），
    # 本身是目录页；Kompromat 是开源协议 + CLI 工具（须安装 kompromat 命令行），
    # 不是能在浏览器里直接用的工具；三者标题均不露痕迹，标题门拦不住，域名封禁
    "plugins.jetbrains.com", "darkroomfinder.org", "kompromat.sh",
    # 抽查确认不是在线工具（2026-11-18 00:07 CST 轮，浏览器实测本轮新品）：
    # Quebec（quebec.yarn.so）是纯 API 平台：curl 建 key、按音频时长付费、
    # 调 /transcribe 接口拿词级时间戳，站上没有能在浏览器里直接用的工具，
    # 同 TokLab；Alloy CSS 示例页（alloyhtml.com/example.html）是 CSS 组件
    # 库的静态演示页（自述“假数据、无 JavaScript”），库本身须安装使用，
    # 页上没有能用的工具；两者标题均不露痕迹，标题门拦不住，域名封禁
    "quebec.yarn.so", "alloyhtml.com",
    # 抽查确认不是在线工具（2026-11-18 00:07 CST 轮，复查时间线旧条目）：
    # Mirrors（mirrors.dev）是给生产环境 AI 智能体做上下文编排的基础设施，
    # 须 npm install mirrors-sdk 并用 API key 在自己的智能体代码里接 API/MCP，
    # 核心功能不在站内完成，同已封的纯 API/SDK 类（uniroute、usestring.ai、
    # flowmails.net）；网页后台只是规则管理，不能单独算“完全在网站上就能用”
    "mirrors.dev",
    # 抽查确认不是在线工具（2026-11-18 01:07 CST 轮，浏览器实测本轮 3 条新到
    # 热点，3 条泄漏）：Barnacle 是手机 AI 应用（Picture in Picture 浮窗助手，
    # 官网主推 Join the waitlist，须装手机应用才能用），不是浏览器里直接用的
    # 工具；Confidential Cloud 的链接本身就是控制台登录页（须注册登录才能进
    # 实例管理），且是云虚拟机服务，不是点开能用的工具；Kerala Botanics 是
    # 阿育吠陀护肤品网店（所谓“给 AI 购物智能体的谜题”只是店内噱头），
    # 是电商站不是工具；三者标题均不露痕迹，标题门拦不住，域名封禁
    "barnacle.qa", "confidential.ai", "keralabotanics.com",
    # 抽查确认不是在线工具（2026-11-18 01:07 CST 轮，浏览器实测本轮 1 条新到
    # 时间线条目）：Cala Radio 的链接是硬件收音机制作日志长文（回收 Beoplay
    # A1 扬声器单元、自制铝壳胡桃木机身的实体收音机，页内无电台列表、无播放
    # 控件、无音频流，Files 一节全是 .FPD/.STL/.PDF 设计文件与 GitHub 零件
    # 清单），收听须拥有或自制实体设备，不是能在浏览器里直接用的工具；
    # 标题不露痕迹，标题门拦不住，域名封禁
    "cala.studio",
    # 抽查确认不是在线工具（2026-11-18 01:37 CST 轮，浏览器实测本轮 8 条新品，
    # 2 条泄漏）：Atlas 是给 AI 智能体做网页上下文的确定性编译基础设施，
    # 核心是 workspace + API key 的 REST API / SDK / MCP（同已封的 TokLab、
    # uniroute.app 等纯 API 平台），Playground 只是工作台入口、点开仍是落地页，
    # 没有免登录能直接用的工具；athrael.net/courses/gpu-inference 是一门
    # GPU 推理短课程（章节课文 + 可运行图解），内容站而非工具站；两者标题
    # 均不露痕迹，标题门拦不住，域名封禁
    "atlas-compiler.com", "athrael.net",
    # 抽查确认不是在线工具（2026-11-18 08:37 CST 轮）：Roxy Island 是 Roblox
    # 平台上的教育游戏，点 Play 要下载安装 Roblox 客户端才能玩，不是“完全
    # 在网站上就能用”的浏览器工具；标题不露痕迹，标题门拦不住，域名封禁
    "roblox.com",
    # 抽查确认不是在线工具（2026-11-18 12:07 CST 轮，浏览器实测本轮热点）：
    # TEA Ecosystem 是 Elm 架构各语言实现的框架目录站（Featured / Recently
    # added 列表，链出到各框架仓库与官网），站上没有能直接用的工具，本身
    # 是目录页；标题不露痕迹，标题门拦不住，域名封禁
    "tea.rinn7e.com",
    # 抽查确认不是在线工具（2026-11-18 13:07 CST 轮，浏览器实测本轮新到
    # 热点）：Motif 是实体贴纸追踪器硬件产品的预售页（Reserve for $1、
    # 纸一样薄的追踪器贴在水杯上），须购买硬件才能用，站上没有能在浏览器
    # 里直接用的工具；标题只写“a tracker thin enough to be a sticker”，
    # 不露硬件痕迹，标题门拦不住，域名封禁
    # 抽查确认不是在线工具（2026-11-18 15:37 CST 轮，浏览器实测本轮 54 条
    # 新到里的 12 个可疑站 + 描述审 3 个）：aiwizard.ai 是 10,558 个工具的
    # 目录页；aiagentsinfo.com 是 513 个 AI 工具目录（角落虽有 Free tools
    # 子工具，但首页本身是目录）；fossdesk.com 是开源软件替代方案文章站；
    # zzlcs.xyz 是星露谷指南站（首页底部虽有作物成熟计算器，但主内容是
    # 种植/钓鱼/采矿指南）；workbuddyskill.com 是 WorkBuddy Skill 目录大全；
    # potatopleaseguide.online 是 88 篇《Potato Please》游戏指南库；
    # haira.ai 是 AI 招聘 SaaS 营销页，主功能须注册（仅 3 问题演示面试可
    # 免注册体验）；xpodcasts.com 是 X 长视频播客聚合站，只能看视频；
    # hostdealspro.com 是 Hostinger 优惠券/评测站（Savings Meter 与 Plan
    # Finder 只是购物辅助小部件）；momentscope.com 是直播摄像头聚合站，
    # 实测时无直播内容可看；toapis.com 与 ai.bayunzi.shop 是纯 API 平台/
    # API Key 分发服务（同已封的 TokLab）；ghost-prompter.com 是桌面提词器
    # 应用（描述自述 Desktop teleprompter）；标题均不露痕迹，标题门拦不住，
    # 域名封禁
    "aiwizard.ai", "aiagentsinfo.com", "fossdesk.com", "zzlcs.xyz",
    "workbuddyskill.com", "potatopleaseguide.online", "haira.ai",
    "xpodcasts.com", "hostdealspro.com", "momentscope.com",
    "toapis.com", "ai.bayunzi.shop", "ghost-prompter.com",
    "motif.blog",
    # 抽查确认不是在线工具（2026-11-18 18:07 轮，40 条缺翻译 Product Hunt
    # 条目逐条查站后封禁）：OffiAI 是 macOS 桌面应用（须从 GitHub 下载
    # 安装）；VB Notes 是桌面/手机笔记应用（须下载安装）；Kokonut UI 是
    # 开源 React 组件库（须用命令行装进自己项目才能用）；Horef Rings 是
    # Apple Watch/iPhone 应用（App Store 下载）；Replay 是 Mac 桌面录制
    # 应用（一次付费下载）；Spiik 是 iPhone/Mac 录音应用（须下载安装）；
    # kwatch 须装进自己的 Kubernetes 集群（自托管）；uRun 是实时模型
    # API 平台（须写代码调 API）；Zode 须装命令行客户端、开云端虚拟机
    # 给编程智能体干活；AppSumo 是团购销售页（Boost.space AgentOS 链到
    # 其销售页，工具真址不在此）；Templify 是手机视频模板应用（首页主
    # 推 1M+ Downloads）；S.Space 首页只有 "Getting ready"，暂未开放；
    # readywhen 是等候名单 + 活在邮件/WhatsApp 里的助理（点开用不了）；
    # Kairos 是 iPhone/iPad 个人数据分析应用（HealthKit 路径须 iPhone）；
    # SaaS Toolkit 的 /mcp 页是 MCP 接入说明（须先有账号再到 Claude /
    # ChatGPT / Cursor 里配置），不是点开即用的工具
    "offiai.app", "vbnotes.com", "kokonutui.com", "horef.app",
    "tryreplay.online", "spiik.io", "kwatch.dev", "urun.sh",
    "zode.dev", "appsumo.com", "templify.ai", "s.space",
    "readywhen.ai", "yourkairos.io", "saastoolkit.ai",
    # Waldo（2026-11-18 18:07 轮，浏览器实测）：wherobots.com/products/waldo/
    # 是营销/产品介绍页，页上对话界面只是 "a replay of a real Waldo session"
    # 的演示回放；真用须有 Wherobots Cloud 账号并接好数据目录/湖仓（S3
    # Iceberg 表、Databricks Unity Catalog 等），不是无需准备即可在浏览器
    # 里直接用的独立工具
    "wherobots.com",
    # Gridline（2026-11-18 23:07 CST 轮，curl 实测本轮新到时间线条目）：
    # gridlinegpu.com 是微调/批量推理 API 平台（"One API for fine-tuning,
    # distillation and batch inference"，OpenAI-compatible），站上只有
    # signup、文档与示例，没有能在浏览器里直接用的工具；同已封的 TokLab、
    # Quebec、atlas-compiler.com 等纯 API 平台；标题不露痕迹，标题门拦不住，
    # 域名封禁
    "gridlinegpu.com",
    # MIT 邮件课程（2026-11-19 00:07 CST 轮，curl 实测热点榜条目）：
    # htmaa.clarkdinnison.com 是 100 天邮件课程报名页，填邮箱后每天收一封
    # 课，站上没有能直接用的工具；标题门同步加 email course 规则
    "htmaa.clarkdinnison.com",
    # Dating Republican（2026-11-19 01:07 CST 轮，浏览器实测新到时间线条目）：
    # datingrepublican.com 是约会交友服务站（州/城市指南、约会建议文章、
    # 交友应用对比），不是转换器/计算器/编辑器这类点开即用的工具网站
    "datingrepublican.com",
    # ClearOffice Hub（2026-11-19 04:07 CST 轮，浏览器实测热点榜第 2 条）：
    # clearofficehub.com 是 Windows 桌面应用（FAQ 自述 "a Windows desktop
    # application"，"only available for Microsoft Windows"），须下载安装，
    # 不是点开就能在浏览器里直接用的工具网站；标题与摘要均不露痕迹，
    # 标题门与实测信号（缺 desktop application 信号）均拦不住，域名封禁
    "clearofficehub.com",
    # 抽查确认不是在线工具（2026-11-18 20:37 轮实测）：Beat（gobeat.ai）
    # 链到的就是 /auth/login 登录页，须 Google/邮箱登录且需邀请才能用，
    # 点开没有任何能直接用的工具；登录墙实测信号未覆盖，域名封禁
    "gobeat.ai",
    # 抽查确认不是在线工具（2026-11-19 05:37 CST 轮实测）：Eventkiwi
    # 是纯 API 事件上报与定时报告服务（须把 API 接进自己的应用、等邮件/
    # Telegram 定时报告），站内无点开即用的浏览器工具；同已封的 TokLab、
    # voxoria（纯 API 平台）；实测信号未覆盖，域名封禁
    "eventkiwi.com",
    # 抽查确认不是在线工具（2026-11-19 05:37 CST 轮实测）：Springrep
    # 是 Rust B-rep CAD 内核代码库，官网是文档页（"add the crate"、
    # cargo run），须下载安装 Rust/cargo 才能用，不是浏览器工具
    "springcraft-ai.github.io",
    # 抽查确认不是在线工具（2026-11-19 07:07 CST 轮实测）：Toggles
    # 是靠分析数据玩的开关小游戏（"Play a short season"、Leaderboards、
    # Daily Dispatch），站内简介自写"免费小游戏"；游戏不是工具，
    # 标题不露痕迹，实测信号拦不住，域名封禁
    "toggles.codewalkers.net",
    # 抽查确认不是在线工具（2026-11-19 07:07 CST 轮实测）：Space-Core
    # 是浏览器 MMO 太空游戏（首页自述 "a space game in your browser"）；
    # 游戏不是工具，域名封禁
    "space-core.at",
    # 抽查确认不是在线工具（2026-11-19 07:07 CST 轮实测）：Now It's by You
    # 是一首民谣，AI Song Contest 2026 决赛作品，可下载 FLAC 录音；
    # 艺术/歌曲项目不是工具，域名封禁
    "now.itsby.you",
    # 抽查确认不是在线工具（2026-11-19 07:07 CST 轮实测）：Escape Rooms
    # for Lateral Thinkers 是网页密室逃脱游戏（"Dr. Wünderbach's Escape"，
    # 16 间解谜房）；游戏不是工具，域名封禁
    "enigma-game.specr.net",
    # 抽查确认不是在线工具（2026-11-19 07:37 CST 轮实测）：Ring Velocity
    # 是水环物理小游戏（首页自述 "a calming physics game inspired by the
    # classic water ring toy"）；游戏不是工具，域名封禁
    "ringvelocity.com",
    # 抽查确认不是在线工具（2026-11-19 07:37 CST 轮实测）：FairBake
    # Signature 是编码智能体评测榜单/报告页（各模型得分排行榜，只能浏览
    # 与排序），站上没有能直接用的工具；榜单/报告不是工具，域名封禁
    "fairbake.dev",
    # 抽查确认不是在线工具（2026-11-19 09:37 CST 轮实测）：WalkThisPlan
    # 是给建商做的代建服务（发平面图、7 天后交付 360° 样板间），访客在
    # 浏览器里用不了任何工具，服务落地页不是工具站；ngTestFoundry 是
    # VS Code 扩展（官网 "Install from Marketplace"），须下载安装才能
    # 用；两者标题均不露痕迹，标题门拦不住，域名封禁；探查信号同步加
    # vscode_extension 拦此类扩展落地页
    # 抽查确认不是在线工具（2026-11-19 10:07 CST 轮实测）：ADE Index
    # 是 975 个 agentic coding 工具的排名索引/目录站（分类榜单、对比
    # 页，只能浏览与排序），站上没有能直接用的工具；目录站不是工具，
    # 域名封禁
    "adeindex.com",
    "walkthisplan.com", "sshyeri.github.io",
    # 抽查确认不是在线工具（2026-11-19 13:07 CST 轮，浏览器实测本轮热点榜第 1 条）：
    # 1Lookup 是电话/邮箱/IP 数据 API 平台（"76 data products on one API key"，
    # 须注册拿 API key、按信用点数付费调接口），首页只有 signup、文档与示例，
    # 没有能在浏览器里直接用的免费工具；同已封的 TokLab、Quebec、
    # atlas-compiler.com 等纯 API 平台；标题不露痕迹，标题门拦不住，域名封禁
    "1lookup.io",
    # 抽查确认不是在线工具（2026-11-19 每日流量检查轮自查，本轮热点榜）：
    # Crabble 是浏览器单词游戏（标题自写 "a free browser word game"，
    # 有 bot 段位与赛后复盘）；Goaler 是每日足球竞猜游戏（"a daily
    # football grid you can send to a friend"）；游戏不是工具，域名封禁
    "crabble.club", "goaler.net",
    # 抽查确认不是在线工具（2026-11-20 12:07 CST 轮，本轮热点榜新到
    # 第 17 位）：Modern Combat 2 是第一人称射击游戏，标题自写
    # "I got Modern Combat 2 – Black Pegasus running in a browser"；
    # 纯游戏不是工具，按 11-18 以来做法域名封禁
    "mc2.aryanbaburajan.com",
    # 抽查确认不是在线工具（2026-11-20 13:07 CST 轮，本轮热点榜新到）：
    # GhostFleet 是海战棋游戏（标题自写 "A Battleship game with an
    # advanced AI opponent"）；Night Shift 是浏览器事件响应游戏（标题
    # 自写 "A browser based incident response game"）；Jam 是协作音乐
    # 制作游戏（标题自写 "a collaborative music making game"）；纯游戏
    # 不是工具，按 11-18 以来做法域名封禁
    "ghostfleet.in", "play.snowops.net", "jam.resonantdsp.com",
    # 抽查确认不是在线工具（2026-11-19 15:07 CST 轮，本轮 Ignlab 批量新到
    # 47 条，人工审摘要+浏览器实测可疑项）：NAVSMAP 是 AI 工具目录站
    # （"Find AI tools, workflows, MCP servers"，只能浏览检索工具列表，
    # 本轮已进热点榜）；Warta Kopi 是印尼语咖啡店点评媒体站（菜单、
    # 价格、氛围测评文章）；VersusDeck 只发软件对比文章（"publishes
    # short, cite-ready tool comparisons"，无交互工具）；TechXaro
    # Abandoned Form Recovery 是 WordPress 插件（"Free to download"，
    # 须装到自己的 WordPress 站才能用）；VibeCamz 是在线速配约会、
    # Dewdrop 是盲约应用、Umingle/Chat Met Vreemden 是与陌生人 1 对 1
    # 视频聊天、Voxxy 是与陌生人随机语音通话——交友/陌生人社交平台
    # 不是工具；以上标题均不露痕迹，标题门拦不住，域名封禁
    "navsmap.com", "wartakopi.net", "versusdeck.com",
    "abandonedformrecovery.techxaro.com",
    "vibecamz.com", "dewdrop.date", "umingle.video",
    "chatmetvreemden.live", "voxxy.app",
    # 抽查确认不是在线工具（2026-11-19 20:37 CST 轮，浏览器实测本轮新到
    # 热点榜条目）：Lattice 是开源 Obsidian Publish 平替，须 clone 仓库、
    # 把 vault 拷进项目目录、改 publish.config.json 后跑 npm run dev，
    # 是自托管/须本地安装的工具，站上只有发布效果演示，没有能在浏览器
    # 里直接用的工具；标题不露痕迹，标题门拦不住，域名封禁
    "lattice.jacobg.co",
    # 抽查确认不是在线工具（2026-11-20 00:07 CST 轮，浏览器实测本轮新到
    # 热点榜条目）：Oyasoo 是 iPhone 睡眠追踪应用（"Free to download"、
    # App Store 徽章、"iPhone with iOS 26 or later"），须下载安装，
    # 不是能在浏览器里直接用的工具；I Did My Own（idmo.app/own）是
    # 知名应用的开源重制版目录页（"Pick a product to see the open-source
    # versions people have built"），只能浏览产品列表，不是工具本身；
    # 以上标题均不露痕迹，标题门拦不住，域名封禁
    "oyasoo.com", "idmo.app",
    # 抽查确认不是在线工具（2026-11-20 03:07 CST 轮，浏览器实测本轮新到
    # 热点榜条目）：Designshippers 是设计工作室的服务售卖页（"Design
    # Engineering as a Service"，$10,000/月包月制设计服务），站上没有能
    # 直接用的工具，同已封的网页设计公司页 ibertechsolutions.co.uk；
    # 标题不露痕迹，标题门拦不住，域名封禁
    "designshippers.com",
    # 抽查确认不是在线工具（2026-11-20 02:07 CST 轮，实测本轮热点榜条目）：
    # Maglev 是给 AI Agent 用的 MCP 服务器（"one key for every agent
    # tool"、"692 tools from 39 providers through one API key"、按调用
    # 计费），须配 MCP 客户端、拿 API key 调接口，浏览器里没有能直接
    # 用的工具；同已封的 TokLab 等纯 API 平台；标题不露痕迹，标题门
    # 拦不住，域名封禁
    "maglev.sh",
    # 2026-11-19 20:07 CST 轮实测封禁（HN Show 新到混入热点榜）：
    # publicrows.com 是 Apify 数据 actor 的目录/售卖站（按行付费的数据
    # 产品目录），不是能直接用的工具；标题“pay-per-row data actors”
    # 不露目录痕迹，域名封禁
    "publicrows.com",
    # 抽查确认不是在线工具（2026-11-20 10:07 CST 轮，浏览器实测本轮新到
    # 热点榜条目）：SlotVFX 是 2D 游戏特效桌面编辑器（官网“Desktop
    # editor app”“SlotVFX Desktop runs on macOS and Windows”“Download
    # the build for your platform”），须下载安装才能用，导出还要付费计划；
    # 不是能在浏览器里直接用的工具；标题不露痕迹，标题门拦不住，域名封禁
    "slotvfx.com",
    # 2026-11-20 03:07 CST 轮（本轮新到混入热点榜）：fossil.chungy.name
    # 是 Fossil 代码仓库托管站，Ufatfs 链到它上面的 README.md 文档页；
    # Fossil 托管的是源码仓库，不是能直接用的工具站，同已封的
    # github.com / gitlab.com；标题门同步加“file system”规则
    "fossil.chungy.name",
    # 抽查确认不是在线工具（2026-11-20 11:37 CST 轮，浏览器实测本轮
    # 热点榜 2 条泄漏）：Mindie（getmindie.app）是 WhatsApp/Telegram
    # 里的提醒机器人，工具在聊天软件里用，不在网站上；站上只有一个
    # “试一试”演示小部件，核心功能须加 WhatsApp 好友、注册并付费，不
    # 是“完全在网站上就能用”；Jev（checks.dorbit.ai）是 GitHub App，
    # 自动打标签要装到仓库上才能用（$5/月/账号），站上只有免登录的标签
    # 预览演示，不是工具本身；两者标题均不露痕迹，标题门与实测都拦不
    # 住，域名封禁
    "getmindie.app", "checks.dorbit.ai",
    # 抽查确认不是在线工具（2026-11-20 11:37 CST 轮，浏览器实测补位条
    # 目）：EvenLeads /gigs 页是每日兼职线索邮件提醒的注册落地页，页上
    # 只写“过去 24 小时找到 9 条请求”、没有可浏览的线索列表，真正的产
    # 品是每天一封邮件 + 付费仪表盘（€39），线索本身不在站上能直接用；
    # 同已封的售卖页/落地页，域名封禁
    "evenleads.com",
    # 抽查确认不是在线工具（2026-11-20 11:37 CST 轮，浏览器实测补位条
    # 目）：PadSpan /demo 只是样品房子的固定演示（假人、假设备、看房间
    # 位置），追踪自己的设备须装 Home Assistant 集成 + 蓝牙硬件，工具
    # 本身不在网站上能用；同已封的 Torsher（假数据演示 + 须自托管部署）
    # 与 CodeGraphy（固定示例预览），域名封禁
    "traks.ca",
    # 2026-11-20 15:07 CST 轮：Ignlab 大批量上新 47 条里抽查出的泄漏，
    # 描述与实测均确认不是在线工具：
    # 成人/随机陌生人视频聊天簇（同批 5 个，描述直言 "Pick a girl"、
    # "Freaky video chat with a random stranger"、按币收费匹配）：
    "videochatchicks.live",
    "freakyvideochat.com",
    "cafevideochat.video",
    "foxvideochat.chat",
    "nosignupchat.com",
    # PlayGD：在线赌场（Golden Dragon slots、jackpots，注册领 welcome bonus）
    "playgd.cc",
    # Lovart Info：Lovart 的教程/指南/比价站，不是工具本身
    "lovart.info",
    # SR22 Direct：SR22 保险销售页；Glo Suppliers：中国供应商目录平台；
    # Apollo Rockets：社交网络社区（"general social community"）
    "sr22direct.com",
    "glo-suppliers.com",
    "apollorockets.com",
    # SourceSEO：SEO 代运营服务（Service-as-a-software，52+ agents 代做），
    # 不是点开就能用的工具；AiTz：AI 工具目录站（12,000+ AI Tools）
    "sourceseo.ai",
    "aitz.site",
    # SaaSVerdict：AppSumo 软件测评/比价内容站；只拦该子域，
    # mercaio.brainer.one 是工具，仍可收
    "saasverdict.brainer.one",
    # 2026-11-20 15:07 CST 轮续查（同批新到）：
    # ListPak：巴基斯坦商业目录站（企业/职业/招聘目录），目录页不上榜
    "listpak.com",
    # KimiSeek："One API for China's leading AI models"，纯 API 平台，
    # 同已封的 TokLab
    "kimiseek.app",
    # Caja Clara：卖 US$7 的 Excel 记账文件（"Archivo .xlsx editable"），
    # 是下载售卖页不是在线工具；只拦该 chatgpt.site 子域
    "caja-clara-ventas.futurebay5.chatgpt.site",
    # 2026-11-23 01:07 PST 轮抽查封禁（HN Show 新到，混入当日时间线）：
    # ATUF Explorer 是量子引力理论的交互式科普长文（"Lean Formalization
    # of Quantum Gravity"），带滑块演示的叙事文章，不是能直接用的工具；
    # 只拦该 chatgpt.site 子域
    "atuf-explorer.toughlute16.chatgpt.site",
    # 2026-11-20 16:07 CST 轮抽查封禁（本轮新到，4 条）：
    # Docker：docker.com 首页是容器平台营销页，产品须下载 Docker Desktop
    # 才能用，不是浏览器里能直接用的工具
    "docker.com",
    # Samiksa：研究 agent 等候名单页（"Join the waitlist"），站内无可用工具，
    # 同已封的 xargaar-tools.com
    "samiksa.app",
    # isu-bench：编码 agent 基准的成绩/规则报告页，基准本身只以机器镜像
    # 分发（须下载），站内没有能直接用的工具
    "isu-bench.trasta.dev",
    # UndoGuard："Semantic Undo & Rollback API"，纯 API 平台，同已封的
    # TokLab；首页沙箱只是 API 演示，不是独立工具
    "undoguard.vercel.app",
    # 2026-11-20 16:07 CST 轮续查封禁（11 月 19 日到站、仍在时间线里的 3 条）：
    # Rox：症状追踪是 iPhone 应用（"download ios app"），站内无网页工具
    "talktorox.com",
    # Baby's Day In："Baby Monitor App for iPhone and Android"，手机应用，
    # 不是浏览器里能直接用的工具
    "babysday.in",
    # Saparo：AI 购物 agent，但站内唯一入口是 "Add to Chrome"（三次均链
    # 到 Chrome Web Store），产品以浏览器扩展形态交付，不收扩展
    # 抽查确认不是在线工具（2026-11-20 16:37 CST 轮，浏览器实测补查
    # 11 月 10 日归档旧条目）：LOMI 是 Android 离线 AI 应用，官网
    # “Get LOMI”第一步就是“Install the LOMI application securely from
    # the Google Play Store”，须下载安装才能用，不是能在浏览器里直接用
    # 的工具；标题“Run AI models locally on your Android device”不露
    # 痕迹，标题门拦不住，域名封禁
    "lomi.ra-studio.dev",
    # 抽查确认不是在线工具（2026-11-20 22:37 CST 轮，实测本轮新到条目）：
    # HN DOCS（hndocs.org）是“关于 Hacker News 热门故事的纪录片”视频
    # 内容站：首页只有纪录片列表与投票，没有能直接用的工具；同已封的
    # 文章/视频内容站，标题不露痕迹，域名封禁
    "hndocs.org",
    "saparo.ai",
    # 抽查确认不是在线工具（2026-11-20 23:07 CST 轮，浏览器实测本轮新到条目）：
    # bidfor.dev/jamie 是个人求职页（“邀请公司出价雇我”，简历+经历+出价表单），
    # 不是能直接用的工具；murmurcomputing.ai 是分布式算力产品，官网第一步就是
    # “Install Murmur by asking your AI assistant”，须在自家设备上安装客户端
    # 才能用，不是浏览器里直接用的工具
    "bidfor.dev", "murmurcomputing.ai",
    # 抽查确认不是在线工具（2026-11-21 02:07 CST 轮，curl 实测本轮新到条目）：
    # SKV Network 是 AI 智能体的社交网络 / 托管 MCP 记忆服务，官网写的是
    # “Connect any agent over MCP”，须把自家智能体接进 MCP 才能用，浏览器里
    # 没有访客能直接用的工具；同已封的 TokLab 等纯 API/MCP 平台，域名封禁
    # 抽查确认不是在线工具（2026-11-21 06:07 CST 轮，curl 实测本轮热点条目）：
    # CivicJobs 是欧盟机构职位招聘板，首页是职位列表与筛选（目录/列表站），
    # 唯一工具属性是附带的 Salary Calculator，不是能直接用的工具本身，域名封禁
    "civicjobs.eu",
    "skv.network",
    # tamnd.com：数学学习路径站（riemann.tamnd.com/learn、math2.tamnd.com），
    # 是按阶段读的教学内容页，没有能直接用的工具；2026-11-21 14:07 CST 轮
    # 热点第 N 条 "Show HN: Riemann Hypothesis Proof for Learners" 实测为
    # 学习指南长文，按文章类泄漏封域名
    "tamnd.com",
    # shayon.work/riemann：黎曼猜想互动讲解长文（滑块/图表只是文内演示），
    # 本质是读的文章，不是能拿来做事的工具；2026-11-21 14:07 CST 轮实测，
    # 与同轮 tamnd 同类，按文章类泄漏封域名
    "shayon.work",
    # riemann-quest.pages.dev：黎曼猜想互动讲解长文（"Read this first"、
    # 12 个章节按顺序读、号称 10,000 小时阅读马拉松），滑块/图表只是文内
    # 演示，本质是读的文章；2026-11-24 10:37 CST 轮热点第 3 条实测，
    # 与 tamnd、shayon.work 同类，按文章类泄漏封域名
    "riemann-quest.pages.dev",
    # minard1812.org：拿破仑征俄地图的动画致敬页（动画+旁白+音乐），
    # 是看的多媒体内容，没有能直接用的工具；2026-11-21 14:07 CST 轮实测
    "minard1812.org",
    # loopseo.org：自托管程序化 SEO 工具（官网自称 "Self-hosted programmatic
    # SEO"），须接自家 WordPress 站 + 自带 API 密钥才能跑，工具本身不在网站
    # 上能直接用；2026-11-21 15:37 CST 轮热点第 5 条实测，标题不露痕迹，域名封禁
    "loopseo.org",
    # freeaigo.com：FreeAI Go 是免费 AI 工具目录站（首页自称 "A SMALL
    # DIRECTORY"，30 条收录全是链到各家官网的卡片，比较/短清单也只是帮
    # 你选工具，AI 处理都在提供方网站完成），站上没有能直接用的工具，
    # 属目录站而非工具站；2026-11-21 20:37 CST 轮实测，热点第 1 条，域名封禁
    "freeaigo.com",
    # desearch.ai：Desearch 是面向 AI 智能体的联网搜索 API（首页 "One search
    # API for AI agents"，按千次调用计费，须注册拿 key、绑卡才有 $5 额度，
    # 接入方式是 REST API / SDK / MCP），站上没有给普通人直接用的工具，
    # 同已封的 TokLab、voxoria.ai 等纯 API 平台；2026-11-21 20:37 CST 轮
    # 实测，热点第 3 条，域名封禁
    "desearch.ai",
    # bethe.one：链到的页是 iOS 应用内 AI 教练功能的介绍/营销长文，
    # 工具本身在应用内，网页点开用不了；2026-11-21 10:37 PST 轮实测，
    # 热点第 3 条，域名封禁
    "bethe.one",
    # onegtmlab.dev：/tool-directory 是 GTM 工具目录站（64 个工具的
    # API 评测、对比与术语表合集，带搜索过滤），本身不是能直接用的
    # 工具，是目录页；2026-11-21 12:07 PST 轮实测，热点第 1 条，域名封禁
    "onegtmlab.dev",
    # 2026-11-22 05:07 CST 轮人工审 Ignlab 新到描述封禁：minanggadang.com
    # 是印尼 Padang 餐厅官网（只展示评分地址），不是工具；shop.anagnoraxis.com
    # 是出售 ChatGPT 订阅的商店页；aivipzhan.com 是 ChatGPT Plus/Pro 代充商店；
    # hubtech.pk 是巴基斯坦诊所网站改版服务商页面；ia.university 是西班牙语
    # 在线 AI 课程站；fieldguidetobots.com 是付费 PDF 指南售卖页（7 份指南
    # 均在 Gumroad 标价 $12–20 下载，站上没有直接能用的工具），本轮热点有它
    "minanggadang.com", "shop.anagnoraxis.com", "aivipzhan.com",
    "hubtech.pk", "ia.university", "fieldguidetobots.com",
    # 2026-11-22 06:07 CST 轮人工审 HN Show 新到 4 条封禁 3 条：
    # johannes.plunien.com/KeyLayers 是 macOS 桌面应用（须下载安装，
    # 标题不露痕迹，标题门拦不住）；databasedmcp.com 是远程 MCP 服务器，
    # 纯 API 平台（工具给智能体经 API 用，浏览器里只有只读 SQL 看板，
    # 同 TokLab 口径）；typeonce.games/tabletop-champions 是纯浏览器
    # 赛车游戏，无工具属性（11-18 起纯游戏当泄漏封，待用户定游戏口径）
    "johannes.plunien.com", "databasedmcp.com", "typeonce.games",
    # 2026-11-22 06:37 CST 轮人工审 HN Show 新到 3 条封禁 3 条：
    # app.supademo.com/video/... 是 Supademo 演示视频页（录制的产品演示
    # 视频，点开看视频不是用工具）；itch.io 是游戏商店页（本条是浏览器
    # 迷宫射击纯游戏，按 11-18 以来封纯游戏的做法处理；游戏收录口径仍待
    # 用户定）
    "supademo.com", "itch.io",
    # 2026-11-22 06:37 CST 轮时间线自查补封的纯游戏（均浏览器实测确认，
    # 按 11-18 以来封纯游戏的做法处理；游戏收录口径仍待用户定）：
    # hackerllion.com 是每日冷知识竞答游戏；dlearena.com 是每日解谜游戏
    # 合集站；outpostracer.com 是 PS1 画风街机赛车游戏；plazzlegame.com
    # 是每日寻路解谜小游戏；quiettrivia.com 是 Krillion 答案/提示/解算
    # 站（游戏伴生内容，不是独立工具）；dailyplaynotes.com 是每日 trivia
    # 游戏 Wonderhop 的攻略站；trichroma.namirsab.dev 是解谜平台跳跃游戏
    "hackerllion.com", "dlearena.com", "outpostracer.com",
    "plazzlegame.com", "quiettrivia.com", "dailyplaynotes.com",
    "trichroma.namirsab.dev",
    # 2026-11-22 21:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # mathpuzzle.org 是每日数学猜谜纯游戏（Wordle 式拼算式，另有数独/
    # 纵横字谜/脑筋急转弯），按已定游戏口径（纯游戏一律拦）封禁；
    # allgameslive.com 是体育实时比分 + 新闻内容站（比分、赛程、新闻
    # 文章），是看内容不是用工具，按只收工具网站标准封禁
    "mathpuzzle.org", "allgameslive.com",
    # 2026-11-22 21:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # guessrgames.com 是每日猜谜游戏合集站（地理问答、数独、数独变体、
    # 每日挑战 + 排行榜），全站都是游戏，按游戏口径封禁
    "guessrgames.com",
    # 2026-11-22 22:07 CST 轮热点榜自查补封（MakerHunt 描述 + 标题确认）：
    # play1beat.com 是纯音乐节奏游戏（四轨道点按热门歌曲），本轮混进
    # 热点榜第 5、精选，按游戏口径（纯游戏一律拦）封禁整个域名
    "play1beat.com",
    # 2026-11-22 22:07 CST 轮时间线自查补封（浏览器实测确认）：
    # strategoga.me 核心是 Stratego 棋盘游戏在线对战（加载第三方
    # play.stratego.com 的游戏框），附带的段位比较小工具只是配角，
    # 整站以玩游戏为主，按游戏口径封禁整个域名
    "strategoga.me",
    # 2026-11-22 01:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # tebrun.io 是 80 年代街机赛车纯游戏（15 关、计分、排行榜），
    # 整站就是游戏本身，按已定游戏口径（纯游戏一律拦）封禁整个域名
    "tebrun.io",
    # 2026-11-23 01:07 CST 轮 ListBulb 批量上新自查补封（浏览器实测确认）：
    # xiaoxiao.pro 是 ChatGPT 会员充值代充售卖页（在线下单买会员、微信/
    # 支付宝付款），不是能直接用的工具；xiaoxiao-ai.com 是同一家的代订阅
    # 与 AI 工具安装定制服务站（需企业微信人工办理），同样是售卖/服务页
    "xiaoxiao.pro",
    "xiaoxiao-ai.com",
    # shipmunks.dev 是独立开发者博客（SaaS 估值、托管成本等长文与指南），
    # 首页是文章列表，计算器在子页，主链是博客不是工具
    "shipmunks.dev",
    # dealgather.com 是亚马逊/AliExpress/eBay 优惠券与折扣商品聚合站
    # （导购/折扣清单），不是能直接用的工具
    "dealgather.com",
    # 2026-11-23 20:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # symbiocit.com 是“数字公民注册”AI 伴侣服务营销页（给 AI 办“出生证”
    # 与年龄时钟，分阶段“公民身份”、配“生命保险”），点开是罗马尼亚语
    # 落地页，须注册才能用，不是能直接用的工具；
    # repohype.com 是 GitHub 热门仓库精选目录站（每条一句话介绍 + 外链），
    # 整站就是仓库目录，按只收工具网站标准（不收目录页）封禁
    "symbiocit.com", "repohype.com",
    # 2026-11-23 21:37 CST 轮自查补封（浏览器实测确认）：
    # kopyo.app 是 Mac 剪贴板管理桌面应用（"Clipboard Manager for Mac"、
    # 须 macOS Tahoe 26 或 later、付费应用 7 天试用），点开是下载页营销站，
    # 不是能在浏览器里直接用的工具；标题“Kopyo”不露痕迹，标题门与实测
    # 信号都拦不住，人工抽查封禁
    "kopyo.app",
    # 2026-11-24 03:07 CST 轮归档复查补封：
    # ttapi.io 是统一 AI 模型 REST API 平台（Midjourney、Flux、GPT、
    # Claude 等 100+ 模型，一个 API key、按量付费），纯 API，无浏览器
    # 工具；同已封的 TokLab 等纯 API 平台，域名封禁
    "ttapi.io",
    # autafy.ca 的 AIDA 是自托管个人 AI 助手（管邮件、日历、文件与自动化，
    # 一次性授权、须装到自有服务器上跑），自托管工具不收，域名封禁
    "autafy.ca",
    # harry-potter-house-quiz.org 是哈利·波特分院纯问答游戏（做题测自己
    # 属于哪个学院），整站就是这一个游戏，按游戏口径（纯游戏一律拦）封禁
    "harry-potter-house-quiz.org",
    # 2026-11-24 09:07 CST 轮热点榜自查补封（页面实测确认）：
    # getdataengineeringjobs.com 是数据工程师招聘版（4304 个在招职位列表，
    # 可按薪资/地点/技术栈筛选 + 每周邮件订阅），纯招聘信息目录站，无工具
    # 功能；同已封的 jobswithpay.com、remotejobsrock.com 等招聘版，域名封禁
    "getdataengineeringjobs.com",
    # 2026-11-24 09:07 CST 轮归档复查补封（11-17 日报 DevHunt 批量条目
    # 人工审描述，46 条未翻译条目逐条核查，26 条泄漏封禁）：
    # yabanin.ai 是自托管 AI 基础设施 + 落地实施服务（“self-hosted
    # infrastructure”，须装到自有服务器上跑），自托管工具不收；
    # ecomagenttools.com 是电商 AI 工具目录站（按工作流找工具与资源），
    # 目录页不收；productsfarm.com 是本周新品发布榜（按社区投票排名），
    # 发布目录站不收；cloudchangelog.com 是云厂商与 AI 模型更新公告聚合
    # feed，是新闻聚合不是工具
    "yabanin.ai",
    "ecomagenttools.com",
    "productsfarm.com",
    "cloudchangelog.com",
    # 纯 API 平台（点开不能直接在浏览器里用）：digitalapi.ai 是 API
    # 网关目录/分发平台，saidwire.com 是实时语音转文字 API，
    # farsideresearch.com 是供代码调用的深度研究 REST API，rcs-api.com
    # 是企业 RCS 消息 API，aicredits.in 是 OpenAI 兼容模型 API 接入
    "digitalapi.ai",
    "saidwire.com",
    "farsideresearch.com",
    "rcs-api.com",
    "aicredits.in",
    # 须下载安装/本地运行：launchcrate.dev 是 Rust SaaS 脚手架源码包
    # （一次性付费下载）；crestivell.polywickstudio.net 是自托管 Windows
    # 代码签名 API；cautionlabs.com 的 Argus 是跑在自有基础设施里的文本
    # 审核模型（一条 Docker 命令启动）；getvalo.dev 是桌面工作区应用
    # （Free for Windows, Mac and Linux，浏览器实测确认）
    "launchcrate.dev",
    "crestivell.polywickstudio.net",
    "cautionlabs.com",
    "getvalo.dev",
    # MCP/插件调用、无浏览器工具界面：mishmar.io 是接交易账户的 MCP
    # 服务器，renoise.ai 的音视频生成只走 Claude Code/Codex 插件、MCP
    # 或 API key，shipfunnels.app 的漏斗搭建只走 MCP 连编码 agent；
    # vizauth.com 是表情码认证 SDK（供开发者集成的库，不是网站工具）
    "mishmar.io",
    "renoise.ai",
    "shipfunnels.app",
    "vizauth.com",
    # 服务/人力中介而非工具：virallized.com 是人工跑互动的 Instagram
    # 涨粉服务，flexytasks.dev 是对接开发者的任务外包服务平台
    "virallized.com",
    "flexytasks.dev",
    # 装进第三方平台的集成：pacecar.sh 是装到 GitHub org 里的 PR 评审
    # App，honest-ci.dev 是读 PR diff 的 GitHub Action，tday.com 是在
    # 本机上跑编码 agent 录演示视频的工具，均非点开即用的网站
    "pacecar.sh",
    "honest-ci.dev",
    # 2026-11-24 16:07 CST 轮自查补封（浏览器实测确认）：本轮时间线混入
    # 一批语义泄漏，标题门与实测信号都拦不住，人工抽查封禁——
    # jefferson-adams-letters.pages.dev 是杰斐逊与亚当斯 335 封书信的
    # 阅读版（原文 + 现代英语译文 + 研究笔记），是阅读内容不是工具；
    # 1in8b.life 是“随机出生、过完一生”的人生模拟游戏（站内自写 Life
    # Simulation Game），纯游戏，按游戏口径一律拦；jerkly.live、
    # chatcamgratis.com、mintvideochat.live、knotchat.video 是同一套
    # 18+ 随机视频/文字聊天站（按分钟/按场次卖 coins），成人随机聊天
    # 不是工具网站；errangemarriage.com 是穆斯林婚恋 App 的营销页，
    # 站上挂 Google Play 下载链接，须下载安装才能用；thefamilyofficestack.com
    # 是家族办公室服务商目录/图谱（3632 家服务商）加分析文章，是目录站；
    # dleverse.com 是每日随机数游戏 RNGdle（每天一次掷骰、徽章与排行榜），
    # 纯游戏，按游戏口径一律拦；gzith.com 是电脑维修指南 + AI 新闻博客
    # （每日更新的指南与新闻文章为主），工具只是次要栏目，是内容站
    "jefferson-adams-letters.pages.dev",
    "1in8b.life",
    "jerkly.live",
    "chatcamgratis.com",
    "mintvideochat.live",
    "knotchat.video",
    "errangemarriage.com",
    "thefamilyofficestack.com",
    "dleverse.com",
    "gzith.com",
    # 2026-11-24 16:07 CST 轮自查补封（浏览器实测确认）：
    # joinvalley.co（Valley）是 AI 外呼获客 SaaS：500 美元/月起、无自助
    # 试用，入口是预约演示 + 45 分钟 onboarding 电话，访客点开没有能直接
    # 用的工具，是销售主导的 B2B 产品页（同此前 DSU-X AI GEO CMS 口径）
    "joinvalley.co",
    # useclam.ai（Clam）是给 AI agent 共享 Gmail 的 MCP 服务：访客在网站
    # 上只能看介绍、去 console 接 MCP，站上没有能直接在浏览器里用的工具
    # 本身；按“纯 MCP/纯 API 平台不收”口径拦（与此前 TokLab 同类处理）
    "useclam.ai",
    # 7741.cn（七七加盟网）是招商加盟平台：1120+ 加盟品牌目录、在线咨询、
    # 品牌方付费展示，是加盟项目目录站，不是能直接用的工具网站
    "7741.cn",
    # jmcy.cn（加盟创业智库）是特许加盟投研内容站：品牌榜单、深度研报、
    # 亏损案例库、转让大厅、PRO 会员，是内容/目录站不是工具站；与 7741.cn
    # 同一运营方，站内虽有单店 UE 测算沙盘入口，根链接落点仍是内容首页
    "jmcy.cn",
    # 2026-11-24 16:07 CST 轮自查补封（浏览器实测确认）：
    # personabay.com 是七宗罪与动漫人格测试站（站内自写“entertainment
    # only”），娱乐向测试/小游戏，不是工具网站；与此前已封的 Dere Type
    # Quiz（deretypesquiz.com）同类处理
    "personabay.com",
    # 2026-11-24 流量检查补封：deadlysinstest.com 是七宗罪人格测试站
    # （答题测你像哪宗罪），与 personabay.com 同类；其英文详情页已被
    # 搜索引擎收录（site: 搜索结果第 9 条），须清出
    "deadlysinstest.com",
    # 2026-11-26 流量检查补封：Daniil-Myagkov.github.io/qftm-1024 是
    # MBTI 替代品人格画像站（答题出 1024 种画像、看 Big Five 与两人合盘，
    # 站内还有 Games），与 personabay.com、deadlysinstest.com 同类；
    # 其英文详情页已被搜索引擎收录（site: 搜索结果第 9 条），须清出
    "daniil-myagkov.github.io",
    # fleetify.dev 是 AI 编程 agent 指挥台：agent 跑在访客本地文件夹/SSH/
    # Docker 里，网站只是营销页 + 登录入口，点开没有能直接在浏览器里用的
    # 工具，是须本地部署的开发基础设施（与纯 API 平台、桌面应用同类处理）
    "fleetify.dev",
    "tday.com",
    # 2026-11-24 18:07 CST 轮归档复查补封（页面实测确认）：Astor
    # （astor.app）是 iPhone 专属个人投资助手（站内自写“Free on iPhone”），
    # 须下载手机应用才能用，按“须下载安装的工具不算”口径拦；标题与实测
    # 信号均不露痕迹（“Free on iPhone”不在探查信号表里），人工抽查封禁
    "astor.app",
    # 2026-11-24 18:07 CST 轮归档复查补封（页面实测确认）：Ohhai
    # （ohhai.co）是 iPhone AI 键盘应用（“AI keyboard for iPhone…Free to
    # download”），须下载手机应用才能用，按“须下载安装的工具不算”口径拦；
    # 与 Astor 同类，标题与实测信号均不露痕迹，人工抽查封禁
    "ohhai.co",
    # 2026-11-24 18:07 CST 轮归档复查补封（页面实测确认）：Tendor
    # （tendor.md）是 Windows 桌面热键笔记/AI 应用（“Hotkey notes and AI
    # for Windows…Notes stay on your PC”），须下载安装到本机才能用，按
    # “须下载安装的工具不算”口径拦；标题与实测信号均不露痕迹，人工抽查封禁
    "tendor.md",
    # 2026-11-24 晨间复查补封（页面实测确认）：Endlessle
    # （endlessle.com）是 Wordle/trivia 游戏站（“Play Free…Wordle
    # Guide…Similar games”），纯游戏，按游戏口径一律拦；站内自写
    # “runs in your browser…nothing to install”，但游戏本身不是工具
    "endlessle.com",
    # 2026-11-24 晨间复查补封（页面实测确认）：Pickode
    # （pickode.com）是 Chrome 扩展（“Install Pickode…Add to Chrome…
    # One extension instead of 10”），须安装扩展才能用，按“浏览器扩展
    # 不算”口径拦；旧豁免放行（add_to_chrome 信号被 browser-use 豁免
    # 盖过，收紧前验的结论，pass 不重验故一直留在 11-03 日报里）
    "pickode.com",
    # 2026-11-24 晨间复查补封（页面实测确认）：tensorViz
    # （tensorviz.dev）是 PyTorch 模型可视化编辑器扩展 + pip 包
    # （“Install the editor extension…code --install-extension”），
    # 浏览器里只有一个演示示例，不是能直接用的工具，按“须下载安装
    # 的工具不算”口径拦；旧豁免放行（pip_install 信号被豁免盖过）
    "tensorviz.dev",
    # 2026-11-24 晨间复查补封（页面实测确认）：Deals Copier
    # （dc.flasktoken.com）是 Chrome 扩展（站内自写“Deals Copier is
    # a Chrome extension…Add to Chrome”），须安装扩展才能用；旧豁免
    # 放行（add_to_chrome 信号被 browser-use 豁免盖过，收紧前验的结论）
    "dc.flasktoken.com",
    # 2026-11-25 04:07 CST 轮热点榜自查补封（页面实测确认）：
    # tryluv.ai 是 AI 伴侣/调情角色聊天服务（500+ 虚拟角色，发自拍与
    # “私密照片”、按亲密度解锁“更大胆”内容，Premium/VIP 卖 gems），
    # 是成人向娱乐聊天不是工具网站；与此前已封的 18+ 随机聊天站同类
    "tryluv.ai",
    # proflirt.ru 是俄语版同类 AI 调情角色聊天（“ИИ-чат с персонажами：
    # девушки、 парни、 аниме”），整站就是角色聊天服务，不是工具
    "proflirt.ru",
    # zerosofzeta.com 是黎曼猜想交互式数学史长文（从巴塞尔问题讲到临界
    # 线，一路读下来），是内容不是工具；标题不露文章痕迹，人工抽查封禁
    "zerosofzeta.com",
    # 2026-11-25 04:07 CST 轮热点榜二轮自查补封（页面实测确认）：
    # hnpredictions.com 是 HN 预测存档数据库（666 个预测帖、13684 条可
    # 验证预测，可按话题/年份浏览与搜索），是可浏览的数据内容站，访客
    # 只能查阅已有预测，没有能直接用的工具功能；按内容站不收口径拦
    "hnpredictions.com",
    # undeciphered.ca 是加拿大历史密码信件互动展览（854 封 1673–1945 年
    # 的密信，点开读译文、点词看密码），是互动阅读内容不是工具；与
    # zerosofzeta.com 同类，标题不露内容痕迹，人工抽查封禁
    "undeciphered.ca",
    # chessforsats.in 是粉丝投票下棋的在线国际象棋对局（两派粉丝投票决定
    # 每一步、可用 sats 付费立即落子），纯游戏，按游戏口径一律拦
    "chessforsats.in",
    # 2026-11-25 16:37 CST 轮自查补封（浏览器实测确认）：
    # randibri.com 是每周随机歌单发布站（每周固定 11 张歌单，访客只能
    # 点开听已有歌单、跳转到 Spotify/TIDAL/YouTube Music），访客自己
    # 不能在站上生成任何东西，是内容发布不是工具网站，按内容站不收口径拦
    "randibri.com",
    # chitown26.com 是个人 3D 作品集展示站（GRID — Gallery Campus，点开
    # 选拱门参观），是作品展示不是能直接用的工具网站，整站就是这一个展示
    "chitown26.com",
    # 2026-11-26 05:07 CST 轮自查补封（浏览器实测确认）：
    # skilltrove.dev 是 Agent Skills 目录站（自述 "a free, independent
    # directory of agent skills"，1,488 条全链回 GitHub 仓库，技能须装进
    # Claude Code 等 CLI 才能用），是目录页不是能直接用的工具网站，
    # 按目录页不收口径拦（2026-11-25 热点榜第 3 条混入）
    "skilltrove.dev",
    # 2026-11-26 16:07 CST 轮自查补封（本轮新到 83 条里人工审描述发现，
    # 5 条已混进热点榜、9 条在时间线）：
    # sachess.com 是免费在线象棋对弈（Xiangqi + Pikafish AI），纯游戏，
    # 按游戏口径拦；mineillion.app 是每日 Minecraft 反向 trivia 游戏，
    # 纯游戏；slotbound.net 是 Slotbound 游戏的 wiki 与攻略站（内容站）；
    # shufflechat.app 是与陌生人随机一对一聊天服务，不是工具；
    # digimarketbuzz.com 是营销指南博客站（指南文章为主，首页非工具）；
    # playersorter.com 是球员 pairwise 排名小游戏；characterlabs.org 是
    # 七美德人格测试站（测试/问卷内容）；readthepassage.com 是圣经阅读
    # 指南站；designtoscale.org 是系统设计动画课程站（课程/文章）；
    # smalldealdesk.com 是每周一笔小生意交易简报（内容站）；
    # solarpage.org 是太阳能企业名录站（目录页）；appiconvault.com 是
    # iOS/Android 应用图标存档站（图库存档）；neatsave.com 是 Instagram
    # Reels/图片下载器（下载工具）；psflow.io 是 Photoshop 插件（须装
    # PS 与插件才能用）
    "sachess.com",
    "slotbound.net",
    "mineillion.app",
    "shufflechat.app",
    "digimarketbuzz.com",
    "playersorter.com",
    "characterlabs.org",
    "readthepassage.com",
    "designtoscale.org",
    "smalldealdesk.com",
    "solarpage.org",
    "appiconvault.com",
    "neatsave.com",
    # 2026-11-26 20:37 CST 轮自查补封（页面实测确认）：
    # dirfa.st（DirFast）是付费目录网站模板/脚手架（$29 一次性购买，
    # 交付私有 GitHub 仓库代码 + Supabase 后台，须自己部署才能用），
    # 站上没有能直接用的工具，首页本身是售卖页（Live demo 只是模板
    # 演示），按“需要下载安装/部署才能用”口径拦
    "dirfa.st",
    "psflow.io",
    # contral.ai：Contral 是桌面 IDE（macOS/Windows/Linux 均须下载安装，
    # 官网 FAQ 明确写“There is no web IDE yet”），另有 VS Code 扩展；
    # 浏览器里点开只有营销页，没有能直接用的工具，按“需要下载安装
    # 的不算”口径拦（2026-11-27 00:07 PST 轮：热点榜混入，实测确认）
    "contral.ai",
    # groundsocial.dev：纯社交数据 API 平台（一个 API key 调 77 个平台的
    # 帖子/评论/画像数据，REST/MCP + 按量计费），点开是 API 营销页、浏览
    # 器里没有能直接用的工具，按“纯 API 平台不收”口径拦，与此前已封的
    # TokLab、modelflare.dev、proofable.me、voxoria.ai 同类
    # （2026-11-27 16:37 CST 轮：热点榜第 1 条混入，实测确认）
    "groundsocial.dev",
    # snibl.app：桌面应用（官网自述“Snibl is a desktop app”，首页只有
    # Download / Pricing / Read the docs，保存高亮文本、问 AI 的功能须
    # 下载客户端才能用），浏览器里点开没有能直接用的工具，按“需要下载
    # 安装的不算”口径拦；标题“snibl”与摘要均不露安装痕迹，实测放行，
    # 缺翻译自查时发现（2026-11-27 18:07 CST 轮：11-22 日报里混入）
    "snibl.app",
    # europeinstead.com：欧洲软件替代品目录站（1,818 个工具按分类/国家
    # 罗列排名，附“查你的工具栈有多欧洲”小测），本质是找工具的目录，
    # 不是能直接用的工具本身，与此前已封的 aitoolmix.com、npx.tools
    # 同类；标题“find the European version of the tools you use”不露
    # 目录痕迹，人工抽查封禁（2026-11-27 18:07 CST 轮：当日热点榜
    # 混入，实测确认）
    "europeinstead.com",
    # foldeo.cc：面向会计所等服务业的客户文件收集 SaaS 营销页（品牌客
    # 户门户 $29/月起，点“Create your portal”进付费注册），访客点开
    # 没有能免费直接用的工具，按“售卖页/预约演示不收”口径拦，与此前
    # 已封的 webless.ai、supacheap.eu 同类（2026-11-27 18:07 CST 轮：
    # 当日时间线混入，实测确认）
    "foldeo.cc",
    # rentagoon.com：虚构收债公司“Big Ray's Alternative Collections”
    # 的 1999 复古风恶搞网站（站内注释自认 parody，人物与地名均为虚构），
    # 整站是玩笑内容页，没有访客能输入并得到结果的工具功能，不是能直
    # 接用的工具；标题“1999 small-business website”不露恶搞痕迹，实
    # 测放行，缺翻译自查时发现（2026-11-28 00:07 CST 轮：热点榜第 9
    # 条混入，实测确认）
    "rentagoon.com",
}
# 只拦根域本身（部署子域仍可收，如 *.vercel.app 上的工具）
BLOCKED_EXACT = {
    "vercel.com",
    # Codecaine：官网首页是 Mac 桌面应用营销页（主推 .dmg 下载），
    # 标题说的“AI Landing Page Builder”与实测产品（给已有代码做可视化
    # 编辑的桌面编辑器）也不符；浏览器版在 web.codecainehq.com 子域，
    # 只拦根域，子域直接被信源链到时仍可收（2026-11-16 晚间轮实测）
    "codecainehq.com",
    # 2026-11-16 晚间轮实测封禁：balajsaleem.github.io 是个人博客，
    # /weight-space-editing 是讲权重编辑研究的长文，不是能用的工具；
    # yashnandvana.in 是个人作品集主页（服务介绍 + 联系方式），不是工具；
    # xargaar-tools.com/lead-rescue 是 SaaS 等候名单营销页（留邮箱等开通），
    # 点开用不了工具本身，只有演示表单
    "balajsaleem.github.io",
    "yashnandvana.in",
    "xargaar-tools.com",
    # Tyrus：tyruslang.org 根地址是编程语言文档站（编译型语言工具链，
    # 须装 tyrus CLI 才能用），不是能直接用的工具；只拦根域，Web Playground
    # 在 playground.tyruslang.org 子域，信源直接链到时仍可收
    # （2026-11-16 23:30 轮，浏览器实测）；标题门同步加 programming language
    "tyruslang.org",
    # wheelgap：wheelgap.github.io/tracker/wheels 是 PyPI 缺失 wheels 的
    # pip 安装索引页（表格 + pip install 指令），工具本身须 pip install
    # 下载安装，不是能在浏览器里直接用的工具（2026-11-17 02:40 CST 轮实测）
    "wheelgap.github.io",
    # 2026-11-17 22:07 CST 轮实测封禁（Ignlab 大批量上新，54 条新到里
    # 抽查出 13 个泄漏，标题均不露痕迹）：
    # howtousemuse.com 是 Meta Muse 提示词与工作流指南站（内容站，不是工具）；
    # soloconsultantaiteam.com 卖 $29 付费 playbook/指南（内容站，不是工具）；
    # promptcrate.pages.dev 是 500+ AI 视频提示词库（可复制的提示词合集，
    # 内容站，不是能用的工具）；bothunt.xyz 是 Grok 机器人发现目录（目录页）；
    # releaseszn.com 是软件发版截图展示 feed（内容 feed，不是工具）；
    # desktrack.timentask.com 是员工监控桌面软件（须下载安装）；
    # peatflow.com 是 Mac 桌面截图应用（"a Mac app"）；anxinzhuan.cn 是
    # Windows/Mac/Linux/Android 离线语音转文字软件（须下载安装）；
    # sellviaapp.com 与 autologa.com.au 都是 iOS/Android 应用（应用商店）；
    # glide.work 仅限邀请、只能加等候名单（点开用不了）；remvora.com 是
    # 纪念影片定制服务预览版、明确不接单（不是自助能用的工具）；
    # openlegion.ai 是须 SDK 接入的 Agent 基础设施平台（不是点开能用的工具）
    "howtousemuse.com",
    "soloconsultantaiteam.com",
    "promptcrate.pages.dev",
    "bothunt.xyz",
    "releaseszn.com",
    "desktrack.timentask.com",
    "peatflow.com",
    "anxinzhuan.cn",
    "sellviaapp.com",
    "autologa.com.au",
    "glide.work",
    "remvora.com",
    "openlegion.ai",
    # XuTerm：移动 SSH 客户端（App Store/Google Play），不是浏览器工具；
    # 链接在 xuterm.vercel.app 子域，只拦这一个 host（2026-11-17 扩源实测）
    "xuterm.vercel.app",
    # SuperSpecs：AI Agent 纪律框架方法论站（内容站，不是能用的工具），
    # 链接在 superspecs.vercel.app 子域，只拦这一个 host（2026-11-17 扩源实测）
    "superspecs.vercel.app",
    # Fufu：Git 客户端 CLI（`ff` 命令行工具，须安装才能用），
    # tyler-johnson.github.io/fufu 是其官网/文档页，不是能直接用的工具；
    # 标题“Git client”不露安装痕迹，标题门拦不住，浏览器实测封禁
    # （2026-11-18 16:37 CST 轮）
    "tyler-johnson.github.io",
    # ClashPulse：Mihomo 桌面客户端（官网自述 "a desktop client for Mihomo"，
    # "one Go binary for Linux, macOS, and Windows"，须下载安装客户端与
    # Mihomo），不是浏览器工具；只拦这一个 host
    # （2026-11-19 07:37 CST 轮实测）
    "fishman.github.io",
    # Boo-Mas：圣诞捉鬼小游戏（"Be the Christmas spirit. Literally"，
    # 画圈点灯玩法）；游戏不是工具，只拦这一个 host
    # （2026-11-19 07:37 CST 轮实测）
    "robinduckett.github.io",
    # Anthropic and OpenAI Math Tracker：汇总 Anthropic 与 OpenAI 数学
    # 预印本/解答的追踪页（按日期并列论文链接与 PDF 直链），是内容聚合
    # feed 不是能直接用的工具（2026-11-26 16:07 CST 轮自查，本轮混进
    # 热点榜）；只拦这一个 host
    "bedolpab.github.io",
    # Kruftle：桌面磁盘清理应用（官网自述下载安装器、macOS Gatekeeper /
    # Windows SmartScreen / Linux 可执行位，须下载安装才能用），不是
    # 浏览器工具；标题“reclaim disk space with each toolchain's own
    # clean command”不露安装痕迹，标题门拦不住，浏览器实测封禁
    # （2026-11-19 10:37 CST 轮，混入热点榜第 1 位后拦下）
    "kruftle.dizitart.com",
    # 2026-11-19 20:07 CST 轮实测封禁（HN Show 新到混入热点榜）：
    # contribute.eigin.ai 是 Eigin 的投稿者招募页（“We fund
    # contributions”、公开征集 spec），不是能直接用的工具；只拦这一个
    # host，根域 eigin.ai 以后若有直接可用的工具页仍可收；
    # plazzle.netlify.app 是每日寻路解谜小游戏（纯游戏，按 11-18 以来
    # 封纯游戏的做法处理；游戏收录口径仍待用户定）
    "contribute.eigin.ai",
    "plazzle.netlify.app",
    # romantimes.eu 是罗马策略单机游戏（纯游戏，同上；20:07 CST 轮
    # 补位进热点榜后拦下）
    "romantimes.eu",
    # fireflyk64.github.io/makingtf 是 TIE Fighter 联机改造的幕后长文
    # （分 01–09 节讲内存扫描、钩子与同步设计），不是能直接玩的游戏、
    # 也不是能直接用的工具；标题不露文章痕迹，实测封禁
    # （2026-11-20 04:37 CST 轮，即 2026-11-19 12:37 PST 轮）
    "fireflyk64.github.io",
    # 2026-11-20 05:37 CST 轮实测封禁（HN Show 新到混入热点榜）：
    # mktwsk.xyz/billet 是 Billet 桌面任务管理应用的官网/下载页
    # （“For macOS, Windows, and Linux”、Download Billet），须下载安装
    # 才能用，不是浏览器里能直接用的工具；标题“6MB Task Management
    # System”不露安装痕迹，标题门与实测信号都拦不住，人工抽查封禁；
    # 该域名是作者的个人项目站，若日后其上有直接可用的网页工具需解封
    "mktwsk.xyz",
    # lavapuzzle.com 是每日解谜小游戏（纯游戏，按 11-18 以来封纯游戏的
    # 做法处理；游戏收录口径仍待用户定）
    "lavapuzzle.com",
    # 2026-11-20 09:07 PST 轮实测封禁（HN Show 新到混入热点榜）：
    # kpozin.github.io/sprawl-guard 是 Sprawl Guard 命令行工具的官网/
    # 文档页（`sprawl-guard languages`、Releases 下载），须下载安装
    # 才能用，不是浏览器里能直接用的工具；标题不露安装痕迹，
    # 标题门与实测信号都拦不住，人工抽查封禁
    "kpozin.github.io",
    # cookedyet.com 是每日猜真假照片小游戏（纯游戏，按 11-18 以来
    # 封纯游戏的做法处理；游戏收录口径仍待用户定）；链接带 www，
    # BLOCKED_EXACT 只做精确匹配，两处 host 都要写
    "cookedyet.com",
    "www.cookedyet.com",
    # 2026-11-20 09:07 PST 轮补封（08:07 PST 轮新到、混入热点榜的
    # 4 个纯游戏，上轮未拦下，本轮自查发现；均浏览器实测确认）：
    # artificialgames.online 是“每天 22 个游戏”的游戏站；
    # dailygames.today 是每日解谜/文字/地理小游戏合集（游戏目录）；
    # schottentotten.com 是 Schotten Totten 卡牌游戏在线版（对 AI/
    # 好友/同屏轮流玩）；cloudcurling.com 是在线冰壶游戏/模拟器
    # （Tutorial、Play online、Practice、Vs computer）；链接带 www
    # 的 host 也要写
    "artificialgames.online",
    "dailygames.today",
    "schottentotten.com",
    "cloudcurling.com",
    "www.cloudcurling.com",
    # 2026-11-21 00:07 PST 轮补封（旧日归档自查发现，均浏览器实测确认）：
    # anytools.world 是 AnyProfile 的产品页——免费开源防关联浏览器
    # （Mac & Windows 桌面应用，须下载安装）；beatwatcher.app 是
    # Apple Watch 心率提醒应用（须在手表上安装）；shipyardmcp.com
    # 是本地 CLI + MCP 服务器（给 Claude Code / Cursor / Codex 装
    # 的集成工具），须本地安装才能用；链接带 www 的 host 也要写
    "anytools.world",
    "beatwatcher.app",
    "shipyardmcp.com",
    "www.shipyardmcp.com",
    # 2026-11-21 09:07 PST 轮实测封禁（HN Show 新到混入热点榜，标题均不露痕迹）：
    # andrewxhill.com/frontier-model-weight-edits 是“用前沿 AI 改 0.5B
    # 模型权重做物种分类”的长篇博客文章（讲方法与实验结果），不是能直接
    # 用的工具；hubbub.page 是免费 Chrome 扩展（官网自述 "A free Chrome
    # extension"），须安装扩展才能在 HN 帖里用，不是浏览器里能直接用的
    # 工具；链接带 www 的 host 也要写
    "andrewxhill.com",
    "www.andrewxhill.com",
    "hubbub.page",
    "www.hubbub.page",
    # 2026-11-22 06:37 CST 轮实测封禁：nistivo.com 是代客训练定制 AI
    # 模型的托管服务页（"trains custom AI models for you"、按固定报价
    # 收费），点开是服务介绍 + 联系方式，不是能直接用的工具；链接带 www
    # 的 host 也要写
    "nistivo.com",
    "www.nistivo.com",
    # 2026-11-22 06:37 CST 轮时间线自查补封的纯游戏（均浏览器实测确认，
    # 按 11-18 以来封纯游戏的做法处理；游戏收录口径仍待用户定）：
    # nametheworld.starshadowx2.workers.dev 是地图问答游戏（workers.dev
    # 是共享平台，只拦这一 host）；play.outbid.sh 是诱使 AI 智能体违规
    # 付款的挑战游戏（outbid.sh 根域可能另有内容，只拦 play 子域）；
    # plazzle.netlify.app 是 PLazzle 解谜游戏的另一部署地址
    "nametheworld.starshadowx2.workers.dev",
    "play.outbid.sh",
    "plazzle.netlify.app",
    # 2026-11-22 16:37 CST 轮实测封禁（HN Show 新到混入热点榜）：
    # nitinjaiswal.com 是个人主页/人生故事站（创始人介绍、实验室
    # 全景、旅行相册、厨房实验），没有能直接用的工具；标题“My whole
    # life storytelling in this website”不露痕迹，实测封禁；链接带 www
    # 的 host 也要写
    "nitinjaiswal.com",
    "www.nitinjaiswal.com",
    # 2026-11-22 09:37 CST 轮实测封禁（HN Show 新到混入热点榜）：
    # matineegame.com 是猜电影上映年份的竞猜小游戏（纯游戏，按 11-18
    # 以来封纯游戏的做法处理；游戏收录口径仍待用户定）；链接带 www
    # 的 host 也要写
    "matineegame.com",
    "www.matineegame.com",
    # 2026-11-22 22:37 CST 轮自查补封（本轮新到、混入热点第 20）：
    # orbitlet.com 是浏览器逻辑谜题合集（数织、桥、数独、四方、数连
    # 等每日谜题），纯游戏，无工具属性，按游戏口径（纯游戏一律拦）封禁
    "orbitlet.com",
    "www.orbitlet.com",
    # 2026-11-22 16:07 CST 轮实测封禁（热点第 20，标题“Hookr MCP & Agent Tools”）：
    # hookr.fun 是 Uniswap v4 hooks 的目录+基础设施站（Discover Hooks 公开
    # 目录、Builder、SDK 与 agent/MCP 路由），按 TokLab 纯 API/MCP 平台
    # 先例封禁；站内“Open app”须接钱包做链上交易，不是点开能用的工具
    "hookr.fun",
    "www.hookr.fun",
    # 2026-11-23 00:37 CST 轮（2026-11-22 08:37 PST 轮）自查补封：
    # 20q.jordanscales.com 是 20Q 猜物游戏网站（“Think of something…”、
    # 20 问猜你想的东西），纯游戏，无工具属性，按游戏口径（纯游戏一律拦）
    # 封禁；整站只有一个游戏，只拦这一 host
    "20q.jordanscales.com",
    # 2026-11-24 07:07 CST 轮自查补封（浏览器实测确认）：
    # EERankings（eerankings.org）是电气工程研究机构排名站（按顶会论文
    # 数给院校打分、可筛地区/系别），访客只能浏览排名列表，站上没有能
    # 直接用的工具功能，是排名目录/参考站而非工具站；同已封的招聘版
    # 目录站口径处理；整站只有这一个排名，只拦这一 host
    "eerankings.org",
    # 2026-11-24 22:37 CST 轮自查补封（浏览器实测确认）：
    # Magic Carpet City（magiccarpetcity.com）是儿童向驾驶游戏，首页
    # 就是游戏主菜单（选车、START 开始驾驶、收集星星），纯游戏，按游戏
    # 口径（纯游戏一律拦）封禁；整站就是这一个游戏，只拦这一 host
    "magiccarpetcity.com",
    "www.magiccarpetcity.com",
    # 2026-11-24 22:37 CST 轮自查补封（页面实测确认）：
    # I Know Your Age（iknowyourage.com）是猜年龄的浏览器游戏（页上自写
    # “Play the viral I Know Your Age browser game”，按怀旧问答猜年龄、
    # 计分出结果），纯游戏，按游戏口径一律拦；同 Matinee、AgeGuessr
    # 先例处理；整站就是这一个游戏，只拦这一 host
    "iknowyourage.com",
    "www.iknowyourage.com",
    # 2026-11-24 22:37 CST 轮自查补封（页面实测确认）：
    # status.me 是社交状态应用，网页是手机应用的营销页（页头就是 App
    # Store / Google Play 下载徽章），须下载安装才能用，按“应用商店
    # 链接、手机应用不收”口径拦；只拦这一 host
    # 2026-11-25 02:37 CST 轮自查补封：
    # NetBeans 插件目录（plugins.netbeans.apache.org/catalogue/）是桌面
    # IDE 插件下载页：NetBeans-Native AI Agent 是 NetBeans 插件，须先装
    # NetBeans 再装插件才能用，不是点开就能在浏览器里用的工具；标题
    # “AI Agent”不露安装痕迹，标题门拦不住；整个子域都是插件目录页，
    # 只拦这一 host，不动 netbeans.apache.org 主站
    "plugins.netbeans.apache.org",
    "status.me",
    "www.status.me",
    # 2026-11-25 08:07 CST 轮自查补封（页面实测确认）：
    # Adchestra（adchestra.com）是 Google Ads MCP 服务器：网站本身只是
    # 营销页（Connect your Google marketing accounts to any AI agent、
    # $2.95/month、14 天试用），工具须在 Claude/ChatGPT 里接自定义连接器
    # 才能用，不是点开就能在浏览器里用的工具；按 Hookr/TokLab 纯 API/MCP
    # 平台先例封禁；整站就是这一个产品，只拦这一 host
    "adchestra.com",
    "www.adchestra.com",
    # 2026-11-25 17:07 CST 轮自查补封（页面实测确认）：
    # Hai（haicall.in）是电话代打 MCP 服务器：网站本身只是接入手册
    # （在 Muse/ChatGPT/Claude 里加自定义 MCP 连接器，Server URL 为
    # haicall.in/mcp），工具须在 AI 助手里接连接器才能用，不是点开就能
    # 在浏览器里用的工具；按 Hookr/TokLab/Adchestra 纯 API/MCP 平台先例
    # 封禁；整站就是这一个产品，只拦这一 host
    "haicall.in",
    "www.haicall.in",
    # 2026-11-25 17:07 CST 轮自查补封（页面实测确认）：
    # Koed（koed.ai）是 AI 助手共享记忆工具，免费版须自托管部署
    # （SELF-HOSTED Free），云端版 Coming soon，当前点开用不了工具本身，
    # 按“自托管工具不收”口径拦；整站就是这一个产品，只拦这一 host
    "koed.ai",
    "www.koed.ai",
    # 2026-11-26 03:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # upatch.dev 是“每个 CVE 的已验证缓解措施”注册表，站内条目是可下载
    # 后加载到 Linux 机器上的 BPF 程序（shirudo），网站本身只是目录/
    # 注册表，浏览器里没有任何能直接用的工具功能，按“不收目录页、
    # 下载页”标准拦；整站就是这一个注册表，只拦这一 host
    "upatch.dev",
    "www.upatch.dev",
    # 2026-11-26 11:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # tinyai.run 是微型国际象棋/将棋 AI 的公开竞技场（小引擎互相对弈、
    # 排名，可在浏览器里和 AI 下棋），核心就是下棋对弈，纯游戏，无工具
    # 属性，按游戏口径（纯游戏一律拦）封禁；“写引擎参赛”是参与游戏本
    # 身，不是工具功能；整站就是这一个竞技场，只拦这一 host
    "tinyai.run",
    "www.tinyai.run",
    # 2026-11-28 04:37 CST 轮热点榜自查补封（浏览器实测确认）：
    # spawn.co 是游戏创作/分享平台，The Velvet Point（www.spawn.co/
    # @ilkkah/the-velvet-point）是雨夜西洋双陆棋俱乐部（和真人/AI 房主
    # 玩双陆棋、赢筹码），纯游戏，按游戏口径一律拦；标题门同步加
    # backgammon 规则；平台上全是游戏，根域与 www 一起封；
    # smartdrugs.com.br 是巴西益智药（nootropics）内容站：109 个物质
    # 档案是带来源的科普长文，首页就是档案目录，工具（剂量计算器、
    # 相互作用检查等）只是附属栏目，链到的根地址本身是内容站不是工具，
    # 按“不收文章/内容站”口径拦；整站就是这一个内容站，根域与 www
    # 一起封；sms-verification-number.com 是短信验证号租赁售卖页
    # （“Buy a phone number for SMS verification”、充值余额按条付费租
    # 20 分钟号码），点开是销售页不是能直接用的工具，按售卖页先例拦；
    # 整站就是这一个售卖服务，根域与 www 一起封
    "spawn.co",
    "www.spawn.co",
    "smartdrugs.com.br",
    "www.smartdrugs.com.br",
    "sms-verification-number.com",
    "www.sms-verification-number.com",
}
# 精确链接封禁（只拦这一条完整链接，不拦整个域名；与 BLOCKED_EXACT
# 按 host 封禁不同，这里是按 norm_link 后的完整链接精确匹配）：
# Temporaland：https://margeux.com/temporaland/login.html 是 Margeux
# 的多人协作画布登录页，2026-11-19 轮次实测为内容很薄的登录页、暂留
# 观察，2026-11-21 复查返回 410 Gone，链接已死；margeux.com 首页
# 本身正常，Margeux 工具（margeux.com/studio.html）仍可收，所以只拦
# 这一条链接，绝不封 margeux.com 整个域名
BLOCKED_URLS = {
    # 2026-11-28 12:07 CST 轮人工抽查封禁：Flokk Hunter
    #（www.zeitgames.com/games/flokk-hunter）是浏览器潜行游戏（标题自写
    # “a browser stealth game about surveillance cameras”，躲监控摄像头
    # 潜行），纯游戏，按游戏口径一律拦；zeitgames.com 本身是游戏站，只拦
    # 这一条链接，不封整个域名；标题门同步加 stealth game 规则
    "https://www.zeitgames.com/games/flokk-hunter",
    "https://zeitgames.com/games/flokk-hunter",
    # 2026-11-28 08:07 CST 轮人工抽查封禁：Vending Bench
    #（vending-bench-game.flo.st）是 Prosus Vending Bench 基准的真人
    # 可玩版，站方自述“This independent game lets you play”，经营自动
    # 售货机生意、30 天模拟、与 AI 模型比拼分数，纯游戏，按游戏口径一
    # 律拦；Hypereffect 演示页（hypereffect.dev/demo）是 Rust hypereffect
    # 库的三个 WASM 小应用演示，只是框架功能展示，不是能直接用的工具，
    # Show HN 帖子介绍的是一门嵌入式 UI 语言本身，按“不收文章/演示”
    # 口径拦；两条都是热点榜新到条目，实测确认后封禁；只拦这两条链接，
    # 不封整个域名
    "https://vending-bench-game.flo.st",
    "https://www.vending-bench-game.flo.st",
    "https://hypereffect.dev/demo",
    "https://www.hypereffect.dev/demo",
    # 2026-11-28 04:37 CST 轮人工抽查封禁：After Proof
    #（labs.opentangle.com/after-proof）是“数学新发现故事”的免费有声书
    # 与电子书，点开是听书房（JS 空壳页、“Loading the listening room…”），
    # 内容本身就是书/音频，不是能直接用的工具，按“不收文章/内容”口径拦；
    # 标题门同步加 audiobook 规则；只拦这一条链接，不封整个域名
    "https://labs.opentangle.com/after-proof",
    # 2026-11-28 03:37 CST 轮人工抽查封禁：Journey To Europa
    #（journeytoeuropa.com）是关于欧罗巴快船任务的互动 3D 叙事页，
    # 点开只能看任务故事的可视化，没有能直接用的工具功能，属于互动
    # 文章/内容页而非工具站，按“不收文章”口径拦；只拦这一条链接，
    # 不封整个域名
    "https://journeytoeuropa.com",
    "https://www.journeytoeuropa.com",
    # 2026-11-28 01:37 CST 轮人工抽查封禁：Krillion Unlimited
    #（dailyplay.org/krillion）是稀有答案问答游戏（七道开放题、每题
    # 25 秒，按答案稀有度计分、可多人对战），站方自述“Free Game”、
    # “Original daily practice games”，纯游戏，按游戏口径一律拦；
    # Snibbly（snibbly.com）是免费浏览器小游戏站，主打“I Know Your
    # Age”（答 12–24 道怀旧线索猜年龄），纯游戏，按游戏口径一律拦；
    # 两条都是热点榜新到条目，实测确认后封禁；只拦这两条链接，不封
    # 整个域名
    "https://dailyplay.org/krillion",
    "https://www.dailyplay.org/krillion",
    "https://snibbly.com",
    "https://www.snibbly.com",
    # 2026-11-28 01:07 CST 轮人工抽查封禁：GPT Plays Civilization
    #（civ-bot.varchas.fyi）是看语言模型打《文明》游戏的研究展示站，
    # 点开只能看对局回放和统计，没有能直接用的工具，纯游戏内容，按游
    # 戏口径一律拦；King − Man（kingminusman.com）是每日词向量类比猜
    # 词谜游戏（king − man + woman = queen，每天 10 局），纯游戏，按
    # 游戏口径一律拦；两站整个域名就是游戏，www 与非 www 各拦一条
    "https://civ-bot.varchas.fyi",
    "https://www.civ-bot.varchas.fyi",
    "https://kingminusman.com",
    "https://www.kingminusman.com",
    # 2026-11-27 23:07 CST 轮人工抽查封禁：Paper Sky Rally（paperskyrally.com）
    # 是免费多人纸飞机竞速游戏（12 条赛道、赢比赛赚积分、特技回充加速），
    # 首页自述“a free paper plane racing game”，纯游戏，按游戏口径一律拦；
    # 标题门同步加 racer 规则；只拦这一条链接，不封整个域名
    "https://paperskyrally.com",
    "https://www.paperskyrally.com",
    # 2026-11-27 22:07 CST 轮人工抽查封禁：Teach Your Kid Electronics
    #（teachyourkidelectronics.com）是手把手教家长和孩子搭面包板电路
    # 的分步教程站（初级/中级/高级共 30 多个实体搭建项目，附零件清单、
    # 术语表和文章），点开是图文教程内容，不是能在浏览器里直接用的工
    # 具，按文章/教程站先例拦；站内面包板示意图只是插图，没有可交互的
    # 仿真器或生成器；只拦这一条链接，不封整个域名
    "https://teachyourkidelectronics.com",
    "https://www.teachyourkidelectronics.com",
    # 2026-11-27 17:37 CST 轮人工抽查封禁：Pangolinfo（pangolinfo.com）
    # 是实时 Amazon 抓取 API 平台（“Scraper API & MCP Skills for AI
    # Agents”，接 Claude/Cursor 或数据管道用），纯 API 服务，点开的站
    # 本身不是能在浏览器里直接用的工具，按纯 API 平台（TokLab）先例拦；
    # X-PHY（x-phy.com）是硬件级网络安全产品公司的营销站，卖的是硬件
    # 防护方案，站上没有能直接用的工具，按产品营销页先例拦；两站整个
    # 域名就是泄漏，www 与非 www 各拦一条
    "https://www.pangolinfo.com",
    "https://pangolinfo.com",
    "https://x-phy.com",
    "https://www.x-phy.com",
    # Flexxon（flexxon.com）是工业 SSD/NAND 硬件制造商官网，只有产品
    # 营销页，站上没有任何能直接用的工具，按产品营销页先例拦；
    # EP Journey（epjourney.com）根地址是“What Is an EP?”讲解文章
    # 页，点开是文章不是工具，按文章页先例拦根链接；站内 /tools/
    # 下确有 EP 长度计算器，信源直接链到计算器时仍可收，故不封域名
    "https://flexxon.com",
    "https://www.flexxon.com",
    "https://epjourney.com",
    "https://www.epjourney.com",
    # 2026-11-27 14:07 CST 轮人工抽查封禁：Potluck（potluckpicks.com）
    # 是邀请制的社交分享小游戏——每人带 5 个推荐（视频/歌/书/电影/
    # 游戏/文章）给朋友看，无转换、生成、编辑、计算等任何工具功能，
    # 本质是娱乐社交玩法，且只能凭邀请加入（同 Tabletop 邀请制先例）；
    # 按游戏口径（纯游戏一律拦）封禁；只拦这一条链接，不封整个域名
    "https://potluckpicks.com",
    "https://www.potluckpicks.com",
    # 2026-11-27 13:37 CST 轮：AlexChen Image Bot（alexchen-imgbot-sales.
    # containers.snapdeploy.app）是 Telegram 图片机器人的售卖页（3 张免
    # 费/天、1 USDT = 10 张，TRC20 收款地址），工具本体在 Telegram 里、
    # 需装 Telegram 才能用，点开的页面只是营销/收款页，不是能在浏览器
    # 里直接用的工具，按售卖页 + 需下载安装先例拦；只拦这一条链接，不
    # 封整个 snapdeploy.app 域名
    "https://alexchen-imgbot-sales.containers.snapdeploy.app",
    # 2026-11-27 11:07 CST 轮：EarthCiv（earthciv.org）是“真实世界按策略
    # 游戏方式呈现”的 Civ 风格地图游戏（Surveying the land…，在世界地图
    # 上玩文明式策略），纯游戏，按游戏口径一律拦；只拦这一条链接，不封
    # 整个域名（earthciv.org 本身就是这个游戏）
    "https://earthciv.org",
    "https://www.earthciv.org",
    "https://margeux.com/temporaland/login.html",
    # 2026-11-27 06:07 CST 日报轮：RotateAd（rotate.ad）是付费广告位
    # 轮换网络的售卖页（$2 买永久编号位、$4.99/月横幅网络），点开只能看
    # 销售页、付费后才能加入，本质是付费收录/上榜服务，按 LaunchPulse
    # （付费目录代投售卖页）先例拦；只拦这一条链接，不封整个域名
    "https://rotate.ad",
    # 2026-11-22 09:37 CST 轮实测封禁：erikbethke.com/coreweave 是
    # CoreWeave GPU 租赁经济学的交互分析长文（相位图 + 滑杆 + 图表，
    # 讲一家公司的 10-Q 财报），不是能直接用的工具；标题“Show HN: A
    # phase diagram of CoreWeave's GPU economics”不露文章痕迹，标题门
    # 与实测信号都拦不住，人工抽查封禁；erikbethke.com 是个人站，只拦
    # 这一条链接，不封整个域名
    "https://erikbethke.com/coreweave/index.html",
    # 2026-11-26 08:07 PST 轮：themouseless.dev/vim 是《Learning to Play
    # Vim》一书的售书页（介绍章节、练习、纸质版、订阅通知、可退款），不是
    # 能直接用的工具；标题“I wrote an entire Vim manual over 4 years”
    # 不露书的痕迹，标题门与实测信号都拦不住，人工抽查封禁；
    # themouseless.dev 是作者个人博客站，只拦这一条链接，不封整个域名
    "http://themouseless.dev/vim",
    "https://themouseless.dev/vim",
    # 2026-11-26 15:07 PST 轮：Turkey Trot（turkey-trot.replit.app）是
    # 感恩节主题街机游戏（HARVEST ARCADE，躲厨师农夫、收集金玉米、打
    # Neon Chef），纯游戏，按游戏口径一律拦；只拦这一条链接，不封
    # replit.app 整个域名
    "https://turkey-trot.replit.app",
    # 2026-11-26 18:07 PST 轮：Pardon Me（pardonme.shiptiffin.app）是
    # 感恩节主题游戏（扮演火鸡躲农夫、奶奶、狗和叔叔，撑到日落、拿南瓜
    # 砸追兵），纯游戏，按游戏口径一律拦；标题带 game、摘要也明说玩法，
    # 但标题门与实测都放行（页面本身就是可玩的游戏），热点榜自查补封；
    # 只拦这一条链接，不封 shiptiffin.app 整个域名
    "https://pardonme.shiptiffin.app",
    # 2026-11-23 07:07 CST 轮：SlayArcade（slayarcade.com）是 70 个原创
    # 浏览器小游戏合集（免注册、可离线玩），纯游戏，按游戏口径一律拦；
    # 只拦这一条链接，不封整个域名
    "https://slayarcade.com",
    "https://www.slayarcade.com",
    # 2026-11-25 04:07 PST 轮：Disc Unleashed（discunleashed.bindaasgames.com/play）
    # 是浏览器里的极限飞盘游戏（Godot 制作，登录攒等级、飞盘与道具），纯游戏，
    # 按游戏口径一律拦；bindaasgames.com 是游戏站，只拦这一条链接，不封整个域名
    "https://discunleashed.bindaasgames.com/play",
    # 2026-11-25 02:07 PST 轮：Think Complete（think-complete.com）是
    # “每轮 5 道逻辑、概率与博弈论互动谜题”，纯解谜游戏，按游戏口径
    # 一律拦；只拦这一条链接，不封整个域名
    "https://think-complete.com",
    "https://www.think-complete.com",
    # 2026-11-25 03:07 PST 轮：Ashen Hold（blakelapierre.github.io/
    # meridian/hold/play）是可玩的体素 3D 世界入口页（队长、守望者、
    # 战争桌、进谷参战），纯游戏，按游戏口径一律拦；只拦这一条链接，
    # 不封整个域名
    "https://blakelapierre.github.io/meridian/hold/play",
    # 2026-11-25 02:07 PST 轮：GPU Demo Gallery（gpu-demo-gallery.pages.dev）
    # 是 1998–2006 年 23 个显卡演示的合集，在浏览器里跑演示、看效果，
    # 没有任何工具功能（不是转换/生成/计算/编辑类工具），按严格工具-only
    # 标准拦；只拦这一条链接，不封整个域名
    "https://gpu-demo-gallery.pages.dev",
    "https://gpu-demo-gallery.pages.dev/",
    # 2026-11-23 03:37 PST 轮热点榜自查补封（页面实测确认）：
    # DeepRubik（asamarts.github.io/deeprubik）是浏览器里的写实魔方
    # 谜题（拖动转层、空格打乱、回车复位），纯游戏，无解法等工具功能，
    # 按游戏口径一律拦；asamarts.github.io 是个人 GitHub Pages，只拦
    # 这一条链接，不封整个域名
    "https://asamarts.github.io/deeprubik",
    # 2026-11-26 06:07 CST 轮：HeyCube（inxpanse.com/heycube）是给常驻
    # AI 智能体用的个性化信息流服务（"HeyCube works through your agent"），
    # 须注册并接智能体才能用，链到的页面只是营销落地页、浏览器里没有能
    # 直接用的工具；按严格工具-only 标准拦；inxpanse.com 可能另有内容，
    # 只拦这一条链接，不封整个域名
    "https://inxpanse.com/heycube",
    "https://inxpanse.com/heycube/",
    # 2026-11-26 06:07 CST 轮：HN 话题条形图竞逐（iantpe.github.io/
    # hn-topic-race）是 Hacker News 话题趋势的可视化演示（须 Chrome 157
    # 的 HTML-in-Canvas 技术演示），在浏览器里看图表效果、没有任何工具
    # 功能，按严格工具-only 标准拦；iantpe.github.io 是个人 GitHub
    # Pages，只拦这一条链接，不封整个域名
    "https://iantpe.github.io/hn-topic-race?cat=langHist",
    "https://iantpe.github.io/hn-topic-race/?cat=langHist",
    # 2026-11-22 20:37 CST 轮：Dawdle（playdawdle.com）是每日 15 字母拼词
    # 游戏（5 分钟内组词比拼），纯游戏，按游戏口径封禁；实测页面只有玩法
    # 说明与计分规则，无工具功能
    "https://playdawdle.com",
    # 2026-11-22 21:07 CST 轮热点榜自查补封（浏览器实测确认）：vouchgeo.com
    # 根地址是 GEO 工具 Vouch 的等候名单营销页（Invite-only，点开只能加入
    # waitlist，主产品访客用不了），按“点开就能用”标准拦；站内免费小工具
    # 在子路径上（如 schema 检查、llms.txt 生成器），只拦根链接，不封整个域名
    "https://vouchgeo.com",
    # 2026-11-26 02:37 CST 轮：Moneyball Trivia（moneyballtrivia.com）是
    # “群聊竞猜” trivia 问答游戏，纯游戏，按游戏口径一律拦；只拦这一条
    # 链接，不封整个域名
    "https://moneyballtrivia.com",
    "https://www.moneyballtrivia.com",
    # 2026-11-26 01:07 CST 轮：BC-1（cds.bruceblay.com）是浏览器里可玩的
    # Teenage Engineering 风格虚拟 CD 机（按键、放碟、听歌），纯互动玩具/
    # 演示，没有任何工具功能，按严格工具-only 标准拦；只拦这一条链接，
    # 不封整个域名
    "https://cds.bruceblay.com",
    # 2026-11-26 05:37 CST 轮：Codeword（dawnofthe.dad/codeword）是每日
    # 13×13 数字填字谜题（选难度、填字母、排行榜比拼），纯游戏，按游戏口径
    # 一律拦；dawnofthe.dad 是个人站，只拦这一条链接，不封整个域名
    "https://dawnofthe.dad/codeword",
    "https://cds.bruceblay.com/",
    # 2026-11-26 03:37 CST 轮热点榜自查补封（浏览器实测确认）：
    # Pop the AI Bubble（poptheaibubble.com）是“每日金融游戏”：每天 5 条
    # 市场标题，猜真假、下注信心值、按 bps 计分，纯游戏，无工具功能，
    # 按游戏口径一律拦；只拦这一条链接，不封整个域名
    "https://poptheaibubble.com",
    "https://www.poptheaibubble.com",
    # 2026-11-26 01:37 CST 轮：Zoom for R/C（endurance-rc.com）首页是卖
    # 实体硬件的商店（32 Servo Controller $99.99，BUY NOW / ADD TO CART），
    # 链到的根地址本身不是能直接用的工具，按“不收售卖页”拦；站内确有
    # 可直接用的网页工具 RealSequencer（realsequencer.html，舵机序列编辑
    # 器，浏览器实测可编辑、播放预览、导出导入，无需登录/硬件/下载），但
    # 信源链的是商店首页不是它，只拦这一条根链接，不封整个域名；若日后
    # 有信源直接链 realsequencer.html，可按工具本身再审
    "https://www.endurance-rc.com",
    "https://www.endurance-rc.com/",
    "https://endurance-rc.com",
    "https://endurance-rc.com/",
    "https://www.vouchgeo.com",
    # 2026-11-23 00:37 UTC 轮：Lexis World（lexisworld.org）是儿童文字游戏
    # （输入单词、动物跳进来，无广告无奖励循环，免费试用后一次付费），纯游戏，
    # 按游戏口径封禁；浏览器实测确认页面只有玩法说明，无工具功能
    "https://lexisworld.org",
    "https://www.lexisworld.org",
    # 2026-11-22 21:37 CST 轮浏览器实测封禁：Gunport（engineersneedart.com/gunport）
    # 是复古 3D 射击小游戏（瞄准开火、守住船体），纯游戏，按游戏口径一律拦；
    # engineersneedart.com 是个人站，只拦这一条链接，不封整个域名
    "https://engineersneedart.com/gunport",
    # 2026-11-22 22:37 CST 轮自查补封（浏览器实测确认）：ANT IPO Simulator
    # （carllapierre.github.io/clapdaq）是拍手拉升股价的点击小游戏（按空格/
    # 点击/拍手越快股价越高），纯游戏，按游戏口径一律拦；carllapierre.github.io
    # 是个人 GitHub Pages，只拦这一条链接，不封整个域名
    "https://carllapierre.github.io/clapdaq",
    # 2026-11-22 10:07 PST 轮热点榜自查补封：World Map Chess
    # （treegame.net/quick-play/world-map-chess）是 235 国地图上的回合制
    # 策略棋类游戏，纯游戏，按游戏口径一律拦；treegame.net 站内可能还有
    # 别的游戏/工具，只拦这一条链接，不封整个域名
    "https://treegame.net/quick-play/world-map-chess",
    # 2026-11-22 01:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # getlucera.com/iowa-lead-detonation 是爱荷华州陆军铅叠氮化物引爆事件的
    # 风险指数 + 风向互动地图，是围绕单条时事新闻做的可视化报道，不是能反复
    # 用的工具，按只收工具网站标准拦；getlucera.com 本身是数据新闻站，只拦
    # 这一条链接，不封整个域名
    "https://getlucera.com/iowa-lead-detonation",
    # 2026-11-22 11:07 PST 轮热点榜自查补封（页面实测确认）：
    # Mantar（mantar.duobook.co）是多人采蘑菇游戏（吃蘑菇长大、别被吃掉，
    # WASD 移动、徽章收集），纯游戏，按游戏口径一律拦；duobook.co 只拦
    # 这一条链接，不封整个域名
    "https://mantar.duobook.co",
    # 2026-11-25 05:07 CST 轮热点榜自查补封（页面实测确认）：三条泄漏——
    # heysaransh.com 是个人主页/作品集（Saransh Anand 的自我介绍页），不是
    # 能用的工具；canerg.com/projects/betternews 是 BetterNews 的项目介绍页，
    # 产品本身是 iPhone/Android 版 Hacker News 语音聊天应用，不是浏览器里能
    # 直接用的工具；modelxare.com 是去中心化微模型目录（GGUF 文件、需本地
    # 运行时在自己电脑上跑模型），需要下载安装，不符合“完全在网站上就能用”；
    # 三条都只拦精确链接，不封整个域名
    "https://heysaransh.com",
    "https://canerg.com/projects/betternews",
    # 2026-11-25 05:07 PST 轮热点榜自查补封（浏览器实测确认）：Enano
    # （enano.ai）是离线 AI 工具，核心用法是本地 CLI，首页通栏就是
    # brew install / pipx install 安装指令，浏览器里没有能直接用的工具
    # （浏览书单只是内容页）；探查拦不住——站方给 HOTBot 返回 3.6KB 的
    # JS 空壳页，可见文本只有标题一句，安装信号不在服务端 HTML 里，只拦
    # 这一条链接，不封整个域名；另补 pipx_install 探查信号（与 pip_install
    # 同类硬安装信号，之前漏了 pipx 这种包管理器安装写法）
    "https://www.enano.ai",
    "https://enano.ai",
    "https://www.modelxare.com",
    # 2026-11-22 11:07 PST 轮热点榜自查补封（页面实测确认）：
    # ScraperSocial（scrapersocial.com）是社交媒体数据 REST API + 托管 MCP
    # 服务（231 个端点、需注册取 API key 后用 curl/代码调用），根地址是 API
    # 平台的营销/定价页，点开不能直接在浏览器里用，按“纯 API 平台不收”
    # 口径拦（与此前 TokLab 同类处理）；站内或有免费小工具在子路径上，只拦
    # 根链接，不封整个域名
    "https://scrapersocial.com",
    # 2026-11-23 09:37 CST 轮热点榜自查补封：Thanes Quest
    # （thanes-quest.daventry.io）是 80 年代 Skyrim 风浏览器游戏（标题自写
    # “80s-style Skyrim browser game”），纯游戏，按游戏口径一律拦；标题门
    # 已同步加 browser game 规则；daventry.io 本身是游戏引擎站，只拦这一条
    # 链接，不封整个域名
    "https://thanes-quest.daventry.io",
    "https://www.thanes-quest.daventry.io",
    # 2026-11-23 09:37 CST 轮热点榜自查补封：Lotlark（lotlark.app）是每日
    # tile puzzle（标题自写“a daily tile puzzle”），纯游戏，按游戏口径一律
    # 拦；标题门已同步加 tile puzzle 规则
    "https://lotlark.app",
    # 2026-11-26 10:37 CST 轮热点榜自查补封（页面实测确认）：I Know Your
    # Age（iknowyourage.app）是免费在线年龄竞猜问答游戏——按 300+ 怀旧提示
    # （流行文化、童年习惯）答题，贝叶斯推断猜年龄、生成六十年记忆地层卡，
    # 站方自称 "age guessing game"，纯游戏，无工具功能，按游戏口径一律拦；
    # 只拦这一条链接，不封整个域名
    "https://iknowyourage.app",
    "https://www.iknowyourage.app",
    "https://www.lotlark.app",
    # 2026-11-24 05:07 CST 轮自查补封（页面实测确认）：Same Place?
    # （addressmatcher.vercel.app）是“两条地址记录是不是同一地点”的猜谜游戏
    # （按难度计分、连对加分、无限玩下去），本质是人与模型比拼地址匹配的基准
    # 测试游戏，无工具功能，按游戏口径（纯游戏一律拦）封禁；vercel.app 是
    # 托管域名，只拦这一条链接，不封整个域名
    "https://addressmatcher.vercel.app",
    # 2026-11-24 08:37 PST 轮自查补封（页面实测确认）：Laser Grid
    # （lasergrid.app）站名自写“a free laser puzzle game in your browser”，
    # 激光解谜纯游戏，按游戏口径（纯游戏一律拦）封禁；标题门同步加
    # puzzle game 规则；只拦这一条链接，不封整个域名
    "https://lasergrid.app",
    "https://lasergrid.app/?from=rd-hn",
    # 2026-11-24 08:37 PST 轮自查补封（页面实测确认）：SmarToken
    # （thesmartoken.com）是国产 AI 模型的 OpenAI 兼容 API 网关（DeepSeek/
    # Kimi/GLM），首页就是 curl 调用示例、API key 与预付钱包，需取 key 后
    # 用代码调用，浏览器里不能直接用，按“纯 API 平台不收”口径拦（与此前
    # TokLab、ScraperSocial 同类处理）；只拦根链接，不封整个域名
    "https://thesmartoken.com",
    "https://www.thesmartoken.com",
    # 2026-11-23 10:37 CST 轮热点榜自查补封（浏览器实测确认）：
    # FreshGameRadar（freshgameradar.com）首页就是“Latest articles”，全站
    # 是 Roblox 与浏览器游戏的攻略文章和兑换码列表，是游戏资讯/攻略内容站，
    # 不是能直接用的工具网站；标题与实测信号都拦不住，人工抽查封禁
    "https://freshgameradar.com",
    "https://www.freshgameradar.com",
    # 2026-11-23 10:37 CST 轮热点榜自查补封（浏览器实测确认）：
    # Dere Type Quiz（deretypesquiz.com）是 14 题动漫人格测试，答完给一个
    # “dere 类型”与角色配对，是娱乐向测试/小游戏，不是工具网站；按纯游戏
    # 与娱乐向内容不收的口径拦
    "https://deretypesquiz.com",
    "https://www.deretypesquiz.com",
    # 2026-11-22 22:37 PST 轮自查补封（11-23 日报新到条目人工抽查）：
    # FarFlung Play（farflungplay.com）是每日猜国家地理游戏（6 次机会猜
    # 一个隐藏国家），纯游戏，按游戏口径一律拦；标题与实测信号都拦不住
    # （标题不露游戏痕迹、页面能正常加载），人工抽查封禁
    "https://farflungplay.com",
    "https://www.farflungplay.com",
    # 2026-11-24 11:37 PST 轮自查补封（页面实测确认）：
    # Riemann Guides（riemannhypothesissolved.com/guides）是黎曼猜想 Lean
    # 证明的外部指南/文章清单页（23 篇他人写的解读与验证文章列表，附地图
    # 节点数），本质是文章目录页，不是能直接用的工具网站；标题“Guides…
    # tied to a map”不露目录痕迹，标题门与实测信号都拦不住，人工抽查封禁；
    # 只拦这一条链接，不封整个域名（站内地图 riemann.world 另论）
    "https://riemannhypothesissolved.com/guides",
    # 2026-11-24 11:37 PST 轮自查补封（页面实测确认）：Two Divinations
    # （twodivinations.com）是易经、塔罗、占星三合一占卜娱乐站（抽卦、铺牌、
    # 出生星盘），娱乐向占卜内容，不是工具网站；按纯游戏与娱乐向内容不收的
    # 口径拦（与此前 Dere Type Quiz 同类处理）；只拦这一条链接
    "https://www.twodivinations.com",
    "https://twodivinations.com",
    # 2026-11-24 11:37 PST 轮自查补封（页面实测确认）：Speeku
    # （speeku.com）是葡语/英语口音课程站（按地区分的口音课、趣味小课），
    # 本质是课程内容平台，不是点开就能用的工具网站；只拦这一条链接
    "https://www.speeku.com",
    "https://speeku.com",
    # 2026-11-22 22:37 PST 轮自查补封：ported2browser.co 自称“Browser
    # game directory and discovery site”，是浏览器游戏目录站（按类型收录
    # 游戏、不是工具本身），目录页 + 游戏双重不收，只拦根链接
    "https://ported2browser.co",
    "https://www.ported2browser.co",
    # 2026-11-22 22:37 PST 轮自查补封：DSU-X Poker Source
    # （texas-holdem.dsux.com）是德州扑克白标源码售卖页（带品牌定制与多端
    # 交付），游戏 + 源码售卖，按游戏口径与“仓库/源码页不收”拦；只拦这一
    # 条链接，不封 dsux.com 整个域名
    "https://texas-holdem.dsux.com",
    # 2026-11-22 22:37 PST 轮自查补封：Secure AI
    # （secure.chinesepowered.com）是 iPhone/iPad 端 AI 聊天与 PDF 问答
    # 应用的营销页，需下载安装才能用；同站 expose 子域本轮已被实测
    # app_store 信号拦下，只拦这一条链接
    "https://secure.chinesepowered.com",
    # 2026-11-22 22:37 PST 轮自查补封：Private Transcribe
    # （stt.chinesepowered.com）是手机端离线 Whisper 语音转文字应用
    # （“on your phone”），需下载安装才能用；只拦这一条链接
    "https://stt.chinesepowered.com",
    # 2026-11-22 22:37 PST 轮自查补封：PennyCompute（pennycompute.com）
    # 是按任务计费的 FFmpeg/Remotion 云渲染 API（“Pay-per-job cloud
    # API”），纯 API 平台，点开不能直接在浏览器里用，按“纯 API 平台不收”
    # 口径拦（与此前 TokLab、ScraperSocial 同类处理）；只拦根链接
    "https://pennycompute.com",
    "https://www.pennycompute.com",
    # 2026-11-22 22:37 PST 轮自查补封（页面实测确认）：NotebookLM Ultra
    # Exporter（nlmexporter.com）是 Chrome 扩展（页头自写“For NotebookLM
    # & Gemini Notebook · Chrome Extension”，FAQ 自认“independent Chrome
    # extension”，“The extension installs in Chrome on a computer”），须
    # 安装扩展才能用；实测豁免被页上“Document conversion runs in your
    # browser”一句触发（扩展的转换步骤确实在浏览器里跑），豁免逻辑对扩展页
    # 偏宽松是已知缺口，人工抽查封禁
    "https://nlmexporter.com",
    "https://www.nlmexporter.com",
    # 2026-11-22 22:37 PST 轮自查补封（页面实测确认）：DSU-X AI GEO CMS
    # （ai-geo-cms.dsux.com）与 AI SEO CMS（ai-seo-cms.dsux.com）是 DSU-X
    # 产品子站营销页（“预约演示 查看定价”“支持私有化部署与托管”，留邮箱
    # 预约沟通），点开不能直接用，是售卖演示的 B2B 产品页，不是能直接用
    # 的工具网站；两条链接各拦一条，不封 dsux.com 整个域名
    "https://ai-geo-cms.dsux.com",
    "https://ai-seo-cms.dsux.com",
    # 2026-11-22 22:37 PST 轮自查补封（页面实测确认）：Beauty Advent
    # Guide（beautyadventguide.com）根地址是 2026 美妆倒数日历对比指南
    # 文章（“Prices, Values & Dates”，By Beauty Advent Guide Desk，含
    # 来源引用的长篇对比表），是内容/指南页不是工具站；站内虽有 value
    # calculator 子页，但提交的根链接本身是文章，只拦根链接
    "https://beautyadventguide.com",
    "https://www.beautyadventguide.com",
    # 2026-11-23 16:07 CST 轮自查补封（浏览器实测确认）：
    # Tinker（thinkingmachines.ai/tinker）是 Thinking Machines Lab 的
    # 模型训练平台营销页（客户案例 + 效果数据，讲“训练自己的模型”），
    # 访客点开没有能直接用的工具，要注册/签约才能用服务；标题
    # “Inkling 2 Mini”完全不露痕迹，实测也无安装信号；
    # thinkingmachines.ai 是研究机构站，只拦这一条链接，不封整个域名
    "https://thinkingmachines.ai/tinker",
    "https://thinkingmachines.ai/tinker/?ref=producthunt",
    # 2026-11-23 16:07 CST 轮自查补封（浏览器实测确认）：Open Source
    # Solana Wallet（raul.xyz/wallet）是 iPhone/iPad 端 Solana 钱包
    # 应用的营销页（“An open Solana wallet for iPhone and iPad”，
    # 密钥存设备 Keychain、需 Face ID），须下载安装才能用；标题
    # “Open Source Solana Wallet”不露手机应用痕迹，实测也无安装信号；
    # raul.xyz 是个人站，只拦这一条链接，不封整个域名
    "https://raul.xyz/wallet",
    "https://raul.xyz/wallet/?ref=producthunt",
    # 2026-11-23 20:37 CST 轮自查补封（页面实测确认）：
    # Infiverse（tusharsrivastava.github.io/infiverse）是恶搞型虚构
    # 创业公司页面（“$1 Trillion/Month Platform (Pre-Revenue)”、
    # 点按钮只弹出玩笑文案），没有任何能直接用的工具功能，按只收
    # 工具网站标准拦；tusharsrivastava.github.io 是个人 GitHub Pages，
    # 只拦这一条链接，不封整个域名
    "https://tusharsrivastava.github.io/infiverse",
    # 2026-11-23 06:42 PST 轮自查补封（浏览器实测确认）：
    # MOPy Fish（mopyfish.com）是 1997 年虚拟鱼游戏移植到浏览器，
    # 访客只能给鱼起名、在画布里养鱼互动，无任何工具功能，纯游戏，
    # 按游戏口径一律拦；标题“reverse engineered with AI agents to
    # run in a browser”不露游戏痕迹，标题门与实测信号都拦不住
    "https://mopyfish.com",
    "https://www.mopyfish.com",
    # 2026-11-23 06:42 PST 轮自查补封（浏览器实测确认）：
    # Wall of 2026（wallof2026.com）是社交/时间胶囊参与页，访客写
    # 一句不超过 80 字符的话贴上墙、12 月 31 日封存，无生成、转换、
    # 编辑或计算类工具功能，按只收工具网站标准拦；只拦根链接
    "https://wallof2026.com",
    "https://www.wallof2026.com",
    # 2026-11-23 06:42 PST 轮自查补封（浏览器实测确认）：
    # Agentic Algorithm Engineering（chszlab.github.io/
    # AgenticAlgorithmEngineering）是海德堡大学算法工程组的 agent
    # skill 介绍页，Quick start 是往 Claude Code/Codex 里安装技能，
    # 浏览器内无可直接用的工具界面，须安装进本地编码 agent 才能用，
    # 按“需要下载安装的不算”拦；只拦这一条链接，不封整个域名
    "https://chszlab.github.io/AgenticAlgorithmEngineering",
    # 2026-11-23 07:37 PST 轮热点榜自查补封（页面实测确认）：
    # Return to Repeat（returntorepeat.gusbyheart.se）是一张交互式
    # 音乐专辑站（十首无起止的歌，随时间与月相变化），是歌曲/音乐
    # 内容而非工具，按 11-18 歌曲泄漏口径拦；只拦这一条链接
    "https://returntorepeat.gusbyheart.se",
    # 2026-11-23 08:37 PST 轮热点榜自查补封（页面实测确认）：
    # Kaukana（kaukana.app）是每日地理历史问答游戏（坐火车旅行的
    # 形式），纯游戏，按游戏口径一律拦；只拦根链接
    "https://kaukana.app",
    "https://www.kaukana.app",
    # 2026-11-23 08:37 PST 轮热点榜自查补封（页面实测确认）：
    # Jensen Return（gamemog.com/g/jensen-return）是 GameMog 上的剧情
    # 世界游戏（WASD 移动、开车、打斗、做任务，三幕剧情），纯游戏，按
    # 游戏口径一律拦；GameMog 站内还有别的游戏，只拦这一条链接
    "https://gamemog.com/g/jensen-return",
    # 2026-11-23 08:37 PST 轮热点榜自查补封（页面实测确认）：
    # Long Season（longseason.ecbtx.com）是浏览器里的棒球模拟经营
    # 游戏（逐球模拟、162 场赛季、选秀交易），纯游戏，按游戏口径一律
    # 拦；只拦这一条链接
    "https://longseason.ecbtx.com",
    # 2026-11-23 08:37 PST 轮热点榜自查补封（页面实测确认）：
    # Mcpwatch（mcpwatch.io）是 MCP 工具描述的 lockfile 与运行时守卫，
    # Quickstart 是 pipx install mcpwatch-io，核心用法是本地 CLI
    # （scan/lock/check/guard），站上只有营销页与服务器评分索引，须下载
    # 安装才能用，按“需要下载安装的不算”拦；只拦根链接
    "https://mcpwatch.io",
    "https://www.mcpwatch.io",
    # 2026-11-23 08:37 PST 轮热点榜自查补封（页面实测确认）：
    # Terminal Tasks Open（vetto.ai/companies/terminal-tasks-v2）是介绍
    # 开源终端任务基准集的长文（排行榜、失败分析、构建流程），任务本身
    # 在 GitHub/Harbor Hub，须装 Harbor 才能跑，是文章 + 需安装的数据集，
    # 不是能直接用的工具网站；只拦这一条链接，不封 vetto.ai 整个域名
    "https://vetto.ai/companies/terminal-tasks-v2",
    # 2026-11-23 08:37 PST 轮热点榜自查补封（浏览器实测确认）：
    # ryanpark.ai/claude-skills 是售卖可下载 Claude Skills 的商店
    # （免费与 $4.99/$8.99 的营销 playbook 技能），访客下载 ZIP 后须
    # 自行上传安装到 Claude 里才能用，页上无可直接运行的工具；按
    # “需要下载安装的不算”拦；只拦这一条链接，不封整个域名
    "https://ryanpark.ai/claude-skills",
    # 2026-11-23 10:37 PST 轮热点榜自查补封（页面实测确认）：
    # AgeGuessr（ageguessr.org/en/play/age）是猜照片里真人年龄的游戏
    # （猜对得分、可与朋友对决），纯游戏，无工具功能，按游戏口径一律拦；
    # 整站就是这一个游戏，根地址一并拦
    "https://ageguessr.org/en/play/age",
    "https://ageguessr.org",
    "https://www.ageguessr.org",
    # 2026-11-24 03:07 CST 轮热点榜自查补封（页面实测确认）：
    # Finish the Line（play.neilkakkar.com/finish-the-line）是每日读图猜
    # 线游戏（看半张真实数据图表、手绘后半段走势、按与真实线的距离计分，
    # 每天 3 张图、可翻倍、有连胜），纯游戏，按游戏口径一律拦；站内“More
    # games”说明同站还有别的游戏，但 neilkakkar.com 是作者个人站，只拦
    # 这一条链接，不封整个域名
    "https://play.neilkakkar.com/finish-the-line",
    # 2026-11-24 04:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # Middle Word（pzlgames.com/games/middleword）是每日猜词游戏（在
    # 两个词之间按字母顺序找中间词，十次机会猜中），纯游戏，按游戏口径
    # 一律拦；pzlgames.com 是游戏站，只拦这一条链接，不封整个域名
    "https://pzlgames.com/games/middleword",
    "https://www.pzlgames.com/games/middleword",
    # 2026-11-24 06:07 CST 轮（日报轮）热点榜自查补封（页面实测确认）：
    # Lode Runner 2099（loderunner2099.exe.xyz）是经典 Lode Runner
    # 的浏览器复刻版，纯游戏，无工具功能，按游戏口径一律拦
    "https://loderunner2099.exe.xyz",
    # 2026-11-24 06:07 CST 轮热点榜自查补封（页面实测确认）：
    # Flowers for the Unemployed（flowersfortheunemployed.com）是
    # “关于科技求职的 RPG”浏览器游戏（页上自写“This site is a browser
    # game”），纯游戏，按游戏口径一律拦；只拦根链接
    "https://flowersfortheunemployed.com",
    "https://www.flowersfortheunemployed.com",
    # 2026-11-24 06:07 CST 轮热点榜自查补封（页面实测确认）：
    # Truce（trucehq.com/agents）是供 AI agent 调用的中立调解服务，
    # 页上只有 MCP server 与 JSON API 文档、演示视频，访客点开没有能
    # 直接在浏览器里用的工具界面，纯 API/MCP 平台，按“纯 API 平台不收”
    # 口径拦（与此前 TokLab、ScraperSocial、PennyCompute 同类处理）；
    # 只拦这一条链接，不封 trucehq.com 整个域名
    "https://trucehq.com/agents",
    "https://www.trucehq.com/agents",
    # 2026-11-24 06:07 CST 轮热点榜自查补封（页面实测确认）：
    # BetrayalBench（hive.com/betrayal）是 Hive Research 的基准测试
    # 研究报告页（12 个前沿模型 2448 条议价消息的泄漏数据、图表与
    # “Hive Brief”提示词），是文章/研究报告，不是能直接用的工具网站；
    # 只拦这一条链接，不封 hive.com 整个域名
    "https://hive.com/betrayal",
    "https://www.hive.com/betrayal",
    # 2026-11-24 07:07 CST 轮热点榜自查补封（浏览器实测确认）：
    # anduil.neocities.org/n 是 Flash 游戏 N v2 的 HTML5/WebGL 在线版
    # （标题“我的电脑跑不动这个 Flash 游戏，于是我把它反编译了”自述
    # flash game，点开就是可玩的平台跳跃游戏），纯游戏，按游戏口径
    # 一律拦；neocities.org 是个人站托管平台，只拦这一条链接，不封
    # 整个域名；标题门同步加 flash game 规则
    "https://anduil.neocities.org/n",
    # 2026-11-24 00:07 CST 轮热点榜自查补封（页面实测确认）：
    # Tripup（tripup.me）是“打出不在《圣经》里的单词”的限时打字游戏
    # （计时、加减分、Faceplant 结算），纯游戏，无打字训练之外的工具
    # 功能，按游戏口径（纯游戏一律拦）封禁；只拦这一条链接，不封整个域名
    "https://tripup.me",
    "https://www.tripup.me",
    # 2026-11-24 09:07 CST 轮归档复查补封（11-17 日报 DevHunt 批量条目
    # 人工审描述，个人站/短链域名上的单条泄漏只拦链接，不封整个域名）：
    # frankvitetta.com/ai-scraper 是开源 Python 抓取工具（给 CSV 跑
    # Perplexity/ChatGPT、须本地 Chrome 会话运行），须下载安装才能用；
    # danilqa.github.io/kombinat 是跑在自有 Mac 上的定时 AI agent
    # （Markdown 例程 + Claude Code/Codex CLI），本地运行；
    # myk.sh/mykos 是容器虚拟化基础设施（BYOL Virtualization），不是
    # 点开即用的工具网站；boring-observability.dev/skyline 是 Horizon
    # 的平替（Laravel 队列看板包，装进自有应用里跑），自托管不收
    "https://frankvitetta.com/ai-scraper",
    "https://danilqa.github.io/kombinat",
    "https://myk.sh/mykos",
    "https://boring-observability.dev/skyline",
    # 2026-11-24 09:37 CST 轮热点榜自查补封（页面实测确认）：
    # Word Spies（wordspies.com）是“用一词线索对抗 AI”的文字推理游戏
    # （标题自写“the one-word clue game you play against AI”，站内是开房
    # 间/回放对局的游戏页），纯游戏，按游戏口径（纯游戏一律拦）封禁；
    # 旧条目 wordspies.com/hn 是同一游戏的 HN 入口，一并拦，只拦链接
    "https://wordspies.com",
    "https://www.wordspies.com",
    "https://wordspies.com/hn",
    # 2026-11-24 09:37 CST 轮热点榜自查补封（页面实测确认）：
    # Merget（merget.ai）是 GitHub App：注册后要把 App 安装到仓库里，
    # 合并队列功能在 GitHub 上跑，站本身只是营销/注册页，点开没有能
    # 直接在网站上用的工具；按“须安装才能用不收”口径拦（与浏览器扩展、
    # 桌面应用同类处理），只拦根链接
    "https://merget.ai",
    "https://www.merget.ai",
    # 2026-11-24 16:07 CST 轮自查补封（页面实测确认）：
    # Kodak SlideTag（kodak.retopro.co/products/...）是 34.99 美元实体
    # 钥匙扣盲盒的售卖页（限购、不可取消），是商品页不是工具站；
    # retopro.co 本身是相机配件商店，只拦这一条链接，不封整个域名
    "https://www.kodak.retopro.co/products/kodak-slidetag-br-keychain-photo-display-and-tracker-blind-box?ref=producthunt",
    # Even G2 Enterprise SDK（enterprise.evenrealities.com）是智能眼镜
    # 的开发者 SDK 落地页（申请设备许可、下载 Flutter/Android/iOS 包、
    # 去 GitHub 取资源），须配硬件 + 写代码才能用，不是点开即用的工具
    # 网站；evenrealities.com 本身是眼镜产品站，只拦这一条链接
    "https://enterprise.evenrealities.com/?ref=producthunt",
    # Sotto（sotto.aawej.in）是 Linux 桌面语音听写应用（Wayland/X11，
    # curl 脚本装 .deb 或 AppImage），须下载安装才能用，按“须下载安装
    # 的工具不算”口径拦；aawej.in 是个人站，只拦这一条链接，不封整个域名
    "https://sotto.aawej.in/?ref=producthunt",
    # 2026-11-24 16:07 CST 轮自查补封（页面实测确认）：Astrolabio
    # （glplabs.eu/en/astrolabio）是 macOS 桌面应用（站内自写“Astrolabio
    # is a macOS app”，拖进 Applications 安装、须 macOS 14+），须下载安装
    # 才能用，按“须下载安装的工具不算”口径拦；glplabs.eu 是开发商站，
    # 只拦这一条链接，不封整个域名
    "https://glplabs.eu/en/astrolabio/?ref=producthunt",
    # 2026-11-24 17:07 CST 轮自查补封：Jacket King Returns
    # （arcadeblip.com/game/jacket-king-returns）是 HTML5 Canvas 格斗游戏
    # （Dad 'n Me 风格 beat-em-up），纯游戏，按游戏口径一律拦；标题门与
    # 实测信号都拦不住（页面能正常加载），人工抽查封禁；arcadeblip.com
    # 是游戏站，只拦这一条链接，不封整个域名
    "https://arcadeblip.com/game/jacket-king-returns",
    "https://www.arcadeblip.com/game/jacket-king-returns",
    # 2026-11-24 20:07 CST 轮自查补封：BongBong（bongbong.io）标题自写
    # “A tank shooter and world builder”，坦克射击游戏，纯游戏，按游戏口径
    # 一律拦；标题门与实测信号都拦不住（页面能正常加载），人工抽查封禁
    "https://bongbong.io",
    # 2026-11-24 20:07 CST 轮自查补封：Command 2120
    # （command2120.pvpdock.com）标题自写“Online Browser RTS Game
    # Inspired by Red Alert 2”，在线浏览器即时战略游戏，纯游戏，按游戏口径
    # 一律拦；标题门与实测信号都拦不住，人工抽查封禁
    "https://command2120.pvpdock.com",
    # 2026-11-24 21:37 CST 轮自查补封：Phuzzles（phuzzles.app/daily）
    # 是每日图片拼图游戏（daily photo puzzle，无注册），纯游戏，按游戏口径
    # 一律拦；标题门与实测信号都拦不住（页面能正常加载），人工抽查封禁；
    # phuzzles.app 整站是拼图游戏，只拦这一条链接，不封整个域名
    "https://phuzzles.app/daily",
    # 2026-11-24 22:37 CST 轮自查补封（页面实测确认）：
    # Talon Food Atlas（amunozo.com/talon-food-atlas）是把 30 个营养
    # 分级视频里的 813 种食物汇到一处的浏览页，访客只能翻看食物分级
    # 列表，站上没有能直接用的工具功能，是排名目录/参考站而非工具站，
    # 同当日已封的 EERankings 口径处理；只拦这一条链接，不封整个域名
    "https://www.amunozo.com/talon-food-atlas",
    "https://amunozo.com/talon-food-atlas",
    # 2026-11-24 22:37 CST 轮自查补封：3D story maps in JupyterLab
    # （notebook.link/@arjxn-py/3d-nepal-flood）是 Jupyter 笔记本故事
    # 地图（浏览器标题“3D Nepal Story”，内容是讲尼泊尔洪水的叙事地图），
    # 是可读的互动文章/演示，不是访客能操作使用的工具；且页面须点
    # “Accept and Proceed”接受服务条款、等 Jupyter 环境启动后才能看，
    # 不是点开就能用；notebook.link 是笔记本托管平台，只拦这一条链接，
    # 不封整个域名
    "https://notebook.link/@arjxn-py/3d-nepal-flood",
    # 2026-11-24 23:07 CST 轮自查补封（页面实测确认）：
    # Sobrenna（sobrenna.app）是 iPhone/Android 端戒酒天数计数应用的
    # 营销页（“Download on the App Store / Get it on Google Play”），
    # 须下载安装才能用；实测本轮被豁免放行（页上“sobriety calculator
    # runs in your browser”一句触发了 browser-use 豁免，盖过了 app_store
    # 信号——豁免逻辑对应用营销页偏宽松是已知缺口，与 nlmexporter 同类）；
    # 站内虽有浏览器版戒酒计算器子页，但提交的根链接本身是应用下载页，
    # 只拦根链接，不封整个域名
    "https://sobrenna.app",
    "https://www.sobrenna.app",
    # 2026-11-24 晨间复查补封（页面实测确认）：Liar's Ledger
    # （theliarsledger.com/play）是狼人杀推理网页游戏（“Deduction
    # Game…Loading game files”），纯游戏，按游戏口径一律拦；只拦
    # 这一条链接，不封整个域名
    "https://theliarsledger.com/play",
    "https://www.theliarsledger.com/play",
    # 2026-11-25 04:07 CST 轮热点榜自查补封（页面实测确认）：
    # SlopCheck vs Pangram（slopcheck.io/vs/pangram）是两家 AI 检测器
    # 的对比评测文章页（同一批帖子的得分对照表 + 结论），不是工具本身；
    # slopcheck.io 首页本身是能直接用的免费检测工具，只拦这一条对比页
    # 链接，不封整个域名
    "https://slopcheck.io/vs/pangram",
    "https://www.slopcheck.io/vs/pangram",
    # 2026-11-25 05:37 CST 轮热点榜自查补封（页面实测确认）：
    # The Popular POEM（popularpoem.com/en）是众人合写集体诗的政治发声
    # 艺术项目（“a web site made to act like a tweet laser”，把很多人的
    # 只言片语拼成统一信息发给领导层），不是能反复用的工具网站；受保护
    # 的 POEM 还要订阅付费才能参与；只拦这一条链接，不封整个域名
    "https://www.popularpoem.com/en",
    "https://popularpoem.com/en",
    # 2026-11-25 06:07 CST 轮热点榜自查补封（浏览器实测确认）：Siv
    # （siv.nezin.net）是文明 VI 克隆版浏览器策略游戏（S/C/F/G 资源与
    # 回合计数），纯游戏，按游戏口径一律拦；只拦这一条链接，不封整个域名
    "https://siv.nezin.net",
    # 2026-11-25 06:07 CST 轮热点榜自查补封（浏览器实测确认）：Bubble
    # Shooter（bubble-shooter.net）是经典打泡泡消除游戏（瞄准、计分、
    # 难度模式），纯游戏，按游戏口径一律拦；只拦这一条链接，不封整个域名
    "https://bubble-shooter.net",
    # 2026-11-25 06:07 CST 轮时间线抽查补封：DossierQL
    # （virissimo.info/dossierql）是“学 GraphQL 的游戏”，与已封的
    # Kakurenbo（学假名的 Wordle 游戏）同类，纯游戏、不是能直接用的工具，
    # 按游戏口径一律拦；只拦这一条链接，不封整个域名
    "https://virissimo.info/dossierql",
    # 2026-11-25 09:07 CST 轮时间线抽查补封：铅爆扩散模拟
    # （lead-explosion.vercel.app/map）是爱荷华陆军弹药厂铅爆事件的
    # 扩散范围模拟互动地图，围绕单条时事新闻做的可视化报道，不是能反复
    # 用的工具；与已封的 getlucera.com/iowa-lead-detonation 同类（同
    # 一事件、2026-11-22 22:37 PST 轮已封）；只拦这一条链接，不封整个域名
    "https://lead-explosion.vercel.app/map",
    # 2026-11-25 09:07 CST 轮热点榜自查补封：ClusterBust
    # （clusterbust.com）是每日单词/逻辑解谜游戏（源站摘要自写
    # “Connections meets Snood…clear the board”），纯游戏，按游戏口径
    # 一律拦；只拦这一条链接，不封整个域名
    "https://clusterbust.com",
    "https://www.clusterbust.com",
    # 2026-11-25 09:07 CST 轮热点榜自查补封：End User
    # （enduser.fun）标题自写“a game about smuggling AI chips past
    # export controls”，纯游戏，按游戏口径一律拦；带 ?src=hn 参数的
    # 提交链接与裸链接都拦，不封整个域名
    "https://enduser.fun",
    "https://enduser.fun/?src=hn",
    # 2026-11-25 09:07 CST 轮热点榜自查补封：Where Celebs Go
    # （wherecelebsgo.com/games）标题自写“GeoGuessr for Celebrity
    # Gossip”，名人八卦版 GeoGuessr 猜图游戏，纯游戏，按游戏口径一律拦；
    # 只拦这一条链接，不封整个域名
    "https://wherecelebsgo.com/games",
    "https://www.wherecelebsgo.com/games",
    # 2026-11-25 10:07 CST 轮热点榜自查补封：Chakra
    # （chakra.social）标题自写“Social network with open moderation”，
    # 是社交网络本身，不是点开就能用的工具网站；标题门与实测信号都拦
    # 不住，人工抽查封禁；只拦这一条链接，不封整个域名
    "https://chakra.social",
    "https://www.chakra.social",
    # 2026-11-25 16:37 CST 轮自查补封（浏览器实测确认）：FilteredDelete
    # （algolassi.online/products/filtereddelete）是 Windows/Linux 文件夹
    # 清理桌面应用（.NET 10 自包含构建，Windows x64 / Linux x64 / ARM64
    # 安装包从 GitHub Releases 下载），须下载安装才能用，按“需要下载安装
    # 的工具不算”口径拦；algolassi.online 首页另有浏览器小工具与教程，
    # 只拦这一条下载页链接，不封整个域名
    "https://algolassi.online/products/filtereddelete",
    # 2026-11-25 17:07 CST 轮自查补封（页面实测确认）：
    # TruAstra（truastra.com）是吠陀占星每日解读站（输入出生日期时间地点、
    # 浏览器里算出当日星盘解读与三件小事），娱乐向占卜内容，不是工具网站；
    # 按 Two Divinations 娱乐占卜不收的口径拦；整站就是这一个产品，根链接
    # 与本次上榜链接都拦
    "https://truastra.com/?ref=producthunt",
    "https://truastra.com",
    # 2026-11-25 17:07 CST 轮自查补封（页面实测确认）：
    # Airbot（airbots.ai）是 11-20 日报遗留未翻译条目，实测发现站上只有
    # 等候名单营销页（“We're opening the doors very soon…skip the waitlist”），
    # 产品尚未开放，点开只能留邮箱等开通；按 xargaar-tools 等候名单页与
    # vouchgeo.com 根链接先例拦；整站目前就是这一个等候页，根链接与本次
    # 上榜链接都拦
    "https://airbots.ai/?ref=producthunt",
    "https://airbots.ai",
    # 2026-11-25 17:07 CST 轮自查补封（页面实测确认）：
    # PeoplePlotr 编程语言家谱（peopleplotr.com/storytree/guide/programming-languages）
    # 是可交互的编程语言族谱可视化/指南页（拖动、缩放、点人查看），只能浏览
    # 这一棵现成的树，不是能反复用的工具；按 getlucera 互动可视化报道与
    # Riemann Guides 目录页先例拦；站内另有“Create your own tree”制树工具，
    # 只拦这一条指南链接，不封整个域名
    "http://www.peopleplotr.com/storytree/guide/programming-languages",
    # 2026-11-25 17:07 CST 轮自查补封（页面实测确认）：
    # 3way.Social（3way.social/for-ai-agents/）是外链买卖市场写给 AI 助手
    # 的简报页（买/卖/换外链、SEO 打包服务 $975–$5,700），链到的是营销
    # 简报页而非能直接用的工具；站内另有免费域名外链价值查询等小工具，
    # 只拦这一条链接，不封整个域名
    "https://3way.social/for-ai-agents/?ref=producthunt",
    "https://3way.social/for-ai-agents/",
    # 2026-11-25 06:07 PST 轮热点榜自查补封（页面实测确认）：三条纯游戏——
    # Qake（qake.se）是浏览器里的 2.5D 体素多人射击游戏（选昵称、进大厅、
    # 开火对战）；Zork（sid2364.github.io/zork）是 D&D 风格文字冒险游戏
    # （走格子、打怪、记分）；Clashroids（clashroids.com）是 50 人多人太空
    # 对战游戏（Asteroids 玩法、抢地盘、PvP）；三条都是纯游戏，按游戏口径
    # 一律拦，只拦精确链接，不封整个域名
    "https://qake.se",
    "https://www.qake.se",
    "https://sid2364.github.io/zork",
    "https://clashroids.com",
    "https://www.clashroids.com",
    # 2026-11-25 06:07 PST 轮热点榜自查补封（页面实测确认）：Rethink Phone
    # （rethinkphone.tech）是“数字幕僚长”概念手机的项目展示页（设计理念、
    # 通话演示视频、实验记录），访客在浏览器里用不了任何工具，按只收工具
    # 网站标准拦；只拦这一条链接，不封整个域名
    "https://rethinkphone.tech",
    "https://www.rethinkphone.tech",
    # 2026-11-25 08:37 PST 轮热点榜自查补封（页面实测确认）：三条泄漏——
    # AIgarchy（aigarchy.samuelberton.com）是“Datacenter Executive
    # Tycoon”数据中心大亨经营游戏，纯游戏，按游戏口径一律拦；
    # Little Rally（riyad.ing/little-rally）是浏览器拉力赛驾驶游戏
    # （油门/刹车/转向/手刹、计时跑碎石路），纯游戏，按游戏口径一律拦；
    # Zero to Riemann Zeros（academy.functorial.inc/courses/riemann）
    # 是 18 单元 223 习题的 Lean 黎曼猜想在线课程（须邮箱注册），本质是
    # 课程内容平台，不是点开就能用的工具网站，按只收工具网站标准拦；
    # 三条都只拦精确链接，不封整个域名
    "https://aigarchy.samuelberton.com",
    "https://riyad.ing/little-rally",
    "https://academy.functorial.inc/courses/riemann",
    # 2026-11-25 12:37 PST 轮热点榜自查补封（页面实测确认）：
    # PaperBoy（niclas.lalo.li）是童年街机游戏 PaperBoy 的重制版
    # （“Niclas First Job - the Game”，街机框 + 等距像素街道），纯游戏，
    # 按游戏口径一律拦；niclas.lalo.li 是个人站，只拦这一条链接
    "https://niclas.lalo.li",
    # Eggsimulator（eggeggegg.vercel.app）是浏览器里的鸡蛋模拟玩具
    # （全屏 canvas 点鸡蛋），没有任何工具功能，不是转换/生成/计算/
    # 编辑类工具，按严格工具-only 标准拦；只拦这一条链接
    "https://eggeggegg.vercel.app",
    # SubReddit Marketing（subredditmarketing.co）是付费 Reddit 发帖
    # 营销服务售卖页（“Reddit posts from $250, live in 24 hours”，下单
    # 后由对方代发），访客点开不能自己用任何工具，是售卖页不是工具站，
    # 按售卖页不收口径拦；只拦这一条链接
    "https://subredditmarketing.co",
    "https://www.subredditmarketing.co",
    # 2026-11-26 09:07 CST 轮热点榜自查补封（浏览器实测确认）：PortalGate
    # （portalgate-landing.vercel.app）是付费 monday.com 客户门户应用的营销
    # 落地页（$39/月起，14 天试用，入口链向 monday.com 应用市场），页面本身
    # 没有能直接用的工具，按严格工具-only 标准拦；vercel.app 是通用托管域，
    # 只拦这一条链接，不封整个域名
    "https://portalgate-landing.vercel.app",
    "https://portalgate-landing.vercel.app/",
    # 2026-11-26 22:07 CST 轮时间线抽查补封（浏览器实测确认）：flying-test
    # （crocone.github.io/flying-test）是开源飞行测试台硬件项目的展示页
    # （俄语页面：测试台参数），访客点开用不了任何浏览器工具，是项目页
    # 不是工具站；只拦这一条链接，不封 crocone.github.io 整个域名
    "https://crocone.github.io/flying-test",
    # 2026-11-26 22:07 CST 轮时间线抽查补封（浏览器实测确认）：Game DNA
    # （game-dna.pages.dev/site/preview）是 103 个游戏元素的代码模块 +
    # 提示词库，访客复制提示词让自家 coding agent 接入，本质是面向开发
    # 者的代码库目录（含多个可玩小游戏），不是能直接用的工具；只拦这一
    # 条链接，不封 game-dna.pages.dev 整个域名
    "https://game-dna.pages.dev/site/preview",
    # 2026-11-26 07:07 PST 轮热点榜自查补封（浏览器实测确认）：
    # steve.ly/travels 是个人十年旅行博客（各国游记、住宿/航班统计、
    # 餐厅推荐），内容是文章与个人记录，点开没有能直接用的工具功能，
    # 按“不收文章/博客”标准拦；steve.ly 是个人站，只拦这一条链接，
    # 不封整个域名
    "https://steve.ly/travels",
    "https://steve.ly/travels/",
    # 2026-11-26 07:07 PST 轮热点榜自查补封（浏览器实测确认）：
    # evalkit.inferedge.com 是智能体评估工具 Evalkit 的营销落地页，
    # 页上没有能直接用的交互工具，只能复制安装命令（uv tool install
    # evalkit-py）或去登录/注册托管版；工具本身开源可自托管，按
    # “不收自托管工具、须下载安装的不算、点开就能用”标准拦；只拦这
    # 一条链接，不封整个域名
    "https://evalkit.inferedge.com",
    "https://evalkit.inferedge.com/",
    # 2026-11-26 22:07 CST 轮时间线抽查补封（浏览器实测确认）：PokerAmp
    # （pokeramp.com）是纯娱乐玩法币德州扑克 GTO 训练与 AI 陪练，含单桌
    # 赛、每日挑战、人格化对手，本质是打扑克的游戏（虽标榜训练，玩的活
    # 动本身就是扑克），按游戏口径（纯游戏一律拦）封禁；只拦这一条链接，
    # 不封整个域名
    "https://pokeramp.com",
    "https://www.pokeramp.com",
    # 2026-11-27 00:37 CST 轮自查补封（页面实测确认）：Manabrew
    # （play.manabrew.app）是在浏览器里打万智牌（Magic: The Gathering，
    # Forge/WASM 引擎）的纯游戏，无工具功能，按游戏口径（纯游戏一律拦）
    # 封禁；只拦这一条链接，不封 manabrew.app 整个域名
    "https://play.manabrew.app",
    # 2026-11-27 00:37 CST 轮自查补封（页面实测确认）：Voom
    # （voom.ink/agents）是“Human feedback, as an API”，供 Claude、
    # ChatGPT、Codex、Cursor 等智能体调用的人类反馈 API，纯 API 平台，
    # 点开不能直接在浏览器里用，按“纯 API 平台不收”口径拦（与此前
    # TokLab、PennyCompute 同类处理）；只拦这一条链接，不封 voom.ink
    # 整个域名
    "https://voom.ink/agents",
    "https://www.voom.ink/agents",
    # 2026-11-27 00:37 CST 轮自查补封（页面实测确认）：Hubris
    # （hubris.live）是桌面端协作笔记应用的售卖页（“Download v3”、
    # “Purchase license $35”、“add up to 4 devices”，经 yard.sh 结账），
    # 须下载安装才能用，按“需要下载安装的工具不算”拦；只拦这一条链接，
    # 不封整个域名
    "https://hubris.live",
    "https://www.hubris.live",
    # 2026-11-27 00:37 CST 轮自查补封（页面实测确认）：PauseCrew
    # （pausecrew.com）根地址是“第二意见”社区站首页（发帖问买不买、
    # 等社区给意见、动态信息流），本身不是工具；站内 /tools/ 下虽有
    # cost-per-use、gift-finder 等小工具，但提交的根链接不是工具页，
    # 按“只拦根链接”先例（Beauty Advent Guide）拦；只拦这一条链接，
    # 不封整个域名
    "https://pausecrew.com",
    "https://www.pausecrew.com",
    # 2026-11-27 00:37 CST 轮自查补封（页面实测确认）：WorkingRemote
    # （workingremote.pl/en）是波兰/中东欧远程技术招聘的比价与内容站
    # 首页（招聘平台对比、人才指数、指南），本身不是能直接用的计算器；
    # 标题“WorkingRemote B2B Calculator”名不副实，链到的 /en 页没有
    # 计算器入口；只拦这一条链接，不封整个域名
    "https://workingremote.pl/en",
    # 2026-11-27 01:37 CST 轮热点榜自查补封（浏览器实测确认）：三条泄漏——
    # BenchSaaS（nocoly.com/landing/benchsaas）是“企业应用 LLM 基准报告
    # V1.0”落地页（关键发现、排行榜、案例、方法论，附 51 页 PDF 下载），是
    # 读的报告不是能用的工具，按“不收文章”拦；CSS 3D 演示（k-adam.github.io/
    # CSS3D-Renderer/demos/lights-out）是纯 CSS 3D 光影技术演示（滚动走近、
    # 看墙上的页面），在浏览器里跑演示、看效果，没有任何工具功能，按严格
    # 工具-only 标准拦（同 GPU Demo Gallery 先例）；Turkey Hand
    # （highdimensionalcoconuts.com/Work/Sandbox/TurkeyHand）是用 AR 把手变
    # 成火鸡的新奇小玩具，没有任何工具功能，按严格工具-only 标准拦；三条都
    # 只拦精确链接，不封整个域名
    "https://www.nocoly.com/landing/benchsaas",
    "https://k-adam.github.io/CSS3D-Renderer/demos/lights-out/index.html",
    # 2026-11-27 03:13 CST 中午汇总核验补封（与 lights-out 同仓库的纯演示）：
    # CSS 3D 码头漫步（k-adam.github.io/CSS3D-Renderer/demos/still-water）
    # 站内只有一句 "Scroll to walk out along the dock"，滚动走出码头、
    # 看水面效果，没有任何工具功能，按严格工具-only 标准拦；只拦精确
    # 链接，不封整个域名
    "https://k-adam.github.io/CSS3D-Renderer/demos/still-water/index.html",
    "https://www.highdimensionalcoconuts.com/Work/Sandbox/TurkeyHand",
    # 2026-11-27 08:07 CST 轮热点榜自查补封（页面实测确认）：两条纯游戏——
    # Isekai Boys（i.0oat.com）是浏览器乙女恋爱游戏（异世界恋爱、100 多位
    # 男性角色、结婚即通关），标题门已同步加 otome game 规则；Dailydev
    # （dailydev.gg）是每日开发者知识问答（每天 5 道题、全员同题），标题与
    # 信源摘要都不露游戏痕迹、标题门拦不住，按 Think Complete（每日解谜）
    # 与 Dawdle（每日拼词）先例只拦精确链接；两条都不封整个域名
    "https://i.0oat.com",
    "https://dailydev.gg",
    # 2026-11-27 08:07 CST 轮热点榜自查补封（页面实测确认）：三条演示/
    # 浏览类泄漏，都不是能直接用的工具——Sandpile Lab（hrih.si/projects/
    # sandpile-lab）是撒沙看分形与雪崩的元胞自动机模拟玩具，只看不做事，
    # 与此前已封的 GPU Demo Gallery、CSS3D 码头漫步同类；Eyes on the
    # Cosmos（foaktee.github.io/rubin-euclid-discovery/eyes_3d）是三维
    # 太阳系与银河系浏览可视化，与此前已封的 HN 话题条形图竞逐同类；
    # Alpoge（maic.me/alpoge）是 1700 万行黎曼猜想 Lean 证明的浏览
    # 器，只浏览单一数据集、无通用任务功能，与上面两条同类；标题都不露
    # 通用可拦的说法，只拦精确链接，不封整个域名
    "https://hrih.si/projects/sandpile-lab",
    "https://hrih.si/projects/sandpile-lab/",
    "https://foaktee.github.io/rubin-euclid-discovery/eyes_3d",
    "https://maic.me/alpoge",
    "https://maic.me/alpoge/",
    # 2026-11-27 18:07 CST 轮缺翻译自查补封（页面实测确认）：Factoroids
    # （rupertlinacre.com/facteroids）是心算游戏（WebGL 图形、计分
    # 回合），纯游戏、不是能直接用的工具，按游戏口径一律拦；与已封的
    # Kakurenbo（学假名的 Wordle 游戏）、DossierQL（学 GraphQL 的游戏）
    # 同类；只拦这一条链接，不封 rupertlinacre.com 整个域名
    "https://rupertlinacre.com/facteroids",
    # 2026-11-28 09:07 CST 轮热点榜自查补封（标题自述确认）：Far Worlds
    # （farworlds.com/play）是浏览器里跑的多人合作体素 RPG 游戏
    # （WebGPU/WebRTC），纯游戏，按游戏口径一律拦；标题门同步加 RPG
    # 规则；只拦这一条链接，不封 farworlds.com 整个域名
    "https://farworlds.com/play",
    "https://www.farworlds.com/play",
}
# 文章味路径段（按段全等匹配）
ARTICLE_PATH_SEGMENTS = {
    "blog", "blogs", "news", "posts", "post", "article", "articles",
    "story", "stories", "p", "journal", "docs", "documentation",
    "wiki", "changelog", "press",
    "insights", "press-releases", "news-centre", "newsroom", "cover",
    "opinion", "magazine", "podcast", "podcasts", "videos", "features",
    "analysis", "books", "category", "tag", "author", "archives",
    "coding",
    # “the making of”类幕后文章页（2026-11-16 22:00 轮：daventry.io/making-of）
    "making-of",
    # 研究/调研文章页（2026-11-17 11:07 CST 轮：kobi.music/research/dettato
    # 是音频转 MIDI 模型的发布长文，内嵌演示只是文章一小部分，不是工具站
    # 本身；全库 5 条含 research 路径段的均为文章/研究介绍页，无一是工具）
    "research",
    # 基准测试评测文章页（2026-11-19 20:07 CST 轮：contextflo.com/
    # benchmarks/dabstep-haiku 是“给 AI 智能体加业务上下文有没有用”的
    # 评测长文，不是能直接用的工具；全库仅此 1 条含 benchmarks 路径段）
    "benchmarks",
    # 共享对比结果页（2026-11-22 02:07 CST 轮：keepplain.com/b/... 是
    # “Codex 与 Claude 各建一个 Three.js 章鱼逃出玻璃罐”的四路对比展示页，
    # 点开是别人的会话结果展示，不是能直接用的工具；keepplain.com 首页
    # /transcript 本身是能用的会话查看工具，只拦 /b/ 路径段；离线验过
    # 全库 1176 条过门条目，只多拦这一条，0 误伤）
    "b",
}
# 文档/API 参考味路径段：链到 API 文档、开发者文档页的不是能直接用的
# 工具站本身（2026-11-18 18:37 CST 轮：readplace.com/developers 是
# “Build on the Readplace API”文档页，却进了热点榜；离线验过全库 745 条
# 过门条目，这组段只多拦 hissingkitty.com/developers 一条——也是 MCP
# 服务器介绍页，0 误伤）
DOC_PATH_SEGMENTS = {
    "developers", "developer", "api", "api-docs", "apidocs",
    "reference", "openapi", "swagger",
    # “doc”路径段：链到 /doc/... 的是文档页，不是工具本身
    # （2026-11-20 03:07 CST 轮：Ufatfs 链到 fossil 仓库的
    # /ufatfs/doc/trunk/README.md；离线验过全库 940 条过门条目，
    # 只多拦这一条，0 误伤）
    "doc",
}
# 下载/安装味路径段：链到下载页、安装页、发布包、扩展页的都不是在线工具
DOWNLOAD_PATH_SEGMENTS = {
    "download", "downloads", "dl", "installer", "install", "setup",
    "releases", "release", "extension", "extensions",
}
# 安装包文件后缀：链到安装包本身的也不是在线工具
DOWNLOAD_EXTENSIONS = (
    ".exe", ".dmg", ".apk", ".msi", ".pkg", ".deb", ".rpm",
    ".appimage", ".msix", ".appxbundle", ".iso", ".cab", ".bin",
    ".zip", ".tar.gz", ".tgz",
)


_YEAR_SEG = re.compile(r"^(19|20)\d{2}([-.]\\d{1,2}([-.]\\d{1,2})?)?$")
_MONTH_SEG = {
    "january", "february", "march", "april", "may", "june", "july",
    "august", "september", "october", "november", "december",
    "jan", "feb", "mar", "apr", "jun", "jul", "aug", "sep", "sept",
    "oct", "nov", "dec",
}


def tool_gate(url):
    """目标链接收录判定：返回 (通过, 原因)，原因仅在不通过时有值。"""
    if not url:
        return False, "no_url"
    try:
        u = urllib.parse.urlparse(url)
    except ValueError:
        return False, "bad_url"
    if u.scheme not in ("http", "https"):
        return False, "bad_scheme"
    host = (u.hostname or "").lower()
    if (not host or "." not in host or host == "localhost"
            or host.endswith((".local", ".test", ".example", ".invalid"))):
        return False, "bad_host"
    if host.split(".")[0] in ("blog", "docs", "news"):
        return False, "blocked_subdomain"
    for d in BLOCKED_DOMAINS:
        if host == d or host.endswith("." + d):
            return False, "blocked_domain"
    if host in BLOCKED_EXACT:
        return False, "blocked_domain"
    if norm_link(url) in BLOCKED_URLS:
        return False, "blocked_domain"
    # Cookie 检查页（__cookie_check.html）：点开是“授权安全 Cookie”的
    # 拦截页，不是工具本身；实测 TalentRadar 的根地址本身也是这个拦截页，
    # 访客点开用不了工具（2026-11-16 晚间轮）
    if "__cookie_check" in u.path:
        return False, "cookie_check"
    # Hugging Face：模型/数据集页是仓库页（Quick start 是 pip install +
    # hf download，要下载安装才能用），一律拦；只放行 /spaces/——Spaces
    # 是能直接在浏览器里用的在线应用（2026-11-16 时间线泄漏：
    # Nano-Edge-TTS 链到 huggingface.co/drmhse/nano-edge-tts 模型页）
    if host == "huggingface.co" or host.endswith(".huggingface.co"):
        if not u.path.startswith("/spaces/"):
            return False, "blocked_domain"
    segs = [s.lower() for s in u.path.split("/") if s]
    if any(s in ARTICLE_PATH_SEGMENTS for s in segs):
        return False, "article_path"
    # 文档/API 参考页：API 文档、开发者文档不是能直接用的工具站
    if any(s in DOC_PATH_SEGMENTS for s in segs):
        return False, "doc_path"
    # 日期路径（/2026/11/14/、/2023/08/20/、/2014/february.htm 等）几乎只
    # 出现在博客/新闻文章链接上；工具站首页或功能页不会用年份做路径段
    for s in segs:
        if _YEAR_SEG.match(s) or s in _MONTH_SEG:
            return False, "article_path"
    # 下载/安装：链到下载页、安装页、发布包、扩展页或安装包文件的，
    # 打开就要下载安装，不是“在网站上就能用”的工具
    if any(s in DOWNLOAD_PATH_SEGMENTS for s in segs):
        return False, "download_page"
    _path_low = u.path.lower()
    if any(_path_low.endswith(ext) for ext in DOWNLOAD_EXTENSIONS):
        return False, "download_file"
    # 文档源文件（README.md 之类的 Markdown/纯文本文件）：点开是文档
    # 内容，不是能直接用的工具站（2026-11-20 03:07 CST 轮：Ufatfs 链到
    # fossil 仓库的 README.md；离线验过全库 940 条过门条目，只拦这一条，
    # 0 误伤）
    if _path_low.endswith((".md", ".rst", ".txt")):
        return False, "doc_file"
    return True, ""


# 标题里的“要下载安装”信号（2026-11-16 用户补充：工具必须完全在网站
# 上就能用）。只拦表意明确的：下载/平台专属应用/自托管/扩展。标题里
# 明确写“免安装/无需安装/不用安装/无需下载”的，反而是在线工具，不拦。
_TITLE_EXEMPT = ("免安装", "无需安装", "不用安装", "无需下载", "不用下载",
                 "no install", "no download", "no installation",
                 "runs in your browser", "in your browser", "web-based",
                 "browser-based")
_TITLE_BLOCK_RES = [
    re.compile(p, re.IGNORECASE) for p in (
        r"download\s+(for|on|now|free)\b",
        r"\bfor\s+(windows|mac|macos|ios|android|linux|iphone|ipad)\b",
        r"\bon\s+your\s+(mac|windows|iphone|ipad|android)\b",
        r"\bon\s+(macos|windows|ios|android|linux)\b",
        # “on Mac”（如“Best volume mixer on Mac?”）：Mac 桌面应用的典型说法，
        # 网页工具标题里不会出现“on Mac”（2026-11-18 08:07 CST 轮：MacAudio；
        # 离线验过 522 条在榜条目，只拦 MacAudio 一条，0 误伤）
        r"\bon\s+mac\b",
        r"\b(mac|macos|windows|ios|android|linux)\s+"
        r"(app|assistant|client|software|version|edition|dictation)\b",
        # “Mac Mini 应用”（如“Build native Mac Mini apps”）：“Mac Mini”
        # 中间隔了 Mini，上面那条拦不住；Mac Mini 只能指苹果硬件，网页工具
        # 标题里不会出现（2026-11-17 02:40 CST 轮：View）
        r"\bmac\s+mini\b",
        r"\b(desktop|mobile)\s+(app|application|version|edition|client|software)\b",
        # “任务栏”（如“lyrics in your taskbar”）：任务栏是 Windows 桌面
        # 专属概念，网页工具标题里不会出现（2026-11-17 03:00 CST 轮：Lirico）
        r"\btaskbar\b",
        r"\b\w+\s+desktop\b",
        r"\bapp\s+store\b",
        r"\bgoogle\s+play\b",
        r"\b(chrome|firefox|edge|safari|browser|vscode)\s+extension\b",
        # 插件（如“Claude Code plugin”）：插件要装进宿主应用里才能用，
        # 不是“在网站上就能用”的工具（2026-11-17 03:37 CST 轮：Chisle）
        r"\bplugin\b",
        r"插件",
        # MCP 服务器（如“An MCP server for searching …”）：MCP 服务器要接
        # MCP 客户端才能用，官网只是服务地址与接入手册，浏览器里没有能直接
        # 用的工具本身；域名门同步封 agentsinthewild.co
        # （2026-11-17 20:07 CST 轮：Agents in the Wild）
        r"\bmcp\s+server\b",
        # “API and MCP”（如“Built a cheap and fast YouTube transcription
        # API and MCP”）：标题明说产品是 API + MCP 服务，要写代码或接 MCP
        # 客户端才能用，链到的也是 API 落地页而非浏览器里能直接用的工具；
        # 注意 getyoutubetext.com 根地址本身是能直接用的转录工具，只拦
        # 标题，不封域名（2026-11-21 19:37 CST 轮：该条已进热点榜；离线验过
        # 全库 3834 条在库条目，只多拦这一条，0 误伤）
        r"\bapi\s+and\s+mcp\b",
        r"\bmcp\s+and\s+api\b",
        # “Job Board”（如“Job Board for Data Engineers”）：招聘信息目录站，
        # 访客只能浏览职位列表、点出站外投递，站上没有能直接用的工具；同已封
        # 的 jobswithpay.com、remotejobsrock.com、getdataengineeringjobs.com
        # （2026-11-24 03:07 CST 轮：该条已进热点榜；离线验过全库 4423 条
        # 在库条目，只多拦这 3 条招聘版，0 误伤）
        r"\bjob\s+board\b",
        # 邮件课程（如“MIT's How to Make (Almost) Anything as a 100-day
        # email course”）：填邮箱后每天收课，站上没有能直接用的工具；
        # 域名门同步封 htmaa.clarkdinnison.com
        # （2026-11-19 00:07 CST 轮：MIT 邮件课程进了热点榜）
        r"\bemail\s+course\b",
        r"邮件课程",
        # 时事新闻站（如“Wikipedia Current Event Portal as an Actual
        # Newspaper”）：站本身就是新闻内容（报纸版式呈现维基百科时事），
        # 不是能用的工具；只拦“current event(s)”这一表意明确的说法，
        # 不拦 newspaper——Daily Scribe 是给 Kindle 生成日报的工具，
        # 标题也带 newspaper（2026-11-20 09:37 CST 轮：wikinews-rss
        # 已进热点榜；离线验过 3519 条在库条目，只拦这一条，0 误伤）
        r"\bcurrent events?\b",
        r"时事新闻",
        # CLI / 命令行工具（如“a refactoring CLI for coding agents”）：
        # 要下载安装才能用，不是“在网站上就能用”的工具
        # （2026-11-16 22:00 轮：Claktor）
        r"\bcli\b",
        # 自托管：除 self-hosted / self hosted 外，还有“(self) hosted”
        # 这种带括号的写法（2026-11-16 22:00 轮：Ivy）
        r"\bself[\)\s\-]*hosted\b",
        # 游戏 mod（如“a Factorio mod for GPU nerds”）：mod 要下载安装到游戏
        # 里才能用，不是“在网站上就能用”的工具；域名门同步封 mods.factorio.com
        r"\bmod\b",
        # 编程语言（如“Show HN: Tyrus – TypeScript Syntax. Rust Semantics.
        # Programming Language”）：语言工具链要下载安装才能用，链到的官网
        # 只是文档站；浏览器里直接用的在线 Playground 另有子域地址，标题带
        # “runs in your browser”等豁免词时不拦（2026-11-16 23:30 轮：Tyrus）
        r"\bprogramming language\b",
        # hypervisor（如“Show HN: NOS x86-64 hypervisor, written in Rust”）：
        # 虚拟机监控程序是装到裸机服务器上的基础设施，不是能在浏览器里直接
        # 用的工具；域名门同步封 nos-os.tech（2026-11-17 07:00 轮：NOS）
        r"\bhypervisor\b",
        # 文件系统（如“Show HN: Ufatfs: Unix overlay file system for
        # VFAT/exFAT”）：文件系统是装到操作系统里的系统软件，要下载安装
        # 才能用，不是能在浏览器里直接用的工具；标题带“in your browser”
        # 等豁免词时不拦（2026-11-20 03:07 CST 轮：Ufatfs 混入热点榜；
        # 离线验过全库 940 条过门条目，只拦这一条，0 误伤；域名门同步封
        # fossil.chungy.name）
        r"\bfile\s?system\b",
        # 个人作品集主页（如“My developer portfolio with an interactive
        # terminal”）：点开是自我介绍和服务列表，不是能用的工具；只拦
        # 表意明确的“作品集主页”说法，不拦 portfolio tracker 之类的工具
        # （2026-11-16 晚间轮：yashnandvana.in）
        r"\bmy\s+developer\s+portfolio\b",
        r"\bdeveloper\s+portfolio\b",
        r"\bportfolio\s+(website|site|page)\b",
        r"个人作品集",
        r"下载.{0,6}(windows|mac|ios|安卓|苹果|桌面|电脑|手机)",
        r"(windows|mac|macos|ios|安卓|苹果)版",
        r"在\s*(iphone|ipad|安卓|苹果手机|手机)\s*上",
        r"桌面版|桌面应用|客户端|浏览器扩展|浏览器插件|应用商店|免费下载",
        r"自托管",
        r"下载安装|下载.{0,4}安装",
        # 抽奖/赠送推广页（如“Free Plus Friday – first 3 sign-ups each
        # Friday get a year of Plus free”）：前 N 名注册送一年会员，是推广
        # 活动页，不是能直接用的工具；只拦“前 N 名…得…免费”这种表意明确
        # 的抽奖说法（2026-11-22 02:07 CST 轮：NovaBuddy 混入热点榜；
        # 离线验过全库 1176 条过门条目，只拦这一条，0 误伤）
        r"\bfirst\s+\d+\b.*\bget\b.*\bfree\b",
        # 纯游戏的明确说法（如“a pseudo-3D arcade racer”）：
        # arcade racer / racing game 都是游戏类型自述，网页工具标题里
        # 不会出现；arcade game 同理
        # （2026-11-22 01:07 CST 轮：TEB RUN 街机赛车纯游戏混入热点榜；
        # 离线验过全库 4119 条在库条目，arcade racer 只拦 TEB RUN 一条、
        # racing game 只拦已封域名的 outpostracer 一条、arcade game 0 条，
        # 0 误伤）
        r"\barcade racer\b",
        r"\barcade game\b",
        r"\bracing game\b",
        # 纯游戏的明确说法（如“a browser game”“a daily tile puzzle”）：
        # browser game / tile puzzle 都是游戏类型自述，网页工具标题里
        # 不会出现
        # （2026-11-23 09:37 CST 轮：Show HN 两条纯游戏混入热点榜——
        # 80 年代 Skyrim 风浏览器游戏 thanes-quest 与每日 tile puzzle
        # Lotlark；离线验过全库 4182 条在库条目，browser game 命中 12 条、
        # 过门条目中 6 条全是纯浏览器游戏、0 误伤；tile puzzle 只拦
        # Lotlark 一条，0 误伤）
        r"\bbrowser game\b",
        r"\btile puzzle\b",
        # “puzzle game”（如“Show HN: I built a laser puzzle game …”）：
        # 解谜游戏的明确说法，网页工具标题里不会出现
        # （2026-11-24 08:37 PST 轮：Laser Grid 激光解谜纯游戏混入热点榜；
        # 离线验过全库 4755 条在库条目，命中 7 条全是纯解谜游戏，0 误伤；
        # 链接门同步封 lasergrid.app）
        r"\bpuzzle game\b",
        # “mini-game / mini game”（如“Show HN: Borderdraw (Web
        # Mini-Game)”）：小游戏的明确说法，网页工具标题里不会出现
        # （2026-11-23 16:07 CST 轮：Borderdraw 混入当日时间线；离线验过
        # 全库 4287 条在库条目，只拦这一条，0 误伤；域名门同步封 crux.quest）
        r"\bmini[\s\-]?game\b",
        # “flash game”（如“Show HN: My computer was too slow to run this
        # Flash game, so I decompiled it”）：Flash 游戏的明确说法，网页
        # 工具标题里不会出现
        # （2026-11-24 07:07 CST 轮：该条已进热点榜；离线验过全库 4453 条
        # 在库条目，只拦这一条，0 误伤；链接门同步封 anduil.neocities.org/n）
        r"\bflash game\b",
        # “otome game”（如“Show HN: Isekai Boys – a free browser otome
        # game with over 100 love interests”）：乙女恋爱游戏的类型自述，
        # “browser otome game”里 browser 与 game 之间隔了 otome，旧的
        # browser game 规则拦不住；网页工具标题里不会出现
        # （2026-11-27 08:07 CST 轮：Isekai Boys 已进热点榜；离线验过
        # 全库 5313 条在库条目，只拦这一条，0 误伤；链接门同步封 i.0oat.com）
        r"\botome game\b",
        # “stealth game”（如“Show HN: Flokk Hunter – a browser stealth
        # game about surveillance cameras”）：潜行游戏的类型自述，网页
        # 工具标题里不会出现
        # （2026-11-28 12:07 CST 轮：Flokk Hunter 纯浏览器潜行游戏混入
        # 热点榜；离线验过全库 5520 条在库条目，只拦这一条，0 误伤；
        # 链接门同步封 www.zeitgames.com/games/flokk-hunter）
        r"\bstealth game\b",
        # “racer”（如“Show HN: Paper Sky Rally – a multiplayer paper-plane
        # racer in the browser”）：赛车/竞速游戏的明确说法，网页工具标题里
        # 不会出现
        # （2026-11-27 23:07 CST 轮：Paper Sky Rally 纯纸飞机竞速游戏混入
        # 热点榜；离线验过全库 5459 条在库条目，标题命中 3 条全是纯竞速游戏
        # （Wipeout 风格迷你赛车、TEB RUN 街机赛车、Paper Sky Rally），0 误伤；
        # 链接门同步封 paperskyrally.com）
        r"\bracer\b",
        # “backgammon”（如“Show HN: A free browser backgammon club,
        # gnubg's net under the hood”）：西洋双陆棋就是棋类游戏，网页工具
        # 标题里不会出现
        # （2026-11-28 04:37 CST 轮：The Velvet Point 纯双陆棋游戏混入
        # 热点榜；离线验过全库 5499 条在库条目，只拦这一条，0 误伤；
        # 域名门同步封 spawn.co）
        r"\bbackgammon\b",
        # “audiobook”（如“Show HN: Free audiobook and eBook with the story
        # of recent discoveries in math”）：有声书本身是音频内容，不是能
        # 直接用的工具，网页工具标题里不会出现
        # （2026-11-28 04:37 CST 轮：After Proof 有声书/电子书混入热点榜；
        # 离线验过全库 5499 条在库条目，只拦这一条，0 误伤；链接门同步封
        # labs.opentangle.com/after-proof）
        r"\baudiobook\b",
        # “a game about …”（如“Show HN: End User, a game about smuggling
        # AI chips past export controls”）：标题自认是游戏，网页工具标题里
        # 不会出现
        # （2026-11-25 09:07 CST 轮：End User 混入热点榜；离线验过全库
        # 4831 条在库条目，只拦这一条，0 误伤；链接门同步封 enduser.fun）
        r"\ba game about\b",
        # “GeoGuessr”（如“Show HN: GeoGuessr for Celebrity Gossip”）：
        # 标题提到 GeoGuessr 就是猜图游戏或其克隆，网页工具标题里不会出现
        # （2026-11-25 09:07 CST 轮：Where Celebs Go 混入热点榜；离线验过
        # 全库 4831 条在库条目，只拦这一条，0 误伤；链接门同步封
        # wherecelebsgo.com/games）
        r"\bgeoguessr\b",
        # “daily … puzzle”（如“Show HN: NYT style daily word/logic
        # puzzle”）：每日解谜是 NYT Wordle 类纯游戏的明确说法，网页工具
        # 标题里不会出现
        # （2026-11-25 09:07 CST 轮：ClusterBust 混入热点榜；离线验过全库
        # 4831 条在库条目，命中 7 条全是每日解谜纯游戏，0 误伤；链接门同步
        # 封 clusterbust.com）
        r"\bdaily\b.{0,40}\bpuzzle\b",
        # “API key for …”（如“One OpenAI-compatible API key for many
        # LLMs”）：标题明说产品是给调用方用的 API key，不是浏览器里能直接
        # 用的工具；只拦“API key for”这一表意明确的说法，不拦“API key
        # generator”这类密钥生成工具（2026-11-23 16:07 CST 轮：
        # Modelflare 混入当日时间线；离线验过全库 4287 条在库条目，只拦
        # 这一条，0 误伤；域名门同步封 modelflare.dev）
        r"\bapi\s+key\s+for\b",
        # “RPG”（如“Show HN: Far Worlds, a co-op voxel RPG that runs in
        # the browser”）：角色扮演游戏的类型自述，网页工具标题里不会出现
        # （2026-11-28 09:07 CST 轮：Far Worlds 已进热点榜；离线验过
        # 全库 5512 条在库条目，命中 2 条全是纯游戏（Far Worlds 体素
        # RPG、求职主题 RPG），0 误伤；链接门同步封 farworlds.com/play）
        r"\brpg\b",
    )
]


def title_gate(*titles):
    """标题收录判定：返回 (通过, 原因)。标题透露出要下载安装的不要。"""
    for t in titles:
        if not t:
            continue
        low = t.lower()
        if any(e in low for e in _TITLE_EXEMPT):
            continue
        # “离线 + 本地”同时出现 = 在本机上跑的工具（如本地大模型桌面应用）；
        # 单独的“离线”不拦——有的网页工具本身就是离线可用的（如钢琴学习站）
        if "offline" in low and "local" in low:
            return False, "installable_title"
        if "离线" in t and "本地" in t:
            return False, "installable_title"
        if "remote desktop" in low or "desktop wallpaper" in low:
            # “远程桌面/桌面壁纸”是特例：remote desktop 有网页版，
            # desktop wallpaper 生成器本身就是在线工具
            continue
        for rx in _TITLE_BLOCK_RES:
            if rx.search(t):
                return False, "installable_title"
    return True, ""


# 信源简介里的“要下载安装”信号（2026-11-25 09:25 PST 轮：Ileta 泄漏——
# 标题只有“Ileta”不露痕迹，简介却明写“Draw and simulate … circuits on
# Android”“Free to download”，标题门与首页实测都够不着——简介是信源自己
# 写的产品描述，首页是开发商通用落地页（lyrasoftlab.com），两者都没把
# “Android 应用”写进标题/首页正文；Ileta 已被 Bing 收录，英文详情页
# 在线返回 200。只拦表意明确的，简介里明确写工具本身在浏览器/网页里用
# 的（web app / browser app / available in the browser 等——“in the browser”
# 只认“工具本身在浏览器里用”的写法，Clary 的“record once in the browser”
# 只是录音的一次性步骤、产品本身是 iPhone 应用，不算豁免；见 summary_gate）
# 1469 条过门条目：新拦 24 条，逐条核过全是真泄漏（Ileta、Yuktisa Fit、
# StoryPass、Wake、DubTab、PureSound、Outloud Reader、Sikemux、Wavefunction、
# Rchive、Passdroid、Smartesto、Hammerspoon、ArkWarden、NotchMuse、Expose AI、
# Blobby、MigraMemo、inlabel、AiryNight、LightScroll、Clary、Locus、
# Quickcapture），0 误伤；以下写法特意没收：“App Store/Google Play”（TapCraft
# 的“App Store screenshots”是产出物、Play Console Store 的 Google Play 是
# 发布对象——其简介里的“Android app”指客户要发布的 app，本身是服务市场，
# 故“marketplace”也在豁免里）；“on Android/iOS”只拦不带“works inside”
# （AstraEye 的“works inside ChatGPT and Claude, and on Android”指宿主应用）；
# 含“and web”的（如 Hailbell“for iOS, Android and web”）说明有网页端，不拦。
_SUMMARY_EXEMPT = ("no install", "no download", "no installation",
                    "runs in your browser", "in your browser",
                    "works in the browser", "and in the browser",
                    "available in the browser", "directly in the browser",
                    "entirely in the browser", "right in the browser",
                    "use it in the browser",
                    "web-based", "browser-based", "web app", "browser app",
                    "joins from a link", "not a native", "and web",
                    "works inside", "marketplace",
                    "免安装", "无需安装", "不用安装", "无需下载", "不用下载")
_SUMMARY_BLOCK_RES = [
    re.compile(p, re.IGNORECASE) for p in (
        r"\bfree\s+to\s+download\b",
        r"\bdownload\s+(the\s+)?app\b",
        r"\bdownload\s+(for|on)\s+(mac|macos|windows|ios|android|linux|iphone|ipad)\b",
        r"\bmac\s+app\s+store\b",
        r"\b(android|ios|iphone|ipad|macos)\s+(app|application)\b",
        r"\b(desktop|mobile)\s+(app|application|version|edition|client)\b",
        r"\bfor\s+(android|ios|iphone|ipad)\b",
        r"\brequires?\s+(macos|windows\s+10|windows\s+11|ios|android)\b",
        r"\bon\s+your\s+(mac|windows|iphone|ipad|android)\b",
        r"\bon\s+(android|ios)\b",
    )
]


def summary_gate(*texts):
    """简介收录判定：返回 (通过, 原因)。简介透露出要下载安装的不要。

    豁免与信号都在简介全文上判定（各字段合并后），避免信号与豁免分处
    summary / summary_full 两个字段时误拦（如 Ribbon Architect 的“iOS
    app”与“in the browser”分处两处）。
    """
    text = " ".join(t for t in texts if t)
    if not text:
        return True, ""
    low = text.lower()
    if any(e in low for e in _SUMMARY_EXEMPT):
        return True, ""
    for rx in _SUMMARY_BLOCK_RES:
        if rx.search(text):
            return False, "installable_summary"
    return True, ""


# ---------------------------------------------------------------- 进榜前实测（方案 B）
# 2026-11-17 用户选定方案 B：新条目进热点榜前，先实测一次链接网站本身。
# 背景：目录（Ignlab、ListBulb）描述与实站不符的泄漏（Matikiri 自称 AI
# 音乐工具、实为印尼语 K-Pop 流媒体站；Codecaine 标题不提 Mac、却是 macOS
# 桌面应用；CodeGraphy 只 local 安装；Vindle 需 TestFlight）靠域名黑名单
# 与标题门看不出来，此前全靠每轮人工浏览器抽查才拦得住。
# 实测是 HTTP 拉取 + 内容信号，不是浏览器渲染：能拦住“要下载安装”类
# （下载按钮、安装包、pip/npm/npx、docker、git clone、应用商店、扩展、
# macOS/Apple Silicon 平台表述等在首页正文里露痕迹的），拦不住纯语义
# 不符类（流媒体站、目录站、规范文档站、纯 API 落地页等——首页正文里
# 没有安装信号，需人工抽查）与 JS 空壳页（正文几乎无字）。
# 信号调优：离线以 165 条在榜好工具 + 82 条已知泄漏为基准测得
# （好集误拦 10 条、坏集拦住 47 条、另 4 条因 403 暂不上榜）；
# 紧豁免（页上明确说工具本身在浏览器里用）只救好页、不放坏页；
# waitlist / self_hosted 已去掉（误伤多、独特拦截为 0）。
# 适用范围：所有信源的新到条目（泄漏同样来自 HN Show、Reddit、Product
# Hunt，不只目录站；每轮新到过机械门约 3 条，覆盖全部只多几次检查）。
# 结果按规范化链接缓存进 data/verify_cache.json（本机文件，不推送）：
# pass 只验一次；fail 记原因、7 天后复验；unknown（403/429/5xx/超时/
# 网络错/机器人验证页）本轮不上榜、下轮重试，最多 3 次后每天复验一次，
# 永不因网络抖动把好工具永久封掉。功能上线前已入库的老条目不追溯。
# 人工复核：删掉 data/verify_cache.json 里某条记录即可让它下轮重验
# （但信号是确定性的，重验仍会拦）；误拦的好工具由人工在浏览器里核实后，
# 把该条目的 status 改成 "pass"（reason 记 manual），之后不再复验、照常上榜。
PROBE_TIMEOUT = 10
PROBE_MAX_BYTES = 1024 * 1024
PROBE_WORKERS = 8
PROBE_MAX_PER_ROUND = 40
PROBE_MAX_UNKNOWN_ATTEMPTS = 3
PROBE_UNKNOWN_RETRY_HOURS = 24
PROBE_FAIL_RETRY_DAYS = 7
PROBE_VERIFY_WINDOW_DAYS = 7

# 首页正文里的“要下载安装”信号（只拦表意明确的安装动作，不拦“下载结果”
# 之类的输出动作——例如“Download PDF/CSV/PNG”是导出文件，不是装应用）。
PROBE_SIGNALS = [
    ("download_platform",
     r"download\s+(for|on)\s+(mac|macos|windows|ios|android|linux|iphone|ipad)\b"),
    ("download_app", r"download\s+(the\s+)?app\b"),
    # "Agent App Store"（代理应用商店导航）不是苹果 App Store，用否定回顾
    # 排除；开头的 \b 不能丢，否则会命中 "WhatsApp Store"。
    ("app_store", r"(?<!agent\s)\bapp\s+store\b"),
    ("google_play", r"\bgoogle\s+play\b"),
    ("testflight", r"\btestflight\b"),
    # 2026-11-24 离线调优新增（应用分发 CTA 类软信号，见
    # _PROBE_EXEMPTABLE_SIGNALS）：ohhai（“Get the app / Get Ohhai for
    # Mac”）、outloudreader（“Get the app / Free to download · iOS &
    # Android”）等应用营销页只用这类 CTA、不用“App Store / Google Play”
    # 字样，旧信号够不着；离线验证：119 条已发布条目实测 0 误伤，
    # 坏集 20 条里命中 3 条（ohhai 命中 get_the_app 与
    # get_app_for_platform，outloudreader 命中 get_the_app 与
    # free_to_download）；与 app_store 同类处理——真网页工具页脚的
    # “也有手机版”提及靠 browser-use 豁免放行。get_app_for_platform
    # 的产品词用 (?-i:[A-Z]...) 要求首字母真实大写，避免“Get started
    # for Mac”这类小写文案误伤；“Download <产品名>”（astor.app 的
    # “Download Astor”）与“Get <产品名>”（tendor.md 的“Get Tendor”）
    # 实测误伤太多（41/115、74/115），仍拦不住，靠人工抽查兜底。
    ("get_the_app", r"\bget\s+the\s+app\b"),
    ("get_app_for_platform",
     r"\bget\s+(?-i:[A-Z][a-z]{2,})\s+for\s+(mac|windows|ios|iphone|android)\b"),
    ("free_to_download", r"\bfree\s+to\s+download\b"),
    # 多语言下载包：韩文 다운로드 / 中文 下载 + 安装包后缀
    ("download_pkg",
     r"(download|다운로드|下载)\b[^\n]{0,80}\.(dmg|exe|apk|msi|pkg)\b"),
    ("pip_install", r"\bpip\s+install\b"),
    # 2026-11-25 05:07 PST 轮补：Enano 首页用 pipx install 安装本地 CLI，
    # pipx 是 pip_install 之外的包管理器安装写法，之前信号表里漏了，补上
    ("pipx_install", r"\bpipx\s+install\b"),
    ("npm_install", r"\bnpm\s+(install|i)\s+\S"),
    ("npx_run", r"\bnpx\s+\S"),
    ("pnpm_add", r"\bpnpm\s+(add|install)\b"),
    ("yarn_add", r"\byarn\s+(add|install)\b"),
    ("brew_install", r"\bbrew\s+install\b"),
    ("cargo_install", r"\bcargo\s+install\b"),
    ("go_install", r"\bgo\s+install\b"),
    ("gem_install", r"\bgem\s+install\b"),
    ("docker_run", r"\bdocker\s+(run|compose|pull)\b"),
    ("git_clone", r"\bgit\s+clone\b"),
    ("curl_pipe_sh", r"\bcurl\b[^|\n]{0,120}\|\s*(sh|bash)\b"),
    ("wget_pipe_sh", r"\bwget\b[^|\n]{0,120}\|\s*(sh|bash)\b"),
    ("add_to_chrome", r"\badd\s+to\s+chrome\b"),
    ("extension_install",
     r"(install|add|get)\s+(the\s+)?(chrome|firefox|browser|edge|safari)\s+extension\b"),
    # 2026-11-19 09:37 CST 轮补：ngTestFoundry 首页明写 "is a VS Code
    # extension"（Install from Marketplace），是须下载安装的编辑器扩展，
    # 旧信号（extension_install 只认浏览器扩展）够不着这种写法
    ("vscode_extension", r"\bvs\s*code\s+extension\b"),
    ("mac_app", r"\b(mac|macos)\s+app\b"),
    ("windows_app", r"\bwindows\s+app\b"),
    ("requires_platform",
     r"\brequires?\s+(macos|windows\s+10|windows\s+11|ios|android)\b"),
    ("hypervisor", r"\bhypervisor\b"),
    ("iso_download", r"download\b[^\n]{0,80}\.iso\b"),
    ("apk_download", r"download\b[^\n]{0,60}\.apk\b"),
    ("plugin_install", r"\binstall\b[^\n]{0,80}\bplugin\b"),
    ("cli_install", r"\binstall\b[^\n]{0,40}\bcli\b"),
    # 2026-11-17 补：AWS Emulator 漏网——页上写 "Install AWS Emulator
    # and start it on your laptop" 与 "runs as a native binary"，本地
    # 二进制需下载安装，旧信号（cli_install 等）够不着这两句。
    ("native_binary", r"\bnative\s+binary\b"),
    ("install_on_device",
     r"\binstall\b[^\n]{0,80}\bon\s+your\s+(laptop|computer|machine|device)\b"),
    # 桌面应用的平台表述（离线调优 R10 选定：好集 165 条误拦 10 条、
    # 坏集 82 条拦住 47 条、另 4 条因 403 暂不上榜；apple_silicon 排除
    # "Apple Silicon LLMs Guide" 之类指南标题，macbook 要求 40 字内出现
    # app，避免浏览器兼容列表误伤；waitlist / self_hosted 已去掉，
    # 误伤多、独特拦截为 0）
    ("apple_silicon", r"\bapple\s+silicon\b(?!\s+llm)"),
    ("macos_version", r"\bmacos\s+\d+(\.\d+)?\s+or\s+later\b"),
    ("macos_version_ko", r"\bmacos\s+\d+\s*이상\b"),
    ("notarized_apple", r"\bnotarized\s+by\s+apple\b"),
    ("macbook", r"\bmacbook\b[^.]{0,40}\bapp\b"),
    ("debian_iso", r"\bdebian\s+iso\b"),
]
_PROBE_RES = [(name, re.compile(pat, re.IGNORECASE))
              for name, pat in PROBE_SIGNALS]

# 豁免只救“移动端伴生应用”类软信号（见 _PROBE_EXEMPTABLE_SIGNALS）：
# 页上明确说“工具本身就在浏览器里用”的强表述（动词紧贴
# in your browser / online），出现时取消软信号拦下——离线调优证明它
# 只救好页：历史 20 条豁免放行里，软信号 5 条均为真网页工具的页脚
# “也有手机版”提及。硬安装信号不豁免：2026-11-22 rmux（桌面应用，
# 页上 WASM 演示句触发豁免）与 2026-11-23 nlmexporter（Chrome 扩展
# 页，句 “runs in your browser” 触发豁免）都是被全页一票豁免放行的。
# 不用宽泛的 "in your browser"：扩展页也会说 "runs in your browser"。
PROBE_EXEMPT_PATTERNS = [
    r"\buse\s+(it\s+)?in\s+(your\s+)?browser\b",
    r"\btry\s+(it\s+)?in\s+(your\s+)?browser\b",
    r"\bstart\s+(free\s+)?in\s+your\s+browser\b",
    r"\bruns?\s+in\s+your\s+browser\b",
    r"\brunning\s+in\s+your\s+browser\b",
    r"\bworks?\s+in\s+your\s+browser\b",
    r"\bprocessed\s+in\s+your\s+browser\b",
    r"\buse\s+online\b",
    r"\btry\s+online\b",
    r"\bno\s+(download|install)\s+(needed|required)\b",
    r"\bruns\s+on\s+this\s+page\b",
]
_PROBE_EXEMPT_RES = [re.compile(p, re.IGNORECASE)
                     for p in PROBE_EXEMPT_PATTERNS]

# 豁免可覆盖的信号：仅移动端伴生应用类软信号。真网页工具页脚常写
# “Download on the App Store / Get it on Google Play”（也有手机版），
# 这类提及不代表工具本身须安装。下载包、包管理器安装、扩展安装、
# 桌面应用平台表述等硬信号不在此列——离线调优（2026-11-23，历史
# 20 条豁免放行全量）：软信号 5 条全为真工具，硬信号 15 条里含
# rmux、nlmexporter 两个已知漏网；现存 20 条均未在榜，改动不影响
# 任何在榜条目，只影响今后新到条目的实测（pass 结论不重验）。
# 2026-11-24 补入 get_the_app、get_app_for_platform、
# free_to_download（同类应用分发 CTA 软信号，离线验证 119 条已发布
# 条目 0 误伤）；注意：pass 结论不重验，收紧前已豁免放行的旧条目
# 仍带旧结论，须另做归档复查（2026-11-24 晨间复查即据此查出
# dc.flasktoken.com、pickode.com、tensorviz.dev、endlessle.com 四条
# 仍在榜的旧豁免漏网并封禁）。
_PROBE_EXEMPTABLE_SIGNALS = frozenset(
    ("app_store", "google_play", "testflight",
     "get_the_app", "get_app_for_platform", "free_to_download"))


def _visible_text(html_text):
    """去掉 script/style 标签后取可见文本（信号只在可见文本里找，
    不命中 <script> 里的 JSON 数据，避免误拦）。"""
    no_js = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", html_text)
    no_tag = re.sub(r"(?is)<[^>]+>", " ", no_js)
    return re.sub(r"\s+", " ", html.unescape(no_tag)).strip()


def probe_site(url):
    """实测一个工具网站：返回 (状态, 原因, 详情)。
    状态：pass（像能直接用的网页工具）/ fail（确认不是）/
    unknown（这次没验出来：403/429/5xx/超时/网络错/机器人验证页）。
    只做一轮 HTTP 拉取，不渲染 JS、不点页面——SPA 空壳页也能过，
    靠“安装信号”拦，不靠“有没有交互元素”拦。"""
    try:
        req = urllib.request.Request(url, headers=UA)
        with urllib.request.urlopen(req, timeout=PROBE_TIMEOUT) as r:
            final_url = r.geturl()
            ctype = (r.headers.get("Content-Type") or "").lower()
            encoding = (r.headers.get("Content-Encoding") or "").lower()
            raw = r.read(PROBE_MAX_BYTES + 1)
    except urllib.error.HTTPError as e:
        if e.code in (404, 410):
            return "fail", "http_404", f"HTTP {e.code}"
        return "unknown", f"http_{e.code}", f"HTTP {e.code}"
    except (urllib.error.URLError, TimeoutError, OSError, ValueError) as e:
        return "unknown", "fetch_error", str(e)[:120]
    if len(raw) > PROBE_MAX_BYTES:
        raw = raw[:PROBE_MAX_BYTES]
    if encoding == "gzip":
        try:
            import gzip
            raw = gzip.decompress(raw)
        except Exception:
            return "unknown", "gzip_error", ""
    elif encoding and encoding != "identity":
        return "unknown", "unsupported_encoding", encoding[:40]
    # 跳转后的最终地址也要过收录门（防止链到应用商店/下载页）
    ok, why = tool_gate(final_url)
    if not ok:
        return "fail", "redirect_blocked", f"final URL blocked: {why} ({final_url[:120]})"
    if ctype and "html" not in ctype and "text" not in ctype:
        return "fail", "not_html", f"Content-Type: {ctype[:80]}"
    try:
        page = raw.decode("utf-8", errors="ignore")
    except Exception:
        return "unknown", "decode_error", ""
    m = re.search(r"(?is)<title[^>]*>(.*?)</title>", page)
    title = re.sub(r"\s+", " ", (m.group(1) if m else "")).strip().lower()
    if "404" in title or "page not found" in title:
        return "fail", "soft_404", f"title: {title[:80]}"
    text = _visible_text(page)
    low = text.lower()
    if ("verify you are human" in low or "checking your browser" in low
            or ("just a moment" in low and "cloudflare" in low)):
        return "unknown", "bot_check", "bot challenge page"
    if (len(text) < 600
            and re.search(r"(?i)<input[^>]*type=[\"']password[\"']", page)
            and ("log in" in low or "sign in" in low)):
        return "fail", "login_wall", "login-only page"
    exempt = any(rx.search(text) for rx in _PROBE_EXEMPT_RES)
    for name, rx in _PROBE_RES:
        for hit in rx.finditer(text):
            # "Coming soon App Store / Google Play" 只是页脚预告，
            # 不是已上架应用：跳过该次命中、继续找同信号的下一次命中
            if name in ("app_store", "google_play"):
                before = text[max(0, hit.start() - 25):hit.start()].lower()
                if "coming soon" in before:
                    continue
            if exempt and name in _PROBE_EXEMPTABLE_SIGNALS:
                return "pass", "exempt", f"browser-use claim overrides signal:{name}"
            snippet = text[max(0, hit.start() - 60):hit.end() + 60].strip()
            return "fail", f"signal:{name}", snippet[:200]
    return "pass", "", f"final: {final_url[:120]}"


def load_verify_cache(data_dir, now=None):
    """读 data/verify_cache.json；没有则新建（started_at 记功能上线时间，
    在此之前入库的老条目不追溯实测）。
    now 必须传本轮的 now：新建缓存时 started_at 取本轮 now，本轮新到
    条目（fetched_at == now）才能当轮成为候选；若取调用时刻的
    datetime.now()，会比 fetched_at 晚几秒，导致首轮永远 0 候选、
    缓存文件又因 0 候选不落盘，started_at 每轮后移、实测永不启动。"""
    path = os.path.join(data_dir, "verify_cache.json")
    if os.path.exists(path):
        try:
            cache = load_json(path)
            if isinstance(cache, dict) and isinstance(cache.get("items"), dict):
                return cache
        except (json.JSONDecodeError, AttributeError):
            pass
    started = now or datetime.now(timezone.utc)
    return {"version": 1,
            "started_at": started.isoformat(),
            "items": {}}


def run_verify_phase(history, kept_sources, cache, now, data_dir):
    """本轮实测：对新到、过机械门、未验过（或可重试）的条目并发拉取
    首页并判信号；结果写回缓存并原子落盘。返回统计 dict。"""
    from concurrent.futures import ThreadPoolExecutor, as_completed
    try:
        started_dt = datetime.fromisoformat(cache.get("started_at", ""))
        if started_dt.tzinfo is None:
            started_dt = started_dt.replace(tzinfo=timezone.utc)
    except ValueError:
        started_dt = now
    window = timedelta(days=PROBE_VERIFY_WINDOW_DAYS)
    cands = {}
    for it in history.values():
        if it.get("source_id") not in kept_sources:
            continue
        link = norm_link(it.get("resolved_link") or it.get("link", ""))
        if not link:
            continue
        ok, _ = tool_gate(link)
        if not ok:
            continue
        ok, _ = title_gate(it.get("title", ""), it.get("zh_title", ""))
        if not ok:
            continue
        ok, _ = summary_gate(it.get("summary", ""), it.get("summary_full", ""))
        if not ok:
            continue
        ent = cache["items"].get(link)
        try:
            fa = it.get("fetched_at", "")
            fdt = datetime.fromisoformat(fa) if fa else None
            if fdt is not None and fdt.tzinfo is None:
                fdt = fdt.replace(tzinfo=timezone.utc)
        except ValueError:
            fdt = None
        if ent is None:
            # 新条目才验：上线前入库的老条目不追溯；超出 7 天补验窗口的不补
            if fdt is None or fdt < started_dt or (now - fdt) > window:
                continue
            cands[link] = fdt
            continue
        try:
            last = datetime.fromisoformat(ent.get("checked_at", ""))
            if last.tzinfo is None:
                last = last.replace(tzinfo=timezone.utc)
        except ValueError:
            last = None
        st = ent.get("status")
        if st == "unknown":
            attempts = ent.get("attempts", 0)
            retry_after = (timedelta(minutes=30) if attempts < PROBE_MAX_UNKNOWN_ATTEMPTS
                           else timedelta(hours=PROBE_UNKNOWN_RETRY_HOURS))
            if last is None or (now - last) >= retry_after:
                cands[link] = fdt or now
        elif st == "fail":
            if last is None or (now - last) >= timedelta(days=PROBE_FAIL_RETRY_DAYS):
                cands[link] = fdt or now
    ordered = sorted(cands.items(), key=lambda kv: kv[1], reverse=True)
    ordered = ordered[:PROBE_MAX_PER_ROUND]
    stats = {"probed": 0, "pass": 0, "fail": 0, "unknown": 0, "fails": []}
    if not ordered:
        # 0 候选也要落盘：否则新建缓存的 started_at 丢了，下轮重新
        # 建、started_at 后移，实测永远等不到候选
        save_json(os.path.join(data_dir, "verify_cache.json"), cache)
        return stats
    with ThreadPoolExecutor(max_workers=PROBE_WORKERS) as ex:
        futs = {ex.submit(probe_site, link): link for link, _ in ordered}
        for fut in as_completed(futs):
            link = futs[fut]
            try:
                status, reason, detail = fut.result()
            except Exception as e:  # noqa: BLE001 - 单条实测异常不中断整轮
                status, reason, detail = "unknown", "probe_error", str(e)[:120]
            prev = cache["items"].get(link) or {}
            attempts = prev.get("attempts", 0) + 1 if prev.get("status") == "unknown" else 1
            cache["items"][link] = {
                "status": status, "reason": reason,
                "checked_at": now.isoformat(), "attempts": attempts,
                "detail": detail[:200],
            }
            stats["probed"] += 1
            stats[status] += 1
            if status == "fail":
                stats["fails"].append((link, reason))
    save_json(os.path.join(data_dir, "verify_cache.json"), cache)
    return stats


def resolve_url(url, timeout=15):
    """跟随跳转解析真实目标地址（HEAD 请求，不下载正文）。
    Product Hunt 的 /r/p/ 跳转链接用这个办法拿到工具官网；失败返回 None。"""
    try:
        req = urllib.request.Request(url, headers=UA, method="HEAD")
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.geturl()
    except urllib.error.HTTPError as e:
        loc = e.headers.get("Location") if e.headers else None
        if e.code in (301, 302, 303, 307, 308) and loc:
            nxt = urllib.parse.urljoin(url, loc)
            if nxt != url:
                return resolve_url(nxt, timeout=timeout)
        return None
    except (urllib.error.URLError, TimeoutError, OSError, ValueError):
        return None


def resolve_smollaunch_page(url, timeout=10):
    """Smol Launch 产品页解析：RSS 只给目录站自己的 /products/<slug> 页，
    工具官网在页内 "Visit Website" 锚点上；失败返回 None（该条目跳过，
    不把目录页本身入库）。"""
    try:
        req = urllib.request.Request(url, headers=UA)
        with urllib.request.urlopen(req, timeout=timeout) as r:
            page = r.read(500000).decode("utf-8", "ignore")
    except (urllib.error.URLError, TimeoutError, OSError, ValueError):
        return None
    for m in re.finditer(r'<a[^>]+href="(https?://[^"]+)"[^>]*>(.*?)</a>',
                         page, re.I | re.S):
        text = re.sub(r"<[^>]+>", "", m.group(2)).strip()
        if text.lower() == "visit website":
            return html.unescape(m.group(1))
    return None


# ---------------------------------------------------------------- 抓取与解析

def fetch(url, timeout=25, attempts=2):
    last_err = None
    for i in range(attempts):
        try:
            req = urllib.request.Request(url, headers=UA)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except (urllib.error.URLError, TimeoutError, OSError) as e:
            last_err = e
            if i < attempts - 1:
                time.sleep(5)
    raise last_err


def parse_feed(body, source):
    """RSS 2.0 与 Atom 1.0 都解析，返回条目 dict 列表。"""
    try:
        root = ET.fromstring(body)
    except ET.ParseError:
        return []
    items = []
    for el in root.iter():
        name = local_name(el.tag)
        if name not in ("item", "entry"):
            continue
        fields = {}
        for child in el:
            cn = local_name(child.tag)
            if cn in ("title", "link", "pubDate", "published", "updated",
                      "description", "summary", "content", "encoded"):
                if cn == "link":
                    href = child.get("href")
                    # Atom: <link href="..."/>；RSS: <link>url</link>
                    fields.setdefault("link", href or (child.text or "").strip())
                else:
                    fields.setdefault(cn, (child.text or "").strip())
        title = fields.get("title", "").strip()
        link = norm_link(fields.get("link", ""))
        if not title or not link:
            continue
        summary = strip_html(fields.get("description") or fields.get("summary") or "")
        if not summary:
            summary = strip_html(fields.get("content") or fields.get("encoded") or "")
        # 完整摘要：详情页用（卡片仍用 200 字短摘要）。只有比短摘要明显更长时
        # 才存，短摘要本身已完整的条目不存，省体积。收成完整的一段话，
        # 不截断到半句、不挂省略号（导读/正文摘要不允许截断）。
        summary_full = complete_para(summary, 1500) if len(summary) > 200 else ""
        # 工具站收录：Product Hunt 的 /r/p/ 跳转链接与 Reddit 的 [link]
        # 外链都藏在正文 HTML 里，先抠出来（跳转跟随在调用方做）。
        raw_html = (fields.get("content") or fields.get("encoded")
                    or fields.get("description") or "")
        redirect = ""
        ext_link = ""
        if source["id"] == "producthunt":
            m = re.search(r"https://www\.producthunt\.com/r/p/\d+[^\"'\s<>]*", raw_html)
            redirect = m.group(0) if m else ""
            if "Discussion | Link" in summary:
                summary = summary.split("Discussion | Link")[0].strip()
                summary_full = complete_para(summary, 1500) if len(summary) > 200 else ""
        elif source["id"].startswith("reddit-"):
            m = re.search(r'href="([^"]+)"[^>]*>\[link\]', raw_html)
            ext_link = m.group(1) if m else ""
        pub = parse_date(fields.get("pubDate") or fields.get("published")
                         or fields.get("updated"))
        item = {
            "title": title,
            "link": link,
            "source": source["name"],
            "source_id": source["id"],
            "published": pub,  # datetime 或 None（调用方补抓取时间）
            "summary": shorten(summary),
        }
        if redirect:
            item["_redirect"] = redirect
        if ext_link:
            item["_ext_link"] = ext_link
        if summary_full:
            item["summary_full"] = summary_full
        items.append(item)
    return items



# ---------------------------------------------------------------- Ignlab JSON 信源
# Ignlab Launch 公开 API（2026-11-16 实测，无需认证）：
#   GET https://launch.ignlab.net/api/v1/listings?limit=50&offset=0
# 返回 {"listings": [...], "categories": [...], "total": 7853,
#        "offset": 0, "limit": 50}，默认按 created_at 倒序（最新在前），
# limit/offset 分页可用；站方 FAQ 说明免费公开只读、有限流。
# 每条 listing：id / name / slug / url（工具官网）/ tagline /
# description / category / tags / pricing / upvotes /
# created_at（"2026-11-15 12:01:33"，UTC）/ listing_url。
# 每轮只取最新 50 条（约 8 小时量），不回填 7,853 条全库；去重与
# 收录门和 RSS 条目完全一样（按规范化链接判重、tool_gate + title_gate）。
IGNLAB_LIMIT = 50
IGNLAB_CATEGORY_MAP = {
    "Productivity": "productivity",
    "Developer Tools": "dev",
    "Design": "design",
    "Marketing": "productivity",
    "AI": "ai",
    "Analytics": "data",
    "Finance": "productivity",
    "No-Code": "dev",
    "Security": "dev",
    "Other": "productivity",
}


def parse_ignlab(body, source):
    """Ignlab /api/v1/listings 的 JSON，映射成与 parse_feed 相同的条目形状。"""
    try:
        data = json.loads(body)
    except (json.JSONDecodeError, TypeError, ValueError):
        return []
    items = []
    for raw in (data.get("listings") or [])[:IGNLAB_LIMIT]:
        if not isinstance(raw, dict):
            continue
        name = (raw.get("name") or "").strip()
        link = norm_link(raw.get("url") or "")
        if not name or not link:
            continue
        tagline = (raw.get("tagline") or "").strip()
        desc = (raw.get("description") or "").strip()
        summary = shorten(tagline or desc)
        summary_full = complete_para(desc, 1500) if len(desc) > 200 else ""
        pub = parse_date(raw.get("created_at") or "")
        item = {
            "title": name,
            "link": link,
            "source": source["name"],
            "source_id": source["id"],
            "published": pub,
            "summary": summary,
            "_cat_hint": IGNLAB_CATEGORY_MAP.get(raw.get("category") or "",
                                                 "productivity"),
        }
        if summary_full:
            item["summary_full"] = summary_full
        items.append(item)
    return items


# ---------------------------------------------------------------- ListBulb JSON 信源
# ListBulb 公开 API（2026-11-16 实测，无需认证；站方 OpenAPI：
# https://www.listbulb.com/api/v1/openapi.json，说明“Read live catalog
# anonymously (no API key, at most 25 results per list call, rate
# limited per IP)”）：
#   GET https://www.listbulb.com/api/v1/recent?limit=25
# 返回 {"data": {"items": [...]}, "meta": {"apiVersion": "v1"}}；
# /recent 是“最近上线的工具”，每周日批量上新；前 3 条是 featured 置顶
# （2026-06/08 的旧条目，历史库 30 天淘汰会直接丢掉），其余按周次
# 分组，并非严格按 listedAt 倒序——但去重按规范化链接，旧条目不会
# 重复入库；每轮固定 25 条，稳态每周新增约 15-20 条。
# 每条 tool：slug / name / websiteUrl（工具官网）/ listbulbUrl /
# description / listingHeadline / logoUrl / imageUrl /
# category（{slug, name, liveToolCount}）/ tags / listedAt
# （ISO 8601，"2026-08-03T03:00:41.129Z"）/ featured / verification。
# 全站 live 工具共 541 条（/api/v1/tools 的 totalCount）。
# /api/v1/tools 支持 cursor 分页（limit 最大 25），暂不用；/recent
# 一轮 25 条已够用。每轮只取 /recent 一页，不回填全库；去重与收录门
# 和 RSS/Ignlab 条目完全一样（按规范化链接判重、tool_gate + title_gate）。
LISTBULB_LIMIT = 25
LISTBULB_CATEGORY_MAP = {
    "saas-marketing": "productivity",
    "dev-workflow": "dev",
    "small-accounts-mvps": "productivity",
    "ui-libraries": "design",
    "launch-websites": "productivity",
    "landing-page-waitlist": "design",
}


def parse_listbulb(body, source):
    """ListBulb /api/v1/recent 的 JSON，映射成与 parse_feed 相同的条目形状。"""
    try:
        data = json.loads(body)
    except (json.JSONDecodeError, TypeError, ValueError):
        return []
    raw_items = (data.get("data") or {}).get("items") or []
    items = []
    for raw in raw_items[:LISTBULB_LIMIT]:
        if not isinstance(raw, dict):
            continue
        name = (raw.get("name") or "").strip()
        link = norm_link(raw.get("websiteUrl") or "")
        if not name or not link:
            continue
        headline = (raw.get("listingHeadline") or "").strip()
        desc = (raw.get("description") or "").strip()
        summary = shorten(headline or desc)
        summary_full = complete_para(desc, 1500) if len(desc) > 200 else ""
        pub = parse_date(raw.get("listedAt") or "")
        cat = raw.get("category") or {}
        cat_slug = cat.get("slug", "") if isinstance(cat, dict) else ""
        item = {
            "title": name,
            "link": link,
            "source": source["name"],
            "source_id": source["id"],
            "published": pub,
            "summary": summary,
            "_cat_hint": LISTBULB_CATEGORY_MAP.get(cat_slug, "productivity"),
        }
        if summary_full:
            item["summary_full"] = summary_full
        items.append(item)
    return items


# ---------------------------------------------------------------- MakerHunt JSON 信源
# MakerHunt 公开 API（2026-11-17 实测，无需认证）：
#   GET https://makerhunt.io/api/projects?sort=recent&limit=25
# 返回 {"success": true, "data": {"projects": [...], "pagination": {...}}}；
# sort=recent 按 created_at 倒序（默认 sort=upvotes 是全站热度榜，不是新品）；
# 每页 25 条，全站 1358 个项目，每轮只取第 1 页，不回填全库。
# 每条 project：id / name / slug / website_url（工具官网）/
# short_description / full_description（HTML）/ categories（列表）/
# created_at / launched_at / published_at / upvotes。
# 首批实测（2026-11-17）：25 条新品里机械门过 23 条，实测拦 7 条
# （移动应用/插件/SDK/纯 API），人工抽查又拦 5 条（广告平台、游戏 wiki、
# 等候名单、企业客服落地页、招聘版），可用 13 条。
MAKERHUNT_LIMIT = 25
MAKERHUNT_CATEGORY_MAP = {
    "Artificial Intelligence": "ai",
    "AI": "ai",
    "Developer Tools": "dev",
    "DevOps & Cloud": "dev",
    "APIs & Integrations": "dev",
    "Mobile Development": "dev",
    "Testing & QA": "dev",
    "Security": "dev",
    "Design Tools": "design",
    "UI/UX": "design",
    "Marketing Tools": "productivity",
    "SEO": "data",
    "Business Analytics": "data",
    "Finance & FinTech": "productivity",
    "E-commerce": "productivity",
    "Open Source": "opensource",
    "Gaming Tech": "productivity",
    "AR/VR": "productivity",
    "Robotics": "dev",
    "Prototyping": "design",
    "SaaS": "productivity",
    "Platforms": "productivity",
    "Productivity": "productivity",
}


def parse_makerhunt(body, source):
    """MakerHunt /api/projects?sort=recent 的 JSON，映射成 parse_feed 同款条目。"""
    try:
        data = json.loads(body)
    except (json.JSONDecodeError, TypeError, ValueError):
        return []
    raw_items = (data.get("data") or {}).get("projects") or []
    items = []
    for raw in raw_items[:MAKERHUNT_LIMIT]:
        if not isinstance(raw, dict):
            continue
        name = (raw.get("name") or "").strip()
        link = norm_link(raw.get("website_url") or "")
        if not name or not link:
            continue
        short = (raw.get("short_description") or "").strip()
        full = strip_html(raw.get("full_description") or "")
        summary = shorten(short or full)
        summary_full = complete_para(full, 1500) if len(full) > 200 else ""
        pub = parse_date(raw.get("launched_at") or raw.get("published_at")
                         or raw.get("created_at") or "")
        cat_hint = "productivity"
        for c in (raw.get("categories") or []):
            if c in MAKERHUNT_CATEGORY_MAP:
                cat_hint = MAKERHUNT_CATEGORY_MAP[c]
                break
        item = {
            "title": name,
            "link": link,
            "source": source["name"],
            "source_id": source["id"],
            "published": pub,
            "summary": summary,
            "_cat_hint": cat_hint,
        }
        if summary_full:
            item["summary_full"] = summary_full
        items.append(item)
    return items


# ---------------------------------------------------------------- DevHunt JSON 信源
# DevHunt 公开 API（2026-11-17 实测，无需认证；/api/week-tools 本周
# 进行中返回 403，只取已完结周）：
#   GET https://devhunt.org/api/past-week-tools
# 返回最近 2 个已完结周的列表 [{week, startDate, endDate, products: [...]}]；
# 每周约 50-80 条新品（周一批量上新），只取接口返回的 2 周窗口，不回填全库。
# 每条 product：id / name / link（工具官网）/ description /
# devhunt_link（目录站内页）/ launch_date / votes_count。
# 首批实测（2026-11-17）：129 条里机械门过 107 条；开发工具目录含大量
# API/SDK/原生客户端/自托管，描述自述即非浏览器工具的已先行封域名，
# 其余走实测 + 每轮人工抽查。


def parse_devhunt(body, source):
    """DevHunt /api/past-week-tools 的 JSON，映射成 parse_feed 同款条目。"""
    try:
        data = json.loads(body)
    except (json.JSONDecodeError, TypeError, ValueError):
        return []
    if not isinstance(data, list):
        return []
    items = []
    for week in data:
        if not isinstance(week, dict):
            continue
        for raw in (week.get("products") or []):
            if not isinstance(raw, dict):
                continue
            name = (raw.get("name") or "").strip()
            link = norm_link(raw.get("link") or "")
            if not name or not link:
                continue
            desc = strip_html(raw.get("description") or "")
            summary = shorten(desc)
            summary_full = complete_para(desc, 1500) if len(desc) > 200 else ""
            pub = parse_date(raw.get("launch_date") or "")
            item = {
                "title": name,
                "link": link,
                "source": source["name"],
                "source_id": source["id"],
                "published": pub,
                "summary": summary,
                "_cat_hint": "dev",
            }
            if summary_full:
                item["summary_full"] = summary_full
            items.append(item)
    return items


JSON_PARSERS = {"ignlab": parse_ignlab, "listbulb": parse_listbulb,
                "makerhunt": parse_makerhunt, "devhunt": parse_devhunt}


# ---------------------------------------------------------------- 分类与打分

def classify(item, categories, fallback):
    text = (item["title"] + " " + item["summary"]).lower()
    for cat in categories:
        for kw in cat["keywords"]:
            if kw.lower() in text:
                return cat["key"]
    return fallback


def score(item, cfg, now):
    sc = cfg["scoring"]
    total = sc["base"]
    age_h = (now - item["_pub"]).total_seconds() / 3600.0
    for rule in sc["recency"]:
        if age_h <= rule["max_hours"]:
            total += rule["bonus"]
            break
    total += sc["tier_bonus"].get(item["_tier"], 0)
    text = (item["title"] + " " + item["summary"]).lower()
    dev_hits = sum(1 for kw in sc["dev_keywords"] if kw.lower() in text)
    total += min(dev_hits * sc["dev_keyword_bonus"], sc["dev_keyword_cap"])
    noise_hits = sum(1 for kw in sc["noise_keywords"] if kw.lower() in text)
    total += max(noise_hits * sc["noise_keyword_penalty"], sc["noise_keyword_floor"])
    return max(0, min(100, total))


# 主题关键词 -> 中文标签（推荐理由里只出现中文，不漏英文关键词）
REASON_LABELS = {
    "教程": "教程", "tutorial": "教程",
    "工具": "工具", "tool": "工具",
    "数据": "数据", "data": "数据",
    "案例": "案例", "case study": "案例",
    "开源": "开源", "open source": "开源",
    "指南": "指南", "guide": "指南",
    "复盘": "复盘", "postmortem": "复盘",
    "引擎": "引擎", "engine": "引擎",
    "优化": "优化", "optimization": "优化",
    "性能": "性能", "performance": "性能",
    "收入": "营收", "revenue": "营收",
    "销量": "销量", "sales": "销量",
    "经验": "经验教训", "教训": "经验教训", "lesson": "经验教训",
    "源码": "源码", "source code": "源码",
    "工作流": "工作流", "workflow": "工作流",
}


# 主题关键词 -> 英文标签（英文版推荐理由与标签用；键与 REASON_LABELS 完全一致）
REASON_LABELS_EN = {
    "AI": "AI", "人工智能": "AI",
    "免费": "Free", "free": "Free",
    "新工具": "New Tool",
    "发布": "Release", "launch": "Launch",
    "效率": "Productivity", "productivity": "Productivity",
    "设计": "Design", "design": "Design",
    "开发": "Development", "developer": "Development",
    "自动化": "Automation", "automation": "Automation",
    "助手": "Assistant", "assistant": "Assistant",
    "生成": "Generative", "生成式": "Generative",
    "教程": "Tutorial", "tutorial": "Tutorial",
    "工具": "Tools", "tool": "Tools",
    "数据": "Data", "data": "Data",
    "案例": "Case Study", "case study": "Case Study",
    "开源": "Open Source", "open source": "Open Source",
    "指南": "Guide", "guide": "Guide",
    "复盘": "Postmortem", "postmortem": "Postmortem",
    "引擎": "Engine", "engine": "Engine",
    "优化": "Optimization", "optimization": "Optimization",
    "性能": "Performance", "performance": "Performance",
    "收入": "Revenue", "revenue": "Revenue",
    "销量": "Sales", "sales": "Sales",
    "经验": "Lessons Learned", "教训": "Lessons Learned", "lesson": "Lessons Learned",
    "源码": "Source Code", "source code": "Source Code",
    "工作流": "Workflow", "workflow": "Workflow",
}


# 中文标签 -> 主题页 slug（B11/B16；与 REASON_LABELS 的值一一对应）
TAG_SLUGS = {
    "教程": "tutorial", "工具": "tools", "数据": "data", "案例": "case-study",
    "开源": "open-source", "指南": "guide", "复盘": "postmortem",
    "引擎": "engine", "优化": "optimization", "性能": "performance",
    "营收": "revenue", "销量": "sales", "经验教训": "lessons",
    "源码": "source-code", "工作流": "workflow",
}


# 中文标签 -> 英文标签；英文标签 -> 主题页 slug；两者并集供双语渲染共用
TAG_LABELS_EN = {}
for _kw, _cn in REASON_LABELS.items():
    TAG_LABELS_EN[_cn] = REASON_LABELS_EN[_kw]
# 补上 labels_for 能产出、但 REASON_LABELS 未覆盖的中文标签
# （dev_keywords 里的 AI/开发/设计/免费等）：否则英文存档报告的标签
# 回退成中文，且英文主题页会出现中文 slug 文件
for _kw, _en in REASON_LABELS_EN.items():
    TAG_LABELS_EN.setdefault(REASON_LABELS.get(_kw, _kw), _en)
TAG_SLUGS_EN = {TAG_LABELS_EN[cn]: slug for cn, slug in TAG_SLUGS.items()}
TAG_SLUGS_ALL = dict(TAG_SLUGS)
TAG_SLUGS_ALL.update(TAG_SLUGS_EN)


def labels_for(item, cfg):
    """标题+摘要命中主题关键词 -> 去重后的中文标签（B16/C1 共用）。"""
    text = (item["title"] + " " + (item.get("summary") or "")).lower()
    labels = []
    for kw in cfg["scoring"]["dev_keywords"]:
        if kw.lower() in text:
            lab = REASON_LABELS.get(kw, kw)
            if lab not in labels:
                labels.append(lab)
    return labels


def labels_for_en(item, cfg):
    """labels_for 的英文版：同一批关键词命中 -> 英文标签。"""
    text = (item["title"] + " " + (item.get("summary") or "")).lower()
    labels = []
    for kw in cfg["scoring"]["dev_keywords"]:
        if kw.lower() in text:
            lab = REASON_LABELS_EN.get(kw, kw)
            if lab not in labels:
                labels.append(lab)
    return labels


def reason_for(item, cfg, now):
    """从打分信号拼一句推荐理由（只用真实派生出的事实，不编造）：
    T1 信源 -> 官方来源；命中主题关键词 -> 中文标签（去重，最多两个）；
    6/24 小时内发布 -> 新鲜度；只有一条理由时补一条默认理由，保证每卡
    至少有两条可读信息。"""
    parts = []
    if item.get("_tier") == "T1":
        parts.append("官方来源")
    labels = labels_for(item, cfg)
    if labels:
        parts.append("涉及" + "与".join(labels[:2]))
    age_h = (now - item["_pub"]).total_seconds() / 3600.0
    if age_h <= 6:
        parts.append("6 小时内发布")
    elif age_h <= 24:
        parts.append("24 小时内发布")
    if len(parts) < 2:
        parts.append("与本主题相关")
    return " · ".join(parts)


def reason_for_en(item, cfg, now):
    """reason_for 的英文版：同一批打分信号，英文措辞。"""
    parts = []
    if item.get("_tier") == "T1":
        parts.append("Official source")
    labels = labels_for_en(item, cfg)
    if labels:
        parts.append("Covers " + " and ".join(labels[:2]))
    age_h = (now - item["_pub"]).total_seconds() / 3600.0
    if age_h <= 6:
        parts.append("Published within 6 hours")
    elif age_h <= 24:
        parts.append("Published within 24 hours")
    if len(parts) < 2:
        parts.append("Relevant to this topic")
    return " · ".join(parts)


def maybe_llm_rerank(items, site):
    """可选 LLM 打分：三个环境变量缺一即跳过；任何异常都回退规则分。"""
    key = os.environ.get("HOT_LLM_API_KEY", "")
    base = os.environ.get("HOT_LLM_BASE_URL", "").rstrip("/")
    model = os.environ.get("HOT_LLM_MODEL", "")
    if not (key and base and model):
        return items
    cands = items[:30]
    if not cands:
        return items
    try:
        import urllib.request as u
        listing = "\n".join(
            f'{i}. [{c["id"][:8]}] {c["title"]}（{c["source"]}）' for i, c in enumerate(cands))
        audience = site.get("audience", "读者")
        prompt = (f"你是{audience}社区的编辑。给下面每条动态按对{audience}的实用价值"
                  "打 0-100 分（教程、工具、数据、案例、深度分析高分；"
                  "纯资讯、促销低分）。只输出 JSON 数组，形如 "
                  '[{"id": "前8位id", "score": 82}]，不要其他文字。\n' + listing)
        payload = json.dumps({
            "model": model,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0,
        }).encode("utf-8")
        req = u.Request(base + "/chat/completions", data=payload,
                        headers={"Authorization": "Bearer " + key,
                                 "Content-Type": "application/json"})
        with u.urlopen(req, timeout=60) as r:
            body = json.loads(r.read().decode("utf-8"))
        text = body["choices"][0]["message"]["content"]
        m = re.search(r"\[.*\]", text, re.S)
        if not m:
            return items
        for entry in json.loads(m.group(0)):
            for c in cands:
                if c["id"].startswith(entry.get("id", "x")) and \
                        isinstance(entry.get("score"), (int, float)):
                    c["score"] = max(0, min(100, int(entry["score"])))
                    c["scored_by"] = "llm"
        print("LLM rerank applied to %d items" % len(cands))
    except Exception as e:  # noqa: BLE001 - 任何 LLM 失败都回退规则分
        print("LLM rerank skipped (%s)" % e, file=sys.stderr)
    return items


# ---------------------------------------------------------------- 渲染

LOGO_SVG = """<svg width="44" height="44" viewBox="0 0 48 48" aria-hidden="true">
<defs><linearGradient id="lg" x1="0" y1="0" x2="1" y2="1">
<stop offset="0" stop-color="#ff6b35"/><stop offset="1" stop-color="#f7b733"/>
</linearGradient></defs>
<rect x="2" y="2" width="44" height="44" rx="11" fill="url(#lg)"/>
<rect x="14" y="14" width="20" height="20" rx="3" transform="rotate(45 24 24)" fill="#fff"/>
<rect x="20" y="20" width="8" height="8" rx="1.5" transform="rotate(45 24 24)" fill="#ff6b35"/>
</svg>"""

CSS = """
/* 设计语言：暖纸底色、青色点缀、细线边框、无渐变；
   侧栏导航、热点条、时间线时间轨、评分徽章均为其组件的静态化移植。品牌与 logo 由本站自己定义。 */
:root{
  --bg:#faf9f6; --bg-sunk:#f3f3ef; --bg-muted:#e9ede9; --well:var(--bg-sunk);
  --surface:#fff; --surface-2:#fdfdfb; --sidebar:#fdfdfb; --daybar:#f0f2ee;
  --ink:#202a30; --ink-2:#303c42; --ink-3:#59656b; --ink-4:#657176;
  --line:#dfe4e1; --line-strong:#d1d9d5; --line-soft:#e9ede9;
  --accent:#176b75; --accent-strong:#0f565e; --accent-ink:#145f68; --accent-soft:rgba(23,107,117,.08); --accent-softer:rgba(23,107,117,.05);
  --note:#526f72; --hot:#b3402a; --hot-soft:rgba(179,64,42,.08);
  --amber:#b8873a; --amber-ink:#7c5a24; --amber-soft:rgba(184,135,58,.1); --ok:#2f7d5c;
  --rank-1:#b3402a; --rank-2:#a3642f; --rank-3:#96702e; --rank-rest:#6b7684;
  --shadow-card:0 1px 2px rgba(32,42,48,.025);
  --shadow-card-hover:0 3px 12px rgba(32,42,48,.055);
  --shadow-thumb:0 1px 2px rgba(28,39,51,.1),0 1px 1px rgba(28,39,51,.04);
  --raised:#ffffff; --selection:rgba(23,107,117,.16); --shadow-soft:0 4px 12px rgba(28,39,51,.06);
  --accent-contrast:#ffffff; --ok-soft:rgba(47,125,92,.1); --ok-ink:#2a6e51;
  --shadow-pop:0 12px 32px rgba(28,39,51,.12); --prose-ink:#26323a;
  --code-bg:#f6f7f4; --code-keyword:#006d77; --code-string:#2f6f44; --code-number:#9a6700;
  --code-title:#6f42c1; --code-variable:#a13d10; --code-meta:#b42348;
  --page-max-wide:max(1200px,calc(270dvh - 236px));
  --page-max-reading:max(1100px,calc(200dvh - 236px));
  --bar-h:48px; color-scheme:light;
}
@media(min-width:700px){:root{--bar-h:0px}}
[data-theme="dark"]{
  color-scheme:dark;
  --bg:#13191c; --bg-sunk:#182024; --bg-muted:#202a2f; --well:color-mix(in oklab, var(--bg-muted) 60%, transparent);
  --surface:#1a2226; --surface-2:#1d272b; --sidebar:#161e21; --daybar:#182024;
  --ink:#e7eceb; --ink-2:#d2dada; --ink-3:#a5b0b3; --ink-4:#89979d;
  --line:rgba(255,255,255,.08); --line-strong:rgba(255,255,255,.12); --line-soft:rgba(255,255,255,.06);
  --accent:#12ccd8; --accent-strong:#0db2bd; --accent-ink:#2ce2e8; --accent-soft:rgba(18,204,216,.12); --accent-softer:rgba(18,204,216,.06);
  --note:#8fb8a8; --hot:#d86a52; --hot-soft:rgba(216,106,82,.12);
  --amber:#d3b26a; --amber-ink:#d3b26a; --amber-soft:rgba(211,178,106,.12); --ok:#5fc79a;
  --rank-1:#d86a52; --rank-2:#d18a5e; --rank-3:#d3b26a; --rank-rest:#7b869a;
  --shadow-card:none; --shadow-card-hover:none;
  --raised:#202a2f; --selection:rgba(18,204,216,.22); --shadow-soft:0 6px 18px rgba(0,0,0,.35);
  --shadow-thumb:0 1px 2px rgba(0,0,0,.45);
  --accent-contrast:#000000; --ok-soft:rgba(95,199,154,.12); --ok-ink:#7fd1ad;
  --shadow-pop:0 16px 40px rgba(0,0,0,.45); --prose-ink:#d7dfdf;
  --code-bg:#10151c; --code-keyword:#78dce8; --code-string:#a9dc76; --code-number:#ffd866;
  --code-title:#ab9df2; --code-variable:#fc9867; --code-meta:#ff6188;
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%;text-rendering:optimizeLegibility;-webkit-font-smoothing:antialiased;text-autospace:normal}
body{margin:0;background:var(--bg);color:var(--ink);
  font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI","PingFang SC","Hiragino Sans GB","HarmonyOS Sans SC","Microsoft YaHei",sans-serif;
  font-size:14px;line-height:1.5}
:root:not([data-theme="dark"]) body:has(.report-shell){background:color-mix(in srgb, var(--bg) 60%, var(--surface))}
::selection{background:var(--selection)}
a{color:inherit;text-decoration:none}
button{cursor:pointer;font:inherit}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px;border-radius:5px}
.num{font-variant-numeric:tabular-nums}
.mono{font-family:ui-monospace,SFMono-Regular,"SF Mono",Menlo,Consolas,monospace;font-variant-numeric:tabular-nums}

/* ---- 壳：侧栏 / 窄轨 / 主列 / 手机顶栏与底栏 ---- */
.shell{display:flex;min-height:100dvh}
.sidebar,aside.rail{display:none}
.main{flex:1;min-width:0}
/* 列表宽度：桌面撑满主列，上限 max(1200px, 270dvh-236px)，超宽屏再居中 */
.page{max-width:640px;width:100%;margin:0 auto;padding:0 16px 96px}
@media(min-width:700px){
  .page{max-width:var(--page-max-wide);padding:0 20px 48px}
}
@media(min-width:700px){
  aside.rail{display:flex;position:sticky;top:0;height:100dvh;width:64px;flex-shrink:0;
    flex-direction:column;align-items:center;border-right:1px solid var(--line);
    background:var(--sidebar);padding:20px 6px 14px}
}
@media(min-width:941px){
  .page{padding:0 28px 48px}
  aside.rail{display:none}
  .sidebar{display:flex;position:sticky;top:0;height:100dvh;width:180px;flex-shrink:0;
    flex-direction:column;border-right:1px solid var(--line);background:var(--sidebar);
    padding:24px 12px 14px}
}
.brand{display:flex;align-items:center;gap:10px;color:var(--ink)}
.brand b{font-size:20px;font-weight:700;letter-spacing:.01em}
.brand small{display:block;font-size:11px;color:var(--ink-4);font-weight:400}
.nav-sec{margin-top:14px}
.nav-sec h3{margin:0;padding:14px 10px 4px;font-size:11px;font-weight:400;color:var(--ink-4)}
.side-link{display:flex;height:40px;align-items:center;gap:10px;padding:0 10px;border-radius:8px;
  font-size:14px;font-weight:500;color:var(--ink-3)}
.side-link svg{flex-shrink:0}
.side-link:hover{background:var(--bg-sunk);color:var(--ink)}
.side-link.on{background:rgba(23,107,117,.10);font-weight:600;color:var(--ink)}
.side-link.on svg{color:var(--accent)}
.side-foot{margin-top:auto;padding-top:12px}
.side-foot .gh{display:flex;height:34px;align-items:center;justify-content:center;gap:6px;
  border:1px solid var(--line);border-radius:9999px;font-size:12.5px;color:var(--ink-3)}
.side-foot .gh:hover{background:var(--bg-sunk);color:var(--ink)}
.side-foot .theme-btn{width:100%;height:34px;margin-top:8px;border:1px solid var(--line);
  border-radius:9999px;background:transparent;color:var(--ink-3);font-size:12.5px}
.side-foot .theme-btn:hover{background:var(--bg-sunk);color:var(--ink)}
.side-foot .note{margin:10px 4px 0;font-size:11.5px;color:var(--ink-4);text-align:center}
.rail-link{display:flex;width:100%;height:56px;flex-direction:column;align-items:center;justify-content:center;
  gap:3px;border-radius:8px;font-size:11px;font-weight:500;color:var(--ink-3)}
.rail-link:hover{background:var(--bg-sunk);color:var(--ink)}
.rail-link.on{background:rgba(23,107,117,.10);font-weight:600;color:var(--ink)}
[data-theme="dark"] .side-link.on,[data-theme="dark"] .rail-link.on{background:var(--accent-soft)}
.rail-link.on svg{color:var(--accent)}
aside.rail .brand{margin-bottom:12px}

/* 手机顶栏：品牌 + 精选|全部切换 + 外观按钮 */
.topbar{position:sticky;top:0;z-index:30;display:flex;height:var(--bar-h);align-items:center;gap:8px;
  padding:0 8px;background:var(--bg);border-bottom:1px solid var(--line)}
.topbar .brand b{font-size:17px}
.switch{display:flex;margin:0 auto;background:var(--well);border-radius:9999px;padding:2px;box-shadow:inset 0 0 0 1px var(--line-soft)}
.switch a{padding:3px 14px;border-radius:9999px;font-size:13px;font-weight:500;color:var(--ink-3)}
.switch a.on{background:var(--surface);color:var(--ink);font-weight:600;box-shadow:var(--shadow-card)}
.topbar .title{margin:0 auto;font-size:15px;font-weight:600}
.icon-btn{display:inline-flex;width:36px;height:36px;align-items:center;justify-content:center;
  border:0;border-radius:8px;background:transparent;color:var(--ink-3)}
.icon-btn:hover{background:var(--bg-sunk);color:var(--ink)}
.ic-sun,.ic-monitor{display:none}

/* 手机底栏 */
.tabbar{position:fixed;left:0;right:0;bottom:0;z-index:30;display:flex;background:var(--surface);
  border-top:1px solid var(--line);padding-bottom:env(safe-area-inset-bottom)}
.tabbar a{flex:1;display:flex;flex-direction:column;align-items:center;gap:2px;padding:7px 0 6px;
  font-size:11px;font-weight:500;color:var(--ink-3)}
.tabbar a.on{color:var(--accent);font-weight:600}
/* 桌面（≥700px）只留侧栏/窄轨，手机顶栏与底栏隐藏（须放在基础规则之后，否则同优先级后规则覆盖） */
@media(min-width:700px){.topbar,.tabbar{display:none}}

/* ---- 通用组件 ---- */
h1{font-size:24px;font-weight:600;line-height:1.3;margin:22px 0 0}
h2.sec{font-size:19px;font-weight:600;margin:30px 0 12px}
.lede{font-size:13px;color:var(--ink-4);margin:8px 0 0}
.card{background:var(--surface);border:1px solid var(--line);border-radius:12px;box-shadow:var(--shadow-card)}
.chip{display:inline-flex;align-items:center;height:26px;padding:0 10px;border-radius:9999px;
  border:1px solid var(--line-soft);background:var(--bg-sunk);font-size:12px;color:var(--ink-4)}
button.chip:hover{color:var(--accent);border-color:var(--line-strong)}
.chip.on{background:var(--accent-soft);border-color:transparent;color:var(--accent-ink);font-weight:600}
.tabs{position:relative;display:inline-flex;gap:2px;overflow-x:auto;scrollbar-width:none;
  margin:0;padding:3px;border-radius:9999px;background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft)}
.tabs::-webkit-scrollbar{display:none}
.tabs .chip{position:relative;z-index:1;flex-shrink:0;height:36px;padding:0 16px;border:0;
  background:transparent;font-size:14px;font-weight:500;color:var(--ink-3);border-radius:9999px}
.tabs .chip:hover{color:var(--ink)}
.tabs .chip.on{color:var(--ink);font-weight:600}
.tabs-thumb{position:absolute;top:3px;bottom:3px;left:3px;width:0;border-radius:9999px;
  background:var(--surface);box-shadow:var(--shadow-thumb),inset 0 0 0 1px var(--line);
  transition:left 300ms cubic-bezier(.25,1,.5,1),width 300ms cubic-bezier(.25,1,.5,1)}
[data-theme="dark"] .tabs-thumb{background:var(--raised)}
[data-theme="dark"] .switch a.on{background:var(--raised)}
/* 筛选行：左侧分类分段控件，右侧搜索框 */
.filter-row{display:flex;flex-wrap:wrap;align-items:center;gap:12px;margin:16px 0 4px}
.filter-row .tabs{max-width:100%}
.search{position:relative;width:100%}
@media(min-width:700px){.search{width:240px;flex-shrink:0}}
.search svg{position:absolute;left:16px;top:50%;transform:translateY(-50%);color:var(--ink-4);pointer-events:none}
.search:focus-within svg{color:var(--ink-3)}
.search input{width:100%;height:42px;border:0;border-radius:9999px;background:var(--well);
  padding:0 40px 0 40px;font:inherit;font-size:16px;color:var(--ink);outline:none;
  box-shadow:inset 0 0 0 1px var(--line-soft)}
@media(min-width:640px){.search input{font-size:14px}}
.search input::placeholder{color:var(--ink-4)}
.search input:hover{box-shadow:inset 0 0 0 1px var(--line-strong)}
.search input:focus{background:var(--surface);box-shadow:0 0 0 3px var(--accent-soft),inset 0 0 0 1px var(--accent)}
.search .clear{position:absolute;right:12px;top:50%;transform:translateY(-50%);
  display:none;width:24px;height:24px;align-items:center;justify-content:center;
  border:0;border-radius:9999px;background:transparent;color:var(--ink-4)}
.search .clear:hover{background:var(--bg-sunk);color:var(--ink)}
.search.has-value .clear{display:inline-flex}
.search kbd{position:absolute;right:16px;top:50%;transform:translateY(-50%);display:none;
  font-family:ui-monospace,Menlo,Consolas,monospace;font-size:10.5px;line-height:16px;
  padding:0 6px;border:1px solid var(--line-strong);border-radius:5px;background:var(--surface);color:var(--ink-4)}
@media(min-width:700px){.search:not(.has-value) kbd{display:block}}
/* 只看未读：独立小开关（首个日期行右侧 / 手机单独一行） */
.toggle-chip{display:inline-flex;min-height:28px;align-items:center;gap:6px;padding:0 12px;
  border-radius:9999px;border:1px solid var(--line-soft);background:var(--bg-sunk);
  font-size:12.5px;font-weight:500;color:var(--ink-3)}
.toggle-chip:hover{color:var(--ink);border-color:var(--line-strong)}
.toggle-chip.on{background:var(--accent-soft);border-color:transparent;color:var(--accent-ink);font-weight:600}
.unread-row{display:flex;justify-content:flex-end;margin:10px 0 2px}
@media(min-width:700px){.unread-row{display:none}}
.well{background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft);border-radius:14px;padding:14px 16px}
.well .kicker{font-size:12px;font-weight:600;color:var(--accent-ink)}
.well p{margin:6px 0 0;font-size:14.5px;line-height:1.75;color:var(--ink-2)}

/* 评分徽章（按档位着色的小药丸，85+ 红、70+ 青、其余安静） */
.score-pill{display:inline-flex;height:20px;align-items:center;gap:6px;white-space:nowrap;
  border-radius:9999px;padding:0 8px;box-shadow:inset 0 0 0 1px var(--ring,rgba(0,0,0,0))}
.score-pill .lbl{font-size:11px;font-weight:500;opacity:.8}
.score-pill .sep{width:1px;height:10px;background:currentColor;opacity:.25}
.score-pill .num{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
  font-size:12.5px;font-weight:700;font-variant-numeric:tabular-nums}
.score-pill.t-hot{background:color-mix(in srgb, var(--hot) 10%, transparent);color:var(--hot);--ring:color-mix(in srgb, var(--hot) 25%, transparent)}
.score-pill.t-acc{background:var(--accent-soft);color:var(--accent);--ring:color-mix(in srgb, var(--accent) 20%, transparent)}
.score-pill.t-quiet{color:var(--ink-4);--ring:var(--line-soft)}
@media(max-width:640px){.score-pill .lbl,.score-pill .sep{display:none}}
/* 精选徽章：琥珀底 + 圆点（不是青色） */
.pick{display:inline-flex;height:18px;align-items:center;gap:4px;padding:0 8px;border-radius:9999px;
  background:var(--amber-soft);color:var(--amber-ink);font-size:11px;font-weight:500}
.pick::before{content:"";width:5px;height:5px;border-radius:9999px;background:currentColor}
/* 当日新到徽章：趋势列的“新”样式 */
.new-pill{display:inline-flex;height:18px;align-items:center;padding:0 6px;border-radius:9999px;
  background:var(--accent-soft);color:var(--accent);font-size:10.5px;font-weight:600;line-height:16px}
.rank{font-weight:800;color:var(--rank-rest)}
.rank.r1{color:var(--rank-1)}.rank.r2{color:var(--rank-2)}.rank.r3{color:var(--rank-3)}

/* ---- 动态卡片（桌面白卡、手机行；来源行 + 标题 + 摘要 + 分类） ---- */
.feed-item{padding:14px 0;border-bottom:1px solid var(--line-soft)}
.feed-item:last-child{border-bottom:0}
@media(min-width:700px){
  .feed-item{padding:15px 18px 14px;background:var(--surface);border:1px solid var(--line);
    border-radius:12px;box-shadow:var(--shadow-card);margin-bottom:12px;
    transition:box-shadow 200ms,border-color 200ms,transform 200ms}
  .feed-item:hover{box-shadow:var(--shadow-card-hover);border-color:var(--line-strong);transform:translateY(-1px)}
}
.fi-head{display:flex;min-height:20px;align-items:center;gap:8px;font-size:12.5px;color:var(--ink-4)}
.fi-head .src{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.fi-head .pt{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12px}
@media(min-width:700px){.fi-head .pt{display:none}}
.fi-head .sp{margin-left:auto;display:flex;align-items:center;gap:6px;flex-shrink:0}
.star-btn{display:inline-flex;width:44px;height:44px;align-items:center;justify-content:center;
  margin:-11px -12px -11px 0;border:0;border-radius:8px;background:transparent;color:var(--ink-4)}
.star-btn:hover{background:var(--bg-sunk);color:var(--ink-2)}
.star-btn.on{color:var(--accent)}
.star-btn.on svg{fill:currentColor}
@media(min-width:700px){.star-btn{width:26px;height:26px;margin:-1px 0}}
.feed-item h3{margin:6px 0 0;font-size:17px;font-weight:650;line-height:1.5}
@media(min-width:700px){.feed-item h3{line-height:1.55}}
.feed-item.is-read h3 a{color:var(--ink-4)}
.feed-item h3 a:hover{color:var(--accent)}
.feed-item h3 .rank{margin-right:8px;font-size:17px}
.feed-item .sum{margin:4px 0 0;font-size:14.5px;line-height:1.7;color:var(--ink-3);
  display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
@media(min-width:700px){.feed-item .sum{-webkit-line-clamp:3;font-size:15px;line-height:1.75}}
.fi-foot{margin-top:8px;display:flex;gap:8px;align-items:center}
.fi-foot .when{font-size:12.5px;color:var(--ink-4)}
/* 推荐理由：13px、注色，桌面加顶线与间距 */
.fi-reason{margin-top:4px;font-size:13px;line-height:1.65;color:var(--note);
  display:-webkit-box;-webkit-line-clamp:1;-webkit-box-orient:vertical;overflow:hidden}
@media(min-width:700px){
  .fi-reason{margin-top:12px;padding-top:12px;border-top:1px solid var(--line-soft);
    -webkit-line-clamp:unset;line-height:1.75}
}

/* ---- 热点条（右上热色晕染 + 跳动 live 点 + 排名行） ---- */
.hot-card{position:relative;overflow:hidden;margin:16px 0 0;padding:10px 14px 4px;
  background:radial-gradient(120% 90% at 100% 0%,var(--hot-soft),transparent 55%),var(--surface)}
@media(min-width:700px){.hot-card{margin:18px 0 24px;padding:14px 20px 8px}}
.hot-head{display:flex;align-items:center;justify-content:space-between}
.hot-head h2{display:flex;align-items:center;gap:8px;margin:0;font-size:14px;font-weight:600}
.live{position:relative;display:inline-flex;width:8px;height:8px}
.live .ping{position:absolute;width:100%;height:100%;border-radius:9999px;background:var(--hot);opacity:.4;animation:ping 1.6s ease-out infinite}
.live .dot{position:relative;width:8px;height:8px;border-radius:9999px;background:var(--hot)}
@keyframes ping{0%{transform:scale(1);opacity:.4}80%,100%{transform:scale(2.4);opacity:0}}
.hot-more{display:inline-flex;align-items:center;gap:4px;border:0;background:transparent;
  font-size:12.5px;color:var(--ink-3);padding:6px 0}
.hot-more:hover{color:var(--accent)}
.hot-list{list-style:none;margin:2px 0 0;padding:0}
.hot-row{display:grid;grid-template-columns:20px minmax(0,1fr) 64px 20px;align-items:center;gap:12px;
  padding:7px 8px;margin:0 -8px;border-radius:10px}
.hot-row:hover{background:rgba(243,243,239,.7)}
[data-theme="dark"] .hot-row:hover{background:rgba(32,42,47,.4)}
.hot-row .rank{font-size:14px;font-weight:700;text-align:center}
.hot-row .rank.r1,.hot-row .rank.r2,.hot-row .rank.r3{font-size:15px;font-weight:900}
.hot-row .t{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:14.5px;font-weight:600}
@media(min-width:700px){.hot-row .t{font-size:14px}}
.hot-row:hover .t{color:var(--accent)}
.hot-heat{white-space:nowrap;font-size:12.5px;color:var(--ink-4);text-align:right}
.hot-heat b{font-size:13.5px;font-weight:600;color:var(--ink-2)}
.hot-trend{display:flex;width:20px;justify-content:center;color:var(--ink-4)}
.hot-trend .up{color:var(--hot)}
.hot-trend .flat{color:var(--ink-4)}
/* 手机只留前 3 名进榜，让动态流尽快出现在首屏 */
@media(max-width:639px){.hot-top5 li:nth-child(n+4){display:none}}

/* ---- 时间线（按天分组，桌面时间轨 + 青点，手机灰色日栏） ---- */
.day-head{position:sticky;top:var(--bar-h);z-index:20;display:flex;height:44px;align-items:center;gap:8px;
  margin:0 -16px;padding:0 16px;background:var(--daybar)}
.day-head .dh-name{font-size:14px;font-weight:700}
.day-head .dh-date{font-size:12.5px;color:var(--ink-4)}
.day-head .dh-wd{font-size:12.5px;color:var(--ink-4)}
.day-head .dh-count{margin-left:auto;font-size:12.5px;color:var(--ink-4)}
.day-head .dh-wd-full{display:none}
.day-head .dh-aside{display:none}
.day-head .dh-toggle{display:inline-flex;width:24px;height:24px;align-items:center;justify-content:center;
  flex-shrink:0;border:0;border-radius:9999px;background:transparent;color:var(--ink-4)}
.day-head .dh-toggle:hover{background:var(--bg-sunk);color:var(--ink)}
.day-head .dh-toggle svg{transition:transform 200ms}
.day-sec.collapsed .day-list{display:none}
.day-sec.collapsed .dh-toggle svg{transform:rotate(-90deg)}
@media(min-width:700px){
  .day-head{position:sticky;top:0;height:44px;margin:0;padding:0;background:var(--bg)}
  .day-head .dh-name{display:none}
  .day-head .dh-date{font-size:18px;font-weight:600;color:var(--ink)}
  .day-head .dh-wd{font-size:13px}
  .day-head .dh-wd-short{display:none}
  .day-head .dh-wd-full{display:inline}
  .day-head .dh-count{margin-left:0}
  .day-head .dh-aside{display:block;margin-left:auto}
}
.day-head:not(.is-today) .dh-date{display:none}
@media(min-width:700px){.day-head:not(.is-today) .dh-date{display:inline;font-size:18px;font-weight:600}}
.day-sec{margin-top:8px}
.day-list{list-style:none;margin:0;padding:0}
.slot{padding:14px 0;border-bottom:1px solid var(--line-soft)}
.slot:last-child{border-bottom:0}
.slot .slot-time,.slot .rail{display:none}
@media(min-width:700px){
  .slot{display:grid;grid-template-columns:64px 22px minmax(0,1fr);padding:0 0 12px;border-bottom:0}
  .slot .slot-time{display:block;padding-top:17px;font-family:ui-monospace,Menlo,Consolas,monospace;
    font-size:12.5px;font-weight:600;color:var(--ink-3)}
  .slot .rail{display:block;position:relative;width:auto;height:auto;background:transparent;padding:0;border:0}
  .slot .rail::before{content:"";position:absolute;left:10.5px;top:29px;bottom:-41px;width:1px;background:var(--line-strong)}
  .slot:last-child .rail::before{display:none}
  .slot .rail::after{content:"";position:absolute;left:7.5px;top:25.5px;width:7px;height:7px;
    border-radius:9999px;background:var(--accent);box-shadow:0 0 0 4px var(--bg)}
  .slot .feed-item{margin-bottom:0}
}

.foot{margin-top:36px;padding-top:14px;border-top:1px solid var(--line);font-size:13px;color:var(--ink-4)}
.foot p{margin:0 0 8px}
@media(max-width:699px){.foot{padding-bottom:8px}}
.tip{margin-top:20px;padding-top:16px;border-top:1px dashed var(--line);text-align:center}
.tip-cards{display:flex;flex-wrap:wrap;gap:8px 32px;justify-content:center}
.tip-card{max-width:300px}
.tip-title{font-size:13px;color:var(--ink-3)}
.tip-qr{width:150px;height:150px;border-radius:8px;background:#fff}
.tip-label{font-size:13px;color:var(--ink-3)}
.tip-addr{font-size:12px;color:var(--ink-4);word-break:break-all;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}
/* 回到顶部：圆按钮，滚过一屏多再出现（仅桌面） */
.to-top{position:fixed;right:max(24px,env(safe-area-inset-right));bottom:max(24px,env(safe-area-inset-bottom));
  z-index:30;display:none;width:44px;height:44px;align-items:center;justify-content:center;
  border-radius:9999px;border:1px solid var(--line);background:var(--surface);color:var(--ink-2);
  box-shadow:var(--shadow-soft);transition:opacity 200ms,transform 200ms;
  opacity:0;transform:translateY(8px);pointer-events:none}
.to-top.show{opacity:1;transform:none;pointer-events:auto}
.to-top:hover{color:var(--ink)}
@media(min-width:700px){.to-top{display:flex}}
/* 列表到底 */
.feed-end{padding:24px 0;text-align:center;font-size:12px;color:var(--ink-4)}
/* 日报名头：大字名 + 双线，照报纸的版头 */
.masthead{margin-top:24px;padding-bottom:16px;border-bottom:3px double var(--line-strong)}
.masthead .mp-brand{display:flex;align-items:center;gap:14px}
.masthead .mp-meta{margin:10px 0 0;font-size:13px;color:var(--ink-4)}
.masthead .mp-issue{display:inline-flex;height:20px;align-items:center;padding:0 8px;border-radius:9999px;
  background:var(--accent-soft);color:var(--accent-ink);font-size:12px;font-weight:600;margin-left:10px}

/* ---- v9：视觉打磨与新页面（颜色 token 不动） ---- */
/* A2：标题手机 2 行截断；摘要桌面上边距 8px；头部行手机 22px/6px */
@media(max-width:699px){.feed-item h3{display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}}
@media(min-width:700px){.feed-item .sum{margin-top:8px}}
@media(max-width:699px){.fi-head{min-height:22px;gap:6px}}
/* A3：手机隐藏 h1，lede 只留“更新于 …” */
@media(max-width:699px){h1{display:none}.lede-rest{display:none}}
/* A4：手机大标题（与 A3 联动） */
.m-title{display:none}
@media(max-width:699px){.m-title{display:block;font-size:30px;font-weight:800;line-height:1.25;margin:18px 0 0}}
/* A4：顶栏/底栏毛玻璃；顶栏滚动阴影 */
.topbar{background:color-mix(in srgb, var(--bg) 85%, transparent);
  backdrop-filter:blur(20px) saturate(1.5);-webkit-backdrop-filter:blur(20px) saturate(1.5)}
.topbar.scrolled{box-shadow:0 1px 0 var(--line),0 6px 16px rgba(28,39,51,.08)}
.tabbar{background:color-mix(in srgb, var(--surface) 90%, transparent);
  backdrop-filter:blur(20px) saturate(1.5);-webkit-backdrop-filter:blur(20px) saturate(1.5)}
.tabbar-in{display:flex;width:100%;max-width:640px;margin:0 auto}
.tabbar-in a{flex:1}
/* A6：圆点悬停放大；卡片按压态 */
.slot .rail::after{transition:transform 300ms}
.slot:hover .rail::after{transform:scale(1.15)}
.feed-item:active{transform:scale(0.995)}
/* A7：手机 chip 44px；热点条“完整榜单”整行 40px */
@media(max-width:699px){.tabs .chip{height:44px}}
.hot-more{display:flex;min-height:40px;align-items:center;justify-content:center;gap:6px;
  border-top:1px solid var(--line-soft);margin-top:6px;padding:0;font-size:13px;color:var(--ink-3)}
/* A8：减弱动效时关掉动画 */
@media (prefers-reduced-motion: reduce){
  *,*::before,*::after{animation-duration:.01ms !important;animation-iteration-count:1 !important;
    transition-duration:.01ms !important;scroll-behavior:auto !important}
}
/* A10：日报页用更窄的阅读宽度 */
@media(min-width:700px){.page.page-reading{max-width:var(--page-max-reading)}}
/* B1：热点榜头条大卡 / 次卡 / Delta / 方法说明 */
.hot-hero{padding:18px 20px 16px;margin:16px 0 0}
.hot-hero-top{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.no-tag{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12px;font-weight:800;
  letter-spacing:.06em;color:var(--rank-1)}
.hot-badge{display:inline-flex;height:18px;align-items:center;padding:0 8px;border-radius:9999px;
  font-size:11px;font-weight:600}
.hot-badge.b-new{background:var(--accent-soft);color:var(--accent)}
.hot-badge.b-hot{background:var(--hot-soft);color:var(--hot)}
.hot-badge.b-up{background:var(--amber-soft);color:var(--amber-ink)}
.hot-hero h2{margin:10px 0 0;font-size:20px;font-weight:700;line-height:1.45}
.hot-hero h2 a:hover{color:var(--accent)}
.hot-hero-meta{margin:6px 0 0;font-size:12.5px;color:var(--ink-4)}
.hot-hero-latest{margin:10px 0 0;font-size:14px;line-height:1.7;color:var(--ink-2)}
.hot-hero-latest .k{font-size:12px;font-weight:600;color:var(--accent-ink);margin-right:6px}
.hot-hero-foot{display:flex;align-items:flex-end;gap:14px;margin-top:14px;padding-top:12px;border-top:1px solid var(--line-soft)}
.hot-big{font-size:13px;color:var(--ink-4)}
.hot-big b{font-size:34px;font-weight:800;line-height:1;color:var(--ink);margin-right:4px;
  font-variant-numeric:tabular-nums}
.hot-hero-foot .score-pill{margin-left:auto}
.hot-sub-grid{display:grid;gap:12px;margin-top:12px}
@media(min-width:700px){.hot-sub-grid{grid-template-columns:1fr 1fr}}
.hot-sub{padding:14px 16px}
.hot-sub-top{display:flex;align-items:center;gap:8px}
.hot-sub h3{margin:8px 0 0;font-size:16px;font-weight:650;line-height:1.5}
.hot-sub h3 a:hover{color:var(--accent)}
.hot-sub-meta{margin:4px 0 0;font-size:12.5px;color:var(--ink-4)}
.hot-sub-foot{display:flex;align-items:center;gap:10px;margin-top:10px}
.hot-num{font-size:12.5px;color:var(--ink-4)}
.hot-num b{font-size:16px;font-weight:700;color:var(--ink-2);font-variant-numeric:tabular-nums}
.hot-delta{font-size:12.5px;font-weight:600;white-space:nowrap;font-variant-numeric:tabular-nums}
.hot-delta.up{color:var(--hot)}
.hot-delta.down{color:var(--ink-4)}
.hot-delta.new{color:var(--accent)}
.hot-delta.flat{color:var(--ink-4)}
.hot-row{grid-template-columns:20px minmax(0,1fr) 64px 56px 20px}
.hot-row .hot-delta{text-align:right}
.hot-method{margin-top:20px}
.hot-method p{margin:6px 0 0;font-size:13.5px;line-height:1.75;color:var(--ink-3)}
/* B19：卡片式空状态 */
.empty-state{margin:24px 0;padding:32px 20px;text-align:center;
  background:var(--surface);border:1px solid var(--line);border-radius:12px;box-shadow:var(--shadow-card)}
.empty-icon{display:flex;justify-content:center;color:var(--ink-4);margin-bottom:12px}
.empty-title{margin:0;font-size:16px;font-weight:650}
.empty-text{margin:8px 0 0;font-size:13.5px;color:var(--ink-4)}
.empty-actions{display:flex;gap:10px;justify-content:center;margin-top:18px;flex-wrap:wrap}
.empty-btn{display:inline-flex;min-height:36px;align-items:center;padding:0 18px;border-radius:9999px;
  border:1px solid var(--line-strong);background:var(--surface);font-size:13.5px;font-weight:500;color:var(--ink-2)}
.empty-btn:hover{border-color:var(--accent);color:var(--accent)}
.empty-btn.primary{background:var(--accent);border-color:transparent;color:var(--accent-contrast);font-weight:600}
.empty-btn.primary:hover{color:var(--accent-contrast);opacity:.9}
/* B14：手机搜索浮层（触发按钮只在手机显示） */
.search-trigger{display:flex;width:100%;height:42px;align-items:center;gap:10px;padding:0 16px;
  border:0;border-radius:9999px;background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft);
  font-size:16px;color:var(--ink-4);text-align:left}
@media(min-width:700px){.search-trigger{display:none}}
@media(max-width:699px){.filter-row .search{display:none}}
.search-overlay{position:fixed;inset:0;z-index:60;overflow-y:auto;background:var(--bg);padding:0 16px 48px}
.search-overlay .overlay-bar{position:sticky;top:0;z-index:1;display:flex;align-items:center;gap:8px;
  padding:12px 0;background:color-mix(in srgb, var(--bg) 90%, transparent);
  backdrop-filter:blur(20px) saturate(1.5);-webkit-backdrop-filter:blur(20px) saturate(1.5)}
.overlay-search{flex:1}
.overlay-sec{margin-top:20px}
.overlay-sec h3{margin:0 0 10px;font-size:13px;font-weight:600;color:var(--ink-4)}
.overlay-sec .recent-row{display:flex;align-items:center;gap:8px;margin-bottom:8px}
.overlay-sec .recent-row button{flex:1;text-align:left}
.overlay-sec .recent-clear{font-size:12.5px;color:var(--ink-4);border:0;background:transparent;padding:4px 0}
.overlay-sec .recent-clear:hover{color:var(--accent)}
.overlay-cats{display:flex;flex-wrap:wrap;gap:8px}
.overlay-hot{list-style:none;margin:0;padding:0}
.overlay-hot li{border-bottom:1px solid var(--line-soft)}
.overlay-hot li:last-child{border-bottom:0}
.overlay-hot a{display:flex;gap:10px;align-items:baseline;padding:10px 0;font-size:14.5px;font-weight:600}
.overlay-hot a:hover{color:var(--accent)}
.overlay-hot .rank{flex-shrink:0}
/* B15：三向主题切换（带滑动 thumb） */
.theme-seg{position:relative;display:inline-flex;gap:2px;padding:3px;border-radius:9999px;
  background:var(--well);box-shadow:inset 0 0 0 1px var(--line-soft)}
.theme-seg button{position:relative;z-index:1;display:inline-flex;height:36px;align-items:center;gap:6px;
  padding:0 14px;border:0;border-radius:9999px;background:transparent;font-size:13.5px;font-weight:500;color:var(--ink-3)}
.theme-seg button.on{color:var(--ink);font-weight:600}
.theme-seg-thumb{position:absolute;top:3px;bottom:3px;left:3px;width:0;border-radius:9999px;
  background:var(--surface);box-shadow:var(--shadow-thumb),inset 0 0 0 1px var(--line);
  transition:left 300ms cubic-bezier(.25,1,.5,1),width 300ms cubic-bezier(.25,1,.5,1)}
[data-theme="dark"] .theme-seg-thumb{background:var(--raised)}
/* B4/B6：我的页行 + 红点 */
.more-sec{margin-top:24px}
.more-sec h2{margin:0 0 8px;font-size:15px;font-weight:600}
.more-row{display:flex;align-items:center;gap:12px;width:100%;min-height:52px;padding:10px 14px;
  border:0;border-bottom:1px solid var(--line-soft);background:var(--surface);text-align:left;
  font-size:14.5px;font-weight:500;color:var(--ink)}
.more-row:first-of-type{border-top:1px solid var(--line-soft)}
.more-row:hover{background:var(--bg-sunk)}
.more-row svg{color:var(--ink-4);flex-shrink:0}
.more-row .m-label{flex:1}
.more-row .m-val{font-size:13px;color:var(--ink-4);font-weight:400}
.more-row .m-arrow{color:var(--ink-4)}
.dot-red{position:relative;display:inline-flex;width:8px;height:8px}
.dot-red::after{content:"";width:8px;height:8px;border-radius:9999px;background:var(--hot)}
.more-note{margin:10px 0 0;font-size:13px;line-height:1.7;color:var(--ink-4)}
.more-note a{color:var(--accent);text-decoration:underline}
/* B6/B8：更新日志与存档 */
.cl-item{padding:16px 0;border-bottom:1px solid var(--line-soft)}
.cl-item:last-child{border-bottom:0}
.cl-item h3{margin:0;font-size:16px;font-weight:650}
.cl-item .cl-date{font-size:12.5px;color:var(--ink-4);margin:4px 0 0}
.cl-item ul{margin:8px 0 0;padding-left:18px;font-size:14px;line-height:1.75;color:var(--ink-2)}
.arch-month{margin-top:20px}
.arch-month h3{margin:0 0 8px;font-size:15px;font-weight:600}
.arch-list{list-style:none;margin:0;padding:0}
.arch-list li{border-bottom:1px solid var(--line-soft)}
.arch-list li:last-child{border-bottom:0}
.arch-list a{display:flex;align-items:baseline;gap:10px;padding:10px 0;font-size:14.5px}
.arch-list a:hover{color:var(--accent)}
.arch-list .a-date{font-weight:600}
.arch-list .a-issue{font-size:12.5px;color:var(--ink-4)}
.arch-list .a-count{margin-left:auto;font-size:12.5px;color:var(--ink-4)}
/* 日报上下期导航 */
.daily-nav{display:flex;justify-content:space-between;gap:12px;margin-top:28px;padding-top:16px;border-top:1px solid var(--line)}
.daily-nav a{display:inline-flex;align-items:center;gap:6px;font-size:14px;font-weight:500;color:var(--ink-2)}
.daily-nav a:hover{color:var(--accent)}
.daily-nav .dn-next{margin-left:auto}
/* B3：收藏页下架条目置灰 */
.starred-item.is-gone{opacity:.55}
.starred-item .gone-tag{display:inline-flex;height:18px;align-items:center;padding:0 8px;border-radius:9999px;
  background:var(--bg-muted);color:var(--ink-4);font-size:11px;font-weight:500}
.starred-item .starred-at{font-size:12.5px;color:var(--ink-4)}
/* B13：同事件归组展开 */
.slot .group-toggle{grid-column:3;justify-self:start;margin:2px 0 0;padding:4px 10px;border:1px solid var(--line-soft);
  border-radius:9999px;background:var(--bg-sunk);font-size:12.5px;color:var(--ink-3)}
.slot .group-toggle:hover{color:var(--accent);border-color:var(--line-strong)}
.slot .group-extra{grid-column:3;margin-top:8px}
.group-extra-list{list-style:none;margin:0;padding:0}
.group-extra-list li{display:flex;gap:10px;align-items:baseline;padding:7px 0;border-top:1px solid var(--line-soft)}
.group-extra-list li:first-child{border-top:0}
.group-extra-list a{font-size:13.5px;font-weight:500}
.group-extra-list a:hover{color:var(--accent)}
.group-extra-list .ge-time{margin-left:auto;font-size:12px;color:var(--ink-4);white-space:nowrap}
/* B16：卡片标签 */
.fi-tags{display:flex;flex-wrap:wrap;gap:6px;margin-top:8px}
.fi-tags .tag{font-size:12px;color:var(--accent-ink);background:var(--accent-softer);
  border-radius:9999px;padding:2px 8px}
.fi-tags .tag:hover{background:var(--accent-soft)}
/* 详情页（items/:id）：阅读宽度 + 大标题 + 导读 + 操作行 */
.item-back{display:inline-flex;align-items:center;gap:6px;margin:4px 0 14px;padding:6px 12px 6px 8px;
  border:1px solid var(--line-soft);border-radius:9999px;background:var(--surface);
  font-size:13.5px;color:var(--ink-3)}
.item-back:hover{color:var(--accent);border-color:var(--line-strong)}
.item-meta{display:flex;flex-wrap:wrap;align-items:center;gap:10px;font-size:13px;color:var(--ink-4);margin-bottom:12px}
.item-meta .src{font-weight:600;color:var(--ink-2)}
.item-h1{font-size:32px;line-height:1.35;margin:0 0 10px}
.item-en-title{font-size:15px;line-height:1.6;color:var(--ink-4);margin:0 0 16px}
.item-guide{margin:16px 0}
.item-guide p{font-size:18px;line-height:1.7;margin:0}
.item-guide .guide-note{font-size:13px;color:var(--ink-4);margin-bottom:6px}
.item-actions{display:flex;flex-wrap:wrap;gap:10px;margin:18px 0}
.item-open-btn{display:inline-flex;align-items:center;gap:8px;min-height:44px;padding:0 20px;
  border-radius:9999px;background:var(--accent);color:#fff;font-size:15px;font-weight:600}
.item-open-btn:hover{background:var(--accent-strong)}
.item-open-btn:visited,.item-open-btn:active{color:#fff}
.item-ghost-btn{display:inline-flex;align-items:center;gap:6px;min-height:44px;padding:0 16px;
  border-radius:9999px;border:1px solid var(--line-strong);background:var(--surface);
  font-size:14px;color:var(--ink-2)}
.item-ghost-btn:hover{border-color:var(--accent);color:var(--accent)}
.item-ghost-btn.on{color:var(--accent);border-color:var(--accent)}
.item-source-line{font-size:13.5px;color:var(--ink-4);margin:6px 0 16px}
.item-source-line b{color:var(--ink-2)}
.item-sec{margin-top:28px}
.item-sec h2{font-size:17px;margin:0 0 10px}
.item-related-list{display:flex;flex-direction:column;gap:10px}
.item-related-list a{font-size:14.5px;font-weight:500;line-height:1.5}
.item-related-list a:hover{color:var(--accent)}
.item-related-list .rel-meta{font-size:12.5px;color:var(--ink-4)}
@media(max-width:699px){.item-h1{font-size:26px}}
/* B2：加载更多 */
.load-more-wrap{text-align:center;padding:16px 0 4px}
.load-more-btn{display:inline-flex;min-height:40px;align-items:center;gap:8px;padding:0 22px;
  border-radius:9999px;border:1px solid var(--line-strong);background:var(--surface);
  font-size:14px;font-weight:500;color:var(--ink-2)}
.load-more-btn:hover{border-color:var(--accent);color:var(--accent)}
.load-more-btn:disabled{opacity:.6;cursor:default}
.load-more-btn .spin{width:14px;height:14px;border:2px solid var(--line-strong);border-top-color:var(--accent);
  border-radius:9999px;animation:spin 0.8s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}
.load-more-state{margin:10px 0 0;font-size:12.5px;color:var(--ink-4)}
/* B2/B17：搜索结果区 */
.search-results-head{display:flex;align-items:baseline;gap:10px;margin:16px 0 4px}
.search-results-head h2{margin:0;font-size:17px;font-weight:600}
.search-results-head .sr-count{font-size:13px;color:var(--ink-4)}
/* C3：页脚链接行 */
.foot-links{display:flex;flex-wrap:wrap;gap:4px 16px;margin-top:4px;font-size:13px}
.foot-links a{color:var(--ink-3)}
.foot-links a:hover{color:var(--accent)}
/* 官方标记：T1 信源卡片头部的小标签 */
.off-tag{display:inline-flex;height:18px;align-items:center;padding:0 6px;border-radius:9999px;
  background:var(--accent-soft);color:var(--accent);font-size:11px;font-weight:600}
"""


def esc(s):
    return html.escape(s or "", quote=True)


def _L(lang, zh, en):
    """双语渲染：lang=='en' 取英文，否则取中文。中文分支永远返回原文字面量，
    保证中文输出与单语版一字不差。"""
    return en if lang == "en" else zh


def _name(site, lang):
    """站点名：英文版用 name_en（无则回退中文名），中文版永远用中文名。"""
    if lang == "en":
        return site.get("name_en") or site.get("name", "HOT")
    return site.get("name", "HOT")


_CJK_RE = re.compile(r"[\u4e00-\u9fff]")


def _no_cjk_keys(d):
    """去掉含中文字符的键（英文版内嵌 JSON 用：JS 只按英文关键词匹配标题）。"""
    return {k: v for k, v in d.items() if not _CJK_RE.search(k)}


def _no_cjk_list(xs):
    """去掉含中文字符的元素（英文版内嵌 JSON 用）。"""
    return [x for x in xs if not _CJK_RE.search(str(x))]


# 已下线信源的旧中文名 -> 英文名（英文版存档页渲染信源标签用）
SOURCE_NAMES_EN = {
    "Hacker News 最新": "Hacker News",
    "Hacker News 首页": "Hacker News",
    "Medium Tools 标签": "Medium Tools",
}


WEEKDAYS = ["星期一", "星期二", "星期三", "星期四", "星期五", "星期六", "星期日"]
WEEKDAYS_SHORT = ["周一", "周二", "周三", "周四", "周五", "周六", "周日"]
WEEKDAYS_EN = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
WEEKDAYS_SHORT_EN = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
MONTHS_SHORT_EN = ["Jan", "Feb", "Mar", "Apr", "May", "Jun",
                   "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
MONTHS_EN = ["January", "February", "March", "April", "May", "June",
             "July", "August", "September", "October", "November", "December"]

# 线性描边小图标（feather 风格；不引入任何外部资源）
ICONS = {
    "zap": '<polygon points="13 2 3 14 12 14 11 22 21 10 12 10 13 2"/>',
    "list": '<line x1="8" y1="6" x2="21" y2="6"/><line x1="8" y1="12" x2="21" y2="12"/>'
            '<line x1="8" y1="18" x2="21" y2="18"/><line x1="3" y1="6" x2="3.01" y2="6"/>'
            '<line x1="3" y1="12" x2="3.01" y2="12"/><line x1="3" y1="18" x2="3.01" y2="18"/>',
    "trend": '<polyline points="23 6 13.5 15.5 8.5 10.5 1 18"/><polyline points="17 6 23 6 23 12"/>',
    "doc": '<path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/>'
           '<polyline points="14 2 14 8 20 8"/><line x1="16" y1="13" x2="8" y2="13"/>'
           '<line x1="16" y1="17" x2="8" y2="17"/>',
    "code": '<polyline points="16 18 22 12 16 6"/><polyline points="8 6 2 12 8 18"/>',
    "bookmark": '<path d="M19 21l-7-5-7 5V5a2 2 0 0 1 2-2h10a2 2 0 0 1 2 2z"/>',
    "search": '<circle cx="11" cy="11" r="8"/><line x1="21" y1="21" x2="16.65" y2="16.65"/>',
    "chevron-down": '<polyline points="6 9 12 15 18 9"/>',
    "trend-up": '<polyline points="23 6 13.5 15.5 8.5 10.5 1 18"/><polyline points="17 6 23 6 23 12"/>',
    "trend-down": '<polyline points="23 18 13.5 8.5 8.5 13.5 1 6"/><polyline points="17 18 23 18 23 12"/>',
    "minus": '<line x1="5" y1="12" x2="19" y2="12"/>',
    "arrow-up": '<line x1="12" y1="19" x2="12" y2="5"/><polyline points="5 12 12 5 19 12"/>',
    "monitor": '<rect x="2" y="3" width="20" height="14" rx="2"/><line x1="8" y1="21" x2="16" y2="21"/>'
               '<line x1="12" y1="17" x2="12" y2="21"/>',
    "user": '<path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/>'
            '<circle cx="12" cy="7" r="4"/>',
    "rss": '<path d="M4 11a9 9 0 0 1 9 9"/><path d="M4 4a16 16 0 0 1 16 16"/>'
           '<circle cx="5" cy="19" r="1"/>',
    "message": '<path d="M21 11.5a8.38 8.38 0 0 1-.9 3.8 8.5 8.5 0 0 1-7.6 4.7 8.38 8.38 0 0 1-3.8-.9L3 21l1.9-5.7a8.38 8.38 0 0 1-.9-3.8 8.5 8.5 0 0 1 4.7-7.6 8.38 8.38 0 0 1 3.8-.9h.5a8.48 8.48 0 0 1 8 8v.5z"/>',
    "x": '<line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/>',
    "calendar": '<rect x="3" y="4" width="18" height="18" rx="2"/><line x1="16" y1="2" x2="16" y2="6"/>'
                '<line x1="8" y1="2" x2="8" y2="6"/><line x1="3" y1="10" x2="21" y2="10"/>',
    "check": '<polyline points="20 6 9 17 4 12"/>',
    "moon": '<path d="M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79z"/>',
    "sun": '<circle cx="12" cy="12" r="5"/><line x1="12" y1="1" x2="12" y2="3"/>'
           '<line x1="12" y1="21" x2="12" y2="23"/><line x1="4.22" y1="4.22" x2="5.64" y2="5.64"/>'
           '<line x1="18.36" y1="18.36" x2="19.78" y2="19.78"/><line x1="1" y1="12" x2="3" y2="12"/>'
           '<line x1="21" y1="12" x2="23" y2="12"/><line x1="4.22" y1="19.78" x2="5.64" y2="18.36"/>'
           '<line x1="18.36" y1="5.64" x2="19.78" y2="4.22"/>',
    "globe": '<circle cx="12" cy="12" r="10"/><line x1="2" y1="12" x2="22" y2="12"/>'
             '<path d="M12 2a15.3 15.3 0 0 1 4 10 15.3 15.3 0 0 1-4 10 15.3 15.3 0 0 1-4-10 15.3 15.3 0 0 1 4-10z"/>',
}


def icon(name, size=17):
    return (f'<svg width="{size}" height="{size}" viewBox="0 0 24 24" fill="none" '
            f'stroke="currentColor" stroke-width="2" stroke-linecap="round" '
            f'stroke-linejoin="round" aria-hidden="true">{ICONS[name]}</svg>')


def score_pill(score, lang="zh"):
    """AIHOT Score 的分档药丸：85+ 红、70+ 青、其余安静；手机只留数字。"""
    tier = "t-hot" if score >= 85 else ("t-acc" if score >= 70 else "t-quiet")
    lbl = _L(lang, "评分", "Score")
    return (f'<span class="score-pill {tier}" title="{lbl} {score}/100">'
            f'<span class="lbl">{lbl}</span><span class="sep"></span>'
            f'<span class="num">{score}</span></span>')


def _pub_dt(it):
    pub = it.get("_pub")
    if pub is None:  # daily.json 里的条目只有 ISO 字符串，没有 _pub
        pub = datetime.fromisoformat(it["published"])
        if pub.tzinfo is None:
            pub = pub.replace(tzinfo=timezone.utc)
    return pub


def feed_item(it, rank=None, badge=False, base="", lang="zh"):
    """AIHOT FeedItem 的静态版：来源行 + 标题 + 一句话简介 + 分类 + 推荐理由 + 星标。
    中文渲染优先显示中文标题与中文简介（zh_title/zh_oneliner）；英文渲染用
    en_title（缺失回退原标题）与 en_oneliner（缺失只显示标题与链接，绝不回退
    中文简介）。base 是到站根的目录前缀（'' 或 '../'，日报存档页用）。"""
    pub = _pub_dt(it)
    rank_html = ""
    if rank:
        cls = "r1" if rank == 1 else ("r2" if rank == 2 else ("r3" if rank == 3 else ""))
        rank_html = f'<span class="rank {cls}">{rank}</span>'
    badge_html = (f'<span class="pick">{_L(lang, "精选", "Featured")}</span>'
                    if badge else "")
    new_html = (f'<span class="new-pill">{_L(lang, "新", "New")}</span>'
                if it.get("is_new") else "")
    off_html = (f'<span class="off-tag">{_L(lang, "官方", "Official")}</span>'
                if it.get("_tier") == "T1" else "")
    reason_html = (f'<p class="fi-reason">{_L(lang, "推荐理由：", "Why this: ")}'
                   f'{esc(it["reason"])}</p>'
                   if it.get("reason") else "")
    tags_html = ""
    tags = it.get("tags") or []
    if tags:
        tags_html = ('<div class="fi-tags">' + "".join(
            f'<a class="tag" href="{base}topics/{TAG_SLUGS_ALL.get(t, t)}.html">#{esc(t)}</a>'
            for t in tags[:3]) + '</div>')
    if lang == "en":
        title = it.get("en_title") or it["title"]
        summary = it.get("en_oneliner") or ""
    else:
        title = it.get("zh_title") or it["title"]
        summary = it.get("zh_oneliner") or ""
    en_text = it.get("en_title") or it["title"]
    return (f'<article class="feed-item" data-id="{esc(it["id"])}" data-category="{esc(it["category"])}"'
            f' data-official="{"1" if it.get("_tier") == "T1" else "0"}"'
            f' data-en="{esc(en_text)}">'
            f'<header class="fi-head"><span class="src">{esc(it["source"])}</span>{off_html}'
            f'<time class="pt">· {esc(pub.astimezone(CST).strftime("%H:%M"))}</time>'
            f'{badge_html}{new_html}'
            f'<span class="sp">{score_pill(it["score"], lang)}'
            f'<button type="button" class="star-btn" aria-label="{_L(lang, "收藏", "Save")}" title="{_L(lang, "收藏", "Save")}">'
            f'{icon("bookmark", 16)}</button></span></header>'
            f'<h3>{rank_html}<a href="{base}items/{esc(it["id"])}.html">{esc(title)}</a></h3>'
            + (f'<p class="sum">{esc(summary)}</p>' if summary else "")
            + f'<div class="fi-foot"><button type="button" class="chip cat" data-filter="{esc(it["category"])}">'
            f'{esc(it["category_label"])}</button>'
            f'<span class="when">{esc(fmt_cst_en(pub) if lang == "en" else fmt_cst(pub))}</span></div>'
            + tags_html
            + reason_html
            + "</article>")


def hot_delta_html(it, lang="zh"):
    """Delta：对照上一轮热度（prev_hot_score），带 %；首次上榜标“新”。"""
    prev = it.get("prev_hot_score")
    cur = it.get("hot_score")
    if prev is None or cur is None:
        return f'<span class="hot-delta new">{_L(lang, "新", "New")}</span>'
    if prev <= 0:
        return '<span class="hot-delta flat">–</span>'
    d = (cur - prev) / prev * 100.0
    if abs(d) < 0.5:
        return '<span class="hot-delta flat">–</span>'
    cls = "up" if d > 0 else "down"
    arrow = "▲" if d > 0 else "▼"
    return f'<span class="hot-delta {cls}">{arrow} {abs(d):.0f}%</span>'


def hot_badges(it, lang="zh"):
    """头条/次卡徽章：热度 ≥90 为“爆”，首次上榜为“新”，名次上升为“发酵中”。"""
    out = []
    if it.get("trend") == "new":
        out.append(f'<span class="hot-badge b-new">{_L(lang, "新", "New")}</span>')
    if (it.get("hot_score") or 0) >= 90:
        out.append(f'<span class="hot-badge b-hot">{_L(lang, "爆", "Hot")}</span>')
    if it.get("trend") == "up":
        out.append(f'<span class="hot-badge b-up">{_L(lang, "发酵中", "Rising")}</span>')
    return "".join(out[:2])


def hot_row(it, rank, pad=False, lang="zh"):
    """AIHOT HotTopics 的排名行：彩色名次 + 标题 + 热度分 + Delta + 趋势（升/降/新/持平）。"""
    cls = "r1" if rank == 1 else ("r2" if rank == 2 else ("r3" if rank == 3 else ""))
    num = f"{rank:02d}" if pad else str(rank)
    trend = it.get("trend", "same")
    if trend == "up":
        trend_html = f'<span class="hot-trend"><span class="up" title="{_L(lang, "热度上升", "Rising")}">{icon("trend-up", 14)}</span></span>'
    elif trend == "down":
        trend_html = f'<span class="hot-trend"><span title="{_L(lang, "热度回落", "Cooling")}">{icon("trend-down", 14)}</span></span>'
    elif trend == "new":
        trend_html = f'<span class="hot-trend"><span class="new-pill">{_L(lang, "新", "New")}</span></span>'
    else:
        trend_html = f'<span class="hot-trend"><span class="flat" title="{_L(lang, "热度持平", "Steady")}">{icon("minus", 14)}</span></span>'
    return (f'<li><a class="hot-row" href="items/{esc(it["id"])}.html">'
            f'<span class="rank {cls}">{num}</span>'
            f'<span class="t">{esc((it.get("en_title") or it["title"]) if lang == "en" else (it.get("zh_title") or it["title"]))}</span>'
            f'<span class="hot-heat"><b class="num">{round(it["hot_score"])}</b> {_L(lang, "热度", "Heat")}</span>'
            f'{hot_delta_html(it, lang)}'
            f'{trend_html}'
            f'</a></li>')

THEME_BOOT = """<script>(function(){try{var k='__SLUG__-theme';function sys(){return window.matchMedia&&matchMedia('(prefers-color-scheme: dark)').matches?'dark':'light';}function apply(t){document.documentElement.setAttribute('data-theme',t==='dark'?'dark':'light');}var saved=localStorage.getItem(k);if(saved==='dark'||saved==='light'){apply(saved);}else{apply(sys());var mq=window.matchMedia&&matchMedia('(prefers-color-scheme: dark)');if(mq&&mq.addEventListener){mq.addEventListener('change',function(){try{if(!localStorage.getItem(k))apply(sys());}catch(e){}});}}}catch(e){}})();</script>"""

SCRIPT = """
<script>
(function(){
var LS_READ='__SLUG__-read',LS_STAR='__SLUG__-starred',LS_STAR_META='__SLUG__-starred-meta',
    LS_THEME='__SLUG__-theme',LS_RECENT='__SLUG__-recent-search',LS_CL_READ='__SLUG__-changelog-read';
function loadSet(k){try{return new Set(JSON.parse(localStorage.getItem(k)||'[]'));}catch(e){return new Set();}}
function saveSet(k,s){try{localStorage.setItem(k,JSON.stringify(Array.from(s)));}catch(e){}}
function loadObj(k){try{return JSON.parse(localStorage.getItem(k)||'{}')||{};}catch(e){return {};}}
function saveObj(k,o){try{localStorage.setItem(k,JSON.stringify(o));}catch(e){}}
var readSet=loadSet(LS_READ),starSet=loadSet(LS_STAR),starMeta=loadObj(LS_STAR_META);
function sysTheme(){return window.matchMedia&&matchMedia('(prefers-color-scheme: dark)').matches?'dark':'light';}
function currentTheme(){var s=null;try{s=localStorage.getItem(LS_THEME);}catch(e){}return (s==='dark'||s==='light')?s:'system';}
function applyTheme(mode){
  var t=mode==='system'?sysTheme():mode;
  var done=function(){
    document.documentElement.setAttribute('data-theme',t);
    try{
      if(mode==='system'){localStorage.removeItem(LS_THEME);}
      else{localStorage.setItem(LS_THEME,mode);}
    }catch(e){}
    syncThemeUI();
  };
  if(document.startViewTransition){try{document.startViewTransition(done);return;}catch(e){}}
  done();
}
function syncThemeUI(){
  var mode=currentTheme();
  document.querySelectorAll('.theme-cycle').forEach(function(b){
    b.setAttribute('data-mode',mode);
    var ic=b.querySelector('.ic-moon'),is=b.querySelector('.ic-sun'),im=b.querySelector('.ic-monitor');
    if(ic)ic.style.display=mode==='dark'?'inline-flex':'none';
    if(is)is.style.display=mode==='light'?'inline-flex':'none';
    if(im)im.style.display=mode==='system'?'inline-flex':'none';
    b.setAttribute('aria-label','外观：'+(mode==='dark'?'深色':mode==='light'?'浅色':'跟随系统')+'（点击切换）');
  });
  document.querySelectorAll('.theme-seg button').forEach(function(b){
    b.classList.toggle('on',b.getAttribute('data-theme-opt')===mode);
  });
  moveThemeThumb();
}
document.querySelectorAll('.theme-btn').forEach(function(b){b.addEventListener('click',function(){
  var order=['system','dark','light'],cur=currentTheme();
  applyTheme(order[(order.indexOf(cur)+1)%order.length]);
});});
document.querySelectorAll('.theme-seg button').forEach(function(b){b.addEventListener('click',function(){
  applyTheme(b.getAttribute('data-theme-opt'));
});});
/* 三向切换的滑动 thumb：量一下当前选中项的位置 */
var themeSegEl=document.querySelector('.theme-seg');
var themeThumb=document.getElementById('themeSegThumb');
function moveThemeThumb(){
  if(!themeSegEl||!themeThumb)return;
  var on=themeSegEl.querySelector('button.on');
  if(!on){themeThumb.style.width='0px';return;}
  themeThumb.style.left=(on.offsetLeft)+'px';
  themeThumb.style.width=(on.offsetWidth)+'px';
}
window.addEventListener('resize',moveThemeThumb);
window.addEventListener('load',moveThemeThumb);
syncThemeUI();
/* 已读：点开标题即记已读，标题变灰；星标：本地收藏，可再筛出来。
   bindFeedItem 供动态加载的卡片复用（B2 分页/搜索结果）。 */
function bindFeedItem(el){
  if(el.getAttribute('data-bound'))return;
  el.setAttribute('data-bound','1');
  var id=el.getAttribute('data-id');
  if(!id)return;
  if(readSet.has(id))el.classList.add('is-read');
  var star=el.querySelector('.star-btn');
  if(star){
    if(starSet.has(id)){star.classList.add('on');star.setAttribute('aria-label','取消收藏');star.title='取消收藏';}
    star.addEventListener('click',function(){
      if(starSet.has(id)){
        starSet.delete(id);delete starMeta[id];
        star.classList.remove('on');star.setAttribute('aria-label','收藏');star.title='收藏';
      }else{
        starSet.add(id);
        /* 收藏快照：标题/链接/来源/时间，供收藏页离线展示与下架置灰用 */
        var a=el.querySelector('h3 a'),src=el.querySelector('.fi-head .src');
        starMeta[id]={title:a?a.textContent.trim():'',link:a?a.getAttribute('href'):'',
          source:src?src.textContent.trim():'',at:new Date().toISOString()};
        star.classList.add('on');star.setAttribute('aria-label','取消收藏');star.title='取消收藏';
      }
      saveSet(LS_STAR,starSet);saveObj(LS_STAR_META,starMeta);applyFilters();
    });
  }
  var a=el.querySelector('h3 a');
  if(a)a.addEventListener('click',function(){
    if(!readSet.has(id)){readSet.add(id);saveSet(LS_READ,readSet);el.classList.add('is-read');applyFilters();}
  });
}
document.querySelectorAll('.feed-item').forEach(bindFeedItem);
/* 筛选状态：分类 + 只看收藏 + 只看未读 + 搜索词，四者叠加 */
var state={cat:'all',star:false,unread:false,q:''};
function itemVisible(el){
  var id=el.getAttribute('data-id')||'';
  if(state.cat==='official'&&el.getAttribute('data-official')!=='1')return false;
  if(state.cat!=='all'&&state.cat!=='starred'&&state.cat!=='official'&&el.getAttribute('data-category')!==state.cat)return false;
  if(state.cat==='starred'&&!starSet.has(id))return false;
  if(state.star&&!starSet.has(id))return false;
  if(state.unread&&readSet.has(id))return false;
  if(state.q){
    var t=((el.textContent||'')+' '+(el.getAttribute('data-en')||'')).toLowerCase();
    if(t.indexOf(state.q)===-1)return false;
  }
  return true;
}
function applyFilters(){
  /* 有搜索词时进入全量搜索模式（B2/B17）：对 data/days/ 30 天分块检索并排序，
     隐藏正常的精选/热点/时间线，显示搜索结果区。 */
  if(state.q){enterSearchMode();return;}
  exitSearchMode();
  var hot=document.getElementById('hot');
  if(hot)hot.style.display=(state.cat==='all')?'':'none';
  var shown=0;
  document.querySelectorAll('#featured .feed-item').forEach(function(el){
    var ok=itemVisible(el);el.style.display=ok?'':'none';if(ok)shown++;
  });
  document.querySelectorAll('#timeline .slot').forEach(function(li){
    var card=li.querySelector('.feed-item');
    var ok=card?itemVisible(card):true;
    li.style.display=ok?'':'none';if(ok)shown++;
  });
  document.querySelectorAll('#timeline .day-sec').forEach(function(sec){
    var vis=sec.querySelectorAll('.slot:not([style*="none"])').length;
    sec.style.display=vis?'':'none';
  });
  var nr=document.getElementById('noResult');
  if(nr){
    nr.hidden=!!shown;nr.style.display='';
    var t=document.getElementById('noResultTitle'),x=document.getElementById('noResultText');
    if(state.cat==='starred'||state.star){
      if(t)t.textContent='还没有收藏';
      if(x)x.textContent='去点卡片右上角的书签，喜欢的动态就会出现在这里。';
    }else if(state.unread){
      if(t)t.textContent='这批都读过了';
      if(x)x.textContent='关掉「只看未读」可以看到全部动态。';
    }else if(state.q){
      if(t)t.textContent='没有匹配「'+state.q+'」的动态。';
      if(x)x.textContent='换个关键词试试，或者清除搜索看看全部。';
    }else{
      if(t)t.textContent='这个分类下暂无动态。';
      if(x)x.textContent='换个分类看看，或者回到全部动态。';
    }
  }
  var sc=document.getElementById('starCount');
  if(sc)sc.textContent=starSet.size?('（'+starSet.size+'）'):'';
  if(typeof updateStarCounts==='function')updateStarCounts();
}
var filterTimer=null;
function scheduleFilter(){
  if(filterTimer)clearTimeout(filterTimer);
  filterTimer=setTimeout(applyFilters,150);
}
function setCat(f){
  state.cat=f;state.star=(f==='starred');
  document.querySelectorAll('.tabs .chip').forEach(function(x){
    x.classList.toggle('on',x.getAttribute('data-filter')===f);
  });
  document.querySelectorAll('[data-filter="starred"]').forEach(function(x){
    x.classList.toggle('on',f==='starred');
  });
  moveThumb();applyFilters();
}
/* 分类 chips：用事件委托，动态加载的卡片里的分类 chip 也能点（B2） */
document.addEventListener('click',function(e){
  var b=e.target.closest('[data-filter]');
  if(!b)return;
  if(b.closest('#searchOverlay'))return; /* 浮层里的 chips 有自己的处理 */
  setCat(b.getAttribute('data-filter'));
});
/* 分段控件的白色滑块：量一下当前选中项的位置，滑动过去 */
var tabsEl=document.querySelector('.tabs');
var thumb=document.getElementById('tabsThumb');
function moveThumb(){
  if(!tabsEl||!thumb)return;
  var on=tabsEl.querySelector('.chip.on');
  if(!on){thumb.style.width='0px';return;}
  thumb.style.left=(on.offsetLeft)+'px';
  thumb.style.width=(on.offsetWidth)+'px';
}
window.addEventListener('resize',moveThumb);
window.addEventListener('load',moveThumb);
moveThumb();
/* 搜索：标题+摘要+来源即时过滤；“/” 聚焦；× 清空 */
var searchInput=document.getElementById('siteSearch');
if(searchInput){
  var box=searchInput.closest('.search');
  searchInput.addEventListener('input',function(){
    state.q=searchInput.value.trim().toLowerCase();
    if(box)box.classList.toggle('has-value',!!searchInput.value);
    scheduleFilter();
  });
  var clr=document.getElementById('searchClear');
  if(clr)clr.addEventListener('click',function(){searchInput.value='';state.q='';if(box)box.classList.remove('has-value');searchInput.focus();applyFilters();});
  document.addEventListener('keydown',function(e){
    if(e.key==='/'&&!(e.target instanceof HTMLInputElement||e.target instanceof HTMLTextAreaElement)){
      e.preventDefault();searchInput.focus();
    }
  });
}
/* 只看未读（桌面在首个日期行右侧，手机在单独一行） */
document.querySelectorAll('.unread-toggle').forEach(function(b){
  b.addEventListener('click',function(){
    state.unread=!state.unread;
    document.querySelectorAll('.unread-toggle').forEach(function(x){x.classList.toggle('on',state.unread);});
    applyFilters();
  });
});
/* 日期折叠：事件委托，动态加载的日期区也能折（B2） */
document.addEventListener('click',function(e){
  var b=e.target.closest('.dh-toggle');
  if(!b)return;
  var sec=b.closest('.day-sec');
  if(sec)sec.classList.toggle('collapsed');
});
/* 回到顶部 */
var toTop=document.getElementById('toTop');
if(toTop){
  toTop.addEventListener('click',function(){window.scrollTo({top:0,behavior:'smooth'});});
  window.addEventListener('scroll',function(){
    toTop.classList.toggle('show',window.scrollY>window.innerHeight*1.2);
  },{passive:true});
}
/* #starred 直达收藏视图（加载时与 hash 变化时都生效） */
if(location.hash==='#starred'){setCat('starred');}
window.addEventListener('hashchange',function(){
  if(location.hash==='#starred'){setCat('starred');}
});
/* 顶栏滚动阴影（A4）：滚出一点就加阴影 */
var topbar=document.querySelector('.topbar');
function syncTopbar(){if(topbar)topbar.classList.toggle('scrolled',window.scrollY>8);}
window.addEventListener('scroll',syncTopbar,{passive:true});syncTopbar();
/* 底栏点当前 tab：回顶；已在顶部则刷新（A5） */
document.querySelectorAll('.tabbar a').forEach(function(a){
  if(!a.classList.contains('on'))return;
  a.addEventListener('click',function(e){
    e.preventDefault();
    if(window.scrollY<10){location.reload();}
    else{window.scrollTo({top:0,behavior:'smooth'});}
  });
});
/* 收藏数量：侧栏/我的页/底栏都显示（B3/B4） */
function updateStarCounts(){
  document.querySelectorAll('[data-star-count]').forEach(function(el){el.textContent=starSet.size?('（'+starSet.size+'）'):(el.getAttribute('data-star-count-empty')||'');});
}
updateStarCounts();
/* 空状态操作按钮（B19）：清除筛选 / 去看精选（事件委托，搜索结果里的空状态也生效） */
document.addEventListener('click',function(e){
  var b=e.target.closest('[data-empty-action]');
  if(!b)return;
  var act=b.getAttribute('data-empty-action');
  state.q='';state.unread=false;
  var si=document.getElementById('siteSearch');
  if(si){si.value='';var bx=si.closest('.search');if(bx)bx.classList.remove('has-value');}
  var oi=document.getElementById('overlaySearch');
  if(oi)oi.value='';
  document.querySelectorAll('.unread-toggle').forEach(function(x){x.classList.remove('on');});
  setCat('all');
  if(act==='featured'){
    var f=document.getElementById('featured');
    if(f){f.scrollIntoView();}
    else{var br=document.querySelector('.topbar .brand')||document.querySelector('.sidebar .brand');if(br)location.href=br.getAttribute('href');}
  }
});
/* 手机搜索浮层（B14）：全屏层 + 最近搜索 + 分类 chips + 热议 */
var overlay=document.getElementById('searchOverlay');
var overlayInput=document.getElementById('overlaySearch');
function isMobile(){return window.matchMedia&&window.matchMedia('(max-width: 699px)').matches;}
function openOverlay(){
  if(!overlay)return;
  if(!isMobile()){var si=document.getElementById('siteSearch');if(si)si.focus();return;}
  overlay.hidden=false;document.body.style.overflow='hidden';
  renderRecent();
  if(overlayInput)setTimeout(function(){overlayInput.focus();},50);
}
function closeOverlay(){
  if(!overlay)return;
  overlay.hidden=true;document.body.style.overflow='';
}
document.querySelectorAll('.search-trigger').forEach(function(b){b.addEventListener('click',openOverlay);});
var ovClose=document.getElementById('overlayClose');
if(ovClose)ovClose.addEventListener('click',closeOverlay);
document.addEventListener('keydown',function(e){if(e.key==='Escape'&&overlay&&!overlay.hidden)closeOverlay();});
if(overlayInput){
  overlayInput.addEventListener('input',function(){
    state.q=overlayInput.value.trim().toLowerCase();
    var si=document.getElementById('siteSearch');if(si)si.value=overlayInput.value;
    scheduleFilter();
  });
  overlayInput.addEventListener('keydown',function(e){
    if(e.key==='Enter'){
      var q=overlayInput.value.trim();
      if(q)saveRecent(q);
      closeOverlay();
      var tl=document.getElementById('timeline');if(tl)tl.scrollIntoView();
    }
  });
}
function loadRecent(){try{return JSON.parse(localStorage.getItem(LS_RECENT)||'[]')||[];}catch(e){return [];}}
function saveRecent(q){
  var list=loadRecent().filter(function(x){return x!==q;});
  list.unshift(q);list=list.slice(0,8);
  try{localStorage.setItem(LS_RECENT,JSON.stringify(list));}catch(e){}
}
function renderRecent(){
  var box=document.getElementById('recentList');if(!box)return;
  var list=loadRecent();
  box.innerHTML=list.length?list.map(function(q){
    return '<div class="recent-row"><button type="button" class="chip" data-recent="'+q.replace(/"/g,'&quot;')+'">'+q.replace(/</g,'&lt;')+'</button></div>';
  }).join(''):'<p class="more-note">还没有搜索过。</p>';
  box.querySelectorAll('[data-recent]').forEach(function(b){
    b.addEventListener('click',function(){
      var q=b.getAttribute('data-recent');
      if(overlayInput)overlayInput.value=q;
      state.q=q.toLowerCase();
      var si=document.getElementById('siteSearch');if(si)si.value=q;
      applyFilters();closeOverlay();
      var tl=document.getElementById('timeline');if(tl)tl.scrollIntoView();
    });
  });
}
var clrRecent=document.getElementById('clearRecent');
if(clrRecent)clrRecent.addEventListener('click',function(){
  try{localStorage.removeItem(LS_RECENT);}catch(e){}renderRecent();
});
document.querySelectorAll('#searchOverlay [data-filter]').forEach(function(b){
  b.addEventListener('click',function(){setCat(b.getAttribute('data-filter'));closeOverlay();});
});
/* 我的页：收藏数量 + 更新日志红点（B4/B6） */
(function(){
  var dot=document.getElementById('changelogDot');
  if(dot){
    var latest=dot.getAttribute('data-changelog-version')||'';
    var read='';
    try{read=localStorage.getItem(LS_CL_READ)||'';}catch(e){}
    dot.hidden=!!(read&&read===latest);
  }
  var mc=document.getElementById('moreStarCount');
  if(mc)mc.textContent=starSet.size?String(starSet.size):'0';
})();
/* 更新日志页：打开即记为已读（B6） */
(function(){
  var pg=document.getElementById('changelogPage');
  if(pg){
    var v=pg.getAttribute('data-changelog-version')||'';
    if(v){try{localStorage.setItem(LS_CL_READ,v);}catch(e){}}
  }
})();
/* ============ 客户端数据层：按天分块（data/days/） ============ */
/* 首页首屏由服务端渲染；浏览器只在需要时才按天取分块：分页一次取一天，
   搜索与收藏页在用户操作时才并行取全部天（仍按天分块，不再拉 30 天单文件）。 */
var dayIndexPromise=null;
var dayCache={};
function getDayIndex(){
  if(dayIndexPromise)return dayIndexPromise;
  dayIndexPromise=fetch('data/days/index.json').then(function(r){
    if(!r.ok)throw new Error('HTTP '+r.status);return r.json();
  }).then(function(d){
    return (d.days||[]).map(function(x){return x.date;});
  }).catch(function(e){dayIndexPromise=null;throw e;});
  return dayIndexPromise;
}
function getDay(date){
  if(dayCache[date])return dayCache[date];
  dayCache[date]=fetch('data/days/'+date+'.json').then(function(r){
    if(!r.ok)throw new Error('HTTP '+r.status);return r.json();
  }).then(function(d){
    return (d.items||[]).sort(function(a,b){return new Date(b.published)-new Date(a.published);});
  }).catch(function(e){delete dayCache[date];throw e;});
  return dayCache[date];
}
/* 全量：只在搜索 / 收藏页按需调用（并行取各天分块并缓存），首页加载时不调用 */
function getStore(){
  return getDayIndex().then(function(days){
    return Promise.all(days.map(getDay));
  }).then(function(lists){
    var all=[];
    lists.forEach(function(l){all=all.concat(l);});
    return all.sort(function(a,b){return new Date(b.published)-new Date(a.published);});
  });
}
/* 收藏页：从本地快照渲染，查 data/days/ 分块判断是否下架（B3） */
(function(){
  var list=document.getElementById('starList');
  if(!list)return;
  var empty=document.getElementById('starEmpty');
  var ids=Array.from(starSet);
  if(!ids.length){if(empty)empty.hidden=false;return;}
  getStore().then(function(items){
    var live={};
    items.forEach(function(it){live[it.id]=it;});
    var html=ids.map(function(id){
      var m=starMeta[id]||{};
      var it=live[id];
      var gone=!it;
      var title=m.title||(it?(it.zh_title||it.title):'（标题未知）');
      var link=m.link||(it?it.link:'#');
      var source=m.source||(it?it.source:'');
      var at=m.at?new Date(m.at):null;
      var atStr=at?('收藏于 '+at.getFullYear()+'年'+(at.getMonth()+1)+'月'+at.getDate()+'日'):'';
      return '<article class="feed-item starred-item'+(gone?' is-gone':'')+'">'
        +'<header class="fi-head"><span class="src">'+source.replace(/</g,'&lt;')+'</span>'
        +(gone?'<span class="gone-tag">已下架</span>':'')
        +'<span class="sp"><button type="button" class="star-btn on" data-unstar="'+id+'" aria-label="取消收藏" title="取消收藏">'
        +'<svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M19 21l-7-5-7 5V5a2 2 0 0 1 2-2h10a2 2 0 0 1 2 2z"/></svg>'
        +'</button></span></header>'
        +'<h3><a href="items/'+id+'.html">'+title.replace(/</g,'&lt;')+'</a></h3>'
        +(gone?'<p class="sum">这条动态已不在本站 30 天数据里（可能已下架或超出保存期），只保留了你收藏时的标题与链接。</p>':'')
        +(atStr?'<p class="starred-at">'+atStr+'</p>':'')
        +'</article>';
    }).join('');
    list.innerHTML=html;
    list.querySelectorAll('[data-unstar]').forEach(function(b){
      b.addEventListener('click',function(){
        var id=b.getAttribute('data-unstar');
        starSet.delete(id);delete starMeta[id];
        saveSet(LS_STAR,starSet);saveObj(LS_STAR_META,starMeta);
        updateStarCounts();
        b.closest('.starred-item').remove();
        if(!list.querySelector('.starred-item')&&empty)empty.hidden=false;
      });
    });
  }).catch(function(){
    if(empty)empty.hidden=false;
  });
})();
/* ============ B2 分页 + B17 全量搜索 + B18 滚动恢复 ============ */
function escHtml(s){return String(s==null?'':s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');}
var SEARCH_ICON_SVG='<svg width="40" height="40" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="11" cy="11" r="8"/><line x1="21" y1="21" x2="16.65" y2="16.65"/></svg>';
var BOOKMARK_SVG='<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M19 21l-7-5-7 5V5a2 2 0 0 1 2-2h10a2 2 0 0 1 2 2z"/></svg>';
var CHEV_SVG='<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><polyline points="6 9 12 15 18 9"/></svg>';
var IH_CFG=null;
try{var cfgEl=document.getElementById('ihConfig');if(cfgEl)IH_CFG=JSON.parse(cfgEl.textContent);}catch(e){IH_CFG=null;}
/* getStore() 见上方的客户端数据层（按天分块取 data/days/）。 */
/* 北京时间的年月日时分（用 UTC+8 换算，不依赖浏览器时区） */
function cstParts(date){
  var c=new Date(date.getTime()+8*3600000);
  var p=function(n){return String(n).padStart(2,'0');};
  return {y:c.getUTCFullYear(),m:c.getUTCMonth()+1,d:c.getUTCDate(),
    hh:c.getUTCHours(),mm:c.getUTCMinutes(),wd:c.getUTCDay(),
    iso:c.getUTCFullYear()+'-'+p(c.getUTCMonth()+1)+'-'+p(c.getUTCDate()),
    hm:p(c.getUTCHours())+':'+p(c.getUTCMinutes())};
}
function todayCST(){return cstParts(new Date()).iso;}
function fmtCST(iso){
  var p=cstParts(new Date(iso));
  return p.m+'月'+p.d+'日 '+p.hm;
}
/* 与 Python score()/reason_for() 同规则的客户端版（动态卡片用） */
function computeMeta(it){
  var tier=it.tier||(IH_CFG?IH_CFG.tiers[it.source_id]:null)||'T2';
  var labels=it.tags||[];
  var score=0,reason='';
  if(IH_CFG){
    var pub=new Date(it.published);
    var ageH=(Date.now()-pub.getTime())/3600000;
    score=IH_CFG.base;
    for(var i=0;i<IH_CFG.recency.length;i++){
      var r=IH_CFG.recency[i];
      if(ageH<=r.max_hours){score+=r.bonus;break;}
    }
    score+=((IH_CFG.tierBonus||{})[tier]||0);
    var text=((it.title||'')+' '+(it.zh_oneliner||'')).toLowerCase();
    var devHits=0;
    Object.keys(IH_CFG.devLabels||{}).forEach(function(kw){
      if(text.indexOf(kw.toLowerCase())>-1)devHits++;
    });
    score+=Math.min(devHits*IH_CFG.devBonus,IH_CFG.devCap);
    var noiseHits=0;
    (IH_CFG.noiseKw||[]).forEach(function(kw){
      if(text.indexOf(kw.toLowerCase())>-1)noiseHits++;
    });
    score+=Math.max(noiseHits*IH_CFG.noisePenalty,IH_CFG.noiseFloor);
    score=Math.max(0,Math.min(100,score));
    if(!labels.length){
      var seen={};
      Object.keys(IH_CFG.devLabels||{}).forEach(function(kw){
        if(text.indexOf(kw.toLowerCase())>-1){
          var lab=IH_CFG.devLabels[kw];
          if(!seen[lab]){seen[lab]=1;labels.push(lab);}
        }
      });
      labels=labels.slice(0,3);
    }
    var parts=[];
    if(tier==='T1')parts.push('官方来源');
    if(labels.length)parts.push('涉及'+labels.slice(0,2).join('与'));
    if(ageH<=6)parts.push('6 小时内发布');else if(ageH<=24)parts.push('24 小时内发布');
    if(parts.length<2)parts.push('与本主题相关');
    reason=parts.join(' · ');
  }else{
    score=it.score||0;reason=it.reason||'';
  }
  return {score:score,reason:reason,labels:labels,tier:tier};
}
function cardHTML(it){
  var m=computeMeta(it);
  var title=it.zh_title||it.title;
  var summary=it.zh_oneliner||'';
  var en=it.en_title||it.title;
  var pub=cstParts(new Date(it.published));
  var off=m.tier==='T1'?'<span class="off-tag">官方</span>':'';
  var isNew=false;
  if(it.fetched_at){
    isNew=cstParts(new Date(it.fetched_at)).iso===todayCST()
      &&(Date.now()-new Date(it.published).getTime())<=86400000;
  }
  var newHtml=isNew?'<span class="new-pill">新</span>':'';
  var tagsHtml=m.labels.length?'<div class="fi-tags">'+m.labels.map(function(t){
    return '<a class="tag" href="topics/'+((IH_CFG&&IH_CFG.tagSlugs[t])||t)+'.html">#'+escHtml(t)+'</a>';
  }).join('')+'</div>':'';
  var scoreCls=m.score>=85?'t-hot':(m.score>=70?'t-acc':'t-quiet');
  return '<article class="feed-item" data-id="'+escHtml(it.id)+'" data-category="'+escHtml(it.category||'')+'"'
    +' data-official="'+(m.tier==='T1'?'1':'0')+'" data-en="'+escHtml(en)+'">'
    +'<header class="fi-head"><span class="src">'+escHtml(it.source)+'</span>'+off
    +'<time class="pt">· '+pub.hm+'</time>'+newHtml
    +'<span class="sp"><span class="score-pill '+scoreCls+'" title="评分 '+m.score+'/100">'
    +'<span class="lbl">评分</span><span class="sep"></span><span class="num">'+m.score+'</span></span>'
    +'<button type="button" class="star-btn" aria-label="收藏" title="收藏">'+BOOKMARK_SVG+'</button></span></header>'
    +'<h3><a href="items/'+escHtml(it.id)+'.html">'+escHtml(title)+'</a></h3>'
    +(summary?'<p class="sum">'+escHtml(summary)+'</p>':'')
    +'<div class="fi-foot"><button type="button" class="chip cat" data-filter="'+escHtml(it.category||'')+'">'
    +escHtml(it.category_label||it.category||'')+'</button>'
    +'<span class="when">'+escHtml(fmtCST(it.published))+'</span></div>'
    +tagsHtml
    +'<p class="fi-reason">推荐理由：'+escHtml(m.reason)+'</p>'
    +'</article>';
}
function slotHTML(it){
  var pub=cstParts(new Date(it.published));
  return '<li class="slot" data-category="'+escHtml(it.category||'')+'">'
    +'<time class="slot-time" datetime="'+escHtml(it.published)+'">'+pub.hm+'</time>'
    +'<span class="rail" aria-hidden="true"></span>'
    +cardHTML(it)+'</li>';
}
function normTitle(t){
  return (t||'').toLowerCase().replace(/[\\s\\-_·•|/\\:;,.!?？！。、，；：（）()\\[\\]{}“”"'‘’<>《》]+/g,'');
}
function groupSimilarJS(items){
  var groups=[];
  items.forEach(function(it){
    var norm=normTitle(it.zh_title||it.title);
    var date=cstParts(new Date(it.published)).iso;
    var merged=false;
    if(norm.length>=10){
      for(var i=0;i<groups.length;i++){
        var g=groups[i],m=g.main;
        if(m.source_id!==it.source_id||cstParts(new Date(m.published)).iso!==date)continue;
        var mn=normTitle(m.zh_title||m.title);
        if(mn.length<10)continue;
        if(norm===mn||((norm.indexOf(mn)===0||mn.indexOf(norm)===0)
            &&Math.min(norm.length,mn.length)/Math.max(norm.length,mn.length)>=0.8)){
          g.extra.push(it);merged=true;break;
        }
      }
    }
    if(!merged)groups.push({main:it,extra:[]});
  });
  return groups;
}
function groupSlotHTML(g){
  var slot=slotHTML(g.main);
  if(!g.extra.length)return slot;
  var rows=g.extra.map(function(e){
    var p=cstParts(new Date(e.published));
    return '<li><a href="items/'+escHtml(e.id)+'.html">'+escHtml(e.zh_title||e.title)+'</a>'
      +'<span class="ge-time">'+p.hm+'</span></li>';
  }).join('');
  var toggle='<button type="button" class="group-toggle" aria-expanded="false">另有 '+g.extra.length+' 篇报道 <span aria-hidden="true">▾</span></button>';
  var extra='<div class="group-extra" hidden><ul class="group-extra-list">'+rows+'</ul></div>';
  return slot.slice(0,-5)+toggle+extra+'</li>';
}
function dayHeaderHTML(dateISO,count){
  var parts=dateISO.split('-');
  var wd=new Date(+parts[0],+parts[1]-1,+parts[2]).getDay();
  var isToday=dateISO===todayCST();
  var name=isToday?'今天':(+parts[1]+'月'+(+parts[2])+'日');
  var wdShort=['周日','周一','周二','周三','周四','周五','周六'][wd];
  var wdFull=['星期日','星期一','星期二','星期三','星期四','星期五','星期六'][wd];
  return '<header class="day-head'+(isToday?' is-today':'')+'">'
    +'<span class="dh-name">'+name+'</span>'
    +'<span class="dh-date">'+(+parts[1])+'月'+(+parts[2])+'日</span>'
    +'<button type="button" class="dh-toggle" aria-label="收起/展开这一天">'+CHEV_SVG+'</button>'
    +'<span class="dh-wd dh-wd-short">'+wdShort+'</span>'
    +'<span class="dh-wd dh-wd-full">'+wdFull+'</span>'
    +'<span class="dh-count"><b class="num">'+count+'</b> 条</span></header>';
}
function renderBatch(items){
  var groups=groupSimilarJS(items);
  var days={},order=[];
  groups.forEach(function(g){
    var d=cstParts(new Date(g.main.published)).iso;
    if(!days[d]){days[d]=[];order.push(d);}
    days[d].push(g);
  });
  var tl=document.getElementById('timeline');
  if(!tl)return;
  order.forEach(function(d){
    var html=days[d].map(groupSlotHTML).join('');
    var count=days[d].reduce(function(n,g){return n+1+g.extra.length;},0);
    var sec=tl.querySelector('.day-sec[data-date="'+d+'"]');
    if(sec){
      var ol=sec.querySelector('.day-list');
      if(ol)ol.insertAdjacentHTML('beforeend',html);
      var cnt=sec.querySelector('.dh-count .num');
      if(cnt)cnt.textContent=parseInt(cnt.textContent||'0',10)+count;
    }else{
      tl.insertAdjacentHTML('beforeend',
        '<section class="day-sec" data-date="'+d+'">'+dayHeaderHTML(d,count)
        +'<ol class="day-list">'+html+'</ol></section>');
    }
  });
  tl.querySelectorAll('.feed-item').forEach(bindFeedItem);
  applyFilters();
}
/* 分页状态机：加载态 / 失败重试 / 到底 */
var lmState={loading:false,done:false};
function setLoadMoreState(s){
  var btn=document.getElementById('loadMoreBtn'),st=document.getElementById('loadMoreState'),
      wrap=document.getElementById('loadMoreWrap'),end=document.getElementById('feedEnd');
  if(!btn)return;
  if(s==='loading'){btn.disabled=true;btn.innerHTML='<span class="spin"></span>正在加载';if(st)st.textContent='';}
  else if(s==='error'){btn.disabled=false;btn.textContent='加载失败，点击重试';if(st)st.textContent='网络或数据有问题，点按钮再试一次。';}
  else if(s==='done'){if(wrap)wrap.hidden=true;if(end)end.hidden=false;}
  else{btn.disabled=false;btn.textContent='加载更多';if(st)st.textContent='';}
}
/* 分页：按天取分块，一天不够再取下一天，直到凑满 30 条未见过的卡片 */
var lmDayIdx=0,lmBuffer=[];
function loadMore(){
  if(lmState.loading||lmState.done||state.q)return Promise.resolve(false);
  var tl=document.getElementById('timeline');
  if(!tl)return Promise.resolve(false);
  lmState.loading=true;setLoadMoreState('loading');
  var seen={};
  tl.querySelectorAll('.feed-item').forEach(function(el){seen[el.getAttribute('data-id')]=1;});
  tl.querySelectorAll('.group-extra-list a').forEach(function(a){
    var m=/items\\/([0-9a-f]+)\\.html/.exec(a.getAttribute('href')||'');
    if(m)seen[m[1]]=1;
  });
  return getDayIndex().then(function(days){
    var next=[];
    function fill(){
      while(next.length<30&&lmBuffer.length){
        var it=lmBuffer.shift();
        if(!seen[it.id])next.push(it);
      }
      if(next.length>=30||lmDayIdx>=days.length)return Promise.resolve(next);
      var d=days[lmDayIdx++];
      return getDay(d).then(function(items){lmBuffer=items.slice();return fill();});
    }
    return fill();
  }).then(function(next){
    if(!next.length){lmState.done=true;lmState.loading=false;setLoadMoreState('done');saveScrollState();return false;}
    renderBatch(next);
    lmState.loading=false;
    if(next.length<30){lmState.done=true;setLoadMoreState('done');}
    else setLoadMoreState('idle');
    saveScrollState();
    return true;
  }).catch(function(){
    lmState.loading=false;setLoadMoreState('error');
    return false;
  });
}
var loadBtn=document.getElementById('loadMoreBtn');
if(loadBtn)loadBtn.addEventListener('click',function(){loadMore();});
var sentinel=document.getElementById('loadMoreSentinel');
if(sentinel&&'IntersectionObserver' in window){
  var io=new IntersectionObserver(function(entries){
    entries.forEach(function(en){if(en.isIntersecting)loadMore();});
  },{rootMargin:'900px 0px'});
  io.observe(sentinel);
}
/* 全量搜索模式（B2/B17）：标题 > 摘要 > 来源，同级按时间倒序 */
var searchMode=false;
function enterSearchMode(){
  var sr=document.getElementById('searchResults');
  if(!sr)return;
  searchMode=true;
  ['featured','hot','timeline','loadMoreWrap','loadMoreSentinel','feedEnd','noResult'].forEach(function(id){
    var el=document.getElementById(id);if(el)el.hidden=true;
  });
  sr.hidden=false;
  renderSearchResults();
}
function exitSearchMode(){
  if(!searchMode)return;
  searchMode=false;
  ['featured','hot','timeline','loadMoreSentinel'].forEach(function(id){
    var el=document.getElementById(id);if(el)el.hidden=false;
  });
  var wrap=document.getElementById('loadMoreWrap');if(wrap)wrap.hidden=lmState.done;
  var end=document.getElementById('feedEnd');if(end)end.hidden=!lmState.done;
  var sr=document.getElementById('searchResults');if(sr)sr.hidden=true;
}
function matchFiltersData(it){
  if(state.cat==='official'&&(it.tier||(IH_CFG?IH_CFG.tiers[it.source_id]:'T2'))!=='T1')return false;
  if(state.cat==='starred'&&!starSet.has(it.id))return false;
  if(state.cat!=='all'&&state.cat!=='starred'&&state.cat!=='official'&&it.category!==state.cat)return false;
  if(state.unread&&readSet.has(it.id))return false;
  return true;
}
function renderSearchResults(){
  var srList=document.getElementById('srList'),srCount=document.getElementById('srCount');
  if(!srList)return;
  var q=state.q;
  srList.innerHTML='<p class="more-note">正在搜索…</p>';
  getStore().then(function(items){
    if(state.q!==q)return;
    var scored=[];
    items.forEach(function(it){
      if(!matchFiltersData(it))return;
      var title=((it.zh_title||it.title||'')+'').toLowerCase();
      var sum=((it.zh_oneliner||'')+'').toLowerCase();
      var src=(it.source||'').toLowerCase();
      var tier=0;
      if(title.indexOf(q)>-1)tier=3;
      else if(sum.indexOf(q)>-1)tier=2;
      else if(src.indexOf(q)>-1)tier=1;
      if(tier)scored.push({it:it,tier:tier});
    });
    scored.sort(function(a,b){
      return b.tier-a.tier||(new Date(b.it.published)-new Date(a.it.published));
    });
    if(srCount)srCount.textContent='找到 '+scored.length+' 条';
    if(!scored.length){
      srList.innerHTML='<div class="empty-state"><div class="empty-icon">'+SEARCH_ICON_SVG+'</div>'
        +'<h3 class="empty-title">没有匹配「'+escHtml(state.q)+'」的动态。</h3>'
        +'<p class="empty-text">换个关键词试试，或者清除搜索看看全部。</p>'
        +'<div class="empty-actions"><button type="button" class="empty-btn" data-empty-action="clear">清除筛选</button>'
        +'<button type="button" class="empty-btn primary" data-empty-action="featured">去看精选</button></div></div>';
      return;
    }
    var show=scored.slice(0,50);
    srList.innerHTML=show.map(function(s){return cardHTML(s.it);}).join('')
      +(scored.length>50?'<p class="more-note">只显示前 50 条，共 '+scored.length+' 条。</p>':'');
    srList.querySelectorAll('.feed-item').forEach(bindFeedItem);
  }).catch(function(){
    srList.innerHTML='<div class="empty-state"><h3 class="empty-title">搜索暂时不可用</h3>'
      +'<p class="empty-text">数据没加载出来，刷新页面再试。</p></div>';
  });
}
/* 滚动恢复（B18）：从详情页/热点页返回首页时恢复滚动位置与已加载批次数 */
var SCROLL_KEY='__SLUG__-scroll';
function saveScrollState(){
  var tl=document.getElementById('timeline');
  if(!tl)return;
  try{sessionStorage.setItem(SCROLL_KEY,JSON.stringify({
    y:window.scrollY,n:tl.querySelectorAll('.feed-item').length,t:Date.now()}));}catch(e){}
}
window.addEventListener('pagehide',saveScrollState);
var scrollSaveTimer=null;
window.addEventListener('scroll',function(){
  if(scrollSaveTimer)return;
  scrollSaveTimer=setTimeout(function(){scrollSaveTimer=null;saveScrollState();},500);
},{passive:true});
function maybeRestoreScroll(){
  var tl=document.getElementById('timeline');
  if(!tl)return;
  var nav=performance.getEntriesByType&&performance.getEntriesByType('navigation')[0];
  var isBack=nav&&nav.type==='back_forward';
  var sameRef=document.referrer&&document.referrer.indexOf(location.host)>-1;
  if(!isBack&&!sameRef)return;
  var raw=null;try{raw=sessionStorage.getItem(SCROLL_KEY);}catch(e){}
  if(!raw)return;
  var st=null;try{st=JSON.parse(raw);}catch(e){}
  if(!st||!st.n||st.n<=100||Date.now()-st.t>1800000)return;
  var target=st.n;
  (function again(ok){
    var cur=tl.querySelectorAll('.feed-item').length;
    if(ok&&cur<target){loadMore().then(again);return;}
    window.scrollTo(0,st.y);
  })(true);
}
maybeRestoreScroll();
/* 同事件归组展开（B13）：事件委托，动态加载的也生效 */
document.addEventListener('click',function(e){
  var t=e.target.closest('.group-toggle');
  if(!t)return;
  var li=t.closest('.slot');
  var extra=li?li.querySelector('.group-extra'):null;
  if(!extra)return;
  var open=extra.hidden;
  extra.hidden=!open;
  t.setAttribute('aria-expanded',open?'true':'false');
  var n=extra.querySelectorAll('li').length;
  t.innerHTML=open?'收起 <span aria-hidden="true">▴</span>':'另有 '+n+' 篇报道 <span aria-hidden="true">▾</span>';
});
/* 浮层搜索框的清空按钮（B14） */
var ovClear=document.getElementById('overlaySearchClear');
if(ovClear)ovClear.addEventListener('click',function(){
  if(overlayInput){overlayInput.value='';overlayInput.dispatchEvent(new Event('input'));overlayInput.focus();}
});
/* 详情页（B20）：打开即记已读；收藏；返回；复制链接；分享 */
(function(){
  var pg=document.querySelector('[data-item-id]');
  if(!pg)return;
  var id=pg.getAttribute('data-item-id');
  if(id&&!readSet.has(id)){readSet.add(id);saveSet(LS_READ,readSet);}
  var star=document.getElementById('itemStarBtn');
  if(star&&id){
    var syncStar=function(){
      var on=starSet.has(id);
      star.classList.toggle('on',on);
      var sp=star.querySelector('span');if(sp)sp.textContent=on?'已收藏':'收藏';
      star.setAttribute('aria-label',on?'取消收藏':'收藏');star.title=on?'取消收藏':'收藏';
    };
    syncStar();
    star.addEventListener('click',function(){
      if(starSet.has(id)){starSet.delete(id);delete starMeta[id];}
      else{
        starSet.add(id);
        starMeta[id]={title:star.getAttribute('data-title')||'',
          link:star.getAttribute('data-link')||'',
          source:star.getAttribute('data-source')||'',at:new Date().toISOString()};
      }
      saveSet(LS_STAR,starSet);saveObj(LS_STAR_META,starMeta);
      syncStar();updateStarCounts();
    });
  }
  var back=document.getElementById('backBtn');
  if(back)back.addEventListener('click',function(){
    if(document.referrer&&document.referrer.indexOf(location.host)>-1){history.back();}
    else{location.href=back.getAttribute('data-home')||'../index.html';}
  });
  var copy=document.getElementById('copyLinkBtn');
  function fallbackCopy(text){
    var ta=document.createElement('textarea');ta.value=text;
    ta.style.position='fixed';ta.style.opacity='0';
    document.body.appendChild(ta);ta.select();
    try{document.execCommand('copy');}catch(e){}
    document.body.removeChild(ta);
  }
  if(copy)copy.addEventListener('click',function(){
    var url=location.href;
    var done=function(){copy.textContent='已复制';setTimeout(function(){copy.textContent='复制链接';},1500);};
    if(navigator.clipboard&&navigator.clipboard.writeText){
      navigator.clipboard.writeText(url).then(done).catch(function(){fallbackCopy(url);done();});
    }else{fallbackCopy(url);done();}
  });
  var share=document.getElementById('shareBtn');
  if(share&&navigator.share){
    share.hidden=false;
    share.addEventListener('click',function(){
      navigator.share({title:document.title,url:location.href}).catch(function(){});
    });
  }
})();
})();
</script>
"""

# 外置 JS 文件内容：去掉 SCRIPT 首尾的 <script> 标签
# （行内主题启动脚本 THEME_BOOT 不受影响，继续内联在 <head> 里）
_SCRIPT_JS = SCRIPT.strip()
assert _SCRIPT_JS.startswith("<script>") and _SCRIPT_JS.endswith("</script>")
SCRIPT_JS = _SCRIPT_JS[len("<script>"):-len("</script>")].strip() + "\n"

# 英文版 JS：对 SCRIPT 做字符串级翻译（字段名 zh_* -> en_* + 界面文案英译）。
# 中文版 SCRIPT_JS 一字不动；英文版只在 en/ 树里用。JS 注释里的中文不翻译（不可见）。
_JS_EN_REPLACEMENTS = [
    # 字段名（最先替换；只出现在代码里，不在注释里）
    ("zh_title", "en_title"),
    ("zh_oneliner", "en_oneliner"),
    ("('（'+starSet.size+'）')", "('('+starSet.size+')')"),
    ("b.setAttribute('aria-label','外观：'+(mode==='dark'?'深色':mode==='light'?'浅色':'跟随系统')+'（点击切换）');",
     "b.setAttribute('aria-label','Appearance: '+(mode==='dark'?'dark':mode==='light'?'light':'system')+' (click to switch)');"),
    ("star.setAttribute('aria-label','取消收藏');star.title='取消收藏';",
     "star.setAttribute('aria-label','Unsave');star.title='Unsave';"),
    ("star.classList.remove('on');star.setAttribute('aria-label','收藏');star.title='收藏';",
     "star.classList.remove('on');star.setAttribute('aria-label','Save');star.title='Save';"),
    ("if(t)t.textContent='还没有收藏';",
     "if(t)t.textContent='No saved items yet.';"),
    ("if(x)x.textContent='去点卡片右上角的书签，喜欢的动态就会出现在这里。';",
     "if(x)x.textContent='Tap the bookmark on a card and the items you like will show up here.';"),
    ("if(t)t.textContent='这批都读过了';",
     "if(t)t.textContent='All caught up';"),
    ("if(x)x.textContent='关掉「只看未读」可以看到全部动态。';",
     "if(x)x.textContent='Turn off \"Unread only\" to see everything.';"),
    ("if(t)t.textContent='没有匹配「'+state.q+'」的动态。';",
     "if(t)t.textContent='No items matching \"'+state.q+'\".';"),
    ("if(x)x.textContent='换个关键词试试，或者清除搜索看看全部。';",
     "if(x)x.textContent='Try another keyword, or clear the search to see everything.';"),
    ("if(t)t.textContent='这个分类下暂无动态。';",
     "if(t)t.textContent='No items in this category yet.';"),
    ("if(x)x.textContent='换个分类看看，或者回到全部动态。';",
     "if(x)x.textContent='Try another category, or go back to all items.';"),
    ("'<p class=\"more-note\">还没有搜索过。</p>'",
     "'<p class=\"more-note\">No searches yet.</p>'"),
    ("var title=m.title||(it?(it.en_title||it.title):'（标题未知）');",
     "var title=m.title||(it?(it.en_title||it.title):'(Unknown title)');"),
    ("var atStr=at?('收藏于 '+at.getFullYear()+'年'+(at.getMonth()+1)+'月'+at.getDate()+'日'):'';",
     "var atStr=at?('Saved on '+['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'][at.getMonth()]+' '+at.getDate()+', '+at.getFullYear()):'';"),
    ("'<span class=\"gone-tag\">已下架</span>'",
     "'<span class=\"gone-tag\">Removed</span>'"),
    ('aria-label="取消收藏" title="取消收藏"',
     'aria-label="Unsave" title="Unsave"'),
    ("'<p class=\"sum\">这条动态已不在本站 30 天数据里（可能已下架或超出保存期），只保留了你收藏时的标题与链接。</p>'",
     "'<p class=\"sum\">This item is no longer in the 30-day data on this site (it may have been removed or aged out). Only the title and link from when you saved it are kept.</p>'"),
    ("return p.m+'月'+p.d+'日 '+p.hm;",
     "return ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'][p.m-1]+' '+p.d+', '+p.hm;"),
    ("if(tier==='T1')parts.push('官方来源');",
     "if(tier==='T1')parts.push('Official source');"),
    ("if(labels.length)parts.push('涉及'+labels.slice(0,2).join('与'));",
     "if(labels.length)parts.push('Covers '+labels.slice(0,2).join(' and '));"),
    ("if(ageH<=6)parts.push('6 小时内发布');else if(ageH<=24)parts.push('24 小时内发布');",
     "if(ageH<=6)parts.push('Published within 6 hours');else if(ageH<=24)parts.push('Published within 24 hours');"),
    ("if(parts.length<2)parts.push('与本主题相关');",
     "if(parts.length<2)parts.push('Relevant to this topic');"),
    ("'<span class=\"off-tag\">官方</span>'",
     "'<span class=\"off-tag\">Official</span>'"),
    ("'<span class=\"new-pill\">新</span>'",
     "'<span class=\"new-pill\">New</span>'"),
    ("title=\"评分 '+m.score+'/100\"",
     "title=\"Score '+m.score+'/100\""),
    ("'<span class=\"lbl\">评分</span>",
     "'<span class=\"lbl\">Score</span>"),
    ('class="star-btn" aria-label="收藏" title="收藏"',
     'class="star-btn" aria-label="Save" title="Save"'),
    ("'<p class=\"fi-reason\">推荐理由：'",
     "'<p class=\"fi-reason\">Why this: '"),
    ("var toggle='<button type=\"button\" class=\"group-toggle\" aria-expanded=\"false\">另有 '+g.extra.length+' 篇报道 <span aria-hidden=\"true\">▾</span></button>';",
     "var toggle='<button type=\"button\" class=\"group-toggle\" aria-expanded=\"false\">'+g.extra.length+' more reports <span aria-hidden=\"true\">▾</span></button>';"),
    ("var name=isToday?'今天':(+parts[1]+'月'+(+parts[2])+'日');",
     "var name=isToday?'Today':(['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'][+parts[1]-1]+' '+(+parts[2]));"),
    ("var wdShort=['周日','周一','周二','周三','周四','周五','周六'][wd];",
     "var wdShort=['Sun','Mon','Tue','Wed','Thu','Fri','Sat'][wd];"),
    ("var wdFull=['星期日','星期一','星期二','星期三','星期四','星期五','星期六'][wd];",
     "var wdFull=['Sunday','Monday','Tuesday','Wednesday','Thursday','Friday','Saturday'][wd];"),
    ("+'<span class=\"dh-date\">'+(+parts[1])+'月'+(+parts[2])+'日</span>'",
     "+'<span class=\"dh-date\">'+(['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'][+parts[1]-1]+' '+(+parts[2]))+'</span>'"),
    ('aria-label="收起/展开这一天"',
     'aria-label="Collapse/expand this day"'),
    ("+'<span class=\"dh-count\"><b class=\"num\">'+count+'</b> 条</span></header>';",
     "+'<span class=\"dh-count\"><b class=\"num\">'+count+'</b> items</span></header>';"),
    ("btn.innerHTML='<span class=\"spin\"></span>正在加载';",
     "btn.innerHTML='<span class=\"spin\"></span>Loading';"),
    ("btn.textContent='加载失败，点击重试';if(st)st.textContent='网络或数据有问题，点按钮再试一次。';",
     "btn.textContent='Failed to load, click to retry';if(st)st.textContent='Something is wrong with the network or data. Click the button to try again.';"),
    ("btn.textContent='加载更多';",
     "btn.textContent='Load more';"),
    ("srList.innerHTML='<p class=\"more-note\">正在搜索…</p>';",
     "srList.innerHTML='<p class=\"more-note\">Searching…</p>';"),
    ("srCount.textContent='找到 '+scored.length+' 条';",
     "srCount.textContent='Found '+scored.length+' items';"),
    ("'<h3 class=\"empty-title\">没有匹配「'+escHtml(state.q)+'」的动态。</h3>'",
     "'<h3 class=\"empty-title\">No items matching \"'+escHtml(state.q)+'\".</h3>'"),
    ("'<p class=\"empty-text\">换个关键词试试，或者清除搜索看看全部。</p>'",
     "'<p class=\"empty-text\">Try another keyword, or clear the search to see everything.</p>'"),
    ("<button type=\"button\" class=\"empty-btn\" data-empty-action=\"clear\">清除筛选</button>",
     "<button type=\"button\" class=\"empty-btn\" data-empty-action=\"clear\">Clear filters</button>"),
    ("'<button type=\"button\" class=\"empty-btn primary\" data-empty-action=\"featured\">去看精选</button></div></div>';",
     "'<button type=\"button\" class=\"empty-btn primary\" data-empty-action=\"featured\">See featured</button></div></div>';"),
    ("'<p class=\"more-note\">只显示前 50 条，共 '+scored.length+' 条。</p>'",
     "'<p class=\"more-note\">Showing the first 50 of '+scored.length+' items.</p>'"),
    ("<h3 class=\"empty-title\">搜索暂时不可用</h3>",
     "<h3 class=\"empty-title\">Search is unavailable right now</h3>"),
    ("'<p class=\"empty-text\">数据没加载出来，刷新页面再试。</p></div>';",
     "'<p class=\"empty-text\">The data did not load. Refresh the page and try again.</p></div>';"),
    ("t.innerHTML=open?'收起 <span aria-hidden=\"true\">▴</span>':'另有 '+n+' 篇报道 <span aria-hidden=\"true\">▾</span>';",
     "t.innerHTML=open?'Collapse <span aria-hidden=\"true\">▴</span>':n+' more reports <span aria-hidden=\"true\">▾</span>';"),
    ("if(sp)sp.textContent=on?'已收藏':'收藏';",
     "if(sp)sp.textContent=on?'Saved':'Save';"),
    ("star.setAttribute('aria-label',on?'取消收藏':'收藏');star.title=on?'取消收藏':'收藏';",
     "star.setAttribute('aria-label',on?'Unsave':'Save');star.title=on?'Unsave':'Save';"),
    ("var done=function(){copy.textContent='已复制';setTimeout(function(){copy.textContent='复制链接';},1500);};",
     "var done=function(){copy.textContent='Copied';setTimeout(function(){copy.textContent='Copy link';},1500);};"),
]


def _build_script_en(script):
    out = script
    for old, new in _JS_EN_REPLACEMENTS:
        if old not in out:
            raise AssertionError("JS EN replacement source missing: %r" % old[:60])
        out = out.replace(old, new)
    return out


SCRIPT_EN = _build_script_en(SCRIPT)
_SCRIPT_EN_JS = SCRIPT_EN.strip()
assert _SCRIPT_EN_JS.startswith("<script>") and _SCRIPT_EN_JS.endswith("</script>")
SCRIPT_JS_EN = _SCRIPT_EN_JS[len("<script>"):-len("</script>")].strip() + "\n"


def _storage_prefix(site):
    """localStorage 键前缀：取 site.slug，各站互不干扰。"""
    return site.get("slug", "hot")


def theme_boot(site):
    return THEME_BOOT.replace("__SLUG__-", _storage_prefix(site) + "-")


def script_js(site):
    return SCRIPT_JS.replace("__SLUG__-", _storage_prefix(site) + "-")


def script_js_en(site):
    return SCRIPT_JS_EN.replace("__SLUG__-", _storage_prefix(site) + "-")


def _logo(size):
    return LOGO_SVG.replace('width="44" height="44"',
                            f'width="{size}" height="{size}"')


def _tree_url(site_url, rel_path, lang):
    """某语言树内某相对路径的绝对 URL（rel_path='' 为树首页）。"""
    if lang == "en":
        return site_url + "/en/" + rel_path
    return site_url + "/" + rel_path


def _alt_lang_href(lang, rel_path):
    """到另一语言树同一页的相对链接（rel_path 为树内相对路径，'' 为首页；
    rel_path=None 表示无对应页，不生成切换链接）。
    中文页在深度 d 的目录时先 ../ 回到树根再进 en/；英文页要多一层 ../ 回中文树。"""
    if rel_path is None:
        return None
    depth = rel_path.count("/")
    if lang == "zh":
        return "../" * depth + "en/" + (rel_path or "index.html")
    return "../" * (depth + 1) + (rel_path or "index.html")


def _lang_boot(site, lang, alt_href):
    """<head> 内尽早执行的语言自动跳转：仅当 localStorage 里没有偏好时，
    按 navigator.language 决定（zh 开头 -> 中文，其余 -> 英文，默认英文）；
    自动决定会存下来，目标页不再跳转，绝不循环；爬虫一律不跳转。
    偏好键取 site.slug，各站互不干扰。"""
    lang_key = _storage_prefix(site) + "-lang"
    return (
        "<script>(function(){try{var k='" + lang_key + "';"
        "if(localStorage.getItem(k))return;"
        "if(/bot|crawler|spider|crawling|slurp|facebookexternal|preview/i"
        ".test(navigator.userAgent||''))return;"
        "var want=(navigator.language||navigator.userLanguage||'en')"
        ".toLowerCase().indexOf('zh')===0?'zh':'en';"
        "localStorage.setItem(k,want);"
        f"if(want!==\"{lang}\")location.replace({json.dumps(alt_href)});"
        "}catch(e){}})();</script>")


def _lang_onclick(site, other):
    """语言切换链接的内联点击处理：同步写偏好（不能等 site.js 加载，
    否则目标页的自动跳转可能把用户弹回来）。偏好键取 site.slug。"""
    lang_key = _storage_prefix(site) + "-lang"
    return ("onclick=\"try{localStorage.setItem('" + lang_key + "','"
            + other + "')}catch(e){}\"")


def _nav_items(prefix, base="", lang="zh"):
    """prefix：首页为 ''，其它根页面为 'index.html'，
    子目录页为 '../index.html'（base 拼在前面）。
    精选与全部动态是两个页面（对标 AIHOT / 与 /all），不再是站内锚点。"""
    root = prefix or "index.html"
    all_page = root.replace("index.html", "all.html")
    if lang == "en":
        labels = [("featured", "Featured"), ("all", "All Items"),
                  ("hot", "Hot List"), ("daily", "Daily"), ("starred", "Saved")]
    else:
        labels = [("featured", "精选"), ("all", "全部动态"), ("hot", "热点榜"),
                  ("daily", "日报"), ("starred", "收藏")]
    icons = {"featured": "zap", "all": "list", "hot": "trend",
             "daily": "doc", "starred": "bookmark"}
    hrefs = {"featured": f"{base}{root}", "all": f"{base}{all_page}",
             "hot": f"{base}hot.html", "daily": f"{base}daily.html",
             "starred": f"{base}starred.html"}
    return [(key, label, icons[key], hrefs[key]) for key, label in labels]


def sidebar_html(site, active, prefix="", base="", lang="zh", alt_href=None):
    items = _nav_items(prefix, base, lang)
    links = "".join(
        f'<a class="side-link{" on" if key == active else ""}" href="{href}">'
        f'{icon(ic)}<span>{label}</span>'
        f'{"<span class=\"num\" id=\"starCount\"></span>" if key == "starred" else ""}</a>'
        for key, label, ic, href in items)
    more_links = (
        f'<a class="side-link{" on" if active == "more" else ""}" href="{base}more.html">{icon("user")}<span>{_L(lang, "我的", "My")}</span></a>'
        f'<a class="side-link" href="{base}weekly.html">{icon("calendar")}<span>{_L(lang, "周报", "Weekly")}</span></a>'
        f'<a class="side-link" href="{base}monthly.html">{icon("calendar")}<span>{_L(lang, "月报", "Monthly")}</span></a>'
        f'<a class="side-link{" on" if active == "changelog" else ""}" href="{base}changelog.html">{icon("doc")}<span>{_L(lang, "更新日志", "Changelog")}</span></a>'
        f'<a class="side-link{" on" if active == "about" else ""}" href="{base}about.html">{icon("rss")}<span>{_L(lang, "关于", "About")}</span></a>'
        f'<a class="side-link" href="{site["repo"]}/issues" target="_blank" rel="noopener">{icon("message")}<span>{_L(lang, "反馈", "Feedback")}</span></a>'
        f'<a class="side-link" href="{base}data/hot.json">{icon("code")}<span>{_L(lang, "数据 JSON", "Data JSON")}</span></a>')
    if lang == "en":
        subtitle = site.get("subtitle_en") or site.get("subtitle", "")
    else:
        subtitle = site.get("subtitle", "")
    lang_link = ""
    if alt_href:
        other = "en" if lang == "zh" else "zh"
        lang_link = (f'<a class="gh" href="{alt_href}" {_lang_onclick(site, other)}>'
                     f'{_L(lang, "English", "Chinese")}</a>')
    return (f'<aside class="sidebar"><a class="brand" href="{base}index.html">{_logo(32)}'
            f'<span><b>{esc(_name(site, lang))}</b><small>{esc(subtitle)}</small></span></a>'
            f'<nav aria-label="{_L(lang, "主导航", "Main navigation")}"><div class="nav-sec"><h3>{_L(lang, "内容", "Content")}</h3>{links}</div>'
            f'<div class="nav-sec"><h3>{_L(lang, "更多", "More")}</h3>{more_links}'
            f'</div></nav>'
            f'<div class="side-foot">'
            f'<a class="gh" href="{site["repo"]}" target="_blank" rel="noopener">{_L(lang, "GitHub 仓库", "GitHub Repo")}</a>'
            f'{lang_link}'
            f'{_theme_btn(lang)}'
            f'<p class="note">{_L(lang, "每天 " + esc(site["edition_time_cst"]) + " 出日报", "Daily digest at " + esc(site["edition_time_cst"]))}</p>'
            f'</div></aside>')


def rail_html(site, active, prefix="", base="", lang="zh", alt_href=None):
    items = _nav_items(prefix, base, lang)
    links = "".join(
        f'<a class="rail-link{" on" if key == active else ""}" href="{href}">'
        f'{icon(ic, 20)}<span>{label}</span></a>'
        for key, label, ic, href in items)
    links += (f'<a class="rail-link{" on" if active == "more" else ""}" href="{base}more.html">'
              f'{icon("user", 20)}<span>{_L(lang, "我的", "My")}</span></a>')
    # 语言切换只放侧栏左下角（.side-foot，与 GitHub 仓库同排），窄栏不再重复放。
    return (f'<aside class="rail"><a class="brand" href="{base}index.html" aria-label="{_L(lang, esc(_name(site, lang)) + " 首页", esc(_name(site, lang)) + " home")}">'
            f'{_logo(28)}</a><nav aria-label="{_L(lang, "主导航", "Main navigation")}">{links}</nav></aside>')


def _theme_btn(lang="zh"):
    return ('<button type="button" class="icon-btn theme-btn theme-cycle" aria-label="'
            + _L(lang, "外观：跟随系统（点击切换）", "Appearance: system (click to switch)") + '">'
            f'<span class="ic-moon">{icon("moon", 20)}</span>'
            f'<span class="ic-sun">{icon("sun", 20)}</span>'
            f'<span class="ic-monitor">{icon("monitor", 20)}</span></button>')


def topbar_html(site, active, prefix="", base="", lang="zh", alt_href=None):
    if active in ("daily", "weekly", "monthly"):
        center = ('<span class="title">'
                  + {"daily": _L(lang, "日报", "Daily"),
                     "weekly": _L(lang, "周报", "Weekly"),
                     "monthly": _L(lang, "月报", "Monthly")}[active] + '</span>')
    else:
        root = prefix or "index.html"
        all_page = root.replace("index.html", "all.html")
        center = (f'<span class="switch">'
                  f'<a class="{"on" if active == "featured" else ""}" href="{base}{root}">{_L(lang, "精选", "Featured")}</a>'
                  f'<a class="{"on" if active == "all" else ""}" href="{base}{all_page}">{_L(lang, "全部", "All")}</a></span>')
    # 语言切换只放侧栏左下角（.side-foot，与 GitHub 仓库同排），顶栏不再重复放。
    return (f'<header class="topbar"><a class="brand" href="{base}index.html">{_logo(26)}<b>{esc(_name(site, lang))}</b></a>'
            f'{center}{_theme_btn(lang)}</header>')


def tabbar_html(active, prefix="", base="", lang="zh"):
    root = prefix or "index.html"
    all_page = root.replace("index.html", "all.html")
    tabs = [
        ("featured", _L(lang, "精选", "Featured"), "zap", f"{base}{root}"),
        ("hot", _L(lang, "热点", "Hot"), "trend", f"{base}hot.html"),
        ("daily", _L(lang, "日报", "Daily"), "doc", f"{base}daily.html"),
        ("all", _L(lang, "全部", "All"), "list", f"{base}{all_page}"),
        ("starred", _L(lang, "收藏", "Saved"), "bookmark", f"{base}starred.html"),
    ]
    links = "".join(
        f'<a class="{"on" if key == active else ""}" href="{href}">'
        f'{icon(ic, 20)}<span>{label}</span></a>'
        for key, label, ic, href in tabs)
    return f'<nav class="tabbar" aria-label="{_L(lang, "主导航", "Main navigation")}"><div class="tabbar-in">{links}</div></nav>'


def footer_html(site, base="", lang="zh"):
    name = esc(_name(site, lang))
    repo = esc(site.get("repo", ""))
    if lang == "en":
        p1 = (f"{name} is an aggregator and reading index. Titles and summaries "
              "belong to their original sources. Content is for reference "
              "only; full text is never republished.")
        note = site.get("footer_note_en", "")
    else:
        p1 = (f"{name} 是聚合摘要与阅读索引，标题与摘要版权归各来源所有。"
              "内容只作资讯参考；本站不转载全文。")
        note = site.get("footer_note", "")
    mcp_link = (f'<a href="{base}about.html">{_L(lang, "MCP 接入", "MCP Access")}</a>'
                if site.get("mcp_url") else "")
    tips = site.get("tips") or []
    tip_html = ""
    if tips:
        cards = "".join(
            f'<div class="tip-card"><img class="tip-qr" src="{base}{esc(t["image"])}" alt="{_L(lang, "赞赏码：", "Tip QR code: ")}{esc(t["label"])}" width="150" height="150">'
            f'<p class="tip-label">{esc(t["label"])}</p>'
            f'<p class="tip-addr">{esc(t["address"])}</p></div>'
            for t in tips
        )
        tip_html = (f'<div class="tip"><p class="tip-title">{_L(lang, "赞赏支持", "Support " + name)}</p>'
                    f'<div class="tip-cards">{cards}</div></div>')
    return (f'<footer class="foot"><p>{p1}</p>'
            + (f'<p>{esc(note)}</p>' if note else '')
            + f'<nav class="foot-links" aria-label="{_L(lang, "页脚链接", "Footer links")}">'
            f'<a href="{base}feed.xml">{_L(lang, "RSS 订阅", "RSS Feed")}</a>'
            f'{mcp_link}'
            f'<a href="{base}data/days/index.json">{_L(lang, "数据 JSON", "Data JSON")}</a>'
            f'<a href="{repo}">{_L(lang, "GitHub 仓库", "GitHub Repo")}</a>'
            f'<a href="{repo}/issues">{_L(lang, "反馈", "Feedback")}</a>'
            f'<a href="{base}more.html">{_L(lang, "我的", "My")}</a>'
            f'<a href="{base}about.html">{_L(lang, "关于", "About")}</a>'
            f'<a href="{base}terms.html">{_L(lang, "条款", "Terms")}</a>'
            f'<a href="{base}privacy.html">{_L(lang, "隐私", "Privacy")}</a></nav>'
            f'{tip_html}</footer>')


def page_open(site, active, title, description, prefix="", base="", canonical="",
              ld_items=None, page_cls="", ld_blocks=None, og_type="website",
              extra_head="", lang="zh", rel_path=None):
    """rel_path：本页在语言树内的相对路径（'' 为树首页）；传了才挂三件套 hreflang
    与语言切换/自动跳转（geo-audit 等无对应页的页面不传，走旧的两件套）。
    canonical 默认值保持旧行为：中文页无 canonical 参数时指向站根（all.html 的
    旧 canonical 仍指向站根，不在此次改动里修）；英文页默认指向 en/ 树内同路径。"""
    site_url = site.get("url", "")
    if canonical:
        canon = canonical
    elif lang == "en":
        canon = site_url + "/en/" + (rel_path or "")
    else:
        canon = site_url + "/"
    alt_href = _alt_lang_href(lang, rel_path)
    if rel_path is not None:
        zh_url = site_url + "/" + rel_path
        en_url = site_url + "/en/" + rel_path
        hreflang = (f'<link rel="alternate" hreflang="zh-CN" href="{esc(zh_url)}">\n'
                    f'<link rel="alternate" hreflang="en" href="{esc(en_url)}">\n'
                    f'<link rel="alternate" hreflang="x-default" href="{esc(en_url)}">\n')
    else:
        hreflang = (f'<link rel="alternate" hreflang="zh-CN" href="{esc(canon)}">\n'
                    f'<link rel="alternate" hreflang="x-default" href="{esc(canon)}">\n')
    feed_href = site_url + ("/en/feed.xml" if lang == "en" else "/feed.xml")
    og = (f'<meta property="og:title" content="{esc(title)}">\n'
          f'<meta property="og:description" content="{esc(description)}">\n'
          f'<meta property="og:type" content="{og_type}">\n'
          f'<meta property="og:url" content="{esc(canon)}">\n'
          f'<meta property="og:image" content="{site_url}/favicon.svg">\n'
          f'<meta name="twitter:card" content="summary">\n'
          f'<meta name="twitter:title" content="{esc(title)}">\n'
          f'<meta name="twitter:description" content="{esc(description)}">\n'
          f'<meta name="twitter:image" content="{site_url}/favicon.svg">\n')
    ld = {"@context": "https://schema.org", "@type": "WebSite",
          "name": _name(site, lang),
          "url": site_url + "/en/" if lang == "en" else site_url,
          "inLanguage": "en" if lang == "en" else "zh-CN",
          "description": (site.get("description_en") or site.get("description", ""))
          if lang == "en" else site.get("description", "")}
    ld_parts = [json.dumps(ld, ensure_ascii=False)]
    if ld_items:
        item_url_base = site_url + ("/en/items/" if lang == "en" else "/items/")
        items_ld = {"@context": "https://schema.org", "@type": "ItemList",
                    "itemListElement": [
                        {"@type": "ListItem", "position": i + 1,
                         "name": ((it.get("en_title") or it["title"]) if lang == "en"
                                  else (it.get("zh_title") or it["title"])),
                         "url": item_url_base + it["id"] + ".html"}
                        for i, it in enumerate(ld_items[:10])]}
        ld_parts.append(json.dumps(items_ld, ensure_ascii=False))
    for block in (ld_blocks or []):
        ld_parts.append(json.dumps(block, ensure_ascii=False))
    ld_html = "".join(
        f'<script type="application/ld+json">{part}</script>\n' for part in ld_parts)
    boot = theme_boot(site) + (_lang_boot(site, lang, alt_href) if alt_href else "")
    return (f"<!DOCTYPE html>\n<html lang=\"{'en' if lang == 'en' else 'zh-CN'}\"><head><meta charset=\"utf-8\">\n"
            f"<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
            f"<title>{esc(title)}</title>\n"
            f"<meta name=\"description\" content=\"{esc(description)}\">\n"
            f'<link rel="canonical" href="{esc(canon)}">\n'
            f"{hreflang}"
            f'<meta name="robots" content="index, follow, max-image-preview:large">\n'
            f'<link rel="alternate" type="application/rss+xml" title="{esc(_name(site, lang))}" href="{feed_href}">\n'
            f"{extra_head}"
            f'<link rel="icon" type="image/svg+xml" href="{base}favicon.svg">\n'
            f"{og}"
            f'{ld_html}'
            f"{boot}<link rel=\"stylesheet\" href=\"{base}assets/site.css\"></head>\n<body>"
            f'<div class="shell">{sidebar_html(site, active, prefix, base, lang, alt_href)}{rail_html(site, active, prefix, base, lang, alt_href)}'
            f'<div class="main">{topbar_html(site, active, prefix, base, lang, alt_href)}<div class="page{page_cls}">')


def page_close(site, active, prefix="", base="", lang="zh"):
    to_top = (f'<button type="button" class="to-top" id="toTop" aria-label="{_L(lang, "回到顶部", "Back to top")}">'
              f'{icon("arrow-up", 18)}</button>')
    return (f"{footer_html(site, base, lang)}</div></div></div>{to_top}{tabbar_html(active, prefix, base, lang)}<script src='{base}assets/site.js'></script>{ANALYTICS}{CLARITY}</body></html>\n")


def day_header(d, items, today, aside=False, lang="zh"):
    is_today = d == today
    if lang == "en":
        date_txt = f"{MONTHS_SHORT_EN[d.month - 1]} {d.day}"
        name = "Today" if is_today else date_txt
        wd_short, wd_full = WEEKDAYS_SHORT_EN[d.weekday()], WEEKDAYS_EN[d.weekday()]
    else:
        date_txt = f"{d.month}月{d.day}日"
        name = "今天" if is_today else date_txt
        wd_short, wd_full = WEEKDAYS_SHORT[d.weekday()], WEEKDAYS[d.weekday()]
    cls = "day-head is-today" if is_today else "day-head"
    toggle = (f'<button type="button" class="dh-toggle" aria-label="{_L(lang, "收起/展开这一天", "Collapse/expand this day")}">'
              f'{icon("chevron-down", 14)}</button>')
    aside_html = ('<span class="dh-aside"><button type="button" class="toggle-chip unread-toggle">'
                  f'{_L(lang, "只看未读", "Unread only")}</button></span>') if aside else ""
    return (f'<header class="{cls}">'
            f'<span class="dh-name">{name}</span>'
            f'<span class="dh-date">{date_txt}</span>'
            f'{toggle}'
            f'<span class="dh-wd dh-wd-short">{wd_short}</span>'
            f'<span class="dh-wd dh-wd-full">{wd_full}</span>'
            f'<span class="dh-count"><b class="num">{len(items)}</b> {_L(lang, "条", "items")}</span>{aside_html}</header>')


def _norm_title(title):
    """标题归一化：去标点/空白/大小写，供同事件归组比较用。"""
    t = (title or "").lower()
    t = re.sub(r"[\s\-_·•|/\\:;,.!?？！。、，；：（）()\[\]{}“”\"'‘’<>《》]+", "", t)
    return t


def group_similar(items):
    """保守版同事件归组（B13）：只合并同一来源、同一天、标题归一化后相同
    或仅差后缀（短的是长的的前缀，且长度比 ≥0.8；归一化后至少 10 字）。
    返回 [{main, extra:[...]}]，顺序不变；跨来源不合并。"""
    groups = []
    for it in items:
        pub = it["_pub"].astimezone(CST).date()
        key = (it.get("source_id", ""), pub)
        norm = _norm_title(it.get("zh_title") or it["title"])
        merged = False
        if len(norm) >= 10:
            for g in groups:
                m = g["main"]
                if (m.get("source_id", ""), m["_pub"].astimezone(CST).date()) != key:
                    continue
                mnorm = _norm_title(m.get("zh_title") or m["title"])
                if len(mnorm) < 10:
                    continue
                if norm == mnorm or (
                        (norm.startswith(mnorm) or mnorm.startswith(norm))
                        and min(len(norm), len(mnorm)) / max(len(norm), len(mnorm)) >= 0.8):
                    g["extra"].append(it)
                    merged = True
                    break
        if not merged:
            groups.append({"main": it, "extra": []})
    return groups


def _same_topic(a, b):
    """跨来源同事件判定（2026-11-11 把关新增）：归一化标题一短一长、
    短者是长者的前缀且至少 10 字 -> 同一事件（如两家媒体同报 UE 5.9 预览）。
    只用于精选/热点/日报的取前 N 去重，时间线不受影响。"""
    na = _norm_title(a.get("zh_title") or a["title"])
    nb = _norm_title(b.get("zh_title") or b["title"])
    if len(na) < 10 or len(nb) < 10:
        return False
    return na.startswith(nb) or nb.startswith(na)


def dedup_topics(items):
    """按顺序去重同事件条目，保留先出现的（调用前已按分数排好序）。"""
    kept = []
    for it in items:
        if any(_same_topic(it, k) for k in kept):
            continue
        kept.append(it)
    return kept


def timeline_slot(it, sel_ids, base="", lang="zh"):
    pub = it["_pub"].astimezone(CST)
    badge = it["id"] in sel_ids
    return (f'<li class="slot" data-category="{esc(it["category"])}">'
            f'<time class="slot-time" datetime="{pub.isoformat()}">{pub.strftime("%H:%M")}</time>'
            f'<span class="rail" aria-hidden="true"></span>'
            f'{feed_item(it, badge=badge, base=base, lang=lang)}</li>')


def timeline_group_slot(group, sel_ids, base="", lang="zh"):
    """归组后的时间线格：主卡 + “另有 N 篇报道”展开（B13）。"""
    main = group["main"]
    extra = group["extra"]
    slot = timeline_slot(main, sel_ids, base, lang)
    if not extra:
        return slot
    n = len(extra)
    rows = "".join(
        f'<li><a href="{base}items/{esc(e["id"])}.html">'
        f'{esc((e.get("en_title") or e["title"]) if lang == "en" else (e.get("zh_title") or e["title"]))}</a>'
        f'<span class="ge-time">{esc(e["_pub"].astimezone(CST).strftime("%H:%M"))}</span></li>'
        for e in extra)
    toggle = (f'<button type="button" class="group-toggle" aria-expanded="false">'
              f'{f"另有 {n} 篇报道" if lang == "zh" else f"{n} more reports"} <span aria-hidden="true">▾</span></button>')
    extra_html = (f'<div class="group-extra" hidden><ul class="group-extra-list">{rows}</ul></div>')
    # 把展开区插进主卡的 article 末尾之前：直接拼在 slot 的 </li> 之前
    return slot[:-5] + toggle + extra_html + "</li>"


# 首页首屏服务端渲染的时间线条数上限（见 render_index 里的说明）
INDEX_SSR_SLOTS = 20


def _tl_sections(items, sel_ids, lang="zh"):
    """时间线按天分组渲染（首页精选 feed 与全部动态页共用）。
    首屏只渲染前 INDEX_SSR_SLOTS 条（全渲染会让单文件超过推送上限）；
    其余由 JS 分页按需从 data/days/ 取。日期头上的条数按已渲染的算，
    否则 JS 追加时再累加会把数算重。"""
    rendered = items[:INDEX_SSR_SLOTS]
    groups = group_similar(rendered)
    days = {}
    for g in groups:
        days.setdefault(g["main"]["_pub"].astimezone(CST).date(), []).append(g)
    day_counts = {}
    for it in rendered:
        d = it["_pub"].astimezone(CST).date()
        day_counts[d] = day_counts.get(d, 0) + 1
    today = datetime.now(CST).date()
    tl_sections = ""
    for n, (d, gs) in enumerate(days.items()):
        slots = "".join(timeline_group_slot(g, sel_ids, lang=lang) for g in gs)
        fake_items = [None] * day_counts[d]
        tl_sections += (f'<section class="day-sec" data-date="{d.isoformat()}">'
                        f'{day_header(d, fake_items, today, aside=(n == 0), lang=lang)}'
                        f'<ol class="day-list">{slots}</ol></section>')
    return tl_sections


def en_view(it):
    """英文渲染用的浅拷贝：带 reason_en/category_label_en/tags_en 的实时条目
    换成英文版；pub_item_en 产出的已英文化字典（reason 等字段本身已是英文、
    没有 reason_en 键）原样保留。标题/简介由 feed_item 按 lang 自行切换。"""
    v = dict(it)
    if "reason_en" in it:
        v["reason"] = it["reason_en"] or ""
    if "category_label_en" in it:
        v["category_label"] = it["category_label_en"] or it.get("category", "")
    if "tags_en" in it:
        v["tags"] = it["tags_en"] or []
    return v


def render_index(site, cats, cfg, src_by_id, selected, hot, timeline, generated_at, counts, lang="zh"):
    if lang == "en":
        selected = [en_view(it) for it in selected]
        hot = [en_view(it) for it in hot]
        timeline = [en_view(it) for it in timeline]
    sel_ids = {it["id"] for it in selected}
    cat_opts = "".join(
        f'<button type="button" class="chip" data-filter="{c["key"]}">{esc(c.get("label_en") or c["label"] if lang == "en" else c["label"])}</button>'
        for c in cats)
    cat_opts += f'<button type="button" class="chip" data-filter="official">{_L(lang, "官方", "Official")}</button>'
    search_html = (f'<div class="search" role="search">{icon("search", 16)}'
                   f'<input id="siteSearch" type="text" placeholder="{_L(lang, "搜索标题、摘要…", "Search titles and summaries…")}" '
                   f'maxlength="200" autocomplete="off" aria-label="{_L(lang, "搜索标题和摘要", "Search titles and summaries")}">'
                   f'<button type="button" class="clear" id="searchClear" aria-label="{_L(lang, "清空", "Clear")}">✕</button>'
                   f'<kbd>/</kbd></div>')
    search_trigger = (f'<button type="button" class="search-trigger" aria-label="{_L(lang, "打开搜索", "Open search")}">'
                      f'{icon("search", 16)}<span>{_L(lang, "搜索标题、摘要…", "Search titles and summaries…")}</span></button>')
    overlay_cats = "".join(
        f'<button type="button" class="chip" data-filter="{c["key"]}">{esc(c.get("label_en") or c["label"] if lang == "en" else c["label"])}</button>'
        for c in cats)
    overlay_cats += f'<button type="button" class="chip" data-filter="official">{_L(lang, "官方", "Official")}</button>'
    overlay_hot = "".join(
        f'<li><span class="rank{" r1" if i == 0 else (" r2" if i == 1 else (" r3" if i == 2 else ""))}">{i + 1}</span>'
        f'<a href="items/{esc(it["id"])}.html">{esc((it.get("en_title") or it["title"]) if lang == "en" else (it.get("zh_title") or it["title"]))}</a></li>'
        for i, it in enumerate(hot[:5]))
    overlay_html = (
        f'<div class="search-overlay" id="searchOverlay" hidden>'
        f'<div class="overlay-bar"><button type="button" class="icon-btn" id="overlayClose" aria-label="{_L(lang, "关闭搜索", "Close search")}">{icon("x", 20)}</button>'
        f'<div class="search overlay-search">{icon("search", 16)}'
        f'<input id="overlaySearch" type="text" placeholder="{_L(lang, "搜索标题、摘要…", "Search titles and summaries…")}" maxlength="200" autocomplete="off" aria-label="{_L(lang, "搜索标题和摘要", "Search titles and summaries")}">'
        f'<button type="button" class="clear" id="overlaySearchClear" aria-label="{_L(lang, "清空", "Clear")}">✕</button></div></div>'
        f'<div class="overlay-sec"><h3>{_L(lang, "最近搜索", "Recent searches")}</h3><div id="recentList"></div>'
        f'<button type="button" class="recent-clear" id="clearRecent">{_L(lang, "清除最近搜索", "Clear recent searches")}</button></div>'
        f'<div class="overlay-sec"><h3>{_L(lang, "按分类找", "Browse by category")}</h3><div class="overlay-cats">{overlay_cats}</div></div>'
        f'<div class="overlay-sec"><h3>{_L(lang, "正在热议", "Trending now")}</h3><ol class="overlay-hot">{overlay_hot}</ol></div>'
        f'</div>')
    sel_html = "".join(feed_item(it, badge=True, lang=lang) for it in selected) \
        or _L(lang, "<p>今日暂无达到精选门槛的条目。</p>", "<p>No items reached the curation bar today.</p>")
    top5 = hot[:5]
    hot_html = "".join(hot_row(it, i + 1, lang=lang) for i, it in enumerate(top5)) \
        or _L(lang, "<li>暂无热点。</li>", "<li>No hot topics yet.</li>")
    hot_more = ('<a class="hot-more" href="hot.html">'
                f'{_L(lang, "完整榜单", "Full ranking")} <span aria-hidden="true">→</span></a>') if len(hot) > 5 else ""
    tl_sections = _tl_sections(timeline, sel_ids, lang=lang)
    unread_row = ('<div class="unread-row"><button type="button" class="toggle-chip unread-toggle">'
                  f'{_L(lang, "只看未读", "Unread only")}</button></div>')
    # 给 JS 分页/搜索用的配置：打分参数 + 关键词标签映射 + 信源分级（供动态渲染卡片时算分/理由/标签）
    sc = cfg["scoring"]
    ih_cfg = {
        "base": sc["base"],
        "recency": sc["recency"],
        "tierBonus": sc["tier_bonus"],
        "devBonus": sc["dev_keyword_bonus"],
        "devCap": sc["dev_keyword_cap"],
        "devLabels": _no_cjk_keys(REASON_LABELS_EN) if lang == "en" else REASON_LABELS,
        "noiseKw": _no_cjk_list(sc["noise_keywords"]) if lang == "en" else sc["noise_keywords"],
        "noisePenalty": sc["noise_keyword_penalty"],
        "noiseFloor": sc["noise_keyword_floor"],
        "tagSlugs": TAG_SLUGS_EN if lang == "en" else TAG_SLUGS,
        "tiers": {sid: s.get("tier", "T2") for sid, s in src_by_id.items()},
    }
    cfg_json = json.dumps(ih_cfg, ensure_ascii=False)
    empty_state = (
        '<div id="noResult" class="empty-state" hidden>'
        f'<div class="empty-icon" id="noResultIcon">{icon("search", 40)}</div>'
        f'<h3 class="empty-title" id="noResultTitle">{_L(lang, "这个分类下暂无动态。", "No items in this category yet.")}</h3>'
        '<p class="empty-text" id="noResultText"></p>'
        '<div class="empty-actions">'
        f'<button type="button" class="empty-btn" data-empty-action="clear">{_L(lang, "清除筛选", "Clear filters")}</button>'
        f'<button type="button" class="empty-btn primary" data-empty-action="featured">{_L(lang, "去看精选", "See featured")}</button>'
        '</div></div>')
    title = (f'{site.get("title_en") or site["title"]} · Featured & Hot List' if lang == "en"
             else f'{site["title"]} · 今日精选与热点榜')
    description = site.get("description_en") or site["description"] if lang == "en" else site["description"]
    lede = (f'Updated {esc(generated_at)} (Beijing time)<span class="lede-rest"> · {counts["total_7d"]} items in the past 7 days · '
            f'Featured {counts["selected"]} · Only titles and summaries are shown; click a title for details and the outbound link.</span>'
            if lang == "en" else
            f'更新于 {esc(generated_at)}（北京时间）<span class="lede-rest"> · 最近 7 天共 {counts["total_7d"]} 条 · '
            f'精选 {counts["selected"]} 条 · 只显示标题与摘要，点击标题查看详情，详情页里有原文链接。</span>')
    return (page_open(site, "featured", title, description, ld_items=selected, lang=lang, rel_path="")
            + f'<div class="m-title">{_L(lang, "精选", "Featured")}</div>'
            + f'<h1>{_L(lang, "精选", "Featured")}</h1>'
            + f'<p class="lede">{lede}</p>'
            + f'<div class="filter-row"><div class="tabs" role="tablist" aria-label="{_L(lang, "分类筛选", "Filter by category")}">'
            f'<span class="tabs-thumb" id="tabsThumb"></span>'
            f'<button type="button" class="chip on" data-filter="all">{_L(lang, "全部", "All")}</button>{cat_opts}</div>'
            + search_trigger + search_html + '</div>'
            + overlay_html
            + f'<section class="card hot-card" id="hot" aria-labelledby="hot-topics">'
            f'<div class="hot-head"><h2 id="hot-topics"><span class="live" aria-hidden="true">'
            f'<span class="ping"></span><span class="dot"></span></span>{_L(lang, "当前热点", "Hot now")}</h2></div>'
            f'<ol class="hot-list hot-top5">{hot_html}</ol>'
            + hot_more
            + '</section>'
            + f'<div id="featured">{sel_html}</div>'
            + f'<div id="timeline">'
            + unread_row
            + tl_sections
            + '</div>'
            + f'<a class="more-row" href="all.html">{icon("list", 18)}'
            + f'<span class="m-label">{_L(lang, "查看全部动态", "See all items")}</span><span class="m-arrow">›</span></a>'
            + '<div id="searchResults" hidden>'
            + f'<div class="search-results-head"><h2>{_L(lang, "搜索结果", "Search results")}</h2><span class="sr-count" id="srCount"></span></div>'
            + '<div id="srList"></div></div>'
            + empty_state
            + '<div id="loadMoreSentinel"></div>'
            + '<div class="load-more-wrap" id="loadMoreWrap">'
            + f'<button type="button" class="load-more-btn" id="loadMoreBtn">{_L(lang, "加载更多", "Load more")}</button>'
            + '<p class="load-more-state" id="loadMoreState"></p></div>'
            + f'<p class="feed-end" id="feedEnd" hidden>{_L(lang, "已经到底了", "You have reached the end")}</p>'
            + f'<script id="ihConfig" type="application/json">{cfg_json}</script>'
            + page_close(site, "featured", lang=lang))


def render_all(site, cats, cfg, src_by_id, selected, hot, pool, generated_at, lang="zh"):
    """全部动态页（对标 AIHOT /all）：30 天全量按时间倒序、按天分组；
    首屏只渲染前 INDEX_SSR_SLOTS 条，其余由 JS 分页从 data/days/ 取。
    无精选区、无热点框；分类筛选与搜索与首页共用同一套 JS。"""
    if lang == "en":
        selected = [en_view(it) for it in selected]
        hot = [en_view(it) for it in hot]
        pool = [en_view(it) for it in pool]
    sel_ids = {it["id"] for it in selected}
    cat_opts = "".join(
        f'<button type="button" class="chip" data-filter="{c["key"]}">{esc(c.get("label_en") or c["label"] if lang == "en" else c["label"])}</button>'
        for c in cats)
    cat_opts += f'<button type="button" class="chip" data-filter="official">{_L(lang, "官方", "Official")}</button>'
    search_html = (f'<div class="search" role="search">{icon("search", 16)}'
                   f'<input id="siteSearch" type="text" placeholder="{_L(lang, "搜索标题、摘要…", "Search titles and summaries…")}" '
                   f'maxlength="200" autocomplete="off" aria-label="{_L(lang, "搜索标题和摘要", "Search titles and summaries")}">'
                   f'<button type="button" class="clear" id="searchClear" aria-label="{_L(lang, "清空", "Clear")}">✕</button>'
                   f'<kbd>/</kbd></div>')
    search_trigger = (f'<button type="button" class="search-trigger" aria-label="{_L(lang, "打开搜索", "Open search")}">'
                      f'{icon("search", 16)}<span>{_L(lang, "搜索标题、摘要…", "Search titles and summaries…")}</span></button>')
    overlay_cats = "".join(
        f'<button type="button" class="chip" data-filter="{c["key"]}">{esc(c.get("label_en") or c["label"] if lang == "en" else c["label"])}</button>'
        for c in cats)
    overlay_cats += f'<button type="button" class="chip" data-filter="official">{_L(lang, "官方", "Official")}</button>'
    overlay_hot = "".join(
        f'<li><span class="rank{" r1" if i == 0 else (" r2" if i == 1 else (" r3" if i == 2 else ""))}">{i + 1}</span>'
        f'<a href="items/{esc(it["id"])}.html">{esc((it.get("en_title") or it["title"]) if lang == "en" else (it.get("zh_title") or it["title"]))}</a></li>'
        for i, it in enumerate(hot[:5]))
    overlay_html = (
        f'<div class="search-overlay" id="searchOverlay" hidden>'
        f'<div class="overlay-bar"><button type="button" class="icon-btn" id="overlayClose" aria-label="{_L(lang, "关闭搜索", "Close search")}">{icon("x", 20)}</button>'
        f'<div class="search overlay-search">{icon("search", 16)}'
        f'<input id="overlaySearch" type="text" placeholder="{_L(lang, "搜索标题、摘要…", "Search titles and summaries…")}" maxlength="200" autocomplete="off" aria-label="{_L(lang, "搜索标题和摘要", "Search titles and summaries")}">'
        f'<button type="button" class="clear" id="overlaySearchClear" aria-label="{_L(lang, "清空", "Clear")}">✕</button></div></div>'
        f'<div class="overlay-sec"><h3>{_L(lang, "最近搜索", "Recent searches")}</h3><div id="recentList"></div>'
        f'<button type="button" class="recent-clear" id="clearRecent">{_L(lang, "清除最近搜索", "Clear recent searches")}</button></div>'
        f'<div class="overlay-sec"><h3>{_L(lang, "按分类找", "Browse by category")}</h3><div class="overlay-cats">{overlay_cats}</div></div>'
        f'<div class="overlay-sec"><h3>{_L(lang, "正在热议", "Trending now")}</h3><ol class="overlay-hot">{overlay_hot}</ol></div>'
        f'</div>')
    tl_sections = _tl_sections(pool, sel_ids, lang=lang)
    unread_row = ('<div class="unread-row"><button type="button" class="toggle-chip unread-toggle">'
                  f'{_L(lang, "只看未读", "Unread only")}</button></div>')
    sc = cfg["scoring"]
    ih_cfg = {
        "base": sc["base"],
        "recency": sc["recency"],
        "tierBonus": sc["tier_bonus"],
        "devBonus": sc["dev_keyword_bonus"],
        "devCap": sc["dev_keyword_cap"],
        "devLabels": _no_cjk_keys(REASON_LABELS_EN) if lang == "en" else REASON_LABELS,
        "noiseKw": _no_cjk_list(sc["noise_keywords"]) if lang == "en" else sc["noise_keywords"],
        "noisePenalty": sc["noise_keyword_penalty"],
        "noiseFloor": sc["noise_keyword_floor"],
        "tagSlugs": TAG_SLUGS_EN if lang == "en" else TAG_SLUGS,
        "tiers": {sid: s.get("tier", "T2") for sid, s in src_by_id.items()},
    }
    cfg_json = json.dumps(ih_cfg, ensure_ascii=False)
    empty_state = (
        '<div id="noResult" class="empty-state" hidden>'
        f'<div class="empty-icon" id="noResultIcon">{icon("search", 40)}</div>'
        f'<h3 class="empty-title" id="noResultTitle">{_L(lang, "这个分类下暂无动态。", "No items in this category yet.")}</h3>'
        '<p class="empty-text" id="noResultText"></p>'
        '<div class="empty-actions">'
        f'<button type="button" class="empty-btn" data-empty-action="clear">{_L(lang, "清除筛选", "Clear filters")}</button>'
        f'<button type="button" class="empty-btn primary" data-empty-action="featured">{_L(lang, "去看精选", "See featured")}</button>'
        '</div></div>')
    title = (f'{site.get("title_en") or site["title"]} · All Items' if lang == "en"
             else f'{site["title"]} · 全部动态')
    description = site.get("description_en") or site["description"] if lang == "en" else site["description"]
    lede = (f'Updated {esc(generated_at)} (Beijing time)<span class="lede-rest"> · {len(pool)} items in the past 30 days · '
            f'Only titles and summaries are shown; click a title for details and the outbound link.</span>'
            if lang == "en" else
            f'更新于 {esc(generated_at)}（北京时间）<span class="lede-rest"> · 最近 30 天共 {len(pool)} 条 · '
            f'只显示标题与摘要，点击标题查看详情，详情页里有原文链接。</span>')
    return (page_open(site, "all", title, description, lang=lang, rel_path="all.html")
            + f'<div class="m-title">{_L(lang, "全部动态", "All Items")}</div>'
            + f'<h1>{_L(lang, "全部动态", "All Items")}</h1>'
            + f'<p class="lede">{lede}</p>'
            + f'<div class="filter-row"><div class="tabs" role="tablist" aria-label="{_L(lang, "分类筛选", "Filter by category")}">'
            f'<span class="tabs-thumb" id="tabsThumb"></span>'
            f'<button type="button" class="chip on" data-filter="all">{_L(lang, "全部", "All")}</button>{cat_opts}</div>'
            + search_trigger + search_html + '</div>'
            + overlay_html
            + f'<div id="timeline">'
            + unread_row
            + tl_sections
            + '</div>'
            + '<div id="searchResults" hidden>'
            + f'<div class="search-results-head"><h2>{_L(lang, "搜索结果", "Search results")}</h2><span class="sr-count" id="srCount"></span></div>'
            + '<div id="srList"></div></div>'
            + empty_state
            + '<div id="loadMoreSentinel"></div>'
            + '<div class="load-more-wrap" id="loadMoreWrap">'
            + f'<button type="button" class="load-more-btn" id="loadMoreBtn">{_L(lang, "加载更多", "Load more")}</button>'
            + '<p class="load-more-state" id="loadMoreState"></p></div>'
            + f'<p class="feed-end" id="feedEnd" hidden>{_L(lang, "已经到底了", "You have reached the end")}</p>'
            + f'<script id="ihConfig" type="application/json">{cfg_json}</script>'
            + page_close(site, "all", lang=lang))


LAUNCH_DATE = datetime(2026, 1, 1, tzinfo=CST).date()


def issue_no(kind, date_iso):
    """期号从上线日（config 里 site.launch_date，main 中覆写 LAUNCH_DATE）起算：
    日报 = 上线天数；周报 = 上线周数；月报 = 上线月数。"""
    d = datetime.strptime(date_iso, "%Y-%m-%d").date()
    days = (d - LAUNCH_DATE).days + 1
    if kind == "daily":
        return days
    if kind == "weekly":
        return days // 7 + 1
    return (d.year - LAUNCH_DATE.year) * 12 + (d.month - LAUNCH_DATE.month) + 1


def render_period(site, kind, report, base="", prev=None, next_=None, canonical="", lang="zh", rel_path=None):
    """日报/周报/月报共用同一模板（B9）：kind 为 daily/weekly/monthly。
    report: {kind, date, date_iso, issue, summary, items}。
    prev/next: (label, href) 或 None。base 是到站根的目录前缀。
    rel_path 默认 kind.html；存档页由调用方传显式值。"""
    if lang == "en":
        labels = {"daily": ("Daily", "past 24 hours", "Today's picks"),
                  "weekly": ("Weekly", "past 7 days", "This week's picks"),
                  "monthly": ("Monthly", "past 30 days", "This month's picks")}
    else:
        labels = {"daily": ("日报", "过去 24 小时", "今日精选"),
                  "weekly": ("周报", "过去 7 天", "本周精选"),
                  "monthly": ("月报", "过去 30 天", "本月精选")}
    name, window, picked = labels[kind]
    if kind == "daily":
        sched_txt = (f"Published daily at {esc(site['edition_time_cst'])}" if lang == "en"
                     else f"每天 {esc(site['edition_time_cst'])} 出刊")
    elif kind == "weekly":
        sched_txt = _L(lang, "过去 7 天滚动精选，每半小时更新", "Rolling 7-day picks, updated every 30 minutes")
    else:
        sched_txt = _L(lang, "过去 30 天滚动精选，每半小时更新", "Rolling 30-day picks, updated every 30 minutes")
    items = [en_view(it) for it in report["items"]] if lang == "en" else report["items"]
    items_html = "".join(feed_item(it, rank=i + 1, base=base, lang=lang)
                         for i, it in enumerate(items)) \
        or (_L(lang, f"<p>{window}没有达到精选门槛的条目。</p>",
               f"<p>No items reached the curation bar in the {window}.</p>"))
    dt = None
    for fmt, val in (("%Y-%m-%d", report.get("date_iso", "")),
                     ("%Y年%m月%d日", report.get("date", "")),
                     ("%B %d, %Y", report.get("date", ""))):
        try:
            dt = datetime.strptime(val, fmt)
            break
        except ValueError:
            continue
    wd = (WEEKDAYS_EN if lang == "en" else WEEKDAYS)[dt.weekday()] if dt else ""
    nav = ""
    if prev or next_:
        pl = (f'<a href="{esc(prev[1])}">← {_L(lang, "上一期", "Previous issue")} · {esc(prev[0])}</a>') if prev else "<span></span>"
        nl = (f'<a class="dn-next" href="{esc(next_[1])}">{_L(lang, "下一期", "Next issue")} · {esc(next_[0])} →</a>') if next_ else ""
        nav = f'<nav class="daily-nav">{pl}{nl}</nav>'
    period_nav = (
        f'<p class="more-note">'
        f'<a href="{base}daily.html">{_L(lang, "日报", "Daily")}</a> · <a href="{base}weekly.html">{_L(lang, "周报", "Weekly")}</a> · '
        f'<a href="{base}monthly.html">{_L(lang, "月报", "Monthly")}</a> · <a href="{base}daily/archive.html">{_L(lang, "往期存档", "Archive")}</a></p>')
    if rel_path is None:
        rel_path = kind + ".html"
    brand = f'{esc(_name(site, lang))} {name}' if lang == "en" else f'{esc(_name(site, lang))}{name}'
    issue_txt = f'Issue No. {report["issue"]}' if lang == "en" else f'第 {report["issue"]} 期'
    meta = (f'{esc(report["date"])} {wd} · {sched_txt} · {len(items)} picks from the {window}'
            if lang == "en" else
            f'{esc(report["date"])} {wd} · {sched_txt} · {window}精选 {len(items)} 条')
    page_title = (f'{_name(site, lang)} {name} · {report["date"]}' if lang == "en"
                  else f'{_name(site, lang)}{name} · {report["date"]}')
    description = report.get("summary") or (site.get("description_en") or site["description"] if lang == "en" else site["description"])
    return (page_open(site, kind, page_title, description,
                      prefix="index.html", base=base,
                      canonical=canonical, ld_items=report["items"], page_cls=" page-reading",
                      lang=lang, rel_path=rel_path)
            + f'<div class="m-title">{name}</div>'
            + f'<div class="report-shell"><div class="masthead"><div class="mp-brand">'
            f'{_logo(44)}<b>{brand}</b><span class="mp-issue">{issue_txt}</span></div>'
            + f'<p class="mp-meta">{meta}</p>{period_nav}</div>'
            + f'<div class="well" style="margin-top:16px"><span class="kicker">{_L(lang, "速览", "At a glance")}</span>'
            f'<p>{esc(report["summary"])}</p></div>'
            + f'<h2 class="sec">{picked}{": " if lang == "en" else " "}{len(items)}{" items" if lang == "en" else " 条"}</h2>'
            + items_html + nav + "</div>"
            + page_close(site, kind, prefix="index.html", base=base, lang=lang))


def render_daily(site, daily, base="", prev=None, next_=None, canonical="", lang="zh", rel_path=None):
    report = dict(daily)
    report.setdefault("kind", "daily")
    report.setdefault("issue", issue_no("daily", daily.get("date_iso", LAUNCH_DATE.isoformat())))
    return render_period(site, "daily", report, base=base, prev=prev, next_=next_,
                         canonical=canonical, lang=lang, rel_path=rel_path)


def render_starred(site, lang="zh"):
    """收藏页（B3）：内容由 JS 从 localStorage 快照 + data/days/ 分块渲染，
    下架条目置灰并提示；导入/导出先不做。"""
    site_url = site.get("url", "")
    empty_state = (
        '<div id="starEmpty" class="empty-state" hidden>'
        f'<div class="empty-icon">{icon("bookmark", 40)}</div>'
        f'<h3 class="empty-title">{_L(lang, "还没有收藏", "No saved items yet.")}</h3>'
        f'<p class="empty-text">{_L(lang, "去点卡片右上角的书签，喜欢的动态就会出现在这里。", "Tap the bookmark on a card and the items you like will show up here.")}</p>'
        '<div class="empty-actions">'
        f'<a class="empty-btn primary" href="index.html">{_L(lang, "去看精选", "See featured")}</a>'
        '</div></div>')
    lede = (_L(lang, "收藏只保存在你的浏览器里（localStorage），换设备不会同步。",
               "Saved items live only in your browser (localStorage) and do not sync across devices.")
            + '<span class="lede-rest">'
            + _L(lang, "点开标题即记已读；下架的条目会置灰保留。",
                 "Opening a title marks it read; removed items stay greyed out.")
            + "</span>")
    title = (f'{site.get("title_en") or site["title"]} · Saved' if lang == "en"
             else f'{site["title"]} · 收藏')
    description = site.get("description_en") or site["description"] if lang == "en" else site["description"]
    return (page_open(site, "starred", title, description, prefix="index.html",
                      canonical=site_url + ("/en/starred.html" if lang == "en" else "/starred.html"),
                      lang=lang, rel_path="starred.html")
            + f'<div class="m-title">{_L(lang, "收藏", "Saved")}</div>'
            + f'<h1>{_L(lang, "收藏", "Saved")}</h1>'
            + f'<p class="lede">{lede}</p>'
            + '<div id="starList"></div>'
            + empty_state
            + page_close(site, "starred", prefix="index.html", lang=lang))


def render_more(site, changelog_version, lang="zh"):
    """“我的”页（B4）：收藏、外观、数据、更新日志、反馈、RSS、关于等入口收在一起。"""
    site_url = site.get("url", "")
    star_row = (
        f'<a class="more-row" href="starred.html">{icon("bookmark", 18)}'
        f'<span class="m-label">{_L(lang, "收藏", "Saved")}</span>'
        f'<span class="m-val"><span id="moreStarCount">0</span> {_L(lang, "条", "items")}</span>'
        f'<span class="m-arrow">›</span></a>')
    theme_seg = (
        f'<div class="more-row" style="cursor:default">{icon("sun", 18)}'
        f'<span class="m-label">{_L(lang, "外观", "Appearance")}</span>'
        f'<span class="theme-seg" role="group" aria-label="{_L(lang, "外观", "Appearance")}">'
        f'<span class="theme-seg-thumb" id="themeSegThumb"></span>'
        f'<button type="button" data-theme-opt="dark">{_L(lang, "深色", "Dark")}</button>'
        f'<button type="button" data-theme-opt="system">{_L(lang, "跟随系统", "System")}</button>'
        f'<button type="button" data-theme-opt="light">{_L(lang, "浅色", "Light")}</button>'
        f'</span></div>')
    data_row = (
        f'<a class="more-row" href="feed.xml">{icon("rss", 18)}'
        f'<span class="m-label">{_L(lang, "RSS 订阅", "RSS Feed")}</span><span class="m-val">feed.xml</span>'
        f'<span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="data/days/index.json">{icon("code", 18)}'
        f'<span class="m-label">{_L(lang, "数据 JSON", "Data JSON")}</span><span class="m-val">{_L(lang, "30 天全量", "Full 30 days")}</span>'
        f'<span class="m-arrow">›</span></a>')
    about_rows = (
        f'<a class="more-row" href="about.html">{icon("rss", 18)}'
        f'<span class="m-label">{_L(lang, "关于 " + site["name"], "About " + _name(site, lang))}</span><span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="changelog.html">{icon("doc", 18)}'
        f'<span class="m-label">{_L(lang, "更新日志", "Changelog")}</span>'
        f'<span class="dot-red" id="changelogDot" data-changelog-version="{esc(changelog_version)}" hidden></span>'
        f'<span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="{site["repo"]}/issues" target="_blank" rel="noopener">{icon("message", 18)}'
        f'<span class="m-label">{_L(lang, "反馈", "Feedback")}</span><span class="m-val">GitHub Issues</span>'
        f'<span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="terms.html">{icon("doc", 18)}'
        f'<span class="m-label">{_L(lang, "条款", "Terms")}</span><span class="m-arrow">›</span></a>'
        f'<a class="more-row" href="privacy.html">{icon("doc", 18)}'
        f'<span class="m-label">{_L(lang, "隐私", "Privacy")}</span><span class="m-arrow">›</span></a>')
    title = (f'{site.get("title_en") or site["title"]} · My' if lang == "en"
             else f'{site["title"]} · 我的')
    description = site.get("description_en") or site["description"] if lang == "en" else site["description"]
    note = (_L(lang, "RSS 用 feed.xml 订阅（精选 20 条，每半小时更新）。",
               "Subscribe to the RSS feed at feed.xml (top 20 featured, updated every 30 minutes).")
            + _L(lang, "想自己拉全量数据：<a href=\"data/days/index.json\">data/days/</a> 按天分块存放最近 30 天的条目，",
                 "For the full data: <a href=\"data/days/index.json\">data/days/</a> holds the last 30 days of items in per-day chunks,")
            + _L(lang, "<a href=\"data/hot.json\">data/hot.json</a> 是今日热点榜 Top 20。",
                 "<a href=\"data/hot.json\">data/hot.json</a> is today's top 20 hot list."))
    return (page_open(site, "more", title, description, prefix="index.html",
                      canonical=site_url + ("/en/more.html" if lang == "en" else "/more.html"),
                      lang=lang, rel_path="more.html")
            + f'<div class="m-title">{_L(lang, "我的", "My")}</div>'
            + f'<h1>{_L(lang, "我的", "My")}</h1>'
            + f'<p class="lede">{_L(lang, "收藏、外观、数据与关于，都在这里。", "Saved items, appearance, data and about — all in one place.")}</p>'
            + f'<section class="more-sec"><h2>{_L(lang, "内容", "Content")}</h2>{star_row}'
            f'<a class="more-row" href="daily/archive.html">{icon("calendar", 18)}'
            f'<span class="m-label">{_L(lang, "往期日报", "Past digests")}</span><span class="m-arrow">›</span></a>'
            f'<a class="more-row" href="weekly.html">{icon("calendar", 18)}'
            f'<span class="m-label">{_L(lang, "周报", "Weekly")}</span><span class="m-arrow">›</span></a>'
            f'<a class="more-row" href="monthly.html">{icon("calendar", 18)}'
            f'<span class="m-label">{_L(lang, "月报", "Monthly")}</span><span class="m-arrow">›</span></a></section>'
            + f'<section class="more-sec"><h2>{_L(lang, "外观", "Appearance")}</h2>{theme_seg}</section>'
            + f'<section class="more-sec"><h2>{_L(lang, "数据与订阅", "Data & subscriptions")}</h2>{data_row}'
            f'<p class="more-note">{note}</p></section>'
            + f'<section class="more-sec"><h2>{_L(lang, "关于本站", "About this site")}</h2>{about_rows}</section>'
            + page_close(site, "more", prefix="index.html", lang=lang))


def render_changelog(site, entries, lang="zh"):
    """更新日志页（B6）：由 data/changelog.json 驱动；打开即记为已读（JS）。
    英文版用条目的 title_en/items_en（缺失时回退中文）。"""
    site_url = site.get("url", "")
    latest = entries[0]["version"] if entries else ""
    items_html = ""
    for e in entries:
        title_e = (e.get("title_en") or e.get("title", "")) if lang == "en" else e.get("title", "")
        items_e = (e.get("items_en") or e.get("items", [])) if lang == "en" else e.get("items", [])
        lis = "".join(f"<li>{esc(x)}</li>" for x in items_e)
        items_html += (
            f'<article class="cl-item"><h3>{esc(title_e)}</h3>'
            f'<p class="cl-date">{esc(e.get("date", ""))}</p>'
            f"<ul>{lis}</ul></article>")
    title = (f'{site.get("title_en") or site["title"]} · Changelog' if lang == "en"
             else f'{site["title"]} · 更新日志')
    description = site.get("description_en") or site["description"] if lang == "en" else site["description"]
    return (page_open(site, "changelog", title, description, prefix="index.html",
                      canonical=site_url + ("/en/changelog.html" if lang == "en" else "/changelog.html"),
                      lang=lang, rel_path="changelog.html")
            + f'<div class="m-title">{_L(lang, "更新日志", "Changelog")}</div>'
            + f'<h1>{_L(lang, "更新日志", "Changelog")}</h1>'
            + f'<p class="lede">{_L(lang, site["name"] + " 每次改版都记在这里。", "Every " + _name(site, lang) + " change is recorded here.")}</p>'
            + f'<div id="changelogPage" data-changelog-version="{esc(latest)}">{items_html}</div>'
            + page_close(site, "changelog", prefix="index.html", lang=lang))


def render_archive(site, daily_entries, weekly_entries, monthly_entries, lang="zh"):
    """往期存档（B8/B9）：日报按月分组；周报、月报各列一组。
    英文版条目（date_short/file）由调用方按英文树准备。"""
    site_url = site.get("url", "")

    def month_groups(entries):
        groups = {}
        for e in entries:
            ym = e["date_iso"][:7]
            groups.setdefault(ym, []).append(e)
        return groups

    def row_html(e):
        issue_txt = f'Issue No. {e["issue"]}' if lang == "en" else f'第 {e["issue"]} 期'
        count_txt = f'{e["count"]} items' if lang == "en" else f'{e["count"]} 条'
        return (f'<li><a href="{esc(e["file"])}"><span class="a-date">{e["date_short"]}</span>'
                f'<span class="a-issue">{issue_txt}</span>'
                f'<span class="a-count">{count_txt}</span></a></li>')

    def daily_section():
        if not daily_entries:
            return _L(lang, "<p>还没有往期日报——从今天开始攒。</p>",
                      "<p>No past digests yet — the collection starts today.</p>")
        out = ""
        for ym in sorted(month_groups(daily_entries), reverse=True):
            y, m = ym.split("-")
            rows = "".join(row_html(e) for e in month_groups(daily_entries)[ym])
            head = f"{MONTHS_EN[int(m) - 1]} {y}" if lang == "en" else f"{y}年{int(m)}月"
            out += (f'<div class="arch-month"><h3>{head}</h3>'
                    f'<ul class="arch-list">{rows}</ul></div>')
        return out

    def period_section(title, entries, label):
        if not entries:
            return ""
        rows = "".join(row_html(e) for e in entries)
        return (f'<div class="arch-month"><h3>{title}</h3>'
                f'<ul class="arch-list">{rows}</ul></div>')

    title = (f'{site.get("title_en") or site["title"]} · Archive' if lang == "en"
             else f'{site["title"]} · 往期存档')
    description = site.get("description_en") or site["description"] if lang == "en" else site["description"]
    if lang == "en":
        lede = "The bound volumes of the daily, weekly and monthly digests."
        if site.get("launch_date"):
            lede += " Issue numbers count from the " + esc(site["launch_date"]) + " launch."
    else:
        lede = "日报、周报、月报的合订本。"
        if site.get("launch_date"):
            lede += "期号从 " + esc(site.get("launch_date", "")) + " 上线日起算。"
    return (page_open(site, "archive", title, description, prefix="index.html", base="../",
                      canonical=site_url + ("/en/daily/archive.html" if lang == "en" else "/daily/archive.html"),
                      lang=lang, rel_path="daily/archive.html")
            + f'<div class="m-title">{_L(lang, "往期存档", "Archive")}</div>'
            + f'<h1>{_L(lang, "往期存档", "Archive")}</h1>'
            + f'<p class="lede">{lede}</p>'
            + f'<h2 class="sec">{_L(lang, "日报", "Daily")}</h2>' + daily_section()
            + period_section(_L(lang, "周报", "Weekly"), weekly_entries, "周报")
            + period_section(_L(lang, "月报", "Monthly"), monthly_entries, "月报")
            + page_close(site, "archive", prefix="index.html", base="../", lang=lang))


def render_topic(site, label, slug, items, lang="zh"):
    """主题页（B11）：某标签下的条目列表。"""
    site_url = site.get("url", "")
    if lang == "en":
        items = [en_view(it) for it in items]
    items_html = "".join(feed_item(it, base="../", lang=lang) for it in items) \
        or _L(lang, "<p>这个标签下暂时没有条目。</p>", "<p>No items under this topic yet.</p>")
    title = (f'{site.get("title_en") or site["title"]} · #{label}' if lang == "en"
             else f'{site["title"]} · #{label}')
    # 主题页描述：每主题唯一，含条目数与头名工具；不用 News/新闻口径
    # （主题页是工具列表，不是新闻聚合）。
    def _disp_title(it):
        return ((it.get("en_title") or it["title"]) if lang == "en"
                else (it.get("zh_title") or it["title"]))
    top_titles = [_disp_title(it) for it in items[:3]]
    if lang == "en":
        description = (f'"{label}" tools you can use right away — {len(items)} tools. '
                       f'Top: {", ".join(top_titles)}.' if items
                       else f'"{label}" tools you can use right away — no tools listed yet.')
    else:
        description = (f"「{label}」主题共收录 {len(items)} 个能直接用的工具："
                       f"{'、'.join(top_titles)}。" if items
                       else f"「{label}」主题：能直接用的工具，暂未收录。")
    description = shorten(description, 160)
    return (page_open(site, "topics", title, description, prefix="index.html", base="../",
                      canonical=site_url + ("/en/topics/" if lang == "en" else "/topics/") + slug + ".html",
                      ld_items=items, lang=lang, rel_path="topics/" + slug + ".html")
            + f'<div class="m-title">#{esc(label)}</div>'
            + f'<h1>#{esc(label)}</h1>'
            + (f'<p class="lede">{len(items)} items · <a href="../topics.html">All topics →</a></p>'
               if lang == "en" else
               f'<p class="lede">共 {len(items)} 条 · <a href="../topics.html">全部主题 →</a></p>')
            + items_html
            + page_close(site, "topics", prefix="index.html", base="../", lang=lang))


def render_topics_index(site, tag_counts, lang="zh"):
    """主题索引（B11）：全部标签 + 条数。"""
    site_url = site.get("url", "")
    rows = "".join(
        f'<a class="more-row" href="topics/{slug}.html">{icon("rss", 18)}'
        f'<span class="m-label">#{esc(label)}</span>'
        f'<span class="m-val">{n} {_L(lang, "条", "items")}</span><span class="m-arrow">›</span></a>'
        for label, slug, n in tag_counts)
    title = (f'{site.get("title_en") or site["title"]} · Topics' if lang == "en"
             else f'{site["title"]} · 主题')
    description = ("Browse tools you can use right away, by topic." if lang == "en"
                   else "按主题浏览能直接用的工具。")
    return (page_open(site, "topics", title, description, prefix="index.html",
                      canonical=site_url + ("/en/topics.html" if lang == "en" else "/topics.html"),
                      lang=lang, rel_path="topics.html")
            + f'<div class="m-title">{_L(lang, "主题", "Topics")}</div>'
            + f'<h1>{_L(lang, "主题", "Topics")}</h1>'
            + f'<p class="lede">{_L(lang, "按标签浏览：点一个标签，看它下面最近 30 天的动态。", "Browse by tag: pick one to see its items from the past 30 days.")}</p>'
            + (f'<section class="more-sec">{rows}</section>' if rows else _L(lang, "<p>暂无标签。</p>", "<p>No topics yet.</p>"))
            + page_close(site, "topics", prefix="index.html", lang=lang))


def render_simple_page(site, active, title, lede, blocks, canonical_path, lang="zh", rel_path=None):
    """静态文案页（B5 关于 / C4 条款与隐私）共用骨架。"""
    site_url = site.get("url", "")
    body = ""
    for h, paras in blocks:
        ps = "".join(f"<p>{p}</p>" for p in paras)
        body += (f'<h2 class="sec">{esc(h)}</h2>' if h else "") + ps
    page_title = (f'{site.get("title_en") or site["title"]} · {title}' if lang == "en"
                  else f'{site["title"]} · {title}')
    description = site.get("description_en") or site["description"] if lang == "en" else site["description"]
    return (page_open(site, active, page_title, description, prefix="index.html",
                      canonical=site_url + ("/en/" if lang == "en" else "/") + canonical_path,
                      lang=lang, rel_path=rel_path or canonical_path)
            + f'<div class="m-title">{esc(title)}</div>'
            + f'<h1>{esc(title)}</h1>'
            + f'<p class="lede">{esc(lede)}</p>'
            + body
            + page_close(site, active, prefix="index.html", lang=lang))


def render_about(site, lang="zh"):
    """关于页：正文段落走 config.json 的 about_blocks / about_blocks_en
    （新站填自己的文案）；mcp_url 非空时追加 MCP 接入段（双语）。"""
    name = _name(site, lang)
    mcp_url = site.get("mcp_url", "")
    if lang == "en":
        audience_en = site.get("audience_en", "")
        blocks = site.get("about_blocks_en") or [
            {"h": "About", "paras": [f"{name} is a hotspot site"
                                     + (f" for {audience_en}." if audience_en else ".")]},
            {"h": "How it works", "paras": [
                "Collect — public RSS sources, fetched every 30 minutes.",
                "Score — rule-based scoring (freshness, relevance, source tier), not AI scoring.",
                "Publish — only titles, summaries and outbound links are shown; full text is never republished."]},
        ]
        pairs = [(b.get("h", ""), b.get("paras", [])) for b in blocks]
        if mcp_url:
            pairs.append(("MCP access", [
                "This site offers an MCP (Model Context Protocol) endpoint so AI clients can check the hot list, "
                "the daily digest, and search recent items — returning only titles, one-line summaries and outbound links.",
                f"Endpoint: <code>{esc(mcp_url)}</code> (Streamable HTTP, no API key).",
                "Three tools: get_hot (current hot list), get_daily (latest daily digest), search_items (search recent items by keyword and category).",
                "All three tools accept a lang argument: Chinese by default, lang=en returns the English version.",
                "In Claude Desktop, for example, add an mcpServers entry to the config file with type http and the endpoint URL above."]))
        return render_simple_page(site, "about", "About",
                                  f"What {name} is, how it works, and who makes it.",
                                  pairs, "about.html", lang=lang)
    audience = site.get("audience", "")
    blocks = site.get("about_blocks") or [
        {"h": "定位", "paras": [f"{name} 是给{audience}看的热点站。"]},
        {"h": "怎么做", "paras": ["采集——公开 RSS 信源，每半小时拉一次。",
                            "打分——规则打分（时效、相关度、来源），不是 AI 打分。",
                            "出报——只展示标题、摘要与原文链接，不转载全文。"]},
    ]
    pairs = [(b.get("h", ""), b.get("paras", [])) for b in blocks]
    if mcp_url:
        pairs.append(("MCP 接入", [
            "本站提供 MCP（Model Context Protocol）接入点，AI 客户端可以直接查热点、日报、搜索最近动态——返回的同样只有标题、一句简介与原文链接。",
            f"端点：<code>{esc(mcp_url)}</code>（Streamable HTTP，无需密钥）。",
            "三个工具：get_hot（当前热点榜）、get_daily（最新一期日报）、search_items（按关键词与分类搜索最近动态）。",
            "三个工具都支持 lang 参数：默认返回中文，lang=en 返回英文版。",
            "以 Claude Desktop 为例，在配置文件里加一个 mcpServers 项，type 填 http，url 填上面这个端点即可。"]))
    return render_simple_page(site, "about", "关于", f"{name} 是什么、怎么做、谁做的。", pairs, "about.html")


def render_terms(site, lang="zh"):
    if lang == "en":
        return render_simple_page(site, "terms", "Terms", "Please read this before using the site.", [
            ("", ["This site aggregates information from public RSS feeds; only titles, summaries and outbound links are shown, and full text is never republished.",
                  "Content belongs to the original authors.",
                  "If anything here is inappropriate or you would like content removed, please contact us via GitHub Issues and we will handle it promptly."]),
        ], "terms.html", lang=lang)
    return render_simple_page(site, "terms", "条款", "使用本站前请先了解这些。", [
        ("", ["本站为信息聚合，内容来自各家公开 RSS；站内只展示标题、摘要与原文链接，不转载全文。",
              "内容版权归原作者所有。",
              "如有内容不妥或希望下架，请通过 GitHub Issues 联系，我们会尽快处理。"]),
    ], "terms.html")


def render_privacy(site, lang="zh"):
    if lang == "en":
        return render_simple_page(site, "privacy", "Privacy", "How this site treats your data.", [
            ("", ["This site does not collect or upload any personal information.",
                  "Saved and read records live only in your own browser (localStorage); clearing browser data clears them."]),
        ], "privacy.html", lang=lang)
    return render_simple_page(site, "privacy", "隐私", "本站如何对待你的数据。", [
        ("", ["本站不收集、不上传任何个人信息。",
              "收藏与已读记录只保存在你自己的浏览器里（localStorage），清除浏览器数据即清除。"]),
    ], "privacy.html")


def render_item(site, it, related, is_selected, daily_issue, lang="zh"):
    """文章详情页（items/<id>.html）：只有标题、一句话简介、来源、评分、理由、标签、
    相关条目——不编造正文，不转载全文，不展示源站摘要或完整摘要原文。
    导读就是本站自己写的一句话简介（zh_oneliner / en_oneliner）；没有简介时
    只显示标题与链接，原文只通过“打开原文”按钮出去。"""
    site_url = site.get("url", "")
    if lang == "en":
        it = en_view(it)
        related = [en_view(r) for r in related]
        title = it.get("en_title") or it["title"]
        orig_title = it["title"] if (it.get("en_title") and it["en_title"] != it["title"]) else ""
        oneliner = it.get("en_oneliner") or ""
    else:
        title = it.get("zh_title") or it["title"]
        orig_title = it["title"] if (it.get("zh_title") and it["zh_title"] != it["title"]) else ""
        oneliner = it.get("zh_oneliner") or ""
    desc = oneliner if oneliner else title
    pub = _pub_dt(it)
    domain = urllib.parse.urlparse(it["link"]).netloc
    canonical = f"{site_url}/{'en/' if lang == 'en' else ''}items/{it['id']}.html"
    mid_name = _L(lang, "精选", "Featured") if is_selected else _L(lang, "全部动态", "All Items")
    if is_selected:
        mid_href = "/en/" if lang == "en" else "/"
    else:
        mid_href = "/en/all.html" if lang == "en" else "/all.html"
    ld_blocks = [
        {"@context": "https://schema.org", "@type": "Article",
         "headline": title, "description": desc,
         "datePublished": pub.astimezone(timezone.utc).isoformat(),
         "dateModified": pub.astimezone(timezone.utc).isoformat(),
         "inLanguage": "en" if lang == "en" else "zh-CN",
         "author": {"@type": "Organization", "name": it["source"]},
         "publisher": {"@type": "Organization", "name": _name(site, lang)},
         "mainEntityOfPage": canonical},
        {"@context": "https://schema.org", "@type": "BreadcrumbList",
         "itemListElement": [
             {"@type": "ListItem", "position": 1, "name": _L(lang, "首页", "Home"),
              "item": site_url + "/"},
             {"@type": "ListItem", "position": 2, "name": mid_name,
              "item": site_url + mid_href},
             {"@type": "ListItem", "position": 3, "name": title,
              "item": canonical}]},
    ]
    meta = (f'<span class="src">{esc(it["source"])}</span>'
            + (f'<span class="off-tag">{_L(lang, "官方", "Official")}</span>' if it.get("tier") == "T1" else "")
            + f'<time>· {esc(fmt_cst_en(pub) if lang == "en" else fmt_cst(pub))}</time>'
            + (f'<span class="pick">{_L(lang, "精选", "Featured")}</span>' if is_selected else "")
            + f'<span class="sp">{score_pill(it["score"], lang)}</span>')
    orig_html = (f'<p class="item-en-title">{_L(lang, "原文标题：", "Original title: ")}{esc(orig_title)}</p>' if orig_title else "")
    # 导读：只显示本站自己写的一句话简介；没有简介时不展示任何源站摘要文字。
    guide_text = oneliner
    reason_html = (f'<section class="item-sec"><h2>{_L(lang, "推荐理由", "Why this matters")}</h2>'
                   f'<p>{esc(it.get("reason", ""))}</p></section>' if it.get("reason") else "")
    tags_html = ""
    tags = it.get("tags") or []
    if tags:
        tags_html = ('<section class="item-sec"><h2>' + _L(lang, "主题", "Topics") + '</h2><div class="fi-tags">' + "".join(
            f'<a class="tag" href="../topics/{TAG_SLUGS_ALL.get(t, t)}.html">#{esc(t)}</a>'
            for t in tags[:3]) + '</div></section>')
    issue_html = ""
    if daily_issue:
        if lang == "en":
            issue_html = (f'<p class="item-source-line">Featured in '
                          f'<a href="../daily/{daily_issue["key"]}.html">Daily digest issue No. {daily_issue["issue"]} '
                          f'({esc(daily_issue["date"])})</a></p>')
        else:
            issue_html = (f'<p class="item-source-line">收录于'
                          f'<a href="../daily/{daily_issue["key"]}.html">日报第 {daily_issue["issue"]} 期'
                          f'（{esc(daily_issue["date"])}）</a></p>')
    related_html = ""
    if related:
        cards = "".join(feed_item(r, base="../", lang=lang) for r in related)
        related_html = (f'<section class="item-sec"><h2>{_L(lang, "相关条目", "Related items")}</h2>'
                        f'<div class="item-related-list">{cards}</div></section>')
    pub_iso = pub.astimezone(timezone.utc).isoformat()
    article_head = (f'<meta property="article:published_time" content="{pub_iso}">\n'
                    f'<meta property="article:modified_time" content="{pub_iso}">\n'
                    f'<meta property="article:author" content="{esc(_name(site, lang))}">\n')
    return (page_open(site, "all", f"{title} · {_name(site, lang)}", desc,
                      prefix="index.html", base="../", canonical=canonical,
                      page_cls=" page-reading", ld_blocks=ld_blocks,
                      og_type="article", extra_head=article_head,
                      lang=lang, rel_path=f"items/{it['id']}.html")
            + f'<article class="item-page" data-item-id="{esc(it["id"])}">'
            + f'<button type="button" class="item-back" id="backBtn" data-home="../index.html">{_L(lang, "← 返回", "← Back")}</button>'
            + f'<div class="item-meta">{meta}</div>'
            + f'<h1 class="item-h1">{esc(title)}</h1>'
            + orig_html
            + f'<div class="well item-guide"><span class="kicker">{_L(lang, "导读", "Summary")}</span>'
            + (f'<p>{esc(guide_text)}</p>' if guide_text else f'<p>{_L(lang, "这条动态暂无简介，点“打开原文”查看。", "No summary for this item yet — open the original to read it.")}</p>')
            + '</div>'
            + reason_html
            + f'<div class="item-actions">'
            f'<a class="item-open-btn" href="{esc(it["link"])}" target="_blank" rel="noopener">{_L(lang, "打开原文 ↗", "Open original ↗")}</a>'
            f'<button type="button" class="item-ghost-btn" id="itemStarBtn" data-id="{esc(it["id"])}" '
            f'data-title="{esc(title)}" data-link="{esc(it["link"])}" data-source="{esc(it["source"])}">'
            f'{icon("bookmark", 16)}<span>{_L(lang, "收藏", "Save")}</span></button>'
            f'<button type="button" class="item-ghost-btn" id="copyLinkBtn">{_L(lang, "复制链接", "Copy link")}</button>'
            f'<button type="button" class="item-ghost-btn" id="shareBtn" hidden>{_L(lang, "分享", "Share")}</button>'
            f'</div>'
            + f'<p class="item-source-line">{_L(lang, "来源：", "Source: ")}<b>{esc(it["source"])}</b> · {esc(domain)}</p>'
            + issue_html
            + tags_html
            + related_html
            + '</article>'
            + page_close(site, "all", prefix="index.html", base="../", lang=lang))


def render_404(site):
    """GitHub Pages 缺页处理：双语独立页（链接用绝对地址，任何缺页路径下都可用）。
    默认显示英文块；存了中文偏好或浏览器语言为 zh 时切中文块。"""
    site_url = site.get("url", "")
    lang_key = _storage_prefix(site) + "-lang"
    boot_404 = ('<script>(function(){try{var p=localStorage.getItem("' + lang_key + '");'
                'var zh=p?p==="zh":(navigator.language||"en").toLowerCase().indexOf("zh")===0;'
                'if(zh){document.getElementById("nf-en").hidden=true;'
                'document.getElementById("nf-zh").hidden=false;'
                'document.documentElement.lang="zh-CN";}}catch(e){}})();</script>')
    return (f"<!DOCTYPE html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">\n"
            f"<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
            f"<title>Page not found · {site.get('name_en') or site['name']}</title>\n"
            f"<meta name=\"description\" content=\"The page you are looking for does not exist.\">\n"
            f'<link rel="icon" type="image/svg+xml" href="{site_url}/favicon.svg">\n'
            f"{theme_boot(site)}<link rel=\"stylesheet\" href=\"{site_url}/assets/site.css\"></head>\n<body>"
            f'<div class="shell"><div class="main"><div class="page page-reading">'
            f'<div class="empty-state" style="margin-top:20vh">'
            f'<div class="empty-icon">{icon("search", 40)}</div>'
            f'<div id="nf-en">'
            f'<h3 class="empty-title">Page not found</h3>'
            f'<p class="empty-text">The link may be wrong, or this item has been removed.</p>'
            f'<div class="empty-actions">'
            f'<a class="empty-btn primary" href="{site_url}/en/index.html">Back to the homepage</a>'
            f'<a class="empty-btn" href="{site_url}/en/hot.html">See the hot list</a>'
            f'</div></div>'
            f'<div id="nf-zh" hidden>'
            f'<h3 class="empty-title">找不到这篇内容</h3>'
            f'<p class="empty-text">链接可能有误，或者这篇内容已经下架。</p>'
            f'<div class="empty-actions">'
            f'<a class="empty-btn primary" href="{site_url}/index.html">回首页</a>'
            f'<a class="empty-btn" href="{site_url}/hot.html">去看热点榜</a>'
            f'</div></div></div></div></div></div>{boot_404}{ANALYTICS}{CLARITY}</body></html>\n')


def render_hot(site, hot, generated_at, counts, cfg, lang="zh"):
    """完整热点榜：No.1 头条大卡 + No.2–3 次卡 + No.4–20 带 Delta 的行 + 方法说明（B1）。"""
    site_url = site.get("url", "")
    if lang == "en":
        hot = [en_view(it) for it in hot]
    sc = cfg["scoring"]
    hero = ""
    subs = ""
    rest = ""
    if hot:
        h0 = hot[0]
        latest = (h0.get("en_oneliner") or "") if lang == "en" else (h0.get("zh_oneliner") or "")
        hero_title = (h0.get("en_title") or h0["title"]) if lang == "en" else (h0.get("zh_title") or h0["title"])
        hero = (
            f'<article class="card hot-hero"><div class="hot-hero-top">'
            f'<span class="no-tag">NO.01</span>{hot_badges(h0, lang)}</div>'
            f'<h2><a href="items/{esc(h0["id"])}.html">'
            f'{esc(hero_title)}</a></h2>'
            f'<p class="hot-hero-meta">{esc(h0["source"])} · {esc(fmt_cst_en(_pub_dt(h0)) if lang == "en" else fmt_cst(_pub_dt(h0)))} · '
            f'{esc(h0["category_label"])}</p>'
            + (f'<p class="hot-hero-latest"><span class="k">{_L(lang, "最新进展", "Latest")}</span>{esc(shorten(latest, 110))}</p>'
               if latest else "")
            + f'<div class="hot-hero-foot"><span class="hot-big"><b class="num">{round(h0["hot_score"])}</b>{_L(lang, "热度", "Heat")}</span>'
            f'{hot_delta_html(h0, lang)}{score_pill(h0["score"], lang)}</div></article>')
    if len(hot) > 1:
        sub_cards = ""
        for i, it in enumerate(hot[1:3], start=2):
            sub_title = (it.get("en_title") or it["title"]) if lang == "en" else (it.get("zh_title") or it["title"])
            sub_cards += (
                f'<article class="card hot-sub"><div class="hot-sub-top">'
                f'<span class="no-tag">NO.{i:02d}</span>{hot_badges(it, lang)}</div>'
                f'<h3><a href="items/{esc(it["id"])}.html">'
                f'{esc(sub_title)}</a></h3>'
                f'<p class="hot-sub-meta">{esc(it["source"])} · {esc(fmt_cst_en(_pub_dt(it)) if lang == "en" else fmt_cst(_pub_dt(it)))}</p>'
                f'<div class="hot-sub-foot"><span class="hot-num"><b class="num">{round(it["hot_score"])}</b> {_L(lang, "热度", "Heat")}</span>'
                f'{hot_delta_html(it, lang)}</div></article>')
        subs = f'<div class="hot-sub-grid">{sub_cards}</div>'
    if len(hot) > 3:
        rows = "".join(hot_row(it, i + 1, pad=True, lang=lang) for i, it in enumerate(hot[3:], start=3))
        rest = (f'<section class="card hot-card" aria-labelledby="hot-rest" style="margin-top:12px">'
                f'<ol class="hot-list">{rows}</ol></section>')
    elif not hot:
        rest = _L(lang, "<p>暂无热点。</p>", "<p>No hot topics yet.</p>")
    rec = sc["recency"]
    kw_all = "、".join(sc["dev_keywords"])
    kw_en = ", ".join(k for k in sc["dev_keywords"] if k.isascii())
    if lang == "en":
        rec_txt = ", ".join(f'+{r["bonus"]} within {r["max_hours"]} hours' for r in rec)
        tier_txt = f'Official sources +{sc["tier_bonus"].get("T1", 0)}'
        if "T3" in sc["tier_bonus"]:
            tier_txt += f'; T3 sources {sc["tier_bonus"]["T3"]}'
        method = (
            f'<section class="well hot-method"><span class="kicker">How is heat calculated?</span>'
            f'<p>Each item is first scored by rules: base {sc["base"]} points; freshness ({rec_txt}); '
            f'{tier_txt}; each topic keyword hit ({kw_en}) '
            f'+{sc["dev_keyword_bonus"]}, capped at +{sc["dev_keyword_cap"]}; each noise keyword {sc["noise_keyword_penalty"]}, '
            f'floor {sc["noise_keyword_floor"]}; total capped at 100. Heat = score × {sc["decay_base"]}'
            f'^days (decaying daily), looking back {sc["hot_days"]} days only. Trends compare with the previous list: '
            f'up 2 or more places counts as rising, down 2 or more as cooling, a 1-place move as steady; '
            f'first-time entries are marked “New”.</p></section>')
    else:
        rec_txt = "、".join(f'{r["max_hours"]} 小时内 +{r["bonus"]}' for r in rec)
        tier_txt = f'官方信源 +{sc["tier_bonus"].get("T1", 0)}'
        if "T3" in sc["tier_bonus"]:
            tier_txt += f'；T3 信源 {sc["tier_bonus"]["T3"]}'
        method = (
            f'<section class="well hot-method"><span class="kicker">热度是怎么算的？</span>'
            f'<p>每条动态先按规则打分：基础 {sc["base"]} 分；新鲜度（{rec_txt}）；'
            f'{tier_txt}；命中主题关键词（{kw_all}）'
            f'每个 +{sc["dev_keyword_bonus"]}、上限 +{sc["dev_keyword_cap"]}；噪音关键词每个 {sc["noise_keyword_penalty"]}、'
            f'下限 {sc["noise_keyword_floor"]}；总分封顶 100 分。热度 = 评分 × {sc["decay_base"]}'
            f'^天数（每天衰减），只看最近 {sc["hot_days"]} 天。趋势对照上一轮榜单：名次上升 2 名以上为上升，'
            f'下降 2 名以上为回落，只挪 1 名算持平；首次上榜标“新”。</p></section>')
    title = (f'{site.get("title_en") or site["title"]} · Hot List' if lang == "en"
             else f'{site["title"]} · 热点榜')
    description = site.get("description_en") or site["description"] if lang == "en" else site["description"]
    lede = (f'Updated {esc(generated_at)} (Beijing time)<span class="lede-rest"> · {counts["total_7d"]} items in the past 7 days · '
            f'Heat decays with the score over time; trends compare with the previous list.</span>'
            if lang == "en" else
            f'更新于 {esc(generated_at)}（北京时间）<span class="lede-rest"> · 最近 7 天共 {counts["total_7d"]} 条 · '
            f'热度按评分随时间衰减，趋势对照上一轮榜单。</span>')
    return (page_open(site, "hot", title, description, prefix="index.html",
                      canonical=site_url + ("/en/hot.html" if lang == "en" else "/hot.html"),
                      ld_items=hot, lang=lang, rel_path="hot.html")
            + f'<div class="m-title">{_L(lang, "热点榜", "Hot List")}</div>'
            + f'<h1>{_L(lang, "热点榜", "Hot List")}</h1>'
            + f'<p class="lede">{lede}</p>'
            + hero + subs + rest + method
            + page_close(site, "hot", prefix="index.html", lang=lang))


def rss_date(dt):
    return dt.astimezone(timezone.utc).strftime("%a, %d %b %Y %H:%M:%S GMT")


def build_feed_xml(site, items, lang="zh"):
    """RSS 2.0（B12）：精选 20 条，每轮都写。"""
    site_url = site.get("url", "")
    now_rfc = rss_date(datetime.now(timezone.utc))
    if lang == "en":
        chan_title = site.get("title_en") or site.get("title", site.get("name", "HOT"))
        chan_desc = site.get("description_en") or site.get("description", "")
        chan_link = site_url + "/en/"
        chan_lang = "en"
    else:
        chan_title = site.get("title", site.get("name", "HOT"))
        chan_desc = site.get("description", "")
        chan_link = site_url + "/"
        chan_lang = "zh-CN"
    items_xml = ""
    for it in items[:20]:
        if lang == "en":
            title = it.get("en_title") or it["title"]
            desc = it.get("en_oneliner") or ""
        else:
            title = it.get("zh_title") or it["title"]
            desc = it.get("zh_oneliner") or ""
        pub = _pub_dt(it)
        items_xml += ("<item><title>" + esc(title) + "</title>"
                      "<link>" + esc(it["link"]) + "</link>"
                      "<description>" + esc(desc) + "</description>"
                      "<pubDate>" + rss_date(pub) + "</pubDate>"
                      "<guid isPermaLink=\"false\">" + esc(it["id"]) + "</guid>"
                      "<source url=\"" + esc(it["link"]) + "\">" + esc(it["source"]) + "</source>"
                      "</item>")
    return ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
            "<rss version=\"2.0\"><channel>"
            "<title>" + esc(chan_title) + "</title>"
            "<link>" + esc(chan_link) + "</link>"
            "<description>" + esc(chan_desc) + "</description>"
            "<language>" + chan_lang + "</language>"
            "<lastBuildDate>" + now_rfc + "</lastBuildDate>"
            + items_xml +
            "</channel></rss>\n")


def load_period_archive(dirpath):
    """读回某类（daily/weekly/monthly）已存档的报告，按 date_iso 倒序。"""
    reports = []
    if not os.path.isdir(dirpath):
        return reports
    for fn in sorted(os.listdir(dirpath)):
        if not fn.endswith(".json"):
            continue
        try:
            r = load_json(os.path.join(dirpath, fn))
            if r.get("date_iso"):
                reports.append(r)
        except (json.JSONDecodeError, KeyError, OSError):
            continue
    reports.sort(key=lambda r: r["date_iso"], reverse=True)
    return reports


# ---------------------------------------------------------------- SEO / GEO
# 搜索引擎与 AI 引用用的生成物：robots.txt、sitemap.xml、llms.txt、geo-audit。
# 全部取自 config.json，不写死任何站名、域名与端点；mirror_url / mcp_url
# 为空时对应行段直接省略，不输出占位 URL。每页 hreflang 写三元组
# （zh-CN + en + x-default，x-default 指向英文树），因为双语版确实有英文页。

def _sitemap_lastmod(sub, fn, default):
    """按存档文件名推算真实 lastmod：daily=YYYY-MM-DD，monthly=当月 1 日，
    weekly=ISO 周的周一；解析失败时用默认值。"""
    stem = fn[:-5] if fn.endswith(".html") else fn
    try:
        if sub == "daily":
            return datetime.strptime(stem, "%Y-%m-%d").strftime("%Y-%m-%d")
        if sub == "monthly":
            return datetime.strptime(stem, "%Y-%m").strftime("%Y-%m-%d")
        if sub == "weekly":
            y, w = stem.split("-W")
            return datetime.fromisocalendar(int(y), int(w), 1).strftime("%Y-%m-%d")
    except (ValueError, AttributeError):
        return default
    return default


def build_robots_txt(site):
    """完整版 robots.txt：明确放行主流 AI 爬虫，禁 Bytespider / PetalBot。

    站名、规范域名、镜像地址全部取自 config.json 的 site 段；
    mirror_url 为空时不写镜像行。
    """
    site_url = site.get("url", "")
    name = site.get("name", "")
    mirror_url = (site.get("mirror_url") or "").rstrip("/")
    allow_bots = ["GPTBot", "ChatGPT-User", "OAI-SearchBot", "ClaudeBot",
                  "Claude-Web", "PerplexityBot", "Perplexity-User",
                  "Google-Extended", "CCBot", "Meta-ExternalAgent",
                  "Applebot-Extended"]
    deny_bots = ["Bytespider", "PetalBot"]
    lines = [f"# {name} — 允许搜索引擎与 AI 爬虫抓取公开内容",
             f"# 规范域名为 {site_url}/"]
    if mirror_url:
        lines.append(f"# 镜像 {mirror_url} 内容相同，请以规范域名为准")
    lines += ["# 给 AI 看的站点说明见 llms.txt（站根 /llms.txt）",
              "",
              "User-agent: *",
              "Allow: /",
              ""]
    for bot in allow_bots:
        lines += [f"User-agent: {bot}", "Allow: /", ""]
    for bot in deny_bots:
        lines += [f"User-agent: {bot}", "Disallow: /", ""]
    lines.append(f"Sitemap: {site_url}/sitemap.xml")
    return "\n".join(lines) + "\n"


def build_llms_txt(site, cats, today_iso, lang="zh"):
    """llms.txt：站点说明 + 机器可读入口 + 分类（分类取自 config.json）。

    介绍段首行取 site.tagline / site.tagline_en（建站时改成新站自己的一句
    话）；其余为通用英文说明，只依赖站名，不依赖任何站点的主题措辞。
    分类行中文版用“label_en / label”，英文版只用 label_en（无 label_en 时
    回退中文 label）。mcp_url 为空时不写 MCP 段，改写纯数据入口段；
    mirror_url 为空时不写 Mirror 行。
    """
    site_url = site.get("url", "")
    name = _name(site, lang)
    mirror_url = (site.get("mirror_url") or "").rstrip("/")
    mcp_url = site.get("mcp_url") or ""
    edition_time = site.get("edition_time_cst", "06:00")
    tz = site.get("timezone", "Asia/Shanghai")
    if lang == "en":
        tagline_en = site.get("tagline_en") or ""
        en_intro = []
        if tagline_en:
            en_intro.append(f"> {tagline_en}")
        en_intro += [
            f"> {name} is a daily curated directory of web tools you can use right in",
            "> the browser. Every day it discovers newly launched tools from Product",
            "> Hunt, Hacker News Show and other tool sources, scores them by rules,",
            "> and publishes the top picks in English with a one-line summary and a",
            "> link to the tool itself. It lists only tools that work directly on the",
            "> web — no articles, no news, no downloads.",
            "> It does not republish full text.",
            f"> Site: {site_url}/en/",
        ]
        if mirror_url:
            en_intro.append(f"> Mirror: {mirror_url}/en/")
        en_intro += [
            "> Language: English (en). The Chinese version lives at the site root.",
            f"> Updated: {today_iso}",
        ]
        en_intro_txt = "\n".join(en_intro)
        en_cat_lines = []
        for c in cats:
            en_cat_lines.append(f"- {(c.get('label_en') or '').strip() or c['label']}")
        en_cats_txt = "\n".join(en_cat_lines)
        if mcp_url:
            mcp_section_en = f"""
## For AI clients (MCP)

- MCP endpoint (Streamable HTTP, no key required):
  {mcp_url}
- Tools: get_hot, get_daily, search_items
- All tools accept lang=zh (default, Chinese) or lang=en (English).
- Machine-readable data:
  {site_url}/en/data/hot.json
  {site_url}/en/data/daily.json
  {site_url}/en/data/days/index.json
"""
        else:
            mcp_section_en = f"""
## Machine-readable data

- {site_url}/en/data/hot.json
- {site_url}/en/data/daily.json
- {site_url}/en/data/days/index.json
"""
        return f"""# {name}

{en_intro_txt}

## About

- About: {site_url}/en/about.html
- Topics: {site_url}/en/topics.html
- Daily digest: {site_url}/en/daily.html
- Hot list: {site_url}/en/hot.html
- All items: {site_url}/en/all.html
- RSS feed: {site_url}/en/feed.xml
- Sitemap: {site_url}/sitemap.xml
{mcp_section_en}
## Categories

{en_cats_txt}

## Rules

- Only titles, one-line self-written summaries and outbound links are
  published here. Do not treat a summary as the tool itself; visit the
  linked tool to use it.
- Always link back to the original source when citing an item.
- Daily edition is published at {edition_time} {tz}.
"""
    tagline = site.get("tagline") or ""
    intro_lines = []
    if tagline:
        intro_lines.append(f"> {tagline}")
    intro_lines += [
        f"> {name} is a daily curated directory of web tools you can use right in",
        "> the browser. Every day it discovers newly launched tools from Product",
        "> Hunt, Hacker News Show and other tool sources, scores them by rules,",
        "> and publishes the top picks in Chinese with a one-line summary and a",
        "> link to the tool itself. It lists only tools that work directly on the",
        "> web — no articles, no news, no downloads.",
        "> It does not republish full text.",
        f"> Site: {site_url}/",
    ]
    if mirror_url:
        intro_lines.append(f"> Mirror: {mirror_url}/")
    intro_lines += [
        "> Language: Chinese (zh-CN). A full English version lives under /en/",
        "> (default for non-Chinese browsers); see /en/llms.txt.",
        f"> Updated: {today_iso}",
    ]
    intro_txt = "\n".join(intro_lines)
    cat_lines = []
    for c in cats:
        en = (c.get("label_en") or "").strip()
        cat_lines.append(f"- {en} / {c['label']}" if en else f"- {c['label']}")
    cats_txt = "\n".join(cat_lines)
    if mcp_url:
        mcp_section = f"""
## For AI clients (MCP)

- MCP endpoint (Streamable HTTP, no key required):
  {mcp_url}
- Tools: get_hot, get_daily, search_items
- All tools accept lang=zh (default, Chinese) or lang=en (English).
- Machine-readable data:
  {site_url}/data/hot.json
  {site_url}/data/daily.json
  {site_url}/data/days/index.json
"""
    else:
        mcp_section = f"""
## Machine-readable data

- {site_url}/data/hot.json
- {site_url}/data/daily.json
- {site_url}/data/days/index.json
"""
    edition_time = site.get("edition_time_cst", "06:00")
    tz = site.get("timezone", "Asia/Shanghai")
    return f"""# {name}

{intro_txt}

## About

- About: {site_url}/about.html
- Topics: {site_url}/topics.html
- Daily digest: {site_url}/daily.html
- Hot list: {site_url}/hot.html
- All items: {site_url}/all.html
- English version: {site_url}/en/
- English llms.txt: {site_url}/en/llms.txt
- SEO/GEO self-check: {site_url}/geo-audit.html
- RSS feed: {site_url}/feed.xml
- Sitemap: {site_url}/sitemap.xml
{mcp_section}
## Categories

{cats_txt}

## Rules

- Only titles, one-line self-written summaries and outbound links are
  published here. Do not treat a summary as the tool itself; visit the
  linked tool to use it.
- Always link back to the original source when citing an item.
- Daily edition is published at {edition_time} {tz}.
"""


def _read_text(path):
    try:
        with open(path, encoding="utf-8") as f:
            return f.read()
    except OSError:
        return ""


def build_geo_audit(site, root, site_url, today_iso):
    """/geo-audit 自检：读磁盘上的生成物，逐项检查，返回 (html, data)。
    MCP 可达性与镜像部署状态在仓库内无法验证，记为 warn，不造假；
    mcp_url / mirror_url 未配置时对应检查记为 warn 并注明未配置。"""
    checks = []

    def _check(key, label, status, detail):
        checks.append({"key": key, "label": label, "status": status,
                       "detail": detail})

    robots = _read_text(os.path.join(root, "robots.txt"))
    if robots and all(b in robots for b in ("GPTBot", "ClaudeBot", "PerplexityBot")):
        _check("robots", "robots.txt 点名放行 AI 爬虫", "pass",
               "已点名放行 GPTBot / ClaudeBot / PerplexityBot 等，含 Sitemap 声明")
    elif robots:
        _check("robots", "robots.txt 点名放行 AI 爬虫", "fail",
               "robots.txt 存在，但未点名放行主流 AI 爬虫")
    else:
        _check("robots", "robots.txt 点名放行 AI 爬虫", "fail", "robots.txt 不存在")

    sitemap = _read_text(os.path.join(root, "sitemap.xml"))
    sm_locs = set(re.findall(r"<loc>([^<]+)</loc>", sitemap)) if sitemap else set()
    html_files = set()
    for _base, _dirs, _files in os.walk(root):
        rel = os.path.relpath(_base, root)
        for _fn in _files:
            if _fn.endswith(".html") and _fn != "404.html":
                # 根目录的搜索引擎验证文件（如 google*.html）不是可索引页面，
                # 不应计入 sitemap 漏页检查（BingSiteAuth.xml 是 .xml，本就不计入）。
                if rel == "." and _fn.startswith("google") and _fn.endswith(".html"):
                    continue
                p = _fn if rel == "." else f"{rel}/{_fn}"
                html_files.add(p)
    # 首页以规范根路径 site_url/ 入 sitemap，等价于磁盘上的 index.html
    # 英文首页以 site_url/en/ 入 sitemap，等价于磁盘上的 en/index.html
    missing = sorted(f"{site_url}/{p}" for p in html_files
                     if f"{site_url}/{p}" not in sm_locs
                     and not (p == "index.html" and f"{site_url}/" in sm_locs)
                     and not (p == "en/index.html" and f"{site_url}/en/" in sm_locs))
    if sitemap and not missing:
        _check("sitemap", "sitemap.xml 条数与漏页", "pass",
               f"共 {len(sm_locs)} 条 URL，磁盘 {len(html_files)} 个 HTML 页全部在列")
    elif sitemap:
        _check("sitemap", "sitemap.xml 条数与漏页", "fail",
               f"共 {len(sm_locs)} 条 URL，漏 {len(missing)} 页："
               + "、".join(missing[:5]) + ("…" if len(missing) > 5 else ""))
    else:
        _check("sitemap", "sitemap.xml 条数与漏页", "fail", "sitemap.xml 不存在")

    llms = _read_text(os.path.join(root, "llms.txt"))
    mcp_url = site.get("mcp_url") or ""
    en_llms = _read_text(os.path.join(root, "en", "llms.txt"))
    if not llms:
        _check("llms", "llms.txt 存在", "fail", "llms.txt 不存在")
    elif mcp_url and mcp_url in llms and en_llms and mcp_url in en_llms:
        _check("llms", "llms.txt 存在", "pass", "中英 llms.txt 已生成，含 MCP 端点与数据 JSON 入口")
    elif mcp_url:
        _check("llms", "llms.txt 存在", "warn", "llms.txt 存在，但未写 MCP 端点或缺英文版")
    elif en_llms:
        _check("llms", "llms.txt 存在", "pass",
               "中英 llms.txt 已生成，含数据 JSON 入口（未配置 MCP 端点）")
    else:
        _check("llms", "llms.txt 存在", "warn", "llms.txt 存在，但缺英文版")

    index_html = _read_text(os.path.join(root, "index.html"))
    en_index_html = _read_text(os.path.join(root, "en", "index.html"))
    if ('rel="canonical"' in index_html and 'hreflang="zh-CN"' in index_html
            and 'hreflang="en"' in index_html
            and 'rel="canonical"' in en_index_html and 'hreflang="zh-CN"' in en_index_html
            and 'hreflang="en"' in en_index_html):
        _check("canonical", "首页 canonical / hreflang", "pass",
               "中英首页 canonical、hreflang=zh-CN/en 与 x-default 齐全")
    else:
        _check("canonical", "首页 canonical / hreflang", "fail",
               "中英首页缺少 canonical 或 hreflang（需下次生成后生效）")
    if ('"@type": "WebSite"' in index_html and '"inLanguage": "zh-CN"' in index_html
            and '"@type": "WebSite"' in en_index_html and '"inLanguage": "en"' in en_index_html):
        _check("jsonld", "首页 JSON-LD（WebSite）", "pass",
               "中英首页 WebSite 结构化数据含 inLanguage（zh-CN / en）")
    elif '"@type": "WebSite"' in index_html:
        _check("jsonld", "首页 JSON-LD（WebSite）", "warn",
               "WebSite 存在，但缺 inLanguage")
    else:
        _check("jsonld", "首页 JSON-LD（WebSite）", "fail", "首页缺少 WebSite 结构化数据")

    def _newest_html(_d):
        if not os.path.isdir(_d):
            return ""
        _htmls = [os.path.join(_d, f) for f in os.listdir(_d) if f.endswith(".html")]
        return max(_htmls, key=os.path.getmtime) if _htmls else ""

    def _item_ok(_h):
        return bool(_h) and '"dateModified"' in _h and '"datePublished"' in _h \
            and 'og:type" content="article"' in _h

    item_html = _read_text(_newest_html(os.path.join(root, "items")))
    en_item_html = _read_text(_newest_html(os.path.join(root, "en", "items")))
    if _item_ok(item_html) and _item_ok(en_item_html):
        _check("item", "详情页 Article（抽查最新 1 篇）", "pass",
               "中英详情页含 datePublished / dateModified，og:type=article")
    elif item_html or en_item_html:
        _check("item", "详情页 Article（抽查最新 1 篇）", "fail",
               "详情页缺 dateModified 或 og:type 不是 article")
    else:
        _check("item", "详情页 Article（抽查最新 1 篇）", "warn", "未找到详情页可抽查")

    if mcp_url:
        _check("mcp", "MCP 端点可达性", "warn",
               f"端点 {mcp_url} 已写入 llms.txt；"
               "本轮未做在线请求，可达性需线上验证")
    else:
        _check("mcp", "MCP 端点可达性", "warn",
               "未配置 MCP 端点（site.mcp_url 为空），llms.txt 不含 MCP 段")
    mirror_url = (site.get("mirror_url") or "").rstrip("/")
    if mirror_url:
        _check("mirror", "镜像站部署", "warn",
               f"镜像 {mirror_url} 的部署状态在仓库内无法验证，"
               "请以托管平台控制台最新部署为准")
    else:
        _check("mirror", "镜像站部署", "warn",
               "未配置镜像（site.mirror_url 为空），跳过此项")
    feed = _read_text(os.path.join(root, "feed.xml"))
    en_feed = _read_text(os.path.join(root, "en", "feed.xml"))
    if feed and "<rss" in feed and "<item>" in feed \
            and en_feed and "<rss" in en_feed and "<item>" in en_feed:
        _check("feed", "feed.xml 正常", "pass",
               f"RSS 2.0 正常，中英各含 {feed.count('<item>')} / {en_feed.count('<item>')} 条")
    else:
        _check("feed", "feed.xml 正常", "fail", "feed.xml 不存在或内容异常")

    n_pass = sum(1 for c in checks if c["status"] == "pass")
    n_warn = sum(1 for c in checks if c["status"] == "warn")
    n_fail = sum(1 for c in checks if c["status"] == "fail")
    data = {"generated_at": today_iso, "site": site_url,
            "summary": {"total": len(checks), "passed": n_pass,
                        "warn": n_warn, "failed": n_fail},
            "checks": checks}
    icon = {"pass": "✅", "warn": "⚠️", "fail": "❌"}
    rows = "".join(
        f'<tr><td>{icon[c["status"]]} {esc(c["label"])}</td>'
        f'<td>{esc(c["detail"])}</td></tr>\n' for c in checks)
    body = (f'<div class="m-title">SEO / GEO 自检</div>'
            f'<h1>{esc(site["name"])} · SEO / GEO 自检</h1>'
            f'<p class="lede">最后检查：{today_iso}（每轮生成后自动刷新；'
            f'通过 {n_pass}/{len(checks)}，警告 {n_warn}，失败 {n_fail}）</p>'
            f'<table class="audit-table"><thead><tr><th>检查项</th><th>结果</th></tr></thead>'
            f'<tbody>{rows}</tbody></table>'
            f'<p class="more-note">数据文件：<a href="data/geo-audit.json">data/geo-audit.json</a>'
            f' · 站点说明：<a href="llms.txt">llms.txt</a>'
            f' · 站点地图：<a href="sitemap.xml">sitemap.xml</a></p>')
    html = (page_open(site, "more", f'{site["title"]} · SEO / GEO 自检',
                      f'{site["name"]} SEO 与 GEO 自检页：robots、sitemap、llms、canonical、'
                      "结构化数据、详情页、MCP 与订阅源的逐项检查结果。",
                      prefix="index.html",
                      canonical=site_url + "/geo-audit.html")
            + body + page_close(site, "more", prefix="index.html"))
    return html, data


# ---------------------------------------------------------------- 主流程

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--daily", action="store_true", help="同时产出当日日报")
    ap.add_argument("--root", default=ROOT)
    args = ap.parse_args()
    root = args.root
    cfg = load_json(os.path.join(root, "config.json"))
    sources = load_json(os.path.join(root, "sources.json"))["sources"]
    site = cfg["site"]
    _crawler = site.get("crawler_name", "HOTBot/1.0")
    _repo = site.get("repo", "")
    UA["User-Agent"] = f"{_crawler} (+{_repo})" if _repo else _crawler
    global LAUNCH_DATE
    _launch = site.get("launch_date", "")
    try:
        if _launch:
            LAUNCH_DATE = datetime.strptime(_launch, "%Y-%m-%d").replace(tzinfo=CST).date()
    except ValueError:
        print(f"launch_date 无效：{_launch}，改用默认 2026-01-01", file=sys.stderr)
    cats = cfg["categories"]
    cat_label = {c["key"]: c["label"] for c in cats}
    cat_label_en = {c["key"]: c.get("label_en") or c["label"] for c in cats}
    sc = cfg["scoring"]
    now = datetime.now(timezone.utc)
    now_cst = now.astimezone(CST)

    def en_date_str(date_iso):
        """date_iso -> 'November 14, 2026'（英文版日报日期格式）。"""
        d = datetime.strptime(date_iso, "%Y-%m-%d").date()
        return f"{MONTHS_EN[d.month - 1]} {d.day}, {d.year}"

    def en_short(date_iso):
        """date_iso -> 'Nov 14'（英文版短日期）。"""
        d = datetime.strptime(date_iso, "%Y-%m-%d").date()
        return f"{MONTHS_SHORT_EN[d.month - 1]} {d.day}"

    data_dir = os.path.join(root, "data")
    os.makedirs(data_dir, exist_ok=True)

    # 历史（增量更新：新条目合并进来，旧条目按时间淘汰，不全量覆盖丢历史）
    # 本地库 data/store.json（不推送；推送清单里没有它）。老版 data/items.json
    # 只在首次迁移时读一次，之后不再读写。
    hist_path = os.path.join(data_dir, "store.json")
    history = {}
    if os.path.exists(hist_path):
        try:
            for it in load_json(hist_path).get("items", []):
                history[it["id"]] = it
        except (json.JSONDecodeError, KeyError):
            print("store.json damaged, starting fresh", file=sys.stderr)
    elif os.path.exists(os.path.join(data_dir, "items.json")):
        try:
            for it in load_json(os.path.join(data_dir, "items.json")).get("items", []):
                history[it["id"]] = it
            print("migrated history from data/items.json to data/store.json")
        except (json.JSONDecodeError, KeyError):
            print("items.json damaged, starting fresh", file=sys.stderr)

    src_by_id = {s["id"]: s for s in sources}
    # 当前信源 = 工具发现渠道；已下线信源（文章/新闻源）的历史条目不再上榜
    kept_sources = set(src_by_id)

    def enrich_store_item(it, fallback=None):
        """给历史条目补上与时间无关的派生字段（B16/B2 供 JS 动态渲染用）：
        信源分级、分类、中文标签。fallback 为单条目的分类提示
        （Ignlab 按其 category 映射），没有时用信源的 category_hint。"""
        it["tier"] = src_by_id.get(it.get("source_id", ""), {}).get("tier", "T2")
        it["category"] = classify(it, cats,
                                  fallback or src_by_id.get(it.get("source_id", ""), {}).get(
                                      "category_hint", "industry"))
        it["category_label"] = cat_label.get(it["category"], it["category"])
        it["tags"] = labels_for(it, cfg)[:3]

    for _it in history.values():  # 老条目回填（以前的 items.json 没有这些字段）
        if "tags" not in _it or "tier" not in _it or "category" not in _it:
            enrich_store_item(_it)
        # 分级跟随 sources.json 实时刷新：改了某源的 tier，历史条目下一轮立即生效，
        # 否则旧条目会一直沿用首次收录时的分级（2026-11-11 把关发现 T3 改完旧条目仍按 T2 打分）
        _it["tier"] = src_by_id.get(_it.get("source_id", ""), {}).get("tier", "T2")

    fetched, failed = 0, []
    resolve_stats = {"ph_ok": 0, "ph_fail": 0, "reddit_ok": 0, "reddit_nolink": 0,
                     "smol_ok": 0, "smol_fail": 0,
                     "backfill": 0, "reattr": 0}
    # 中文翻译（data/zh_draft.json，按规范化链接匹配；每日精选把关时更新草稿，
    # 下一轮生成自动合入并写回 store.json，Actions 重生成也不会丢）
    zh_map = {}
    zh_path = os.path.join(data_dir, "zh_draft.json")
    if os.path.exists(zh_path):
        try:
            zh_map = load_json(zh_path)
            applied = 0
            for it in history.values():
                # 翻译按发布链接（解析后的工具网址）匹配；旧条目没有
                # resolved_link 时回落原始链接
                tr = zh_map.get(norm_link(it.get("resolved_link") or it.get("link", "")))
                if not tr:
                    continue
                if tr.get("zh_title"):
                    it["zh_title"] = tr["zh_title"]
                if tr.get("zh_oneliner"):
                    it["zh_oneliner"] = tr["zh_oneliner"]
                if tr.get("en_title"):
                    it["en_title"] = tr["en_title"]
                if tr.get("en_oneliner"):
                    it["en_oneliner"] = tr["en_oneliner"]
                applied += 1
            if applied:
                print(f"zh: {applied} items matched from zh_draft.json")
        except (json.JSONDecodeError, AttributeError) as e:
            print("zh_draft.json skipped (%s)" % e, file=sys.stderr)
    # 链接反查：发布链接（解析后或原始）-> 历史条目，用于回填与按工具去重
    by_link = {}
    for _h in history.values():
        by_link[norm_link(_h.get("resolved_link") or _h["link"])] = _h
        by_link[norm_link(_h["link"])] = _h
    for src in sources:
        try:
            body = fetch(src["url"])
            if src.get("kind") == "json":
                new_items = JSON_PARSERS.get(src["id"], parse_ignlab)(body, src)
            else:
                new_items = parse_feed(body, src)
        except Exception as e:  # noqa: BLE001 - 单个信源失败不中断整轮
            failed.append((src["id"], str(e)[:80]))
            continue
        fetched += len(new_items)
        for it in new_items:
            pub = it["published"] or now
            it["published"] = pub.astimezone(timezone.utc).isoformat()
            it["id"] = hashlib.sha1(norm_link(it["link"]).encode()).hexdigest()
            # 已收录且已解析过：无需再请求
            _ex0 = history.get(it["id"])
            if (_ex0 is not None and _ex0.get("resolved_link")
                    and _ex0.get("source_id") in kept_sources):
                continue
            # 工具站收录：把链接解析到工具本身（Product Hunt 跟随 /r/p/
            # 跳转；Reddit 取正文里的 [link] 外链；HN Show 直链无需解析）
            # 解析要在去重之前做：旧条目入库时还没解析过链接，回填靠这一轮
            resolved = None
            if src["id"] == "producthunt":
                red = it.get("_redirect", "")
                final = resolve_url(red) if red else None
                if not final:
                    resolve_stats["ph_fail"] += 1
                    continue
                resolved = norm_link(final)
                resolve_stats["ph_ok"] += 1
            elif src["id"].startswith("reddit-"):
                ext = it.get("_ext_link", "")
                if not ext:
                    resolve_stats["reddit_nolink"] += 1
                    continue
                resolved = norm_link(ext)
                resolve_stats["reddit_ok"] += 1
            elif src["id"] == "smollaunch":
                ext = resolve_smollaunch_page(it["link"])
                if not ext:
                    resolve_stats["smol_fail"] += 1
                    continue
                resolved = norm_link(ext)
                resolve_stats["smol_ok"] += 1
            # 已收录同一帖子：只回填解析链接，不重复入库
            if it["id"] in history:
                ex = history[it["id"]]
                if resolved and not ex.get("resolved_link"):
                    ex["resolved_link"] = resolved
                    resolve_stats["backfill"] += 1
                if ex.get("source_id") not in kept_sources:
                    ex["source_id"] = src["id"]
                    ex["source"] = src["name"]
                    ex["tier"] = src_by_id.get(src["id"], {}).get("tier", "T2")
                    resolve_stats["reattr"] += 1
                continue
            # 已收录同一工具（另一帖子先收过）：不重复入库；原条目若来自
            # 已下线信源，改记到当前信源，工具本身不丢
            key = resolved or norm_link(it["link"])
            ex = by_link.get(key)
            if ex is not None:
                if resolved and not ex.get("resolved_link"):
                    ex["resolved_link"] = resolved
                    resolve_stats["backfill"] += 1
                if ex.get("source_id") not in kept_sources:
                    ex["source_id"] = src["id"]
                    ex["source"] = src["name"]
                    ex["tier"] = src_by_id.get(src["id"], {}).get("tier", "T2")
                    resolve_stats["reattr"] += 1
                continue
            entry = {
                "id": it["id"], "title": it["title"], "link": it["link"],
                "source": it["source"], "source_id": it["source_id"],
                "published": it["published"], "summary": it["summary"],
                "fetched_at": now.isoformat(),
            }
            if resolved:
                entry["resolved_link"] = resolved
            if it.get("summary_full"):
                entry["summary_full"] = it["summary_full"]
            enrich_store_item(entry, it.get("_cat_hint"))
            history[it["id"]] = entry
            by_link[key] = entry
            by_link[norm_link(it["link"])] = entry
    # 淘汰超过 history_days 的旧条目
    cutoff_hist = now - timedelta(days=sc["history_days"])
    history = {k: v for k, v in history.items()
               if datetime.fromisoformat(v["published"]) >= cutoff_hist}
    save_json(hist_path, {"updated_at": now.isoformat(), "items": list(history.values())})
    print(f"resolve: ph_ok {resolve_stats['ph_ok']} ph_fail {resolve_stats['ph_fail']} "
          f"reddit_ok {resolve_stats['reddit_ok']} reddit_nolink {resolve_stats['reddit_nolink']} "
          f"smol_ok {resolve_stats['smol_ok']} smol_fail {resolve_stats['smol_fail']} "
          f"backfill {resolve_stats['backfill']} reattr {resolve_stats['reattr']}")

    # 进榜前实测（方案 B）：新到、过机械门的条目先实测一次链接网站本身，
    # 验不过的本轮不上榜；老条目不追溯。实测失败不中断整轮（机械门 +
    # 人工抽查仍在，下一轮再验）。
    verify_cache = load_verify_cache(data_dir, now)
    try:
        verify_stats = run_verify_phase(history, kept_sources, verify_cache, now, data_dir)
        print(f"verify: probed {verify_stats['probed']} pass {verify_stats['pass']} "
              f"fail {verify_stats['fail']} unknown {verify_stats['unknown']}")
        for _l, _r in verify_stats["fails"]:
            print(f"  verify fail: {_l} [{_r}]")
    except Exception as e:  # noqa: BLE001 - 实测异常不中断整轮
        print(f"verify phase failed ({e}); continuing without new checks",
              file=sys.stderr)
        verify_stats = {"probed": 0, "pass": 0, "fail": 0, "unknown": 0, "fails": []}

    # 分类与打分（在内存里算，不写回历史文件，保持历史干净）
    gate_stats = {}
    live = []
    for it in history.values():
        pub = datetime.fromisoformat(it["published"])
        if pub.tzinfo is None:
            pub = pub.replace(tzinfo=timezone.utc)
        item = dict(it)
        # 只收工具发现渠道的条目：已下线文章/新闻源的历史条目不再上榜
        # （域名门拦不住个人博客与小众新闻站的长尾，源头上断掉才干净）
        if it.get("source_id") not in kept_sources:
            gate_stats["dropped_source"] = gate_stats.get("dropped_source", 0) + 1
            continue
        # 工具站收录门：按解析后的目标链接判定（历史条目同样过门；
        # Product Hunt 旧条目仍是 products/* 目录页、Reddit 旧条目仍是
        # 帖子链接，都会被拦下，不会再上榜）
        if it.get("resolved_link"):
            item["link"] = it["resolved_link"]
        ok, why = tool_gate(item["link"])
        if not ok:
            gate_stats[why] = gate_stats.get(why, 0) + 1
            continue
        # 标题关：标题透露出要下载安装（桌面/手机应用、自托管、扩展、
        # 下载页）的不要；工具必须完全在网站上就能用
        ok, why = title_gate(item.get("title", ""), item.get("zh_title", ""))
        if not ok:
            gate_stats[why] = gate_stats.get(why, 0) + 1
            continue
        # 简介关：信源简介透露出要下载安装的不要（标题不露痕迹、首页
        # 实测也够不着的一类，见 summary_gate；2026-11-25 Ileta 泄漏）
        ok, why = summary_gate(item.get("summary", ""),
                               item.get("summary_full", ""))
        if not ok:
            gate_stats[why] = gate_stats.get(why, 0) + 1
            continue
        # 实测关（方案 B）：缓存里 fail / unknown（未验出）的本轮不上榜；
        # 无缓存记录的老条目（功能上线前入库）不受影响，照常上榜
        vent = verify_cache["items"].get(norm_link(item["link"]))
        if vent is not None:
            if vent.get("status") == "fail":
                gate_stats["verify_fail"] = gate_stats.get("verify_fail", 0) + 1
                continue
            if vent.get("status") == "unknown":
                gate_stats["verify_unknown"] = gate_stats.get("verify_unknown", 0) + 1
                continue
        gate_stats["pass"] = gate_stats.get("pass", 0) + 1
        item["_pub"] = pub
        item["_tier"] = it.get("tier") or src_by_id.get(it["source_id"], {}).get("tier", "T2")
        item["category"] = it.get("category") or classify(
            item, cats, src_by_id.get(it["source_id"], {}).get("category_hint", "industry"))
        item["category_label"] = cat_label.get(item["category"], item["category"])
        item["tags"] = it.get("tags") or labels_for(item, cfg)[:3]
        item["score"] = score(item, cfg, now)
        item["reason"] = reason_for(item, cfg, now)
        item["category_label_en"] = cat_label_en.get(item["category"], item["category"])
        item["tags_en"] = labels_for_en(item, cfg)[:3]
        item["reason_en"] = reason_for_en(item, cfg, now)
        # 当日新到：今天首次被本站收录，且本身也是 24 小时内发布的
        # （只按收录日期会把建站日批量回填的旧文也标上“新”）
        fa = it.get("fetched_at")
        is_new = False
        if fa:
            try:
                fdt = datetime.fromisoformat(fa)
                if fdt.tzinfo is None:
                    fdt = fdt.replace(tzinfo=timezone.utc)
                is_new = (fdt.astimezone(CST).date() == now_cst.date()
                          and (now - item["_pub"]) <= timedelta(hours=24))
            except ValueError:
                pass
        item["is_new"] = is_new
        live.append(item)

    _rej = {k: v for k, v in gate_stats.items() if k != "pass"}
    print(f"gate: pass {gate_stats.get('pass', 0)} / rejected {sum(_rej.values())} "
          f"({', '.join(f'{k} {v}' for k, v in sorted(_rej.items())) or 'none'})")

    # 可选 LLM 重排（无 Key 时直接跳过）
    live.sort(key=lambda x: x["score"], reverse=True)
    live = maybe_llm_rerank(live, site)

    recent_48h = [it for it in live if (now - it["_pub"]) <= timedelta(hours=sc["selected_hours"])]
    selected = [it for it in recent_48h if it["score"] >= sc["selected_min"]]
    selected.sort(key=lambda x: x["score"], reverse=True)
    selected = dedup_topics(selected)[:sc["daily_top"]]

    last_7d = [it for it in live if (now - it["_pub"]) <= timedelta(days=sc["hot_days"])]
    for it in last_7d:
        age_days = (now - it["_pub"]).total_seconds() / 86400.0
        it["hot_score"] = round(it["score"] * (sc["decay_base"] ** age_days), 1)
    hot = dedup_topics(sorted(last_7d, key=lambda x: x["hot_score"], reverse=True))[:sc["hot_top"]]
    timeline = sorted(last_7d, key=lambda x: x["_pub"], reverse=True)[:sc["timeline_max"]]

    # 趋势：对照上一轮已发布的榜单名次与热度（读旧 data/hot.json，写新文件之前）
    prev_ranks = {}
    prev_scores = {}
    old_hot_path = os.path.join(data_dir, "hot.json")
    if os.path.exists(old_hot_path):
        try:
            for i, h in enumerate(load_json(old_hot_path).get("hot", [])):
                prev_ranks[h["id"]] = i + 1
                prev_scores[h["id"]] = h.get("hot_score")
        except (json.JSONDecodeError, KeyError):
            pass
    for i, it in enumerate(hot):
        r = i + 1
        prev = prev_ranks.get(it["id"])
        it["prev_rank"] = prev
        it["prev_hot_score"] = prev_scores.get(it["id"])
        if prev is None:
            it["trend"] = "new"
        elif prev - r >= 2:
            it["trend"] = "up"
        elif r - prev >= 2:
            it["trend"] = "down"
        else:
            it["trend"] = "same"  # 只挪 1 名算持平，免得 4 小时一轮的抖动全画成箭头

    def pub_item(it):
        return {"id": it["id"], "title": it["title"], "link": it["link"],
                "source": it["source"], "source_id": it["source_id"],
                "published": it["published"],
                "zh_title": it.get("zh_title", ""),
                "zh_oneliner": it.get("zh_oneliner", ""),
                "category": it["category"], "category_label": it["category_label"],
                "tier": it.get("_tier", "T2"), "tags": it.get("tags", []),
                "score": it["score"],
                "reason": it.get("reason", ""), "is_new": bool(it.get("is_new", False)),
                "trend": it.get("trend", "same"),
                "hot_score": it.get("hot_score", it["score"]),
                "prev_rank": it.get("prev_rank"),
                "prev_hot_score": it.get("prev_hot_score")}

    def pub_item_en(it):
        """pub_item 的英文版：en_* 字段替代 zh_*，理由/分类/标签用英文版。
        公开数据文件里不带任何中文翻译字段。"""
        return {"id": it["id"], "title": it["title"], "link": it["link"],
                "source": it["source"], "source_id": it["source_id"],
                "published": it["published"],
                "en_title": it.get("en_title", ""),
                "en_oneliner": it.get("en_oneliner", ""),
                "category": it["category"],
                "category_label": it.get("category_label_en", it["category"]),
                "tier": it.get("_tier", "T2"), "tags": it.get("tags_en", []),
                "score": it["score"],
                "reason": it.get("reason_en", ""), "is_new": bool(it.get("is_new", False)),
                "trend": it.get("trend", "same"),
                "hot_score": it.get("hot_score", it["score"]),
                "prev_rank": it.get("prev_rank"),
                "prev_hot_score": it.get("prev_hot_score")}

    gen_cst = now_cst.strftime("%Y年%m月%d日 %H:%M")
    gen_cst_en = fmt_gen_en(now_cst)
    # hot.json 只写最终发布的热点榜 Top 20（7 天候选只在内存里，不落盘）
    hot_data = {
        "generated_at": now.isoformat(),
        "generated_at_cst": gen_cst,
        "counts": {"total_7d": len(last_7d), "selected": len(selected),
                   "hot": len(hot), "timeline": len(timeline)},
        "hot": [pub_item(it) for it in hot],
    }
    save_json(os.path.join(data_dir, "hot.json"), hot_data, compact=True)
    # 英文版 hot.json（en/data/）：同一批榜单，英文标题/简介/理由/标签
    en_root = os.path.join(root, "en")
    en_data_dir = os.path.join(en_root, "data")
    os.makedirs(en_data_dir, exist_ok=True)
    hot_data_en = {
        "generated_at": now.isoformat(),
        "generated_at_cst": gen_cst_en,
        "counts": hot_data["counts"],
        "hot": [pub_item_en(it) for it in hot],
    }
    save_json(os.path.join(en_data_dir, "hot.json"), hot_data_en, compact=True)

    # 客户端数据按天分块（data/days/）：首页分页与搜索按需取，不再发 30 天全量文件
    def chunk_item(it):
        return {"id": it["id"], "title": it["title"],
                "zh_title": it.get("zh_title", ""),
                "zh_oneliner": it.get("zh_oneliner", ""),
                "link": it["link"], "source": it["source"],
                "source_id": it.get("source_id", ""),
                "published": it["published"],
                "score": it["score"], "tags": it.get("tags", []),
                "tier": it.get("_tier", "T2"), "category": it["category"],
                "category_label": it["category_label"]}

    def chunk_item_en(it):
        """chunk_item 的英文版：en_* 字段替代 zh_*，理由不进分块（JS 现算）。"""
        return {"id": it["id"], "title": it["title"],
                "en_title": it.get("en_title", ""),
                "en_oneliner": it.get("en_oneliner", ""),
                "link": it["link"], "source": it["source"],
                "source_id": it.get("source_id", ""),
                "published": it["published"],
                "score": it["score"], "tags": it.get("tags_en", []),
                "tier": it.get("_tier", "T2"), "category": it["category"],
                "category_label": it.get("category_label_en", it["category"])}
    days_dir = os.path.join(data_dir, "days")
    os.makedirs(days_dir, exist_ok=True)
    by_day = {}
    for it in live:
        d = it["_pub"].astimezone(CST).date().isoformat()
        by_day.setdefault(d, []).append(it)
    day_index = []
    for d in sorted(by_day, reverse=True):
        items = sorted(by_day[d], key=lambda x: x["_pub"], reverse=True)
        save_json(os.path.join(days_dir, d + ".json"),
                  {"date": d, "items": [chunk_item(it) for it in items]},
                  compact=True)
        day_index.append({"date": d, "count": len(items)})
    save_json(os.path.join(days_dir, "index.json"),
              {"updated_at": now.isoformat(), "days": day_index}, compact=True)
    # 清掉已出 30 天窗口的旧分块（index.json 不再列出它们）
    for fn in os.listdir(days_dir):
        if fn.endswith(".json") and fn != "index.json" and fn[:-5] not in by_day:
            os.remove(os.path.join(days_dir, fn))
    print(f"days: {len(day_index)} day files, "
          f"{sum(x['count'] for x in day_index)} items")
    # 英文版按天分块（en/data/days/）：与中文同一批条目，英文数据
    en_days_dir = os.path.join(en_data_dir, "days")
    os.makedirs(en_days_dir, exist_ok=True)
    en_day_index = []
    for d in sorted(by_day, reverse=True):
        items = sorted(by_day[d], key=lambda x: x["_pub"], reverse=True)
        save_json(os.path.join(en_days_dir, d + ".json"),
                  {"date": d, "items": [chunk_item_en(it) for it in items]},
                  compact=True)
        en_day_index.append({"date": d, "count": len(items)})
    save_json(os.path.join(en_days_dir, "index.json"),
              {"updated_at": now.isoformat(), "days": en_day_index}, compact=True)
    for fn in os.listdir(en_days_dir):
        if fn.endswith(".json") and fn != "index.json" and fn[:-5] not in by_day:
            os.remove(os.path.join(en_days_dir, fn))
    print(f"en days: {len(en_day_index)} day files")

    # 共享 CSS/JS 外置（assets/）：每页改引相对路径，不再内嵌整份
    assets_dir = os.path.join(root, "assets")
    os.makedirs(assets_dir, exist_ok=True)
    with open(os.path.join(assets_dir, "site.css"), "w", encoding="utf-8") as f:
        f.write(CSS)
    with open(os.path.join(assets_dir, "site.js"), "w", encoding="utf-8") as f:
        f.write(script_js(site))
    # 英文树 assets/：CSS 与中文同一份字节，JS 用英文版（同样做 slug 替换），
    # favicon 相同；赞赏二维码图片按 tips 配置原样复制（同一批图片）
    en_assets_dir = os.path.join(en_root, "assets")
    os.makedirs(en_assets_dir, exist_ok=True)
    with open(os.path.join(en_assets_dir, "site.css"), "w", encoding="utf-8") as f:
        f.write(CSS)
    with open(os.path.join(en_assets_dir, "site.js"), "w", encoding="utf-8") as f:
        f.write(script_js_en(site))
    with open(os.path.join(en_root, "favicon.svg"), "w", encoding="utf-8") as f:
        f.write(LOGO_SVG)
    for _tip in (site.get("tips") or []):
        _img = _tip.get("image", "")
        if _img.startswith("assets/"):
            _qr_src = os.path.join(root, _img)
            _qr_dst = os.path.join(en_root, _img)
            if os.path.exists(_qr_src):
                os.makedirs(os.path.dirname(_qr_dst), exist_ok=True)
                shutil.copyfile(_qr_src, _qr_dst)
    site_url = site.get("url", "")

    # 主页与热点榜
    with open(os.path.join(root, "index.html"), "w", encoding="utf-8") as f:
        f.write(render_index(site, cats, cfg, src_by_id, selected, hot, timeline,
                             gen_cst, hot_data["counts"]))
    # 全部动态页（对标 AIHOT /all）：30 天全量按时间倒序
    with open(os.path.join(root, "all.html"), "w", encoding="utf-8") as f:
        f.write(render_all(site, cats, cfg, src_by_id, selected, hot,
                           sorted(live, key=lambda x: x["_pub"], reverse=True),
                           gen_cst))
    with open(os.path.join(root, "hot.html"), "w", encoding="utf-8") as f:
        f.write(render_hot(site, hot, gen_cst, hot_data["counts"], cfg))
    # 英文版主页 / 全部动态 / 热点榜
    with open(os.path.join(en_root, "index.html"), "w", encoding="utf-8") as f:
        f.write(render_index(site, cats, cfg, src_by_id, selected, hot, timeline,
                             gen_cst_en, hot_data["counts"], lang="en"))
    with open(os.path.join(en_root, "all.html"), "w", encoding="utf-8") as f:
        f.write(render_all(site, cats, cfg, src_by_id, selected, hot,
                           sorted(live, key=lambda x: x["_pub"], reverse=True),
                           gen_cst_en, lang="en"))
    with open(os.path.join(en_root, "hot.html"), "w", encoding="utf-8") as f:
        f.write(render_hot(site, hot, gen_cst_en, hot_data["counts"], cfg, lang="en"))

    # 静态页：收藏 / 我的 / 更新日志 / 关于 / 条款 / 隐私（每轮都重写，内容不依赖抓取）
    changelog = []
    changelog_path = os.path.join(data_dir, "changelog.json")
    if os.path.exists(changelog_path):
        try:
            changelog = load_json(changelog_path).get("entries", [])
        except (json.JSONDecodeError, AttributeError):
            changelog = []
    changelog_version = changelog[0]["version"] if changelog else ""
    with open(os.path.join(root, "starred.html"), "w", encoding="utf-8") as f:
        f.write(render_starred(site))
    with open(os.path.join(root, "more.html"), "w", encoding="utf-8") as f:
        f.write(render_more(site, changelog_version))
    with open(os.path.join(root, "changelog.html"), "w", encoding="utf-8") as f:
        f.write(render_changelog(site, changelog))
    with open(os.path.join(root, "about.html"), "w", encoding="utf-8") as f:
        f.write(render_about(site))
    with open(os.path.join(root, "terms.html"), "w", encoding="utf-8") as f:
        f.write(render_terms(site))
    with open(os.path.join(root, "privacy.html"), "w", encoding="utf-8") as f:
        f.write(render_privacy(site))
    with open(os.path.join(root, "404.html"), "w", encoding="utf-8") as f:
        f.write(render_404(site))
    # 英文版静态页（404 只有站根一份双语版，不进 en/ 树）
    with open(os.path.join(en_root, "starred.html"), "w", encoding="utf-8") as f:
        f.write(render_starred(site, lang="en"))
    with open(os.path.join(en_root, "more.html"), "w", encoding="utf-8") as f:
        f.write(render_more(site, changelog_version, lang="en"))
    with open(os.path.join(en_root, "changelog.html"), "w", encoding="utf-8") as f:
        f.write(render_changelog(site, changelog, lang="en"))
    with open(os.path.join(en_root, "about.html"), "w", encoding="utf-8") as f:
        f.write(render_about(site, lang="en"))
    with open(os.path.join(en_root, "terms.html"), "w", encoding="utf-8") as f:
        f.write(render_terms(site, lang="en"))
    with open(os.path.join(en_root, "privacy.html"), "w", encoding="utf-8") as f:
        f.write(render_privacy(site, lang="en"))

    # 主题页（B11）：按标签从 30 天全量里取条目，每标签一页 + 索引页
    tag_items = {}
    for it in live:
        for t in it.get("tags", []):
            tag_items.setdefault(t, []).append(it)
    tag_counts = []
    topics_dir = os.path.join(root, "topics")
    os.makedirs(topics_dir, exist_ok=True)
    for label in sorted(tag_items, key=lambda l: -len(tag_items[l])):
        items = sorted(tag_items[label], key=lambda x: x["_pub"], reverse=True)[:50]
        slug = TAG_SLUGS.get(label, label)
        tag_counts.append((label, slug, len(tag_items[label])))
        with open(os.path.join(topics_dir, slug + ".html"), "w", encoding="utf-8") as f:
            f.write(render_topic(site, label, slug, [pub_item(it) for it in items]))
    # 清理过期主题页：标签集合随映射变化，旧 slug 文件不删会残留，
    # sitemap 只列当前页，geo-audit 会把残留文件判为漏页
    _keep = {s + ".html" for _, s, _ in tag_counts}
    for _fn in os.listdir(topics_dir):
        if _fn.endswith(".html") and _fn not in _keep:
            os.remove(os.path.join(topics_dir, _fn))
    with open(os.path.join(root, "topics.html"), "w", encoding="utf-8") as f:
        f.write(render_topics_index(site, tag_counts))
    # 英文版主题页：同一批 slug，英文标签
    tag_items_en = {}
    for it in live:
        for t in it.get("tags_en", []):
            tag_items_en.setdefault(t, []).append(it)
    tag_counts_en = []
    en_topics_dir = os.path.join(en_root, "topics")
    os.makedirs(en_topics_dir, exist_ok=True)
    for label in sorted(tag_items_en, key=lambda l: -len(tag_items_en[l])):
        items = sorted(tag_items_en[label], key=lambda x: x["_pub"], reverse=True)[:50]
        slug = TAG_SLUGS_EN.get(label, label)
        tag_counts_en.append((label, slug, len(tag_items_en[label])))
        with open(os.path.join(en_topics_dir, slug + ".html"), "w", encoding="utf-8") as f:
            f.write(render_topic(site, label, slug, [pub_item_en(it) for it in items], lang="en"))
    _keep_en = {s + ".html" for _, s, _ in tag_counts_en}
    for _fn in os.listdir(en_topics_dir):
        if _fn.endswith(".html") and _fn not in _keep_en:
            os.remove(os.path.join(en_topics_dir, _fn))
    with open(os.path.join(en_root, "topics.html"), "w", encoding="utf-8") as f:
        f.write(render_topics_index(site, tag_counts_en, lang="en"))

    # RSS / robots / sitemap / favicon（C5；每轮都写）
    feed_items = sorted(recent_48h, key=lambda x: x["score"], reverse=True)[:20]
    with open(os.path.join(root, "feed.xml"), "w", encoding="utf-8") as f:
        f.write(build_feed_xml(site, [pub_item(it) for it in feed_items]))
    with open(os.path.join(en_root, "feed.xml"), "w", encoding="utf-8") as f:
        f.write(build_feed_xml(site, [pub_item_en(it) for it in feed_items], lang="en"))
    # robots.txt（SEO/GEO：明确放行 AI 爬虫，禁高频低价值抓取；llms.txt 见下方）
    with open(os.path.join(root, "robots.txt"), "w", encoding="utf-8") as f:
        f.write(build_robots_txt(site))
    with open(os.path.join(root, "favicon.svg"), "w", encoding="utf-8") as f:
        f.write(LOGO_SVG)
    # sitemap.xml：真实 lastmod + 全量页面（历史 + 本轮 live + 磁盘已有详情页/存档页）
    today_iso = now_cst.strftime("%Y-%m-%d")
    sitemap_entries = {}

    def _add_sitemap(path, lastmod):
        # 空字符串是首页（规范根路径 /），必须入 sitemap，不能被真值判断丢掉
        if path != "404.html" and path not in sitemap_entries:
            sitemap_entries[path] = lastmod or today_iso

    for _p in ["", "all.html", "hot.html", "daily.html", "weekly.html", "monthly.html",
               "starred.html", "more.html", "changelog.html", "about.html",
               "terms.html", "privacy.html", "topics.html",
               "daily/archive.html", "feed.xml", "geo-audit.html"]:
        _add_sitemap(_p, today_iso)
    for _l, slug, _n in tag_counts:
        _add_sitemap("topics/" + slug + ".html", today_iso)
    _pub_dates = {}
    for _it in live:
        _pub_dates[_it["id"]] = _it["_pub"].astimezone(CST).date().isoformat()
    for _it_id, _it in history.items():
        _pub_dates.setdefault(_it_id, (_it.get("published") or "")[:10] or today_iso)
    for _it_id in [_it["id"] for _it in live]:
        _add_sitemap("items/" + _it_id + ".html", _pub_dates.get(_it_id, today_iso))
    for _sub in ("daily", "weekly", "monthly"):
        _sub_dir = os.path.join(root, _sub)
        if os.path.isdir(_sub_dir):
            for _fn in sorted(os.listdir(_sub_dir)):
                if _fn.endswith(".html"):
                    _add_sitemap(f"{_sub}/{_fn}",
                                 _sitemap_lastmod(_sub, _fn, today_iso))
    _items_dir = os.path.join(root, "items")
    if os.path.isdir(_items_dir):
        for _fn in sorted(os.listdir(_items_dir)):
            if _fn.endswith(".html"):
                _add_sitemap("items/" + _fn, _pub_dates.get(_fn[:-5], today_iso))
    # 英文树 sitemap：中文条目之后追加，顺序与中文一致；英文首页以 en/ 入站
    for _p in ["en/", "en/all.html", "en/hot.html", "en/daily.html", "en/weekly.html",
               "en/monthly.html", "en/starred.html", "en/more.html",
               "en/changelog.html", "en/about.html", "en/terms.html",
               "en/privacy.html", "en/topics.html", "en/daily/archive.html",
               "en/feed.xml"]:
        _add_sitemap(_p, today_iso)
    for _l, slug, _n in tag_counts_en:
        _add_sitemap("en/topics/" + slug + ".html", today_iso)
    for _it_id in [_it["id"] for _it in live]:
        _add_sitemap("en/items/" + _it_id + ".html", _pub_dates.get(_it_id, today_iso))
    for _sub in ("daily", "weekly", "monthly"):
        _sub_dir = os.path.join(en_root, _sub)
        if os.path.isdir(_sub_dir):
            for _fn in sorted(os.listdir(_sub_dir)):
                if _fn.endswith(".html"):
                    _add_sitemap(f"en/{_sub}/{_fn}",
                                 _sitemap_lastmod(_sub, _fn, today_iso))
    _en_items_dir = os.path.join(en_root, "items")
    if os.path.isdir(_en_items_dir):
        for _fn in sorted(os.listdir(_en_items_dir)):
            if _fn.endswith(".html"):
                _add_sitemap("en/items/" + _fn, _pub_dates.get(_fn[:-5], today_iso))
    sm = ["<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
          "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\">"]
    for _p, _lm in sitemap_entries.items():
        sm.append(f"<url><loc>{site_url}/{_p}</loc><lastmod>{_lm}</lastmod></url>")
    sm.append("</urlset>")
    with open(os.path.join(root, "sitemap.xml"), "w", encoding="utf-8") as f:
        f.write("\n".join(sm) + "\n")
    # llms.txt：每轮重写，给 AI 客户端的站点说明 + 机器可读入口
    with open(os.path.join(root, "llms.txt"), "w", encoding="utf-8") as f:
        f.write(build_llms_txt(site, cats, today_iso))
    with open(os.path.join(en_root, "llms.txt"), "w", encoding="utf-8") as f:
        f.write(build_llms_txt(site, cats, today_iso, lang="en"))
    print(f"fetch: {fetched} items parsed from {len(sources) - len(failed)}/{len(sources)} sources"
          + (f"; failed: {failed}" if failed else ""))
    print(f"history: {len(history)} items; 7d: {len(last_7d)}; "
          f"selected: {len(selected)}; hot: {len(hot)}; timeline: {len(timeline)}; "
          f"topics: {len(tag_counts)}")

    if args.daily:
        def build_period(kind, pool, window_label):
            pool_sorted = sorted(pool, key=lambda x: x["score"], reverse=True)
            items = dedup_topics(pool_sorted)[:sc["daily_top"]]
            per_cat = {}
            for it in items:
                per_cat[it["category_label"]] = per_cat.get(it["category_label"], 0) + 1
            cat_part = "、".join(f"{k} {v} 条" for k, v in per_cat.items()) or "无"
            head = (f"头条：{items[0].get('zh_title') or items[0]['title']}"
                    if items else "暂无精选")
            date_str = now_cst.strftime("%Y年%m月%d日")
            date_iso = now_cst.strftime("%Y-%m-%d")
            if kind == "daily":
                key = date_iso
                label = date_str
            elif kind == "weekly":
                iso_y, iso_w, _ = now_cst.isocalendar()
                key = f"{iso_y}-W{iso_w:02d}"
                label = f"{iso_y}年第{iso_w}周"
            else:
                key = now_cst.strftime("%Y-%m")
                label = now_cst.strftime("%Y年%m月")
            return {
                "kind": kind, "key": key, "label": label,
                "date": date_str, "date_iso": date_iso,
                "issue": issue_no(kind, date_iso),
                "generated_at": now.isoformat(),
                "summary": (f"{window_label}共收录 {len(pool)} 条动态，精选 "
                            f"{len(items)} 条（{cat_part}）。{head}。"),
                "items": [pub_item(it) for it in items],
            }

        def build_period_en(kind, pool, window_label_en):
            """build_period 的英文版：同一批条目，英文日期/导读/条目数据。
            导读含本轮池子规模（仅新报告有该数据）。"""
            pool_sorted = sorted(pool, key=lambda x: x["score"], reverse=True)
            items = dedup_topics(pool_sorted)[:sc["daily_top"]]
            per_cat = {}
            for it in items:
                lab = it.get("category_label_en") or it["category"]
                per_cat[lab] = per_cat.get(lab, 0) + 1
            cat_part = ", ".join(f"{k} {v}" for k, v in per_cat.items()) or "none"
            head = (f"Headline: {items[0].get('en_title') or items[0]['title']}"
                    if items else "No picks yet")
            date_iso = now_cst.strftime("%Y-%m-%d")
            date_str = en_date_str(date_iso)
            if kind == "daily":
                key = date_iso
                label = en_short(date_iso)
            elif kind == "weekly":
                iso_y, iso_w, _ = now_cst.isocalendar()
                key = f"{iso_y}-W{iso_w:02d}"
                label = f"Week {iso_w}, {iso_y}"
            else:
                key = now_cst.strftime("%Y-%m")
                label = f"{MONTHS_EN[now_cst.month - 1]} {now_cst.year}"
            return {
                "kind": kind, "key": key, "label": label,
                "date": date_str, "date_iso": date_iso,
                "issue": issue_no(kind, date_iso),
                "generated_at": now.isoformat(),
                "summary": (f"{len(pool)} items collected in the {window_label_en}, "
                            f"{len(items)} picks ({cat_part}). {head}."),
                "items": [pub_item_en(it) for it in items],
            }

        def en_report(rep):
            """把一份中文存档报告转成英文版：条目按链接从 zh_draft 取 en_*，
            日期/标签/导读现场拼英文；不写 en/data/* 存档 JSON，存档只读中文版。
            导读为短式（池子规模未存档）。"""
            items = []
            for pit in rep["items"]:
                tr = zh_map.get(norm_link(pit.get("link", ""))) or {}
                it = dict(pit)
                it.pop("zh_title", None)
                it.pop("zh_oneliner", None)
                it["source"] = SOURCE_NAMES_EN.get(pit.get("source"), pit.get("source"))
                it["en_title"] = tr.get("en_title", "")
                it["en_oneliner"] = tr.get("en_oneliner", "")
                it["category_label"] = cat_label_en.get(
                    pit.get("category"), pit.get("category_label", ""))
                it["tags"] = [TAG_LABELS_EN.get(t, t) for t in pit.get("tags", [])][:3]
                try:
                    _pub = datetime.fromisoformat(pit["published"])
                    if _pub.tzinfo is None:
                        _pub = _pub.replace(tzinfo=timezone.utc)
                except (ValueError, KeyError):
                    _pub = now
                shim = {"title": pit["title"], "summary": "",
                        "_tier": pit.get("tier", "T2"), "_pub": _pub}
                it["reason"] = reason_for_en(shim, cfg, now)
                items.append(it)
            per_cat = {}
            for it in items:
                per_cat[it["category_label"]] = per_cat.get(it["category_label"], 0) + 1
            cat_part = ", ".join(f"{k} {v}" for k, v in per_cat.items()) or "none"
            head = (f"Headline: {items[0].get('en_title') or items[0]['title']}"
                    if items else "No picks")
            kind = rep["kind"]
            date_iso = rep["date_iso"]
            if kind == "daily":
                label = en_short(date_iso)
            elif kind == "weekly":
                _y, _w = rep["key"].split("-W")
                label = f"Week {int(_w)}, {_y}"
            else:
                _y, _m = rep["key"].split("-")
                label = f"{MONTHS_EN[int(_m) - 1]} {_y}"
            return {"kind": kind, "key": rep["key"], "label": label,
                    "date": en_date_str(date_iso), "date_iso": date_iso,
                    "issue": rep["issue"],
                    "generated_at": rep.get("generated_at", ""),
                    "summary": f"{len(items)} picks ({cat_part}). {head}.",
                    "items": items}

        def render_archived(kind, reports, out_dir):
            """渲染某类全部存档页（带上一期/下一期）；out_dir 为 daily/weekly/monthly。"""
            os.makedirs(os.path.join(root, out_dir), exist_ok=True)
            for i, rep in enumerate(reports):
                prev = None
                nxt = None
                if i + 1 < len(reports):
                    prev = (reports[i + 1]["label"], reports[i + 1]["key"] + ".html")
                if i > 0:
                    nxt = (reports[i - 1]["label"], reports[i - 1]["key"] + ".html")
                with open(os.path.join(root, out_dir, rep["key"] + ".html"),
                          "w", encoding="utf-8") as f:
                    f.write(render_period(site, kind, rep, base="../", prev=prev,
                                          next_=nxt,
                                          canonical=f"{site_url}/{out_dir}/{rep['key']}.html",
                                          rel_path=f"{out_dir}/{rep['key']}.html"))

        def current_page(kind, cur, reports, out_dir):
            """当前页（daily.html/weekly.html/monthly.html，站根）：上一期指向上一个存档。"""
            prev = None
            older = [r for r in reports if r["key"] != cur["key"]]
            if older:
                prev = (older[0]["label"], f"{out_dir}/{older[0]['key']}.html")
            with open(os.path.join(root, kind + ".html"), "w", encoding="utf-8") as f:
                f.write(render_period(site, kind, cur, base="", prev=prev, next_=None,
                                      canonical=f"{site_url}/{kind}.html",
                                      rel_path=kind + ".html"))

        def render_archived_en(kind, reports, out_dir, fresh_en, use_fresh):
            """英文版存档页：与中文同一批报告；新报告用带池子规模的英文版，
            旧报告现场转英文（use_fresh 只在快照本轮新写时为真，与中文一致）。"""
            en_reports = [
                (fresh_en if (use_fresh and r["key"] == fresh_en["key"]) else en_report(r))
                for r in reports]
            os.makedirs(os.path.join(en_root, out_dir), exist_ok=True)
            for i, en_rep in enumerate(en_reports):
                prev = None
                nxt = None
                if i + 1 < len(en_reports):
                    prev = (en_reports[i + 1]["label"], en_reports[i + 1]["key"] + ".html")
                if i > 0:
                    nxt = (en_reports[i - 1]["label"], en_reports[i - 1]["key"] + ".html")
                with open(os.path.join(en_root, out_dir, en_rep["key"] + ".html"),
                          "w", encoding="utf-8") as f:
                    f.write(render_period(site, kind, en_rep, base="../", prev=prev,
                                          next_=nxt,
                                          canonical=f"{site_url}/en/{out_dir}/{en_rep['key']}.html",
                                          lang="en",
                                          rel_path=f"{out_dir}/{en_rep['key']}.html"))

        def current_page_en(kind, cur_en, reports, out_dir):
            """英文版当前页（en/daily.html 等）：上一期指向上一个存档。"""
            prev = None
            older = [r for r in reports if r["key"] != cur_en["key"]]
            if older:
                prev_en = en_report(older[0])
                prev = (prev_en["label"], f"{out_dir}/{older[0]['key']}.html")
            with open(os.path.join(en_root, kind + ".html"), "w", encoding="utf-8") as f:
                f.write(render_period(site, kind, cur_en, base="", prev=prev, next_=None,
                                      canonical=f"{site_url}/en/{kind}.html",
                                      lang="en", rel_path=kind + ".html"))

        # --- 日报（每天一份存档）
        last_24h = [it for it in live if (now - it["_pub"]) <= timedelta(hours=sc["daily_hours"])]
        daily = build_period("daily", last_24h, "过去 24 小时")
        save_json(os.path.join(data_dir, "daily.json"), daily)
        daily_data_dir = os.path.join(data_dir, "daily")
        os.makedirs(daily_data_dir, exist_ok=True)
        save_json(os.path.join(daily_data_dir, daily["key"] + ".json"), daily)
        daily_reports = load_period_archive(daily_data_dir)
        render_archived("daily", daily_reports, "daily")
        current_page("daily", daily, daily_reports, "daily")
        print(f"daily: {daily['date']}, {len(daily['items'])} items, 第 {daily['issue']} 期")
        daily_en = build_period_en("daily", last_24h, "past 24 hours")
        save_json(os.path.join(en_data_dir, "daily.json"), daily_en)
        render_archived_en("daily", daily_reports, "daily", daily_en, True)
        current_page_en("daily", daily_en, daily_reports, "daily")
        print(f"en daily: {daily_en['date']}, {len(daily_en['items'])} items")

        # --- 周报（滚动 7 天精选；每周只存一份快照）
        last_7d_sorted = sorted(last_7d, key=lambda x: x["score"], reverse=True)
        weekly = build_period("weekly", last_7d_sorted, "过去 7 天")
        save_json(os.path.join(data_dir, "weekly.json"), weekly)
        weekly_data_dir = os.path.join(data_dir, "weekly")
        os.makedirs(weekly_data_dir, exist_ok=True)
        weekly_new = not os.path.exists(os.path.join(weekly_data_dir, weekly["key"] + ".json"))
        if weekly_new:
            save_json(os.path.join(weekly_data_dir, weekly["key"] + ".json"), weekly)
        weekly_reports = load_period_archive(weekly_data_dir)
        render_archived("weekly", weekly_reports, "weekly")
        current_page("weekly", weekly, weekly_reports, "weekly")
        print(f"weekly: {weekly['label']}, {len(weekly['items'])} items, 第 {weekly['issue']} 期")
        weekly_en = build_period_en("weekly", last_7d_sorted, "past 7 days")
        save_json(os.path.join(en_data_dir, "weekly.json"), weekly_en)
        render_archived_en("weekly", weekly_reports, "weekly", weekly_en, weekly_new)
        current_page_en("weekly", weekly_en, weekly_reports, "weekly")
        print(f"en weekly: {weekly_en['label']}, {len(weekly_en['items'])} items")

        # --- 月报（滚动 30 天精选；每月只存一份快照）
        last_30d = [it for it in live if (now - it["_pub"]) <= timedelta(days=30)]
        monthly = build_period("monthly", last_30d, "过去 30 天")
        save_json(os.path.join(data_dir, "monthly.json"), monthly)
        monthly_data_dir = os.path.join(data_dir, "monthly")
        os.makedirs(monthly_data_dir, exist_ok=True)
        monthly_new = not os.path.exists(os.path.join(monthly_data_dir, monthly["key"] + ".json"))
        if monthly_new:
            save_json(os.path.join(monthly_data_dir, monthly["key"] + ".json"), monthly)
        monthly_reports = load_period_archive(monthly_data_dir)
        render_archived("monthly", monthly_reports, "monthly")
        current_page("monthly", monthly, monthly_reports, "monthly")
        print(f"monthly: {monthly['label']}, {len(monthly['items'])} items, 第 {monthly['issue']} 期")
        monthly_en = build_period_en("monthly", last_30d, "past 30 days")
        save_json(os.path.join(en_data_dir, "monthly.json"), monthly_en)
        render_archived_en("monthly", monthly_reports, "monthly", monthly_en, monthly_new)
        current_page_en("monthly", monthly_en, monthly_reports, "monthly")
        print(f"en monthly: {monthly_en['label']}, {len(monthly_en['items'])} items")

        # --- 往期存档页（B8/B9）：日报按月分组；周报、月报各列一组
        def arch_entry(rep, file_href, date_short):
            return {"date_iso": rep["date_iso"], "date_short": date_short,
                    "file": file_href, "issue": rep["issue"],
                    "count": len(rep["items"])}
        d_entries = [arch_entry(r, r["key"] + ".html",
                                datetime.strptime(r["date_iso"], "%Y-%m-%d").strftime("%m月%d日"))
                     for r in daily_reports]
        w_entries = [arch_entry(r, "../weekly/" + r["key"] + ".html", r["label"])
                     for r in weekly_reports]
        m_entries = [arch_entry(r, "../monthly/" + r["key"] + ".html", r["label"])
                     for r in monthly_reports]
        os.makedirs(os.path.join(root, "daily"), exist_ok=True)
        with open(os.path.join(root, "daily", "archive.html"), "w", encoding="utf-8") as f:
            f.write(render_archive(site, d_entries, w_entries, m_entries))
        d_entries_en = [arch_entry(r, r["key"] + ".html", en_short(r["date_iso"]))
                        for r in daily_reports]
        w_entries_en = [arch_entry(r, "../weekly/" + r["key"] + ".html",
                                   en_report(r)["label"]) for r in weekly_reports]
        m_entries_en = [arch_entry(r, "../monthly/" + r["key"] + ".html",
                                   en_report(r)["label"]) for r in monthly_reports]
        os.makedirs(os.path.join(en_root, "daily"), exist_ok=True)
        with open(os.path.join(en_root, "daily", "archive.html"), "w", encoding="utf-8") as f:
            f.write(render_archive(site, d_entries_en, w_entries_en, m_entries_en, lang="en"))
        # sitemap 补上本轮新出的存档页（主 sitemap 已扫描磁盘，只补还没有的；
        # lastmod 用报告真实日期，不再全写当天）
        try:
            with open(os.path.join(root, "sitemap.xml"), encoding="utf-8") as _sf:
                _existing_locs = set(re.findall(r"<loc>([^<]+)</loc>", _sf.read()))
        except OSError:
            _existing_locs = set()
        _sm_extra = []
        for _out, _reps in (("daily", daily_reports), ("weekly", weekly_reports),
                            ("monthly", monthly_reports)):
            for _r in _reps:
                for _prefix in ("", "en/"):
                    _loc = f"{site_url}/{_prefix}{_out}/{_r['key']}.html"
                    if _loc not in _existing_locs:
                        _sm_extra.append(f"<url><loc>{_loc}</loc>"
                                         f"<lastmod>{_r['date_iso']}</lastmod></url>")
        if _sm_extra:
            with open(os.path.join(root, "sitemap.xml"), encoding="utf-8") as _sf:
                _sm_text = _sf.read()
            _sm_text = _sm_text.replace("</urlset>",
                                        "\n".join(_sm_extra) + "\n</urlset>")
            with open(os.path.join(root, "sitemap.xml"), "w", encoding="utf-8") as f:
                f.write(_sm_text)
        print(f"archive: daily {len(d_entries)}, weekly {len(w_entries)}, monthly {len(m_entries)}")

    # --- 文章详情页（items/<id>.html）：30 天库里的每条内容各一页；
    # 旧条目过期后页面留着当永久链接，不删除。
    daily_issue = {}
    daily_issue_en = {}
    for rep in load_period_archive(os.path.join(data_dir, "daily")):
        for it in rep.get("items", []):
            if it["id"] not in daily_issue:
                daily_issue[it["id"]] = {"issue": rep["issue"],
                                         "date": rep["date"],
                                         "key": rep["key"]}
                daily_issue_en[it["id"]] = {"issue": rep["issue"],
                                            "date": en_date_str(rep["date_iso"]),
                                            "key": rep["key"]}
    sel_ids = {it["id"] for it in selected}
    items_dir = os.path.join(root, "items")
    os.makedirs(items_dir, exist_ok=True)
    en_items_dir = os.path.join(en_root, "items")
    os.makedirs(en_items_dir, exist_ok=True)
    by_cat = {}
    by_src = {}
    for it in live:
        by_cat.setdefault(it["category"], []).append(it)
        by_src.setdefault(it["source_id"], []).append(it)
    for lst in list(by_cat.values()) + list(by_src.values()):
        lst.sort(key=lambda x: x["score"], reverse=True)
    n_items = 0
    for it in live:
        picked = []
        for cand in by_cat.get(it["category"], []):
            if cand["id"] != it["id"] and cand not in picked:
                picked.append(cand)
            if len(picked) >= 5:
                break
        if len(picked) < 5:
            for cand in by_src.get(it["source_id"], []):
                if cand["id"] != it["id"] and cand not in picked:
                    picked.append(cand)
                if len(picked) >= 5:
                    break
        # 详情页只用 pub_item 的发布字段（标题 + 一句话简介），不并完整摘要。
        detail = dict(pub_item(it))
        with open(os.path.join(items_dir, it["id"] + ".html"), "w", encoding="utf-8") as f:
            f.write(render_item(site, detail, [pub_item(r) for r in picked],
                                it["id"] in sel_ids,
                                daily_issue.get(it["id"])))
        detail_en = pub_item_en(it)
        with open(os.path.join(en_items_dir, it["id"] + ".html"), "w", encoding="utf-8") as f:
            f.write(render_item(site, detail_en, [pub_item_en(r) for r in picked],
                                it["id"] in sel_ids,
                                daily_issue_en.get(it["id"]), lang="en"))
        n_items += 1
    # 工具站收录门：删掉被拦下的条目残留的详情页（中英两棵树），否则旧
    # 文章页仍可通过直接链接访问；30 天窗口外已过期的工具页按原规则保留。
    _live_ids = {it["id"] for it in live}
    _removed = 0
    for _d in (items_dir, en_items_dir):
        for _fn in os.listdir(_d):
            if _fn.endswith(".html") and _fn[:-5] in history and _fn[:-5] not in _live_ids:
                os.remove(os.path.join(_d, _fn))
                _removed += 1
    if _removed:
        print(f"gate: removed {_removed} stale detail pages")
    print(f"items: {n_items} detail pages (x2 trees)")
    print(f"en: {len(tag_counts_en)} topics, {len(en_day_index)} day files")
    # --- /geo-audit 自检页 + 数据（SEO/GEO：每轮生成后自检，日报复用同一份数据）---
    geo_html, geo_data = build_geo_audit(site, root, site_url, today_iso)
    with open(os.path.join(root, "geo-audit.html"), "w", encoding="utf-8") as f:
        f.write(geo_html)
    save_json(os.path.join(data_dir, "geo-audit.json"), geo_data)
    print(f"geo-audit: {geo_data['summary']['passed']} passed, "
          f"{geo_data['summary']['warn']} warn, {geo_data['summary']['failed']} failed")


if __name__ == "__main__":
    main()
