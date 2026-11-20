# 工具站 HOT（Tool Site HOT）

每天发现最新工具网站，只收点开就能直接用的工具。

- **在线访问**：https://staroltest.github.io/tool-hot/（主站）
- **镜像**：https://tool-hot.pages.dev/
- **RSS**：https://staroltest.github.io/tool-hot/feed.xml（英文版：`/en/feed.xml`）
- **MCP**：https://tool-hot.pages.dev/mcp（`get_hot` / `get_daily` / `search_items`）

## 收什么，不收什么

只收能在网站上直接用的工具网站，例如汇率计算器、格式转换、图片处理、代码工具。
文章、新闻、博客、帖子、目录页、下载页、应用商店、桌面 / 手机应用、浏览器扩展、
自托管工具一律不收。每个新条目进榜前都会实测一次链接本身，确认能在浏览器里用。

## 站点内容

- 首页：精选 10 条 + 热点榜 20 条，每半小时更新
- 日报 / 周报 / 月报、主题页（AI、开发、设计、效率、数据、开源）、全部动态（30 天）
- 每个工具一条详情页：原标题 + 一句简介 + 原文链接，不转载正文与摘要
- 中英双语（`/en/` 英文树与中文树同构，按浏览器语言自动切换、可手动切换）

## 信源（7 个）

Product Hunt、Hacker News Show、Ignlab、ListBulb、MakerHunt、Smol Launch、DevHunt。

## 技术说明

纯静态站，`tools/generate.py`（纯 Python 标准库，零依赖）每半小时拉取信源、
去重、过收录门、打分、生成全站；托管在 GitHub Pages（主站）+ Cloudflare Pages
（镜像），并附带一个 MCP 接入点。

站内 SEO / GEO：全站 `canonical`、hreflang 三元组（`zh-CN` + `en` + `x-default`）、
`robots` meta、RSS 发现链接、WebSite JSON-LD；`robots.txt` 点名放行 AI 爬虫并屏蔽
Bytespider / PetalBot；`sitemap.xml` 用真实发布日期；`llms.txt`（站点说明 + MCP
端点 + 数据入口，英文版在 `/en/llms.txt`）；详情页 `og:type=article` 与
`dateModified`；`/geo-audit` 9 项自检页（覆盖双树）。站名、域名与各端点全部取自
`config.json`，不要手改生成物。

想用同一套流水线搭别的主题站，请用干净的模板仓库
[Staroltest/hot-site-template](https://github.com/Staroltest/hot-site-template)，
按其中 [BOOTSTRAP.md](BOOTSTRAP.md) 的 playbook 操作。本仓库只推工具站 HOT
本身的内容，不再作为模板使用。

## 许可与出处

MIT License，Copyright (c) 2026 Camille。

流水线源自 IndieHOT 的实践；IndieHOT 的信息架构与界面风格参考了卡兹克
（张仁杰）的开源项目 [AIHOT](https://github.com/KKKKhazix/AIHOT)（MIT 协议）。
