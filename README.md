# HOT 流水线模板

一套“热点站”流水线的标准模板：从公开 RSS 信源采集内容，规则打分精选，
生成纯静态站，托管在 GitHub Pages（主站）+ Cloudflare Pages（镜像），
并附带一个 MCP 接入点。IndieHOT 就是用这套流水线跑出来的第一个站；
想做电商 HOT、AI HOT 或别的主题时，从这个仓库起手，改配置、换信源即可。

## 一句话开新站

跟 agent 说一句话，例如：

> 用 hot-site-template 给我搭一个电商 HOT，面向电商从业者，信源你来找。

agent 按 [BOOTSTRAP.md](BOOTSTRAP.md) 里的 playbook 全套办完：
建仓库、填配置、找信源、首轮生成、双站部署、定时任务、验收。
你只需要确认站名、主题和受众；信源 agent 会逐个实测后定。

## 模板里有什么

| 文件 | 作用 |
| --- | --- |
| `tools/generate.py` | 生成器：拉 RSS → 去重 → 规则打分 → 生成全站。纯 Python 标准库，零依赖 |
| `tools/geo_audit.py` | GEO 自检：独立运行，只读生成物，输出 `geo-audit.html` + `data/geo-audit.json` |
| `config.json` | 全部可调项：站名、受众、分类与关键词、打分权重、关于页、页脚、赞赏码 |
| `sources.json` | 信源清单（示例 2 条，搭建时必换） |
| `_worker.js` | MCP 端点（Cloudflare Pages Advanced Mode，单文件无依赖） |
| `_routes.json` | 只把 `/mcp` 交给 worker，其余路径静态托管 |
| `favicon.svg` | 通用站标 |
| `data/changelog.json` | 更新日志种子（示例 1 条） |
| `docs/cron-half-hourly.md` | 每半小时更新任务的指令模板 |
| `docs/cron-daily-curation.md` | 每日精选把关任务的指令模板 |
| `docs/pipeline-notes.md` | 流水线踩过的坑与铁律 |
| `BOOTSTRAP.md` | **agent 开新站的完整 playbook** |

## 站点长什么样

首页（精选 10 条 + 热点框）、全部动态（30 天全量按天分组）、热点榜、
日报 / 周报 / 月报、主题页、收藏、RSS（`feed.xml`）、MCP（`/mcp`）。
只展示原标题 + 一句自己写的一句话简介 + 原文链接，不转载正文与摘要。

## SEO / GEO（生成器自带）

每轮生成自动产出：全站 `canonical`、hreflang（`zh-CN` + `x-default`）、
`robots` meta、RSS 发现链接、WebSite JSON-LD；`robots.txt` 点名放行 AI 爬虫
并屏蔽 Bytespider / PetalBot；`sitemap.xml` 用真实发布日期；`llms.txt`
（站点说明 + MCP 端点 + 数据入口）；详情页 `og:type=article` 与
`dateModified`；`/geo-audit` 9 项自检页。全部取自 `config.json`：
站名/域名/`tagline`（llms.txt 介绍段首行）、`mcp_url`、`mirror_url`、
`edition_time_cst` / `timezone`（llms.txt 出刊行）、分类的 `label_en`（可选）。
`mcp_url` / `mirror_url` 留空时对应行段直接省略。

两条硬规则：hreflang 只写 `zh-CN` + `x-default`，绝不加 `hreflang="en"`
（0 个英文页，造假互链会被判作弊）；站长平台验证文件等用户给验证码再加，
不要凭空新建。

## 成本

免费额度内：GitHub Pages 免费；Cloudflare 直传不消耗每月 500 次构建额度，
静态访问不限量；MCP 调用每天 10 万次免费额度。详见 BOOTSTRAP.md。

## 许可与出处

MIT License，Copyright (c) 2026 Camille。

流水线源自 IndieHOT 的实践；IndieHOT 的信息架构与界面风格参考了卡兹克
（张仁杰）的开源项目 [AIHOT](https://github.com/KKKKhazix/AIHOT)（MIT 协议）。
本站模板按 MIT 协议开源，欢迎取用，署名链请保留。
