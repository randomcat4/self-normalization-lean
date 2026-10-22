# EnergyPathLaw 发布源码格式独立形式补充票

STATUS: CORRECT
CHECK_STATUS: FULLY_CHECKED
FORMAL_STATUS: LEAN_FULLY_CHECKED
SCOPE: SOURCE_FORMAT_EQUIVALENCE_AND_FORMAL_RECHECK_ONLY
TICKET_STATE: FROZEN
REVIEW_DATE: 2026-10-22
E3_STATUS: OPEN
ROOT_STATUS: OPEN

## 裁决与版本归属

新 canonical `Shao/OQ4/EnergyPathLaw.lean` 精确等于旧冻结源码末尾追加且仅追加一个 LF 字节。全部既有字节相同，反向删除该 LF 恢复旧 SHA256。本轮在指定服务器对新源码重新执行独立 no-o、完整源码全部新常量和实际 33 个 OQ4 模块共存／所属常量公理门，均通过。

原形式票 `energy-path-law-formal-review-v1.md` 的 SHA256 `7b72f6ba3838dc9ef3bcbc152b9db6d414c574a9ad69539cbb90207fc953590f` 准确绑定旧源码 `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536`。本补充票另行绑定新源码 `3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177`，不重写或倒改原票的字节归属。

本轮没有修改源码、输出目标编译产物、修改数学证明或覆盖任何原票；只新增本补充票。这里不重复纯数学审查。既有数学内容、声明与证明由逐字节对应及本轮完整签名／公理比对确认保持相同；认证范围仍仅为式 (7) 第一叶，完整 E3、E2、OQ4 和根组不因此关闭。

## 独立旧字节证据与唯一 LF 对应

旧字节来自本审稿人上轮成功的完整源码审计输入：

`/tmp/oq4-energy-path-law-independent-v1-14gj0lq3/fullsource-audit-v2.stdin.lean`

先独立验证该完整输入 SHA256 为 `25961d6acdf29b2831ca3bcaf61b023b726dc311728050d038799fea52c30d81`，再读取其前 15246 字节，复核旧源码完整 SHA256；将其存于本轮独立证据目录的 `old-frozen-source.lean`。因此旧字节不依赖作者对本次变化的描述，也不是仅相信给定的新 SHA。

| 对象 | 字节数 | 完整 SHA256 |
|---|---:|---|
| 独立恢复的旧冻结源码 | 15246 | `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536` |
| ready 后实际 canonical 新源码 | 15247 | `3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177` |
| 新源码删去最后一个 LF 的恢复字节 | 15246 | `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536` |

独立逐字节结果为 `new == old + b'\n'`。旧源码严格 UTF-8、无 BOM、无 CR、无末尾 LF；新源码严格 UTF-8、无 BOM、无 CR、末尾连续 LF 数恰为 1。没有发现任何非末尾 LF 的变化；脚本在运行 Lean 前即对这项要求作失败即停止的断言。

作者明确 ready 前，本审稿人只处理上述旧审计证据，没有读取新 target 或启动 Lean。收到 ready 后才读取实际 canonical 新源码并开始本轮形式门。

## 服务器与独立执行

服务器工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。

只读复核分支 `feat/oq4-centering-and-path`，HEAD `1695839731c586cbeb34f157f9aec2246ec00c7a`。全部 Lean 命令均先激活指定服务器环境，随后进入该工作树，绑定 `taskset -c 0-3`；使用既有钉死 Lean `4.36.0-rc1`／mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。没有本地 Lean、安装、Git 写入、缓存写入或旧目标重编译。

本轮服务器独立证据目录：

`/tmp/oq4-energy-path-law-source-format-independent-v1-0texadva`

| 检查 | 实际命令 | 退出码 | 秒数 |
|---|---|---:|---:|
| 新精确 target no-o | `taskset -c 0-3 lake env lean Shao/OQ4/EnergyPathLaw.lean` | 0 | 4.401 |
| 新完整源码＋全部新常量审计 | `taskset -c 0-3 lake env lean --stdin` | 0 | 5.057 |
| 实际全 33 模块共存＋全部模块所属常量公理门 | `taskset -c 0-3 lake env lean --stdin` | 0 | 26.873 |

三次均未指定 `-o`，标准错误均为空，target no-o 标准输出也为空。作者已输出 target 的 `.olean` 在本轮前后均为 493120 字节，SHA256 同为 `6331d6941ff5d6c857191d5a4693035dfeb7ba811f2ba26dcf732c951a367669`；本审稿人未输出或改变它。

| 本轮服务器审计文件 | 完整 SHA256 |
|---|---|
| `fullsource-new-audit.stdin.lean` | `eed5a01e13ff9af892add13c5b49d01fedf802cd04de9b543258664795a909ac` |
| `fullsource-new-audit.stdout.log` | `584b4547aa802156ed2d98c2e402f1d62ac9b374a8a8bebe93ac7fc347d82c58` |
| `coexist-all33-new.stdin.lean` | `6c05c199c93c21cfb07c559985b50e6be80c09df3bd2cb6deb297643fea1c341` |
| `coexist-all33-new.stdout.log` | `43aeaff621f244e46a4896b33288af1a51206c02b87a6c93436b2f8630a8607b` |

这些 stdout 是本轮重新实际执行得到；即使输出 SHA 与上轮相同，也没有以复用旧结果代替新检查。完整实际源码先全部送入标准输入，再执行独立审计命令；不是导入目标模块替代源码检查。

## 全部新常量、完整类型与公理比对

完整新源码审计集合仍是：

`env.constants.toList.filter (fun p => (env.getModuleIdxFor? p.1).isNone)`。

不使用名称或命名空间筛选；全部 22 项逐项打印完整类型并调用 `Lean.collectAxioms`，严格拒绝标准三公理以外的依赖。实际分类仍为 9 个源码公开定理、4 个源码私有定理、1 个定义、8 个生成定理，即 21 个 theorem 常量和 1 个 def 常量。

22 项完整实际类型、公理分别与上轮独立完整源码输出及本轮真实导入模块的 22 个所属常量比对，结果均完全相同。只规范化打印空白及 `_private._stdin.0.` 与 `_private.Shao.OQ4.EnergyPathLaw.0.` 的标准私有名前缀；没有删除或重写类型前提。记录在 `signatures-new-vs-old-and-compiled.result.json`，包括全部 22 项规范化类型指纹与实际公理集合。完整全限定类型和宇宙参数保留在本轮成功 stdout 中。

以下 S 精确表示 `[propext, Classical.choice, Quot.sound]`，P 精确表示 `[propext]`。私有名字以前缀 `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.` 展开。

| 新源码实际常量 | 实际传递公理 |
|---|---|
| `Shao.OQ4.energyPathIntegrand` | S |
| `Shao.OQ4.energyPathIntegrand.eq_1` | S |
| `Shao.OQ4.energyPathIntegrand_integrable` | S |
| `Shao.OQ4.energyPathIntegrand_le` | S |
| `Shao.OQ4.energyPathIntegrand_measurable` | S |
| `Shao.OQ4.energyPathIntegrand_nonneg` | S |
| `Shao.OQ4.energyPathLaw_integral` | S |
| `Shao.OQ4.energyPathLaw_integral_iid` | S |
| `Shao.OQ4.energyPathLaw_real_apply` | S |
| `Shao.OQ4.energyPathLaw_withDensity` | S |
| `Shao.OQ4.finitePi_withDensity` | S |
| 私有 `energyPath_closed_density` | S |
| 私有 `energyPath_density_integrable` | S |
| 私有 `energyPath_energy_le` | S |
| 私有 `finitePi_withDensity_lintegral` | S |
| 私有 `energyPath_closed_density._simp_1_1` | P |
| 私有 `energyPath_closed_density._simp_1_2` | P |
| 私有 `energyPath_closed_density._simp_1_3` | P |
| 私有 `energyPath_closed_density._simp_1_4` | P |
| 私有 `energyPath_closed_density._simp_1_5` | P |
| 私有 `energyPath_closed_density._simp_1_6` | S |
| 私有 `energyPath_closed_density._simp_1_7` | P |

共 16 项 S、6 项 P。新主结论仍同时返回真正可积性和精确实际有限路径身份，iid 定理仍同时给真正可积转移与积分转移；没有新增密度、归一化正性、μ 概率性、正生存概率、正长度或额外矩假设。这里的相同性来自完整类型逐项比对，而非只检查定理名字。

## 全 33 共存与旧 32＋公共源码保持

本轮从实际目录重新枚举 33 个 OQ4、全部 8 个 Basic、全部 24 个 Probability 源文件。实际 33 个 OQ4 导入名单与上轮独立冻结清单完全相同，包含 EnergyLinearTiltCentering 和新 EnergyPathLaw；`EnergyE2Bounds.lean` 在本轮前后仍 ABSENT。

本轮真实导入全部 33 个 OQ4 模块，按 `getModuleIdxFor?` 的实际模块归属审计全部 637 个所属常量，逐项传递公理白名单门通过；target 实际所属常量为 22。该共存输入与实际重新枚举名单逐项核对，不是只凭固定数量判断。

本轮开始前即将除 target 外的 64 行源元数据，与上轮本人独立保存的完整冻结清单逐项比较：旧 32 个 OQ4＋8 个 Basic＋24 个 Probability 的路径、字节数、SHA256、BOM 标记全部相同。该 64 行规范化清单 SHA256 为：

`b83359fd8b8ae95fdbd4f107da13e60e151d0df436dc1f798de68083e5975b48`

新 target 加入后，本轮完整 65 行清单前后逐项相同，路径集合也与旧清单相同。服务器 `sources-before.json`、`sources-after.json` 的 SHA256 均为：

`84dba88ee7cea04e914d9e65ce74b90f8c5b7813e5c971a51da741acbd3d6f0c`

| 本轮源组 | 文件数 | 前后相同的完整清单 SHA256 |
|---|---:|---|
| OQ4 | 33 | `922e88b6cdeb7ac3908034c5c0b04148d29298e082a4386df95e04a7ff84dfa6` |
| Basic | 8 | `7c0ae6eafeb435ff68841f88b7b66cb4f234052ab94a3d4ee26acbf5b2892ae4` |
| Probability | 24 | `c41d6756c0252a779edfc35d3d24460a715aa7a31fa29d43544f8816635faa01` |

所有 65 份源严格 UTF-8 解码通过；单词边界禁词扫描 `sorry`、`admit`、`axiom`、`unsafe`、`native_decide` 命中为空。详细记录为 `format-and-baseline.result.json`、`stability-and-final.result.json`。原始输入、日志、元数据和编译产物均只在服务器，本地只保存本补充票。

全部服务器检查结束时 `liveLeanLake=[]`。已通知 lead 该独立稳定窗口结束，本审稿人不再运行服务器或源码检查。

## 原认证保持与本补充范围

原 proof 仍以 `6262f545ddd10fe868db3386b426d417cb53940fc1e3ab55375f79147dafc601` 为冻结锚点，原数学票仍以 `5d16459c67934758ffb5c54d2dae3c6998fe68d1cced9b8555087712e9c98894` 为锚点，原形式票仍以 `7b72f6ba3838dc9ef3bcbc152b9db6d414c574a9ad69539cbb90207fc953590f` 为锚点，证明发布格式票仍以 `cf0d8973cf97bf6b2569e4026c1c68bee20a060382f907c68f9a628794a5e3f2` 为锚点。本轮没有写入或重生成这些文件。

本补充的 CORRECT / FULLY_CHECKED 精确绑定 15247 字节的新源码 `3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177`：它证明唯一末尾 LF 的格式对应，并补齐该新字节版本上的独立 no-o、完整源码和全 33 共存机械证据。它不把原形式票的旧字节绑定改写成新绑定，也不扩大式 (7) 第一叶以外的数学范围。
