# EnergyPathLaw 源码末尾换行：作者格式修复补充 v1

状态：AUTHOR_FORMAT_RECHECK_PASSED。新版本的父验收及独立最终补充门单列等待；本文件不是独立CORRECT票。

本补充仅记录父明确授权的必要格式修复：在正式源码最后追加恰好一个LF字节。没有重写匿名数学证明、旧作者收据或任何旧数学／最终审稿票，也没有作其他修复。

## 旧新字节与规范源码

| 工件 | 字节数 | SHA256 |
|---|---:|---|
| 原冻结源码 | 15246 | `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536` |
| 新规范源码 | 15247 | `3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177` |
| 原匿名数学证明，保持不变 | — | `6262f545ddd10fe868db3386b426d417cb53940fc1e3ab55375f79147dafc601` |

服务器及本地副本都逐字节断言：

```python
new_bytes == old_bytes + b"\n"
len(new_bytes) == len(old_bytes) + 1
new_bytes.endswith(b"\n") and not new_bytes.endswith(b"\n\n")
```

原文件没有末LF；新文件无BOM、仅LF、恰好一个末LF。除最后新增0x0A外，先前15246字节完全一致。新摘要由作者独立读取实际字节计算，且与父独立计算的expectedSHA一致。

- 服务器正式目标仍为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyPathLaw.lean`。
- 改写前准确源备份为 `repro_outputs/oq4-energy-path/source-format-lf-v1/EnergyPathLaw.4feb.pre-lf.lean`，备份读取校验与原canonical完全相同。
- 原olean也仅在服务器备份为同目录 `EnergyPathLaw.4feb.pre-lf.olean`。
- 本地原4feb源码 `EnergyPathLaw.lean` 保留不覆盖；新规范副本为 `EnergyPathLaw-published.lean`。
- 本地原 `receipt.md` 保留，当前SHA256 `ab18e1436ce7e0cf2dcc1a38fc716fb17af1da32d353439dd90ff79494775fce`；原 `summary.json` 保留，当前SHA256 `156462311ea66296d0d60af9bf0c0e8f93217dc590a187e891ff27887ef66ba8`。
- 新版整理证据另存 `source-format-author-summary-v1.json`，SHA256 `4752f77ccab04c29a21f0c5d28513e634d75c868eaf3ff78d65014717867b537`。其中保留22项完整签名／公理、逐文件旧32和公共文件摘要、实际命令及退出码。
- 拟发布文档映射：`docs/oq4-energy-path-law-source-format-author-supplement-v1.md`；本轮作者只写drafts下本补充，由父另行整合。

## 指定服务器重验与唯一生成

父确认分支仍为 `feat/oq4-centering-and-path`，HEAD `1695839731c586cbeb34f157f9aec2246ec00c7a`；作者没有运行Git。父指定本次33源窗口无其他canonical writer，E2新canonical未加入。

所有Lean均只在指定服务器激活后重新进入 `workspaces/lead-oq4`，按 `taskset -c 0-3` 单进程顺序执行。没有重编旧target，没有安装、cache操作或修改公共／根文件。新版本唯一-o生成有独占attempt标记，未重复调用。

实际Lean命令如下；最后两项通过进程stdin传入相应精确文件字节。

```sh
taskset -c 0-3 lake env lean Shao/OQ4/EnergyPathLaw.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/EnergyPathLaw.olean Shao/OQ4/EnergyPathLaw.lean
taskset -c 0-3 lake env lean --stdin
# stdin: repro_outputs/oq4-energy-path/source-format-lf-v1/CoexistExactAudit.lean
taskset -c 0-3 lake env lean --stdin
# stdin: repro_outputs/oq4-energy-path/source-format-lf-v1/Audit.lean
```

| 检查 | 实际退出码 | 原始日志字节数 |
|---|---:|---:|
| 新canonical目标无-o检查 | 0 | 0 |
| 作者对新版本唯一-o生成 | 0 | 0 |
| 旧32实际导入＋新精确源码体，全部getModuleIdxFor?none常量 | 0 | 11704 |
| 实际33导入，全新owner签名及全33传递公理 | 0 | 70156 |

全部门零错误、零警告。所有原始日志、exit、command记录和二进制仅位于服务器 `repro_outputs/oq4-energy-path/source-format-lf-v1/`，没有下载到本地。

旧olean SHA256：`6331d6941ff5d6c857191d5a4693035dfeb7ba811f2ba26dcf732c951a367669`。

新版本实际生成olean SHA256：`6331d6941ff5d6c857191d5a4693035dfeb7ba811f2ba26dcf732c951a367669`。

两个摘要实际相同；这里记录的是对新源真实执行一次-o后读取的结果，不是沿用旧收据或省略新版本生成。

工具链 `leanprover/lean4:v4.36.0-rc1`；mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，均未改动。

## 全部新增常量、共存与公理

精确新源无-o审计仍全取22个 `getModuleIdxFor? == none` 常量。实际导入审计按 `getModuleIdxFor? → moduleNames[idx] == Shao.OQ4.EnergyPathLaw` 全取22个目标模块常量，不按命名空间／名称根筛掉私有或生成项。

实际计数保持为：9个公开定理、1个透明定义、4个私有定理、8个生成常量。新版22项名称集合、完整逐项签名和逐项传递公理记录，与旧4feb作者记录全部严格相等；其中16项依赖标准三公理，6项仅propext，额外公理为空。

实际导入数仍33。全33模块owner与Shao.OQ4命名空间并集仍为637项，逐项传递公理全部属于 `{propext, Classical.choice, Quot.sound}`。没有用换行修复改变冻结前提、结论、真实law、路径事件、可积性或归一化因子；匿名proof6262不变。

## 旧32及公共文件保持

服务器在追加前记录快照，全部重验后再逐文件校验；文件清单及摘要均完全相等：

- 除新目标以外32份OQ4源码全部不变，同时与原4feb作者阶段的旧32快照相同。
- 公共快照38个文件全部不变。范围为 `Shao/Basic/**/*.lean`、`Shao/Probability/**/*.lean`、`Shao/C1/**/*.lean`、`Shao/C2/**/*.lean`、`Shao/*.lean`、存在的根 `Shao.lean`、`lean-toolchain`、lakefile及 `lake-manifest.json`。
- 旧32摘要字典排序规范JSON的SHA256：`4155b9d86ea0ef4ec726cce426dc22513d4728a2cb8cb36f458593e2d269b574`。
- 公共38摘要字典排序规范JSON的SHA256：`90f19286f6f3b5693525cdfe83fc40906290f0d8959f128606857cd0a7dbfcd9`。
- 逐文件摘要全表保留在新版JSON证据中；服务器before.json／mutation.json及最终整理结果记录了前后比较。

本轮未读取或覆盖旧math5d／final7b等审稿票；旧作者receipt和原4feb本地源均保留。当前无作者live Lean进程，规范源3336与proof6262冻结，交父及独立reviewer补充新版本gate。本补充不改变完整E2/E3/OQ4及根仍OPEN的状态。
