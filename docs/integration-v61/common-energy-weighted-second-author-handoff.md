# 实际源能量加权 regulator 平方和：作者最终交接

状态：`AUTHOR_KERNEL_AND_ALL_OWNED_AUDIT_PASS / FRESH_COMPLETE_REVIEW_PENDING / WRITER_RELEASED`。本作者释放该成功源的实现写权；当前无 Lean/audit 进程、无 root-heavy.lock 占用。审查前不再修改成功源或重跑成功检查。未开 PR、未合并、未创建额外上下文。所有原研究根与完整概率/Taylor 组装仍 OPEN。

## 唯一成功源与 source-only commit

- 模块：`Shao/Probability/SourceLindleyRegulatorEnergyWeightedSecond.lean`，499 个实际源行。
- 本地精确副本：`drafts/c12-energy-weighted-square/SourceLindleyRegulatorEnergyWeightedSecond.lean`。
- 唯一远端 worktree：`/root/rivermind-data/shao-lean-20261021/workspaces/common-cone-derivatives-v44`。
- branch：`feat/common-energy-weighted-square`。
- source-only commit：`ba600e9fbcaeeb2142266a20ebf34b476605c911`。
- parent：`3993099d893ada6b91d53f6bbbadfdfaff96c123`。
- commit 的唯一变更路径经 `diff-tree` 确认就是上述新模块；所有原 producer source/object 保持只读。
- 新源 SHA256：`4fe9feece681194f9941691881695420f19cb0da3c8269bba023cb762f610859`。
- 格式：首次写入即严格 UTF-8、LF、无 BOM。成功源禁止项扫描无 sorry/admit/new axiom/unsafe/native_decide。

## 冻结一致性与数学范围

冻结文件为 `coordination/public-energy-weighted-regulator-square-declaration-freeze.md`，SHA256 `0b02ff5a791d09e452e390cd2a6f9904d09864173396494e1e8025ce6db5f0e4`。最终三个完整头（private 两个、public 一个）已与冻结全文逐字比对 `3/3 PASS`，包括每个 let 与 literal。零新增 global/private/generated 定义，无头/原假设/常数变化，无需 addendum。

唯一公开结论保留真实固定 x 条件律、非零实际 μ 和 μρ、包含当前坐标的 Q、同一 ambient N 长度 P、完整段与所有 first K≤N 的真正可积性/非负积分以及两个同 C 的数值界；`C=1024*exp(16+3*1024)`。

实现中有一项安全的内部加强，供独审定位：从 `2s exp(S)≤(1+y)^2` 与**同一** Λ 的两个非负 summand，先得到 `NM≤Λ/(1+y)≤1/4`，再放大为候选 `N|μρ|≤11/32`。这样避免战术对两个除法界的复杂处理；它没有改变任一头或增添假设。其后仍用 `NVρ≥1/6`，平方支付所有 k≤N 的漂移≤1 与 `m2ρ≤2Vρ`。min 缩放分支完整保留，实际 `Csurv=16exp(12+3*1024)`，换回原矩后的 prefix 系数 `48exp(14+3*1024)`。有限时钟中间系数 `768exp(14+3*1024)`，最终放大为冻结 C。

## 原成功 kernel/object 与直接返回值

服务器 artifact 根：`/root/rivermind-data/shao-lean-20261021/artifacts/common-energy-weighted-square/`。

`check002/` 是**首次完整源成功**的原记录：

- 同一命令检查完整新源并 `-o .lake/build/lib/lean/Shao/Probability/SourceLindleyRegulatorEnergyWeightedSecond.olean`；直接 rc 为 0，记录在 `check002/direct.exit`。
- 原成功源持久保存于 `check002/source.lean`，哈希同上。
- 原成功对象持久保存于 `check002/SourceLindleyRegulatorEnergyWeightedSecond.olean`。
- 对象 SHA256：`6416147d26faeb896927c9b708995d640b5cc531e0c41b40e7b0fc7054907eff`。
- `source.sha256`、`objects.sha256`、原 stdout/stderr 均保留在服务器；没有把原日志/二进制复制到本地工作区。

实际检查均为固定环境上的 `lake env lean -M8192 -j4 -DautoImplicit=false`，CPU10–13，并通过 `/root/rivermind-data/shao-lean-20261021/locks/root-heavy.lock` 与根/另一作者串行。没有本地 Lean、旧 producer 重编、缓存写入、旧 AX 重放或整库重复 build。

## 全所属实际类型/值与传递公理

在原成功对象上执行一次 established all-owned gate；`final/owned-audit.direct.exit=0`。选取依据是 actual module owner，覆盖 private/generated，非名称前缀估计。

- 11 个 actual owned constants，全部 theorem；其中 3 个显式定理（private2/public1）、8 个编译生成定理。
- 公开目标 1 个。
- 定义 0 个，须阅读的 literal definition values 为 0。
- 完整实际类型 11 个，使用 `pp.all=true`、`pp.maxSteps=10000000`、`pp.deepTerms=true`、`pp.proofs=true`。
- 原 audit stdout 与提取的 11 个完整实际类型均扫描 `⋯`/`…`，计数为 0。
- 每个 actual owned constant 均执行传递 `Lean.collectAxioms`，结果全部在 `propext / Classical.choice / Quot.sound` 白名单内。

精确证据：

| 文件 | SHA256 |
|---|---|
| `owned-audit.lean`（复用 established gate，仅换 target/public/path） | `8d60e028d2fb1463d46ea7faf908ec88aa1570d2aab75c234586e701f99630dc` |
| `actual-declarations.json`（完整 11 类型） | `43994492369e9593b72e8641cdbc666d68eaace7c301e50aee6e65ee1a675956` |
| `owned-axioms.json`（服务器 `final/owned-audit.json`） | `7c787c78e3887269d4338275807e5d9ee616cf393d517c17dbc6660f8c40130a` |
| `author-receipt.json` | `b14a8b667aa850c50a6c3e8216a182312e405a961e52d59c63f7c42a57a935ba` |
| 原 audit stdout，仅在服务器 | `55437219f8726c4635f45a0d26a40a4e8c4438a3827e80c6e5bc20e201c1c25c` |

前三份结构化证据均在本地本目录；服务器 `final/` 有相同字节。原成功 object/kernel/audit 可以直接复用，独审无需再次编译。

activation map SHA256 `f4197b6ad426673cf1708c6b1a55d901c51974c2469fe9b47d17fce46718ee45` 中 37 组上游 source/object 均在本单元结束时按实际字段重新算哈希，全部未变；这只是字节保全检查，不是旧证明或旧 AX 重跑。

## 原失败保全

`check001/direct.exit=1` 原样保留。其原源 SHA256 为 `cd9d83fa289e4c3925e9b7b7b5aee782f406db0bb5e4d2caebb8b8d7fe3f9fb9`；首次检查前已记录哈希，源后来通过完整逆转精确 proof-only 修复恢复，重算哈希逐字匹配该首次值。恢复字节保存于服务器 `check001/source.lean` 与本地 `check001-source.lean`，没有重跑失败检查。

失败原因仅为两个乘法单位等式未显式重写、两个平方根不等式交给 nlinarith 时缺少显式平方展开、一个战术分隔语法和一个已无目标的 rfl。修复只在 proof bodies，第二次整源即成功。两个 kernel 检查的原 rc、源字节和日志都保留；成功之后没有再修改生产源或重跑 kernel/audit。

## 后续源依赖

本单元下一步是根安排新鲜、作者独立的完整 source-to-statement/proof 审查，读取 499 行源与全部 11 实际所属类型，复用本 exact-source kernel/AX 收据。当前未发现本加权平方界的数学接口障碍。它与已接受 first-sum 共同填补原 supplement `h:eq:weighted`；完整 Taylor/概率预算仍需消费实际 kernel 导数界、不同时间区间的求和及后续比较链，本单元不把这些剩余义务计作已闭合。
