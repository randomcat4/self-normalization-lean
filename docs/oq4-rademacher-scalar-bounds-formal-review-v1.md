# OQ4 RademacherScalarBounds 独立最终形式审查 v1

STATUS: CORRECT
LEAN_STATUS: LEAN_FULLY_CHECKED
阶段：FINAL；已收到明确 AUTHOR_CANONICAL_READY。
时间：2026-10-22T01:18:25.116670+00:00

结论仅覆盖冻结的 SCA0、SCA1、SCA2、全域 scalar_bounds 及 z/rho 的实际 Cosine 透明定义桥。匿名数学证明完整，规范源在原始导入环境下独立无输出检查通过，正式导入后的完整陈述、定义、所有者、公理和实例登记一致。没有遗留数学或形式阻碍。

本次不认证 C_log/C_tan、概率 S2–S5、Brownian、strict 事件、一般 cosets 或 OQ4 root。原文72提供渐近展开；这里证明同一固定整数 H 的显式全 m≥1 辅助强化，不声称原文已给出这些全域常数。

## 独立性、输入与固定状态

本报告替换本人原 FINAL 路径中的 PREP 报告；PREP 原字节由 lead 归档为 [rademacher-scalar-bounds-prep-review-v1.md](<C:/game/shao lean/drafts/oq4/review/rademacher-scalar-bounds-prep-review-v1.md>)，11833 bytes，SHA256 ac6c97b7c9621c191891e136296001af55573e45541371dbf371007add1ec6c8。本人原 PREP raw/工具/命令日志的全部已登记指纹在最终阶段仍精确一致；FINAL 工具、raw 和日志另存 final/。

已在 PREP 完整读取 AGENTS.md、SERVER.md、coordination/TEAM.md、math-theorem 技能及必需 references；本轮沿用同一审查边界，不派发子智能体，不回滚他人工作。

数学与实现输入逐字节匹配：

| 输入 | bytes | SHA256 |
| --- | ---: | --- |
| 冻结声明 v1 | 9414 | 225b63ae8522a126cb5c126f83cb782b024e95f592e9e2da5f36f56e0ce21356 |
| 匿名 proof.md | 9434 | 17c21a775cc0e524e74614bb20c1c40ae2103408f8710fc259dd491f8929efcd |
| 原始 spectrum01.md | 4306 | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b |
| 规范 RademacherScalarBounds.lean | 11062 | 12670bd33a813849156b245cad28f5efb783a55919f8a0743fcf3fb9fbff329f |
| 唯一正式 .olean | 1011440 | eca40068036732752546d5280ce828ded6e42eeeb3c347c2d84a964617ad5380 |

规范逻辑模块为 Shao.OQ4.RademacherScalarBounds。
server worktree 为 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4；
branch feat/oq4-scalar-bounds；
基准 HEAD 045f6680004b1b62163b7a4a4c2612f9a42de3d6，审查结束时未改动。
Lean 4.36.0-rc1，commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e；Lake 5.0.0-src+c9afcdd；mathlib 807d3836b165983210ee2ecf3cd28f239436949c。

未读取作者执行回执、作者审计工具/raw、scratch/notes、其他数学或形式审查的推理。匿名证明自身获准全文读取；其自报状态不作为通过依据。旧 theorem proofbody 不导出、不人工读取；旧完整类型和透明定义值只从本人实际导入环境取得。所有代码与大 raw 仅在本人 server repro 目录，本地仅本审查报告。未写 Git/common/cache，未安装、更新或重发射构建产物。

## 数学与冻结陈述忠实性

八个定义全部展开核对：

H(m)=(m:ℝ)+1；
u(m)=π/(4H(m))；
z(m)=π/(2H(m))；
a(m)=H(m)⁻¹ cos(u(m))/sin(u(m))；
rho(m)=cos(z(m))；
lambda=π²/8；
C_a=π/3；
C_rho=π⁴/48。

SCA0 的17个合取项完整保留：H≥2，H/H²/H⁴>0；0<u≤π/8<π/2；0<z≤π/4<π/2；sin u、cos u、cos z、a、rho、πa/4 严格为正，且 rho<1。这些都是从 1≤m 推出的结论，没有变为额外假设。

独立逐步核对匿名证明及规范实现的承重推理。在 I=[0,π/4]，cos t>0 且 cos²t≥1/2。导数非负法（匿名稿以积分表示，实现以导数单调性表达）给出：

- t≤tan t≤2t；
- 0≤tan t−t≤4t³/3；
- 0≤−log(cos t)−t²/2≤t⁴/3。

cos 的正性先于除法、log 与导数使用；闭区间端点0和π/4均涵盖，没有循环引用待证 Taylor 余项。
对真实 u，a=(4/π)(u/tan u)，tan u≥u>0，所以去绝对值及分母比较合法，得到 |a−4/π|≤(π/3)/H²。
对真实 z，lambda/H²=z²/2，log 余项的符号与绝对值对应准确，得到 |log rho+lambda/H²|≤(π⁴/48)/H⁴。

scalar_bounds 的存在量词先选两个绝对实常数，再对全部自然数 m≥1 量化；没有逐 m 常数、H0、“充分大”、自由 H、h/n、序列、奇偶或概率正性前提。m=1 对应 H=2,u=π/8,z=π/4；m=2 对应 H=3,u=π/12,z=π/6，均保留且经独立 Lean 专项检查。

Semantic.lean 实际检查八个定义的完整展开、SCA0/1/2 的显式三角函数版本、全域存在常数量词顺序、m=1/m=2，以及
z(m)=Shao.OQ4.RademacherCosine.angle m、
rho(m)=Shao.OQ4.RademacherCosine.rho m。
检查只用这些已认证透明定义识别，未把 S1/Pair/Tail 或概率结论引为本叶前提。

## 原始源码环境与真实导入比较

规范文件本身独立运行：
taskset -c 0-3 lake env lean -R . Shao/OQ4/RademacherScalarBounds.lean
退出0，5.065秒，无 -o。

A/AProject 都只前置必要的 import Lean，随后原11062 bytes连续完整保留于 [12,11074)，再追加本人反射。真实 -R 主模块为 Shao.OQ4.RademacherScalarBounds；无 --stdin、无 self-import、无旧42 imports 前缀。A 对所有 getModuleIdxFor? none 无任何 name 过滤。

原始四项导入保持原顺序：
Shao.OQ4.RademacherCosine；
Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv；
Mathlib.Analysis.SpecialFunctions.Log.Deriv；
Mathlib.Analysis.Calculus.Deriv.MeanValue。
A 的实际直接导入只有这四项加审计 Lean 和隐式 Init。原 noncomputable section 与已结束的 namespace 作用域也按实际状态对齐。

| 环境 | 实际用途与结果 |
| --- | --- |
| A | 原完整源码、真实模块、ALL none：59声明 = 8 definition + 51 theorem，其中private9 |
| AProject / A0 | 源码实际加载的69个项目声明，与原四项纯imports及相同词法上下文逐字段一致 |
| B0 | 全旧42实际imports，补原数学导入以对齐closure，全部旧931声明 |
| B1 | 全旧42 + 实际 import 新target；实际全43导入，实测990声明 = 108 definition + 882 theorem |
| Direct | 实际直接import target，按真正module owner选择：全部59项与A完全一致 |

B1 的完整导入闭包实测5680模块。OQ4 实际导入模块为43个；有自有声明的 owner module 为42个。差异恰为 Shao.OQ4.Foundations 在实际环境中无自有声明记录，不能人为制造一项声明或伪报43个owner。990是对实际B1记录计数，未用931+59代替测量。

旧42的全部931记录均保留，包括 namespace 外的 Shao.closedUpper.eq_1、private 包装和生成声明。比较 raw Name、user Name、kind、全部宇宙参数、完整 Expr type、100个完整def value、元字段、安全/partial/private/instance标记、公理与 actual owner。源/direct 的全部8个新def value也完整一致。opaque kind 实测0；theorem proofbody 不作为旧记录导出。

真实 raw Name 的 old∩source 为0，归一 userName 的交集为0；这是由实际集合计算出的事实。source 与 old raw/user OQ4 namespace 范围的交集为59，不能将其误作空集或重复计入旧记录。比较器从不预设 raw 交集为空；旧 owner 保留逻辑已在本人PREP的实际旧外名/private def交集 fixture 中验证，并在本轮对全931旧记录实际核对。

## 全部实例登记、公理与保护

逐结构直接比较，不以摘要哈希代替登记或 Expr 比较：

- PREP旧环境到B0：全部共同模块的 imported instance/default entries 及共同模块顺序逐项保留，旧931字段和100定义体精确保留。
- B0到B1：完整运行态登记一致；额外真实target的 instance entries 与 default entries 均恰为一条空数组。
- A0到A/AProject：同原imports、同noncomputable section、同opens与section作用域的完整登记一致。
- A到Direct：同闭包与词法上下文，除真实target空登记模块外完整一致。

核对范围包括 active/global/scoped/private/inactive/erased/new、instanceNames、全部 stateStack、activeScopes、delimitsLocal、scopeChanged、scopeChangedDecls、default class entries/priorities，以及 discrTree 实际 chain/node/path/entry/children。keys、val、priority、globalName、synthOrder、attrKind及所有 order_sensitive 数组顺序均保留；没有任意删登记或排序这些数组。Name/Level/Expr/MData/Syntax/key为完整构造器编码，无深度截断，无仅pretty-print的表达式比较。

对实际全部990声明逐个核公理及flags：新增axiom kind=0，unsafe=0，partial=0。公理并集恰为 propext、Classical.choice、Quot.sound。新源码禁用项扫描通过，没有 sorry/admit/axiom/unsafe/partial/native_decide。

前后及收尾逐字节SHA保护全部通过：旧134源/配置加规范Source，精确whole source/config fileset=135；旧99构建产物加唯一soleolean，精确whole .lake/build fileset=100。没有额外target .ilean/.hash/.trace/.c/.o等产物。完整每项路径、bytes、expected/actual散列见 protection-before.json / protection-after.json。唯一soleolean保持上述1011440 bytes与eca40068完整散列。

emit0 / liveLean0 / reviewerPrivateLeanArtifact0。全部8次FINAL Lean调用均退出0，无后台任务；未重发射规范或私有Lean构建产物。

## 命令、失败与检查点

所有Lean/大JSON工作仅指定server，先source activate、再cd工作树，taskset -c 0-3单进程，无 -o。完整原命令、stdout/stderr及其散列在 final/commands.jsonl 和 final/final-receipt.json。

| 日志名 | 秒 | 退出 |
| --- | ---: | ---: |
| Canonical | 5.065 | 0 |
| A | 21.958 | 0 |
| AProject | 21.989 | 0 |
| A0 | 20.355 | 0 |
| B0 | 30.690 | 0 |
| B1 | 30.472 | 0 |
| Direct | 20.405 | 0 |
| Semantic | 4.217 | 0 |
| Compare | 94.029 | 1 |
| Compare2 | 119.851 | 1 |
| Tail | 9.801 | 0 |

FINAL有两项本人检查器失败，均如实保留：
第一轮错误地要求43个“有声明owner”，实际应分别记录43 imports和42 owners；在旧931/100定义体与B0/B1完整登记已通过后，于计数断言退出1。
第二轮已完成全部结构比较、原始raw/user交集、A/Direct/A0登记与字段、135/100保护及PREP指纹核对，最后把第一轮比较器失败日志也混算为“Lean失败”，故仅收尾分类断言退出1。实际8次Lean均0。

未重跑有效Lean。保留 check.first.py、check.second.py、failure.first.json、failure.second.json 及两次stderr；只从第二轮已通过的完整结构检查点恢复正确的命令分类、Semantic执行状态、交集独立复计与终端保护。Tail退出0，9.801秒；最终72项证据检查全部通过。当前check.py已修正分类谓词，但最终通过依据明确是保留的Compare2结构检查点与实际执行的Tail收尾，不伪称失败命令退出0。PREP的7项历史在原归档中保持不变。

## 服务器证据定位与指纹

本人server根目录：
/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-scalar-bounds-independent-v1/
本轮所有raw/代码/日志位于其 final/。本地没有取回任何大raw。

| final/文件 | bytes | SHA256 |
| --- | ---: | --- |
| A.json | 173969320 | 293739fa6c6240d5838bdd0cbad48d70be7c97d3ca444896854b4f330d755130 |
| AProject.json | 174126008 | 26c96f5265fc63d6657b65094e30d4d4ed894f5a9c668729fde31a72f51a1f7f |
| A0.json | 174125930 | e2e72842f335380648a26b43199d387244b80c6d4f73cd8d1680b26c24c09028 |
| B0.json | 199168155 | 42f2b55b2eae95f0aeedf4d18f8961ea8d5b93810cdadc3638817eae8e5cf963 |
| B1.json | 199445658 | 76d15a581d094e18aece370790907b75ffba2b65d55d5ce22cd145a1410c970f |
| Direct.json | 173969215 | 61b3772a2886799464877176f245be22e8e212b617babbe57bf2cd9c25156d91 |
| Semantic.lean | 3254 | de98ced069eef58eb0d5737f3ea890ac00276e9339518f3cca60a9a64154e359 |
| comparison-results.json | 21172 | 9a8811371546776a50092d7dd49445ccd0e8deb401f21db45d2738d8733d637f |
| protection-after.json | 66595 | 05fd19404bd69438a13342881921212715226db80aad3059db33377ca029b125 |
| verified-comparison-inputs.json | 1784 | 5d543bce15c8b27cb3cc54dd4f770051f9127014a62c38ea84f4986ed31e98d0 |
| commands.jsonl | 4884 | d960e7a92c28f51f47ecef67ffdcec1e34f2aded7ec30cc7f3e386161a26ecd4 |
| check.first.py | 10638 | f6e595f1af56543802aa7addcda0a9c07050d71f1a54d61c988b01074e8d7305 |
| check.second.py | 11102 | 3c35db5edacb398d9b7e01e53fa82f2002d7de4bcd2d17e6b9476962de465610 |
| check.py | 11139 | f9349f5a29dc78d864ad2cf243dd53b5e808cab24d76c1bbc30a02c4603123b6 |
| tail.py | 6991 | c088204c1bca53553835791f075ef7166819464e1634d654a66f151e0c505949 |
| final-receipt.json | 19877 | 3aba00dbe40f1462b0be9eb0ceeeecad1eae442d92d000600fc6aaa48bb387d2 |

完整清单还覆盖生成receipt、所有stdout/stderr、各纯imports驱动与恢复脚本，均在 final-receipt.json。PREP基线 raw SHA256 0ecf1c5e6401ee00f71acb9d98d2e597235c42d461b2fbc0bbffd0d86f239409（140080519 bytes）及全部原工具指纹保留。

最终裁决：冻结SCA0/SCA1/SCA2及其全域绝对常数存在结论、实际Cosine桥，CORRECT / LEAN_FULLY_CHECKED。没有待修数学缺口；后继概率与OQ4 root范围仍由各自独立门处理。
