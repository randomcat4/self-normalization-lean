STATUS: CORRECT

独立完整数学/Lean 审查结论：精确 499 行实现忠实证明冻结的实际能量加权 regulator 平方和；未发现关键数学缺口或证据缺口。本结论只认证此辅助模块。所有本单元涉及的原研究根组、完整概率/Taylor 预算与 C1/C2 总组装仍 OPEN；既有其他根的状态不由本报告改写。

审查者 `/root/common_energy_weighted_second_full_review` 是 fresh 非作者上下文，只写本报告、同名 JSON/coverage 和指定辅助证据。遵守 math-theorem 与当前 streamlined acceptance；未使用 math-ultra，未改源码、冻结、旧证据、共享实现或 cache，未运行任何 Lean/旧 producer/旧公理检查，未开 PR 或合并。作者已在交接中 AUTHOR FINAL 并释放写权。本审查完成后也释放审查写权。

**精确对象与冻结。** 完整阅读 [499 行源码](</C:/game/shao lean/drafts/c12-energy-weighted-square/SourceLindleyRegulatorEnergyWeightedSecond.lean>)、[三份完整冻结头](</C:/game/shao lean/coordination/public-energy-weighted-regulator-square-declaration-freeze.md>)、source-contract、handoff、原唯一成功 kernel stdout/stderr，以及 11 个所属常量的完整实际类型、all-owned gate 和原传递公理收据。三个冻结头逐字存在于成功源码中（2 private + 1 public，3/3）；没有新增全局、private 或 generated 定义，需读的定义值为 0。源码为 24,728 字节、UTF-8/LF、无 BOM，禁止项扫描为空。实际类型与原 stdout 逐项逐字匹配，类型自身哈希全部重算吻合，原 stdout 与类型的 `⋯`/`…` 均为 0。

**原文到陈述。** 逐行读原 `main.tex:546–564,623–625,637–645` 与 `supplement.tex:573–595,797–818,2238–2329`。原 main 的固定 x 条件律明确允许非零均值；这里确为 `ν=cond ν0 {|a|≤ε/(1+x)}`，cutoff 不随 y 改变，`P=ν^N`。`Path N=Fin N→ℝ`，`lindleyState` 是从 0 开始的真实反射递归，`U_i` 是当前反射前位置的负部；`Q_i=prefixSquares a (i.val+1)` 是包括当前坐标的未中心化平方和。已读这些字面定义、`maxWithZero` 的 0..k 前缀最大值，以及 `truncationBudget=N∫truncationF((1+x)a)dν0` 的实际值。

公开假设与已接受 first-sum 的全部源假设相同：原律二阶可积、N 倍原二阶矩归一化、原均值零、x/ε/ε0 条件、实际 truncationBudget、κ 与固定窗。没有给原 ν0 新增三阶矩、对称/密度/无原子条件、条件均值零、倾斜均值零或结论型生存/BE/SP 前提。N=0 由原归一化排除。bounded support 及真实条件律/倾斜律的三阶可积性由所消费旧接口给出；不是借不可积 Bochner 积分默认值来获得结论。

新结论 `E_P Σ_i U_i² exp(-κy²Q_i)` 对齐原 supplement 的 weighted 第二式；它没有变成 `(ΣU_i)²`、终端能量加权和或边缘期望乘积。对所有 K≤N，`FK` 仍在同一 N 长度 P 下，以 `i.val<K` 截取。原证明 2305–2329 实际求和到 N，故全段并不背离原机制；K=0、K=N 和 i=0 都保留。固定允许的 κ 后，显式 κ^(-1/2) 是原文固定小 κ 所吸收常数的展开；没有宣称与 κ 无关的界。

**完整证明审查。**

1. 源码 18–25 的 `ews_min_one_mul` 在 v≤1 时使用 min≤u≤Av，在 v>1 时使用 min≤1≤A；没有用裸线性界代替后续实际 min predicate。
2. 27–124：令 s=κy²、S=sh²、E=exp S、ρ=ν.tilted(-sa²)。完整消费 `boundedEnergyTilt_drift_decay` 的实际律、可积性、Vρ=raw2ρ−μρ²、双向 raw3 与 V 比较；S∈[0,1] 给 1≤E≤3、V≤EVρ，故 NVρ≥1/6>0。
3. 125–165：`2sE≤(1+y)²` 与同一个 Λ 的两个非负 summand 联合给 `(1+y)NM≤Λ`，其中 M=|μ|+2sE m3。由 Λ≤1/2、1+y≥2 得 NM≤1/4，进而 N|μρ|≤1/4≤11/32。此内部加强没有增加任何公开/冻结前提。平方后 `(11/32)²<1/6` 与 NVρ≥1/6 给 Nμρ²≤Vρ；因此所有 k≤N 的 `|μρ|√k/√Vρ≤1`，以及 raw2ρ≤2Vρ。实际非零 drift factor 被支付，而非删掉。
4. 166–236：从 m3cρ≤8E m3、m3≤E m3ρ、E²≤exp2 得 m3cρ≤A m3ρ，A=8exp2≥1。正分母下把 survival 的 centered-third 比率压到 A 倍 raw-third 比率，再用完整 min 缩放。独立资格确认的 `iid_closed_survival_nonzero_drift` 允许 atoms 与真实非零均值；漂移因子≤exp4，故 `Csurv=2exp(6+3·1024)·8exp2·exp4=16exp(12+3·1024)`。真实 `lindleyPrefixSurvivalBound ρ N Csurv` 的全部 k/r 条件均已构造。随后 second-moment consumer 的 probability、raw3 可积、Vρ>0、raw2ρ≤2Vρ、C≥0 与 min 生存前提全部逐项满足。
5. 238–277：`√V≤E√Vρ` 与 m3ρ≤E m3 给 `m3ρ/√Vρ≤exp2·m3/√V`。`max 1 (3Csurv)=3Csurv` 已支付，得到每个真实 ρ^N 下 regulator 平方的可积性和 `Cp m3/(√V√(i+1))`，Cp=48exp(14+3·1024)。
6. 346–386：只从旧 first-sum 提取真实 law/support、S≤1、Nm2≥3/4、NV≤4/3 和 Λ 数据；不拿 first-sum 数值结论充当平方矩。另由实际 variance_bounds 得 V>0、NV≥1/2。对 ν 和 ρ 的 probability 实例与实际定义一致。
7. 387–408：完整消费联合 prefix change-of-measure 的 r=2 分支，给 `E_P[U_i² exp(-sQ_i)]=Z^(i+1) E_(ρ^N)[U_i²]` 及真正加权项可积性。U_i、Q_i 共同依赖前 i+1 个坐标；这里从未使用其边缘独立。Z>0 与 `Z^j≤exp(-(s m2/2)j)` 均是同一真实 ν/ρ 的值。
8. 409–477：非负且逐项可积，故有限和积分交换合法。取 t=(s m2/2)N，N>0 后确有 t/N=s m2/2，与旧 finite clock 的 exponent 精确相同。H≤4√N/(1+√t)、√N/√V≤2N、t≥3κy²/8、√t≥(√κ/2)y 和 √κ≤1 给 `1+√t≥(√κ/2)(1+y)`。因此中间系数 16Cp=768exp(14+3·1024)≤冻结 C=1024exp(16+3·1024)。所有除法分母严格正；sqrtκ 因子未丢失。
9. 478–497：`(1+y)^3 Nm3≤Λ` 产生相同 C 的 `CΛ/[√κ(1+y)^4]`，四次幂正确。任一 FK 通过相同 P 下的非负子和≤F、可积性及 integral_mono 得同样两个界；不更换概率律。所有原冻结头、假设、常数和结论因子均无变化。

**实际所属逐项覆盖。** 下表 P 表示完整公开名 `Shao.Probability.sourceTruncation_lindleyRegulator_energy_weighted_second_sum`；R 表示 `_private.Shao.Probability.SourceLindleyRegulatorEnergyWeightedSecond.0.Shao.Probability.`。完整展开名称、每项实际类型 SHA256 和公理列表见 [coverage JSON](</C:/game/shao lean/coordination/common-energy-weighted-second-full-review-coverage.json>)。每行实际类型已完整阅读，并与原成功对象的原唯一 all-owned stdout 比对；不是用名称前缀估计所属。

| 所属名称（用上述 P/R 展开） | 实际类型/语义审查 | 传递公理 | 结论 |
|---|---|---|---|
| R`ews_min_one_mul` | 三实数与 A≥1、u≤Av；完整 min 两支 | propext, Classical.choice, Quot.sound | CORRECT |
| R`ews_tilted_second_moment` | 完整原 helper 假设、所有 let、ρ 概率及逐 i 可积/平方界 | 同上 | CORRECT |
| P | 完整源假设/所有 let、全段及全部 K≤N 的真实积分结论 | 同上 | CORRECT |
| P`._simp_1_1` | NeZero 1 下 (0=1)=False | propext | CORRECT |
| P`._simp_1_2` | NeZero 2 下 (2=0)=False | propext | CORRECT |
| P`._simp_1_3` | NeZero 3 下 (3=0)=False | propext | CORRECT |
| P`._simp_1_4` | NeZero 4 下 (4=0)=False | propext | CORRECT |
| P`._simp_1_5` | 无零因子且 a,b 非零时 (ab=0)=False | propext | CORRECT |
| P`._simp_1_6` | IsReduced MonoidWithZero、a≠0、n:Nat，(a^n=0)=False | propext | CORRECT |
| P`._simp_1_7` | GroupWithZero、a≠0、n:Int，(a^n=0)=False | propext, Classical.choice, Quot.sound | CORRECT |
| P`._simp_1_8` | CharZero AddMonoidWithOne、n:Nat，(Nat.cast n+1=0)=False | propext | CORRECT |

8 个 generated 项都是证明 elaboration 产生的合法非零简化命题，未携带新的数学假设或隐藏定义。全所属集合恰为 11 theorem / 0 definition / 1 public；原 `Lean.collectAxioms` 对全部实际 module-owned 常量递归执行，限于 propext/Classical.choice/Quot.sound。审计脚本确按 env 的 actual owner 选取并包含 private/generated。没有 sorryAx 或其他公理。

**原服务器证据复用。** 2026-10-23T19:40:46.345965+00:00 只读观察确认 worktree `common-cone-derivatives-v44` 的 HEAD=`ba600e9fbcaeeb2142266a20ebf34b476605c911`，parent=`3993099d893ada6b91d53f6bbbadfdfaff96c123`，branch=`feat/common-energy-weighted-square`；tracked 工作树干净，commit 唯一 A 路径为本模块。提交 blob、当前源、check002 原源和本地源 SHA 相同；当前对象与 check002 原对象 SHA 相同。没有制造替代成功对象。

原 check002/direct.exit=0、final/owned-audit.direct.exit=0，保全的 check001/direct.exit=1；未重放任何一次。原成功 kernel stdout 仅含 letI/战术风格 linter，stderr 为已接受 package view 的 local-changes 提示，无 Lean error。作者原收据记录整源同命令 `lake env lean -M8192 -j4 -DautoImplicit=false ... -o ...`，CPU10–13/root-heavy.lock，原同次对象按原 objects.sha256 与实物哈希核对。固定 lean-toolchain=`leanprover/lean4:v4.36.0-rc1`，manifest/mathlib HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`；packages 实际解析到已接受 `cache-overlays/shared-v34/packages`。没有重新安装、更新、编译或更改 package view。

activation-map 的实际 37 行 source/object 对逐行重算均不变（37/37），仅为轻量字节保全；没有重读/重编旧 37 个证明或原生 DAG。新 Finite/Source survival 的既有 qualified 全审报告哈希也与指定值相同，按根已完整资格确认的结论复用；本次完整读取其实际消费头及全部条件，不重复旧证明。辅助本地解析最初把多行 AXIOMS 当单行，造成暂时 7 项；已按原 marker/multiline 格式修正，11/11 类型、名称、公理逐项吻合，原日志无改动，未触发 Lean 重跑。

**精确 SHA256。**

| 证据 | SHA256 |
|---|---|
| 成功新源（local/current/commit/check002） | `4fe9feece681194f9941691881695420f19cb0da3c8269bba023cb762f610859` |
| 原同次成功对象（current/check002） | `6416147d26faeb896927c9b708995d640b5cc531e0c41b40e7b0fc7054907eff` |
| 冻结 | `0b02ff5a791d09e452e390cd2a6f9904d09864173396494e1e8025ce6db5f0e4` |
| 11 完整类型 actual-declarations.json | `43994492369e9593b72e8641cdbc666d68eaace7c301e50aee6e65ee1a675956` |
| 全所属传递公理 owned-axioms.json | `7c787c78e3887269d4338275807e5d9ee616cf393d517c17dbc6660f8c40130a` |
| 作者原收据 author-receipt.json | `b14a8b667aa850c50a6c3e8216a182312e405a961e52d59c63f7c42a57a935ba` |
| 作者释放交接 handoff.md | `8623a413e8b56d43a171d6edd1ad48dbeaf92b2de9f277d24ab9d4abd02e21ac` |
| 原 all-owned gate | `8d60e028d2fb1463d46ea7faf908ec88aa1570d2aab75c234586e701f99630dc` |
| 原 all-owned stdout | `55437219f8726c4635f45a0d26a40a4e8c4438a3827e80c6e5bc20e201c1c25c` |
| 原成功 kernel stdout | `5926f0ae360c6016d19615b903de8ecb2f6c06b20d973d8294a913cd7733d129` |
| 原成功 kernel stderr | `e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b` |
| 原成功 direct.exit | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |
| 原 audit direct.exit | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |
| activation-map / 37 组不变源对象 | `f4197b6ad426673cf1708c6b1a55d901c51974c2469fe9b47d17fce46718ee45` |
| 保全 check001 原源 | `cd9d83fa289e4c3925e9b7b7b5aee782f406db0bb5e4d2caebb8b8d7fe3f9fb9` |
| main.tex | `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` |
| supplement.tex | `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd` |
| 既有合格 Finite/Source full review MD | `f50aeb9443ebab106618f2022fe9cf31be7d170c8a62fe11dd7613dcea8e3f8c` |
| 同 JSON | `10a61cdf820308970f7d4316aacc4076522e099bbe9b1625f424ab3afefe2cb6` |
| 本审覆盖表 | `fdecd820244983f46adaacc13d624334e313d242bf00d550f8fc70994d0a0b48` |
| 本审服务器只读观察 | `6b1d1e1dca7b44a64ea26059f319c2c88d40c45e4272048d8194a186c4eb197d` |
| 本审本地只读观察 | `c1a5ee4e90c8726e5fbadffd1a42d4a23026361e9bc74fdc7db834998fea0974` |

原完整日志/二进制仅留服务器 `artifacts/common-energy-weighted-square/check001,check002,final`；本地只新增紧凑可读观察与审查报告。无剩余修复请求。本单元可进入根的精确哈希/接口/交互与原范围验收；后续仍须实际消费 kernel/Taylor、时间区间求和和比较/去平滑链，不能由本平方和宣布根闭合。审查写权已释放，当前无本审进程、Lean 命令或锁占用。
