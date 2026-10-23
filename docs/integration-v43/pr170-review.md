# PR170 独立根验收

STATUS: CORRECT

本结论限于冻结的 `Shao.OQ3.CompactTiltCovarianceSpectrum` 完整数学证明、Lean 源码语义和所交付服务器检查证据。两个公开定理忠实实现 U21d 冻结接口；未发现遗漏量词、暗加前提、把真实概率对象换成任意矩阵或总化积分的关键缺口。OQ3 B/C/D 仍为 OPEN。本报告不替代主协调随后执行的实时 head 查询与正常服务器整合门。

审查者 `/root/pr170_acceptance`，根协调 `01a16680-f408-7391-8c52-d1d5041bda8b`；只拥有本 `.md/.json` 两个文件的写权。已读 AGENTS.md、SERVER.md、TEAM.md、REGISTRY.json、接管与 OQ3 交接。使用 math-theorem 及其验证协议；没有启用 math-ultra。全程本地静态阅读，无 Lean、远程操作、Git 操作、缓存修改、源码修复或子代理。

独立评估在 **2026-10-23 02:31:42 UTC** 完成：此时尚未读取 `drafts/oq3/u21d-proof-review.md`。以下数学判断先独立形成；旧票只允许在此后作查漏交叉核对。

## 1. 冻结版本与字节绑定

| 工件 | 本轮核对值 |
|---|---|
| PR | https://github.com/randomcat4/shao-lean/pull/170 |
| 分支 | `feat/oq3-compact-tilt-covariance-spectrum` |
| 冻结 head | `7bf3e70682f203a08aa36043f8dc6e6e7362d701` |
| 冻结 tree | `d5f1ec72e93e4baeb450b957afe622061a4798c7` |
| parent | `7832c37251145161d095daac02e3506db90b3910` |
| 生产源 | `Shao/OQ3/CompactTiltCovarianceSpectrum.lean`，本地审阅副本 `drafts/oq3/CompactTiltCovarianceSpectrum.lean` |
| 源 SHA256 | `99b8b9b20f1860ddd7890d8b4d317825ce76572e1c0d209d6843340a33b0c634`，285 行 / 14942 字节 |
| 冻结接口 | `drafts/oq3/eightieth-unit-scope.md`，83 行 / 7782 字节，SHA256 `b30cd580532e687dc5bc385a06965281e93ea55cc8160363824c5ed70d655b83` |
| 实际类型 | `drafts/oq3/u21d-actual-types.txt`，99 行 / 5853 字节，SHA256 `5b1f060217abea8a6d7459e0934cf6f6af54ab9e68a5e32f75102c47c60bf270` |
| 作者收据 | `drafts/oq3/u21d-receipt.json`，SHA256 `76dfbe0bd2a3590f635c2f5a694cf9d445e8da18dada1e3fa0551e032b377da5` |
| 审计程序 | `drafts/oq3/u21d-Audit.lean`，SHA256 `f7bbfd69e07ace9cd69873798bcd839cd654543650980cc08ddcdc57e7c38863` |
| 审计记录 | `drafts/oq3/u21d-audit-record.json`，SHA256 `c9a347fcc03029ccbbbb66fe006f4e6f9acf12988798777a274647eb39c76c1f` |
| 原文 R2 | `C:/game/shao/current/oq3/proofs/r2/report.md`，SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55` |

源、冻结、实际类型、收据、Audit、审计记录和 R2 的上述 SHA256 均由本轮对本地实际文件计算。head/tree/parent 从 `oq3-handoff.json`、`u21d-pr-handoff.json`、`u21d-commit-state.json`、`u21d-api-publication.json` 与 `u21d-pr-verification.json` 交叉核对一致；后者记录一个提交、一个新增生产模块及五个 docs 工件，未修改已有生产源。没有声称本轮自行验证了实时远端 head。

## 2. 原文、冻结、源码与实际类型

原文 R2 38–60 定义 `W=(X,X²)`、真实指数倾斜律及协方差谱 (2)；74–76、343–369 要求有界情形从参考单点 WC 得到紧参数族的统一常数；83–92 是随后标准化的消费者。本次不是完整鞍点展开、Hessian 等于协方差或标准化装配的证明。

已逐行阅读 83 行冻结、285 行源码及 99 行完整 owned 实际类型。公开接口逐项相符：

- `parabolaCovariance_pos_of_weakCramer`：冻结 17–30、源 99–112、实际类型 25–43。输入为真实概率律、AE 有界、`M≥0`、任意实 `beta/R`、`c>0` 与半径大于 R 的实际联合特征函数界；输出两对角元、行列式严格正，及所有非零二维方向的严格二次型正性。没有假设原子质量、先给正定矩阵或较强非格点性。
- `exists_compact_tilted_covariance_spectral_bounds`：冻结 32–64、源 182–214、实际类型 57–99。`mu0` 与每个 `mup` 都是同一底律的真实二次倾斜，D0 固定为 `parabolaCovariance mu0`。单个 `m>0, m≤1` 在 `∀ p∈K` 之外，且固定 `lambdaMin=m*det(D0)/trace(D0)`、`lambdaMax=2(M²+M⁴)+1+lambdaMin`。输出同一族的概率性、AE 支撑、两个真 L²、同 m 的测度下界、全部频率的上下二次型界和同 `beta/R`、新常数 `m²c/2` 的原始 WC。

没有 K 非空、参考点属于 K、协方差连续性、统一正定下界或调用者传入谱的额外前提。两公开定理的隐式上下文只有 `IsProbabilityMeasure mu`；实际类型没有捕获额外 section 变量。0 公开定义、2 公开定理与冻结一致。

## 3. 真实对象与已接受依赖

沿实际导入与定义检查：

- `library/Shao/OQ3/JointNonlattice.lean` 20–24：`jointPhase xi eta x = exp(i*(xi*x+eta*x²))`，`jointCharacteristic` 是其对所给 measure 的 Bochner 积分；26–35 给单位模和真可积性。未把需要证明的 CF 界重新命名为定义。
- `library/Shao/OQ3/RegularCovariance.lean` 20–24：矩阵确为 `Var(X), Cov(X,X²), Var(X²)`；两个交叉项字面相同，是真实对称协方差，不是任意矩阵。旧文件的特定四原子/固定界正定定理没有被拿来覆盖本次任意有界律。
- `library/Shao/OQ3/TiltedMeasureDomination.lean` 17–34：AE 有界保证任意实二次参数的指数真可积；36–79 展开 Mathlib `Measure.tilted` 的归一化密度，分割函数严格正后才除法；81–102 给参考与目标倾斜律下界。
- `library/Shao/OQ3/CompactTiltDomination.lean` 15–28：对紧 K 的连续坐标差给统一盒界；30–56 得统一正 `m0=exp(-2B)`。空 K 不需选择元素。
- `library/Shao/OQ3/CharacteristicMeasureDomination.lean` 17–62：在真概率测度分解 `nu=(nu-m*mu)+m*mu` 上积分，剩余质量 `1-m`，得真实 CF 模上界。
- `library/Shao/OQ3/CompactTiltWeakCramer.lean` 17–91：取 `m=min m0 1`，给同 m 的测度下界、平方缺口与 `m²c/2` WC。该定理的完整签名已核对，本次源 228–229 仅调用一次，244–245 保持其同 m 输出。

`u21d-prerequisite-hashes.json` 的全部 **18** 个项目依赖条目与正式 `library/verification/receipt-v42.json` 的 `source_files_sha256` 字典逐项比较，差异为空；没有重新哈希稳定依赖或缓存。v42 收据为 PASS，审计 5547 个项目所属常量，白名单 std3，Lean `leanprover/lean4:v4.36.0-rc1`、Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，记录的 actual Mathlib commit 相同。本轮依赖信任边界为此已接受库及其标准概率定义；没有在本地另外安装或构建 Mathlib。

## 4. 四个私有引理的完整核查

**源 17–27，`bounded_parabola_memLp`。** 连续的 X 在 AE 绝对值界下由 `MemLp.of_bound` 得真 L²；将 `|X|≤M` 平方得 `|X²|≤M²`，再得 X² 的真 L²。`pow_le_pow_left₀` 用 `0≤|x|` 和实际 hb，不依赖未经证明的矩。该辅助不需要 hM 参数，不产生更强公开假设。

**源 29–45，`quadratic_variance_eq`。** 在两个真实 L² 输入下，`variance_fun_add`、`variance_const_mul`、协方差左右常数乘法把 `Var(xi X+eta X²)` 精确变为 `xi² a+2 xi eta b+eta² d`；真实矩阵定义可 `change` 展开，ring 只做代数归并。没有把不可积函数的总化 variance 当真方差使用。

**源 47–65，`variance_lower_of_measure_lower`。** 双方均为真概率、f 在双方都是真 L²，m 非负且 `ofReal m • mu≤nu`。取 `z=E_nu f`。在 mu 下，平移不变性与 L² 的 `variance_eq_sub` 给 `Var_mu f≤∫(f-z)² dmu`；在 nu 下同一中心正是 `Var_nu f=∫(f-z)² dnu`。非负平方在 nu 真可积，`integral_mono_measure` 后用 `integral_smul_measure` 与 `toReal_ofReal hm` 得 `m∫(f-z)² dmu≤∫(f-z)² dnu`。再乘 m 非负并传递。中心平方比较是正确的；没有假定方差本身对 measure 无条件单调。

**源 67–97，`quadratic_variance_upper`。** AE 界给 `x²≤M²`、`x⁴≤M⁴`。非负平方 `(xi*x²-eta*x)²` 等价于二维 Cauchy 上界，故 `(xi*x+eta*x²)²≤(xi²+eta²)(M²+M⁴)`。真 L² 使平方可积，概率积分把常数积分化为本身，`Var=E f²-(Ef)²≤E f²`。证明实际得到比冻结上界更强的系数 `B=M²+M⁴`，随后合法扩大到冻结的 lambdaMax。

## 5. weakCramer 到严格正定的承重链

源 113–164 对任意 `xi≠0 ∨ eta≠0`，先获得投影 f 的真 L²。若不能证明正方差，由 variance 非负得 variance=0；`ae_eq_integral_of_variance_eq_zero hf` 给 **真实均值的 AE 常值性**，不是每个点常值。

源 125–138 令 `rho=sqrt(xi²+eta²)>0`、`T=(|R|+1)/rho>0`。先证分母正，再证明放大后的半径恰为 `|R|+1`，所以严格大于任意实 R。源 139–154 把 AE f 常值性代入相同测度的实际 `jointPhase`；概率律常数积分给特征函数等于单位复指数，其模恰为 1。源 158–163 用正半径的实幂对 **任意实指数** 严格为正，再乘 `c>0`，与 WC 的严格亏损矛盾。既不需要 beta/R 非负，也没有拿非零频率的模小于 1 当作额外输入。

源 165–180 依次取方向 `(1,0)`、`(0,1)` 得 a,d>0；取 `(-b,a)`，由 a>0 保证方向非零，得 `a*(a*d-b²)>0`，再以 a>0 得判别式正。`Matrix.det_fin_two` 加真实交叉项对称性把它绑定为实际 det>0。输出的全方向严格正性是同一 hpos，未仅证明有限个方向。

## 6. 紧倾斜族统一谱的承重链

源 215–224 在所有后续方差推理之前，已由真指数可积构造 `IsProbabilityMeasure mu0`，由 `tilted_absolutelyContinuous.ae_le` 传递 AE 支撑，再得两个真 L² 和参考 a,d,det>0；trace>0。源 225–235 因真实对称性得到 det 公式、定义固定 lo/hi，并先证 lo>0 与 hi>lo。没有除以可能为零的 trace。

源 228–245 从已接受 159 接口得到单个 m，保留同 m 的测度下界与 WC；任意 p∈K 的 mup 又独立证明是真概率及 AE 支撑、L²。m 与 lo/hi 在 p 和频率外固定。

源 247–263 对任意实频率写 rr=xi²+eta²≥0、参考二次型 q0，证明精确恒等式

`trace(D0)*q0 - det(D0)*rr = (a*xi+b*eta)² + (b*xi+d*eta)² ≥ 0`。

trace 正，故 `det(D0)/trace(D0)*rr≤q0`。这是完整二维方向的谱下界，不只是 det 正性。源 264–277 给双方投影真 L²，调用私有中心方差比较并用精确 qD=variance，得 `m*q0≤qp`；与前式相乘、传递，正好得到冻结的 `lo*rr≤qp`。

源 278–282 应用真概率上界 `qp≤B*rr`；由 B≥0、lo>0 得 `B≤hi`，再以 rr≥0 扩大为 `qp≤hi*rr`。lambdaMax 严格大于 lambdaMin 不借助 K 中的任意点。所有频率含 `(0,0)`，不存在只对非零频率成立的遗漏。

## 7. 全部 owned 声明与传递公理覆盖

Audit 源 25–38 遍历整个 `env.constants.toList`，用 `getModuleIdxFor?` 的实际所属模块筛选，**没有仅按 Shao 命名空间或公开名单筛选**。每个 owner 常量先拒绝 axiom，再 `Lean.collectAxioms name` 递归收集并逐项拒绝 std3 外公理；目标检查要求两个公开名实际为 theorem。末尾报告全部 theorem/常量数。`pp.deepTerms/pp.maxSteps` 只影响打印；生产源没有 set_option，也未见 sorry/admit/新 axiom/unsafe/native_decide/implemented_by。

完整实际类型输出列出 **7 owned = 7 theorem = 2 public + 4 private + 1 generated**，0 definition：

| owned 声明（私有名共同前缀见下） | 实际类型行 | 传递公理 |
|---|---|---|
| `bounded_parabola_memLp` | 1–4 | propext, Classical.choice, Quot.sound |
| `quadratic_variance_eq` | 6–14 | 同 std3 |
| `variance_lower_of_measure_lower` | 16–23 | 同 std3 |
| `Shao.OQ3.parabolaCovariance_pos_of_weakCramer` | 25–43 | 同 std3 |
| `quadratic_variance_upper._simp_1_1` | 45–47 | 空集 |
| `quadratic_variance_upper` | 49–55 | 同 std3 |
| `Shao.OQ3.exists_compact_tilted_covariance_spectral_bounds` | 57–99 | 同 std3 |

私有完整前缀为 `_private.Shao.OQ3.CompactTiltCovarianceSpectrum.0.Shao.OQ3.`。生成项实际类型为 `∀ {M : Type u_2} [Monoid M] (a : M) (m n : ℕ), (a^m)^n=a^(m*n)`，是源码 82 的 pow_mul 化简生成证明，无公理；不是漏审的概率假设或协方差定义等式。其余六项全部在 std3 内。输出没有省略号，公开类型与冻结逐项一致。没有漏掉私有项、生成项或旧命名空间 owner 项的证据。

服务器记录：源码 attempt 1，2026-10-23T01:53:47.137622+00:00 开始，`lake env lean -M8192 -j4 -DautoImplicit=false -o ... Shao/OQ3/CompactTiltCovarianceSpectrum.lean`，exit 0，5.446220692 秒，log SHA256 `9bf40faca95d17d491f79dcc23a03e481bc1a3190916b4f620408460419f625b`，1433 字节；4 条未用绑定/letI 样式警告不改变证明。owner audit 2026-10-23T01:54:51.244363+00:00，exit 0，5.512016213 秒，log SHA256 `c9e6f8a849d04f0c62e875b99d51fa8e3694d65a6b1c9ea9cb629e38f47b17ae`，5961 字节。二者绑定同一源 SHA，CPU14–17、8192 MiB、j4。首成功后无源修改、无重复成功检查。

机械证据来源是本地收据、build-history、audit-record、完整实际类型与已阅读审计程序；全量原始日志按项目规定留在服务器，本轮没有读取或重新计算其摘要。这里接受既有服务器检查收据，不伪称本审查者亲自重跑。缺少实时远端查询及正常根整合门是明确留给主协调的工作，不是静态证明缺口。

## 8. 量词、边界与范围

- K 可空；此时 lo/hi 仍由参考 WC 的正定性构造，非空假设没有被偷用。参考 `(u0,v0)` 可在 K 外。
- M=0 没有被删除；真实概率支撑退化到 0 时与 c>0 的 WC 不相容，证明会由前述方差矛盾处理，而非除以 M。
- `beta,R` 任意实；正定矛盾只在正半径 `|R|+1` 处用 rpow。后续 PR169 若要求 `beta≥0,R≥0`，仍应在装配中显式保留，不能由本定理静默删除。
- 全频率谱界含零频率；严格投影正性只要求非零方向，rho 除法前有严格正性。协方差/积分在使用时均有概率性与真 L²。
- 同一 m 同时用于测度下界、lambdaMin 与 WC 新常数；m、lo/hi、参考律与所有输入均在 p/频率/n 外固定，沒有 n 依赖。
- 本次关闭的是有界紧倾斜真实协方差谱这一具体承重前提；**尚未**与 PR169 白化/全阶矩/标准化 WC 组装成完整有界 C 接口，不自动关闭 C。
- 一般无界 B、通用 Hessian=cov/均值逆、Edgeworth/胞重建/Laplace/远区概率、D 的丢番图幅值/十六抛物线原子/近共振/小 x 鞍点等均不在本次证明范围。原 A 的 v40/fixed-x0/vCorr 既有结论不扩展。
- 没有新颖性、最优 beta、端点或随 x 一致性裁决。

## 9. 旧审查后置查漏

在以上独立评估写入本报告后，完整读取了旧 `u21d-proof-review.md` 的 343 行，实际 SHA256 `339f915b7fb68519d5c489fca2f07257e7c644a304e0c6b8c1bc5d237f12a790`。其最终 CORRECT 位于 146、341 行，开头 IN_PROGRESS 是保留的盲审历史检查点；其 325 行的 parent HEAD 是提交前观察，不能当作当前 PR head。当前 head 由第 1 节的后续提交/发布/交接证据绑定。

旧报告与本轮独立结论一致，未发现额外关键缺口。后置查漏确认了私有方差比较允许 m=0、生成项不是协方差定义等式、较强私有上界 B 的 Cauchy 恒等式，以及标准化消费者仍须保留 beta/R 符号门；这些要点已经在本轮先行独立评估中核查。旧报告还记录了其当时对固定 Mathlib API 与服务器实际日志续行的阅读；那是旧审查者的观察，本轮没有把它改写为自己的远程检查。

最终 **STATUS: CORRECT**；没有源码修订或需要回送作者的关键缺口。主协调仍需核对实时精确 head 并完成正常服务器整合门；原 OQ3 B/C/D 保持 OPEN。
