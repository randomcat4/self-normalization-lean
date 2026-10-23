# OQ3 U22u / U22v 独立完整最终审查

STATUS: CORRECT

Udet: CORRECT. Uamplitude: CORRECT. Vexp: CORRECT. Vweighted: CORRECT. Batch: CORRECT.

本裁决限于两个冻结模块的四条完整声明及证明。没有发现冻结范围内的关键缺口。现有精确源码的服务器内核和全部实际所属声明的递归公理检查可以复用；本审查没有重新运行 Lean。原 OQ3 B/D 及其他未闭合根不因本报告而闭合。

审查时间：2026-10-23，服务器证据最后核对时间 09:38 UTC。角色为本次唯一 fresh 独立完整最终审查员，与作者分离；委派配置为 gpt-6.1-sol / xhigh。仅本报告具有写权。未修改源码、冻结声明、旧报告、收据、缓存或版本锁，未启动其他上下文。本上下文没有可核验的输入、缓存输入、输出、推理子集 token 计数，故未填造用量或订阅比例。

## 1. 冻结版本与覆盖

本地证据目录为 `C:/game/shao lean/drafts/oq3/`。对以下文件实际计算 SHA256，并与任务绑定及服务器运行目录中的对应文件逐字节哈希核对。

| 单元 | 文件 | SHA256 |
| --- | --- | --- |
| U | u22u-source.lean | c6f20047e1ef46331b19619f05a72dd7e3ecf60bc1ffad7d2d952599ce5f8a1e |
| U | hundred-second-unit-scope.md | 29ab529b5cf63cc672fd56a283c2472b2600fedaab6cdfcb295c69e001755cd7 |
| U | u22u-receipt.json | 8515a250f98df237d3a878fdfbdfa7bba3da062ae4ac2ac35bc587be32047677 |
| U | u22u-actual-types.txt | b3db72b19a4f35be514bea5073d000a38dc82299ae4fae089623ac7e858d977a |
| V | u22v-source.lean | 5fbfe14dd8e6cf5bb36269c7b988d212e55cb4f0ba6eb5b943337581ed0f1ae7 |
| V | hundred-third-unit-scope.md | fced2535f79179810a173acc21fb98314a4ba69b58f9ed93e89abc97c6ed464f |
| V | u22v-receipt.json | 1943d3a58819822b316216de1dd43fc0285ffdd916dbc27d82bc10e36f4f871b |
| V | u22v-actual-types.txt | 9efcd108785fbefd95d0479886279a1efe96a1e00e8fd3e3d739eb4a9b5b6075 |

U 源为 178 行、8956 字节；V 源为 49 行、2363 字节。两份 Lean 源均严格 UTF-8、无 CR、以 LF 分行。服务器当前工作树源码和成功运行保存的 U source-02.lean / V source-01.lean 均与这些源码匹配。收据原有 CRLF 字节保持原状，没有为了格式统一改写冻结证据。

已完整读取两份冻结范围、两份源码、两份 actual-types 和两份 Audit.lean。还独立比较了四条源码声明在 `:= by` 之前的完整签名与冻结代码：仅压缩空白后全部相等。量词、前提、let 定义、合取结构及存在常数的顺序均未变化。

| 所属模块与声明 | 声明行 | 证明行 | 覆盖 |
| --- | --- | --- | --- |
| Shao.OQ3.OpenDomainCovarianceAmplitude: open_domain_quadratic_covariance_det_contDiffOn | U9–14 | U15–56 | 完整 |
| 同模块: open_domain_chart_covariance_amplitude | U58–89 | U90–175 | 完整 |
| Shao.OQ3.BoundaryLaplaceExponential: abs_exp_neg_sub_exp_neg_le | V8–10 | V11–22 | 完整 |
| 同模块: abs_weighted_exp_neg_sub_le | V24–28 | V29–46 | 完整 |

U1–8、U177–178、V1–7、V48–49 的导入、命名空间和 section 边界也已检查；其余为空行。实际所属声明共四条，全部是上表定理。两个模块各为 2 public theorem、0 definition、2 all-owned、2 all-theorem、0 private/generated theorem；没有额外所属定义的值需要遗漏补审。证明内所有实际局部 let 值均在以下证明检查中覆盖，不能把它们误计为新增模块定义。

## 2. 原始来源与实际接口

原始只读来源为 `C:/game/shao/current/oq3/proofs/r2/repair01.md`，全文件 SHA256 为 `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`。完整读取了所需第 1–210 行：式 (8) 的边界坐标、式 (12) 的真实协方差振幅，以及式 (14) 所需定量相对余项的语境。

U 的 G(r,z) 正是式 (8) 的反向坐标 `(a0+r, (a0+r)^2/level^2-z)`。其 P 是所给实际均值图表的逆函数与 G 的复合，detF 是同一 mu 的真实二次倾斜律在 P 上的协方差行列式，A 是该行列式平方根的倒数。没有以任意形式矩阵或另一概率律代替原振幅。

按实际使用核对了旧 D/E 接口及真实协方差定义；旧证明的已有验收保持复用，没有重开旧单元验收：

- `C:/game/shao lean/drafts/oq3/OpenDomainSmoothMean.lean`，SHA256 `d6457d90d9d0e1ccdae6d6ea041d8caef65f70b3cb6d5fa8baea1867a5bffb8e`。D 给出真实均值在真实 Ω 上的 C∞，以及每个 Ω 内点的完整严格 Fréchet 导数，其两个行正是实际协方差的两行。
- `C:/game/shao lean/drafts/oq3/OpenDomainMeanInverse.lean`，SHA256 `d99022fad2a59a6e90782405113d9ec22ca0d3d56d8ea54af5a90500daa8fa53`。E 在真实中心行列式非零时提供连续线性等价 L，并给出其底层线性映射等于这些协方差行的乘积。U 只保留这个 L 和等式 hL。
- `C:/game/shao lean/drafts/oq3/RegularCovariance.lean` 第 20–24 行把 parabolaCovariance 定义为 `(X,X²)` 的真实方差/协方差矩阵。两个非对角元定义相同，因此 U38 的对称性 rfl 正确。

D/E 的服务器当前源码哈希也与上述接口哈希一致。

## 3. Udet 的完整证明检查

U16–27 的 Ω、nu、means、D 分别是真实 MGF 域内部、真实二次倾斜律、该律的一二阶均值、该律协方差。pr0/pr1 为固定坐标投影；Q 是真实均值导数在两个标准基上的列式表达，不是额外假设的协方差函数。

U28–36 从 D 取出 means 的 C∞ 和实际严格导数，并由严格导数取得通常 Fréchet 导数的唯一值。在每个 p∈Ω，两个导数列依次为 `(D00,D01)` 与 `(D01,D11)`。因此 U37–41 用二阶行列式公式和真实对称性得到 `det D = D00*D11-D01*D01 = Q`。这一环节将形式导数式绑定到实际协方差，没有假定 det 本来光滑。

U42–52 在任意 p∈Ω 上，使用 Ω 开性把 ContDiffOn 提升为环境空间中的 ContDiffAt。对真实 means 取 fderiv，∞+1≤∞ 满足固定库 fderiv_right 的阶数条件；对两个固定向量求值及投影、乘法、相减保持 C∞，故 Q 在 p 是 C∞。

U53–56 利用 Ω 是 p 的邻域，只在该邻域内使用已证 `det D = Q`，再由最终相等传递 ContDiffAt，并限制回 Ω。没有要求 Ω 外的均值导数或协方差有正则性，也没有要求协方差处处可逆或正定。空 Ω 和退化协方差不造成遗漏。结论是冻结声明中的真实行列式在整个真实开域上 C∞。

Udet verdict: CORRECT.

## 4. Uamplitude 的完整证明检查

U58–89 的实际打印类型逐项保留：任意概率 mu；theta 属于真实 Ω；正 level、正 a0；真实中心均值身份；任意给定 OpenPartialHomeomorph e，其完整前向函数等于真实 means；theta∈e.source；真实中心协方差行列式严格为正。结论的 Ω/G/P/detF/A 与源码的实际 let 值相同。

U103–109 从同一个输入 e 得到 `e.symm(means theta)=theta` 和 `means theta∈e.target`，分别使用 source 上的左逆身份与 map_source。这两项条件没有从另一个图表借用。

U110–117 调用 E 时，只借中心严格正性推出行列式非零，再取出 L 和实际协方差导数等式 hL。E 同时产生的另一个图表及其逆函数光滑性都被丢弃。由 D 的严格导数和 hL 得到真实 means 在 theta 的导数为 L；D 另给 means 在 theta 的环境 C∞。

关键的 U118–123 确实对输入的 e 调用 `e.contDiffAt_symm`，没有把 E 的存在图表替换给 e。固定 Mathlib 原始类型要求：(i) a∈e.target；(ii) 在 e.symm a 处前向函数有可逆导数 L；(iii) 在该点前向函数 C∞。这里 a=means theta，(i) 由 ht，(ii)/(iii) 均先用 hcenter 把 e.symm a 换回 theta，再用 hemeans 把输入 e 的前向函数换成真实 means。L 是连续线性等价，ℝ×ℝ 完备。因此所有 API 条件完整满足，所得光滑性属于同一个 e.symm。

U124–133 用真实 hmean 得到 G(0)=means theta，进而 P(0)=theta。G 的分母 level² 对变量 w 是常数，所以 G 是全空间光滑函数；复合上述同一个逆图表得到 P 在中心 C∞。hlevel 和 ha0 保留在冻结声明及 actual type 中，未用于这个辅助证明不构成弱化；两个 unused-variable 警告保持原状。

U134–146 消费本模块已证 Udet，并在 theta∈Ω 使用开性，得到真实 detParam 在中心 C∞。复合 P 后 detF 在中心 C∞，真实 hpositive 和 P(0)=theta 给出 detF(0)>0。sqrt 的光滑性用 detF(0)≠0；倒数的光滑性还用严格正性推出 sqrt(detF(0))>0。故 A 的光滑性没有把“行列式非零”误当“行列式正”，也没有预设目标振幅界。A(0) 的身份通过同一 P 中心等式直接化简，仍是同一真实倾斜律的行列式。

U147–159 从 A 在中心可微，得到一个 C>0 和邻域上的中心增量界 `|A(w)-A(0)|≤C*‖w‖`。P 的连续性及 theta∈开集 Ω 给出 P(w)∈Ω 的邻域条件；detF 的连续性及中心严格正性给出 detF(w)>0 的邻域条件。三个邻域被一次相交，得到同时满足所有要求的 hnear。

U160–175 从 hnear 取得一个 δ>0 的环境开球，统一取 rho=δ/2>0。对整个闭矩形 `|r|≤rho, 0≤z≤rho`，积空间范数为 max(|r|,|z|)，两坐标均≤δ/2<δ，因此闭端点也在球内。z≥0 给出 `‖(r,z)‖=max(|r|,z)≤|r|+z`；C>0 允许保序相乘。因此一次选出的 rho/C 对所有矩形点同时给出 P∈Ω、真实 detF>0 和所需线性振幅变化界。没有把逐点常数当成统一常数，也没有把开矩形误写成闭矩形。

精确范围为 P/A 在中心 C∞，及一个固定闭矩形上的三个列出性质。声明没有声称整个闭矩形上的 ContDiffOn，也没有列出 G(w)∈e.target、means(P(w))=G(w) 或 Jacobian 等其他坐标几何结论；消费者若需要这些，应使用已有图表几何并相容缩小窗口。target 的开性和中心身份保证图表逆的实际局部含义，这不需要换图表。这里不存在冻结声明缺口。

Uamplitude verdict: CORRECT.

## 5. Vexp 的完整证明检查

V8–10 的实际打印类型正是任意实 a,b,d 及 d≤a、d≤b 下的指数差界，未加入 d≥0、a≤b 或小误差假设。

V11–13 由 exp 的链式法则求得 `t↦exp(-t)` 的完整实导数 `-exp(-t)`。V14–17 在完整闭区间 `[min(a,b),max(a,b)]` 上，以 `d≤min(a,b)≤t` 得到 `-t≤-d`，再用 exp 单调性及 exp 严格为正，得到导数范数≤exp(-d)。这个证明与 d 的符号无关。

V18–22 使用该完整闭区间的凸性和每一点的 HasDerivWithinAt；后者来自环境 HasDerivAt，故包含端点。传给固定库平均值不等式的第一个点是 b、第二个点是 a，均以 min/max 的显式不等式证明在区间内，最终得到的有序差正是 exp(-a)-exp(-b) 和 a-b。a<b、b<a、a=b 都被覆盖，实数范数化绝对值没有改变结论。

Vexp verdict: CORRECT.

## 6. Vweighted 的完整证明检查

V24–28 的所有七个实参数及四个数值前提与冻结/actual type 一致；w、w0、d 都没有符号限制。

V29 从非负绝对值及 hamplitude 推出 Q≥0，故不是额外加入误差常数的符号假设。V30–32 先用幅度误差和 `exp(-a)≤exp(-d)`，以 exp(-a)>0 及 Q≥0 满足 mul_le_mul 的全部保序条件，得到第一项≤Q exp(-d)。

V33–36 对指数差使用已经完整证明的 Vexp，再以 exp(-d)>0 将 |a-b|≤E 放大；之后乘以 |w0|≥0。E≥0 本来也由绝对值前提推出，此处不需要把它另列为假设。w0 可以任意为负，所用系数始终是 |w0|。

V37–46 的恒等式把差精确写成 `(w-w0)exp(-a)+w0(exp(-a)-exp(-b))`。三角不等式、乘积绝对值及 exp 的正性给出两项，再与前面两界相加，最后环代数整理为 `(Q+|w0|E)exp(-d)`。没有省略交叉项、假定权重非负或错误反转乘法不等式。

Vweighted verdict: CORRECT.

## 7. 固定库条件与服务器证据复用

服务器工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`。实际读取其 lean-toolchain，仍为 `leanprover/lean4:v4.36.0-rc1`；mathlib 实际解析到共享只读包视图 `/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages/mathlib`，Git HEAD 为 `807d3836b165983210ee2ecf3cd28f239436949c`。

实际读取并逐项核对固定版本的主要 API：ContDiff/Operations.lean:888–891 的同图表 contDiffAt_symm，ContDiff/Comp.lean:724–726 的 fderiv_right 阶数条件，FDeriv/Basic.lean:835–840 的中心增量 Big-O，MeanValue.lean:695–699 的完整凸集平均值不等式，Sqrt.lean:150–152 的 sqrt 光滑性。对上述五个文件及 ExpDeriv.lean 逐个比较工作树文件与固定 HEAD 原始字节，六者均一致。因此日志中的既有共享视图 local-changes 警告没有掩盖本次所依赖 API 的修改。未联网更新依赖。

已读并复核两份服务器成功 build 日志、完整 audit 日志、审计源码、audit-record、environment 与 receipt。运行目录分别为 `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22u-20261023` 和同目录下的 `u22v-20261023`。

| 单元 | 首次完整成功 | 内核秒数 | 全所属公理秒数 | build 日志 SHA256 | audit 日志 SHA256 |
| --- | --- | --- | --- | --- | --- |
| U | attempt 02 | 5.537077778950334 | 5.851329322904348 | c211700bbdf68b6032281437e47ce82b48f8a98a8afb5763e101d82c793aecdd | c2fee2fb88946ae0226b33a829b86282524f9625805b2cd3d5fc64a2f5bc9de2 |
| V | attempt 01 | 4.747582234442234 | 6.096528168767691 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 | 6bc58ad10d73eecbd9e9994e27c1a8328ec0a182a31c6878183adae8773a326d |

两次成功内核与公理命令退出码均为 0；记录的配置均为 CPU14–17、native memory 8192 MiB、jobs 4、autoImplicit=false。U 的 attempt 01 属于不同旧源码 SHA256 `071964f60ddc86d1ec83b78e215a7663a8450c99ab436b9235da0556e9d07015`，失败证据保留，未算作通过；本轮没有重放旧失败或成功检查。

U Audit.lean SHA256 为 `3bbc7e3d28c19790bef38d4111a8c067380c9039b42c95cf304f3197e96114e3`；V 为 `341b4f1163877866671c8762a1e4c72bada98e80fb3d1563f4af66b9933f23ed`。两份审计都先确认冻结名称实际是 theorem，再遍历环境全部常量，按实际 getModuleIdxFor? 所属模块筛选，拒绝项目新 axiom，并对每个所属常量调用 collectAxioms。不是仅对手写公开名单检查。

完整 audit 输出分别为 ALL_DECLARATIONS=2、ALL_THEOREMS=2、FROZEN_THEOREMS=2、FROZEN_DEFINITIONS=0、AXIOM_GATE PASS。每一条实际所属声明的完整打印类型均已读过，恰好覆盖上表四条声明；没有隐藏 private/generated 声明或未检查 definition value。每条递归公理集合均恰为 `[propext, Classical.choice, Quot.sound]`。当前两份源码的 forbidden-token 扫描也没有 sorry/admit/axiom/unsafe/native_decide。

U 成功 build 的三个警告为既有共享薄视图警告以及冻结 hlevel/ha0 的两个 unused-variable 警告；V 只有同一共享薄视图警告。源码没有压制它们，也没有为了消除警告改签名。

## 8. 最终范围与交还

U 已完整证明式 (12) 的这一实际协方差振幅辅助接口：真实开域上的行列式 C∞，给定同一个实际均值图表时中心 P/A 的 C∞、真实中心身份，以及固定正闭矩形上的真实域内性、真实行列式正性和统一线性变化界。中心严格正性仍是明确输入，原根需从保留的实际谱正性提供。

V 已完整证明两个通用定量点态 producer。它保留了后续达到式 (14) 定量余项所需的指数误差与振幅误差因子；本单元没有证明缩放积分、积分主常数、相对 O(n^(-1/2)) 或最终 Laplace 结论。不得将其“source binding 为式 (14)”解释成式 (14) 已闭合。

本批没有新增 Jacobian、尾事件等价、实际 far-probability、Edgeworth/small-cell、完整积分缩放或原 B/D 根结论。原始实际谱/WC、0<beta<2/5、矩条件、全局鞍点、positive Lambda1、显式远场概率差距以及 Song/Angst–Poly 等外部结果归属均保持原有作用域，不由四条辅助定理删除或代证。p54 等其他修复也没有变化。

最终裁决：四条冻结完整声明及全部证明均 CORRECT；实际类型/零定义值/全部所属声明覆盖完整；精确服务器内核和递归公理凭据核对通过并复用。没有待作者修复的关键缺口。本报告是一次 final 完整审查，不是部分意见或仅凭 kernel pass 的放行。

报告写入并完成字节/行数/SHA256 自检后，本审查员停止工具与写入，向父实例交还；不启动下一任务，也不以本报告暗示持续运行。
