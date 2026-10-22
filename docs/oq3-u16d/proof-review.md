# U16d 完整独立证明、来源与实际类型审查

STATUS: CORRECT

唯一审查 lease 1，只拥有本新报告及服务器 proof-review.md，不修改实现/scope/旧票/共同文件/缓存，不 spawn、Lean/probe/build/复编或下载原始完整日志。并非独占代码库，保留他人编辑。承认已有声明上下文存在，本次仍先仅提取actual公开定义完整体及定理完整类型，独立翻译并先落盘；尚未读实际proof/private或本次机械证据。

## 第一阶段：actual完整定义体与完整类型盲译

实际输入 CenteredLogMGF.lean，SHA256 `1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4`，5622字节/118行。此阶段只读一公开定义完整体和一公开完整目标类型。

`centeredNormalLogMGF(mu,q,a,v,s)` 是真实实指数exp(centeredNormalProjection(q,a,v,s,x))对mu的Bochner实积分，再取标准Real.log。定义本身对任意实数测度/参数总化，不给可积或normalizer正性；定理必须真实产出这两门，不能借不可积积分0或log0扩展解释为真实MGF。

`exists_centeredNormalLogMGF_cubic_upper`：给真实实数概率mu、同一mu-AE |x|≤4+sqrt10、实数q/a以及真实E(normalValue)=q和EX=a，存在同一实C>0和delta>0，先于全部实v/s选择；对闭l1参数球|v|+|s|≤delta，真实exp投影函数真Integrable、其积分严格正，且actual logMGF≤actual normalTangentQuadratic(mu,v,s)/2+C(|v|+|s|)³。完整类型没有正定/非退化/S/D/阶段/原子性或q正性门，不能在proof中偷偷添加。mu、两个中心和Q必须同源，不能用任意系数二次型替代。

零参数v=s=0、闭球边界、退化mu和退化方向都在结论内；C/delta必须仍严格正且在全参数外。必须先真可积再积分线性/比较，先Z>0再用log不等式。实际投影/均值与真实二阶矩接口、指数三阶余项、共同AE界及全部私有/生成项留后实际核对，不由名称或作者成功门推断。

本盲译先保存。后续严格scope/R1→全118行proof/private/locals/固定库及真实承重链→全部actual TYPE→receipt/机械LAST。实际Legendre/Fenchel/Chernoff/紧族uniform/LLT/hW与根A/B/C/D保持OPEN。

## 第二阶段：冻结声明、真实来源及承重语义

盲译先落盘后才读取完整scope/真实R1和actual实现。冻结scope SHA256 `54a2a3f9a6da1e56a1ff07e612c43c43088c32dc4b4b48f207e93db1449a6dbf`，已接受声明票SHA256 `670f3e4118644411284d9ba896bdf828b6e693ecae1a3a3fbf4807bc39699ac0`。本次独立提取actual公开定义完整体与公开定理完整类型，去空白后分别与冻结Lean fence相等；三条导入、namespace/open/noncomputable均保持。

真实只读R1路径 `C:/game/shao/current/oq3/proofs/r1/report.md`，SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，本次直接复核350–371行。351行K_c是真实中心实指数积分取log，与actual定义一致，没有复相位或负似然替代。370–371行是Legendre率I的逆协方差展开；当前定理给K_c的协方差二次上界，是标准充分前置，不是直接证明I展开、概率Chernoff或紧族Fourier常数。

actual NormalTangentMoments.lean SHA256 `8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1` 的定义和完整公开接口已重新读取：projection=v(Y−q)+s(X−a)，Y=normalValue=8x−x²；hb/真实概率给MemLp2，同一hq/ha给真积分0及真实二阶矩=normalTangentQuadratic。后者actual NormalTangentGaussian.lean SHA256 `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`19–22行是Var(Y)v²+2Cov(Y,X)vs+Var(X)s²，非任意系数或逆矩阵。在真实有界/L²门下是actual平方积分，未用variance.toReal的不可积总化，也不需协方差正定。

actual InverseTilt.lean SHA256 `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`26–34行 integrable_continuous_of_fixed_bounds 要求mu概率、同一hb和函数全局连续，实际证明在紧Icc上有界后由AE支撑得到真Integrable。main的真实exp调用恰好具备该完整门，不声称任意概率下所有连续函数自动可积。全部实际项目闭包/hash留最后机械阶段核验。

## 第三阶段：全部118行proof、两个private与所有locals

本数学阶段先于Audit TYPE和receipt读取并先落盘。

第1–12行只有冻结的三导入、命名空间、MeasureTheory及真实log定义，未添加实例、概率模型或新公开定义。

### private real_exp_cubic_upper（14–19行）

输入任意实z及|z|≤1，结论exp z≤1+z+z²/2+|z|³。16行对实际Real.exp_bound取n=3并提供0<3。17行仅展开真实range3有限和/阶乘，余项系数4/(6*3)=2/9。18行先有expz−多项式≤其绝对值，19行配合该真实余项及|z|³≥0，将2/9上界放大至1。既没有假设z≥0，也不套仅正z版本或将自然数除法当0。闭小球边界|z|=1合法。

### private exists_uniform_projection_bound（21–54行）

完整接口仅有任意mu、hb、固定q/a，先∃K>0，再∀v/s、μ-AE投影绝对值≤K(|v|+|s|)，无需概率门。25–29行令g(x)=|Y−q|+|X−a|，此连续函数在真实固定Icc上的范数有同一个有限C上界；实际compact API没有Nonempty前提，代码不从mu支持或紧集提取点。30–32行K=|C|+1真实>0且C≤K，即使原C未显式非负仍合法。

33行先返回K,hK，34行才引入v/s，35行只在同一hb的AE集合内工作。36–45行从|g(x)|≤C和g(x)≤|g(x)|得两个特征绝对值和≤C，再分别利用另一项非负与C≤K给|Y−q|、|X−a|≤K。46–54行真实三角不等式和abs_mul后，分别乘|v|、|s|≥0，得到统一投影界。没有逐方向选K，也没有错用不可数AE交；接口为∀参数后AE，main按每对参数消费，样本支撑来自同一个hb。

### main见证、真实积分与normalizer（65–85行）

65行先取统一K及全参数hbound，66行在所有v/s前选择C=K³>0、delta=K⁻¹>0；67行之后才固定任意参数与闭球门。f为实际投影，R=K³(|v|+|s|)³。70–73行建立真实连续性；74–76行消费actual投影MemLp2，以概率有限测度下1≤2取得f真Integrable，并从MemLp2取得f²真Integrable。

77–78行以真实exp连续复合和hb固定支撑接口先建立exp(f)的真Integrable；79行才用integral_exp_pos得Z>0，真实概率提供NeZero。80–85行再把hsmall乘K≥0、只在K≠0后消K*K⁻¹，得整个闭参数球内AE |f|≤1。不是把积分总化为0后取log，也不借复相位模恒1证明正指数可积。

### 真AE指数比较和积分线性（86–112行）

86–93行把同一参数下hbound及hsmallf的两个AE门有限相交，先用abs f≥0的实幂单调给|f|³≤[K(|v|+|s|)]³=R，再接private实指数上界。三次函数在积分前已被有限常数R替换，因此actual证明不需要额外先积分|f|³；其消耗的右函数是1+f+f²/2+R。

94–97行从同一mu、q/a及真实hq/ha得∫f=0、∫f²=actualQ，未混用別的中心或概率。98–102行逐层建立1+f、加f²/2、再加R的真Integrable；这些门都先于103–109行的integral_add。除以2仅为常数乘逆，2非零且不依赖方向；概率的真实总质量1给常数积分1与R。所得右积分恰为1+Q/2+R。110–112行实际integral_mono_ae明确消费exp侧hE、右侧hP以及AE hpoint后，才给Z上界；无先用总化积分单调性的空缺。

### 输出与全部边界（113–115行）

113行返回真hE和hZ。114行展开实际definition和R，115行仅在Z>0之后调用真实Real.log_le_sub_one_of_pos，再由Z≤1+Q/2+R合法减1，得到公开上界。未使用Z≥1或Q>0，也没有非法log负数/除normalizer/方差归一化。

v=s=0时actual f恒0、exp0恒1、Z=1、log1=0、Q0=0、R0=0；代码所有门真实成立。若mu为单点或某方向退化，真实中心条件让相应f=0 μ-AE、Q为真实平方积分；C仍由K>0给正值、delta仍正，无非退化假设。q/a任意符号只进入连续绝对界；闭支持端点和闭参数球端点均满足≤门。实际proof无n/J/θ/格点或未来倾斜族uniform假设，不能据此将C升为另一个mu族共同常数。

全部118行及每个have/let/filter_upwards/calc/积分改写已核，数学阶段结论CORRECT。源码有两个authored private theorem，生成项是否存在留待actual TYPE，不由作者给定数量代替审查。

## 第四阶段：实际固定库门

指定服务器只读核对：

- Complex.Exponential SHA256 `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`517–521行Real.exp_bound真实门|x|≤1和n>0；n3确为2/9三阶系数。
- Log.Basic SHA256 `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97`307–310行log_le_sub_one_of_pos真实要求严格正normalizer，main hZ先于使用。
- Bochner.Basic SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`792–798行integral_exp_pos要求NeZero及真exp可积；662–667行integral_mono_ae要求左右真Integrable和AE≤。IsProbabilityMeasure.neZero实际Probability.lean87–88行实例语义已在声明阶段核实，概率质量1也给有限测度。
- Analysis.Normed.Group.Bounded SHA256 `7ff0b64a69f6e44ea002c3f21fac6011801737d81629fc9c2d4280e4b8846042`91–95行to_additive生成实际IsCompact.exists_bound_of_continuousOn：连续于紧s给∃C,∀x∈s,‖f x‖≤C，无Nonempty门。actual g连续和Icc紧性满足。
- Function.L2Space SHA256 `c5737e32b9b1e2a6a0d04b411244ed90d0fcf25aab0449b51865d39182eb4593`42–43行MemLp.integrable_sq，L1Space.Integrable SHA256 `d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759`646–648行MemLp.integrable要求指数≥1和有限测度；main p2、真实概率均提供。

上述全部actual数学/接口判断先保存，然后才读所有actual owned TYPE，再最后才读作者receipt及机械事实；未运行Lean或API probe。

## 第五阶段：全部4个actual owned TYPE

数学与固定库阶段先落盘后，从真实现有Audit.log仅过滤DECL/TYPE并读取全部长续行；此时尚未读公理/PASS/receipt。真实四项逐一为：

1. `_private.Shao.OQ3.CenteredLogMGF.0.Shao.OQ3.real_exp_cubic_upper`，实际第2行完整TYPE：∀z:ℝ，|z|≤1→exp z≤1+z+z²/2+|z|³。没有z≥0或额外小球门，与实际私有证明完全一致。
2. `Shao.OQ3.centeredNormalLogMGF`，第5行完整TYPE为 `Measure ℝ→ℝ→ℝ→ℝ→ℝ→ℝ`，即mu/q/a/v/s后输出实数，无隐含概率、可积或Z正门；完整定义体已先实际审查，不能仅凭箭头TYPE判断积分语义。
3. `Shao.OQ3.exists_centeredNormalLogMGF_cubic_upper`，实际第8–21行全部长续行读取。真实mu概率、hb、固定q/a和两个真实均值门之后，∃C/delta>0在∀v/s之前；闭l1球内同时有真Integrable、真实exp积分严格正和实际Q/2+C*l1³上界。没有隐藏非退化/阶段/原子性/q正门，也没有削掉integrability/normalizer输出。三个结论的同mu/同中心/同参数保持。
4. `_private.Shao.OQ3.CenteredLogMGF.0.Shao.OQ3.exists_uniform_projection_bound`，实际第24–27行全部读取：任意mu、hb、q/a后∃K>0，先于∀v/s，再μ-AE真实投影绝对值界。该私有TYPE确实不需IsProbabilityMeasure，也不是AE∀不可数参数；K在全部参数前，支持main共同窗口。

实际只有1 public def、1 public theorem和2 authored private theorem，共4个owned、3 theorem；没有生成TYPE项。此结论来自真实枚举而非按作者数量假定，后续机械阶段再核完整stem/private覆盖。全部actual TYPE及其续行已核，类型阶段结论CORRECT。随后才读取收据、真实构建/Audit/pins/依赖哈希。

## 第六阶段：最后读取的真实机械证据与冻结绑定

数学/全部actual TYPE已先完成并落盘，此后才读取本地U16d-receipt.json、真实远端receipt、Audit源/公理/计数、现有build/olean、真实闭包与pins；作者门只作为机械证据，不替代独立数学审查。本次未运行Lean、API probe或目标/Audit复编，未下载原始完整日志。

- 本地actual、远端worktree `Shao/OQ3/CenteredLogMGF.lean` 和run冻结快照同为5622字节/118行，SHA256 `1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4`。实际源无CR、尾空白和sorry/admit/axiom/unsafe/implemented_by/extern。公开定义完整体、公开完整类型已在本审查独立去空白对照冻结范围而相同；三导入无变化。
- scope本地/远端hash均 `54a2a3f9a6da1e56a1ff07e612c43c43088c32dc4b4b48f207e93db1449a6dbf`，已接受声明票两端hash均 `670f3e4118644411284d9ba896bdf828b6e693ecae1a3a3fbf4807bc39699ac0`。本地/远端receipt均4270字节，SHA256 `7140312f1ac34e27b7a700730dd8ab2a7aacb8760ebc8c26055d66a084aa7146`；其pending/No commit PR是author-check时历史状态，不误当本次最终裁决。
- 实际build-02.log为0字节，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。作者回执记录实际 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/CenteredLogMGF.olean Shao/OQ3/CenteredLogMGF.lean` 命令exit0；空文件本身不独立证明退出码。本次只读核实际目标olean存在，392960字节，SHA256 `b2b41305b1a44892f86fff88c3db29971f8945274bd4922cd627903e16746cc2`，未重跑成功构建。
- 实际Audit.lean为1628字节/36行，SHA256 `5bbc7fdb54204a1d5a9b1e658b6b6edef060af3c3edf550235556f4aa108257e`，全文核读：目标核isTheorem、定义核defnInfo，遍历公开目标/定义的完整stem和完整 `_private.Shao.OQ3.CenteredLogMGF` 前缀；对每项拒绝isAxiom、Lean.collectAxioms检查全部传递依赖，只允许propext/Classical.choice/Quot.sound。覆盖不是只检查公开一条目标。
- 实际Audit.log为1691字节/32行，SHA256 `6a8687b43d2d36394056a07cbd2543fbaba338394ab1fcc0b6ef502d2fb403a3`，真实输出1 frozen、3 theorem、4 owned，`U16D_AXIOM_GATE PASS`。四项实际AXIOMS均为[propext,Classical.choice,Quot.sound]；实际无generated owned项。全部TYPE和所有长续行已在前一阶段核查，没有以PASS或计数代替类型语义。
- 实际branch `feat/oq3-centered-log-mgf`，HEAD `33f20ede7c71788a9397cd96e6b2e45b3b0dfc0f`，git status仅 `?? Shao/OQ3/CenteredLogMGF.lean`。实际toolchain `leanprover/lean4:v4.36.0-rc1`，lean-toolchain SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`；manifest pin与实际mathlib HEAD均 `807d3836b165983210ee2ecf3cd28f239436949c`。两个直接Mathlib导入的既有olean存在，Exp为210592字节、Log.Basic为264384字节。

从实际目标递归解析Shao imports，恰好10份项目前置，路径集合与receipt一致；每份实际SHA逐项MATCH，10份既有olean全部存在。真实prerequisite-hashes.json为1038字节/12行，SHA256 `247225034a64499162523725a42b21bae9bf581a8f2367f3cb7e8317792d2ad2`，其内容独立程序核对与receipt完全相同。实际值如下（共同Shao/OQ3前缀省略）：

| 实际项目前置 | SHA256 |
| --- | --- |
| AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| NormalTangentGaussian.lean | `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39` |
| NormalTangentMoments.lean | `8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1` |
| PositiveRate.lean | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| RegularCovariance.lean | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |
| SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: actual公开定义完整体/完整类型与冻结scope及真实K_c来源匹配；全118行、两个private、所有locals和全部4实际TYPE已独立核查。统一K在所有v/s之前选定，正C=K³与delta=K⁻¹给闭l1球内真正AE小球；实指数n3余项系数2/9被合法放大并在积分前换成常数。真exp及右二次多项式可积、真实均值0和实际二阶矩同mu绑定、积分单调性完整门、Z>0先于log上界都实际成立。退化mu/方向、零参数和闭端无额外正定或归一化门。实际4owned/3theorem全部传递白名单、10份真实前置与source/scope/receipt/Audit/build/pins绑定一致，没有发现需要修改的声明、数学、来源、类型或机械缺口。

本票仅接受真实中心logMGF在共同参数球内的二次加三次上界，并显式接受真exp可积与正normalizer；不输出真实Legendre/Fenchel、I三次minorant或逆Hessian、紧倾斜族统一Fourier质量常数、Chernoff(16)/(17)、远区率gap、完整层和(19)、LLT/hW、WC/KL、全局最小化、最优性或新颖性。实际Legendre/Fenchel/Chernoff、紧族uniform、LLT/hW及根A/B/C/D均保持OPEN。只写本新报告和授权远端副本，不改任何源/scope/旧票/shared/cache，不spawn或复编。
