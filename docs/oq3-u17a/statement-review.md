# U17a EnergyBernoulliMGF 独立声明/source/API 审查

STATUS: CORRECT

本票只审冻结声明，无实现。唯一 reviewer lease 1，不spawn、Lean/probe/build、改缓存或其他文件。第一阶段仅读取 scope 的 Lean fence，先把以下完整类型与独立盲译持久化，再读正文/来源/路线/真实前置；已有其他声明/证明审查上下文存在，不把作者预期作为数学证据。

冻结 scope SHA256：`39919380a98af96855ca44ebc8ee8f060892582a3b6dd951cdf731f38c424277`。

## 1. 冻结的两个完整公开类型（零新定义）

```lean
theorem exists_binary_exponential_test (p z L : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    (hL : L < binaryRelativeEntropy p z) :
    ∃ theta : ℝ, 0 < 1 - z + z * Real.exp theta ∧
      L < theta * p - Real.log (1 - z + z * Real.exp theta)

theorem bounded_energy_logMGF_le_bernoulli (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H t : ℝ) (hH : 0 < H)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    Integrable (fun x : ℝ => Real.exp (t * (x ^ 2 - q))) mu ∧
      0 < (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu) ∧
      Real.log (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu) ≤
        -t * (q - 1) + Real.log
          (1 - (q - 1) / H + ((q - 1) / H) * Real.exp (t * H))
```

## 2. 独立盲译（先落盘）

第一目标给实数 p,z,L，要求 p∈[0,1]、z∈(0,1)，且 L 严格小于实际 binaryRelativeEntropy p z。它断言存在一个**有限实数** theta，使 B=1−z+z exp(theta) 严格正，且 L<theta*p−log(B)。p=0 和 p=1 都包含；类型不提供无穷参数或极限值作为见证。L 可正可负或0，只受严格上界限制；后续必须核实际 binaryRelativeEntropy 定义在端点的 log/乘0总化语义，不能将名字直接当作已证明的一般 KL。

第二目标固定同一实概率 μ，给 μ-AE |x|≤4+sqrt10，任意实 q,H,t，H>0，μ-AE 1≤x²≤1+H，且真实二阶矩积分 ∫x²=q。它同时断言：实际函数 exp(t(x²−q)) 对 μ 真正 Integrable；它的真实积分 Z 严格正；然后真实 logZ≤−t(q−1)+log[1−(q−1)/H+((q−1)/H)exp(tH)]。t 可为任意正负或0，不要求“小参数”。同一 μ 的二阶矩 q 出现在指数中心和 Bernoulli 系数 z=(q−1)/H，H正门允许真实除法；类型没有另显式假设 z∈[0,1]，必须从 henergy/hsecond 与真实可积证明，或用真正正的积分上界建立所需对数门。不能凭实 log 总化对非正数继续代数。

两个目标是独立通用陈述，不断言能量试验已经用于任何远区紧覆盖或全局大偏差，也没有给出 General KL、Chernoff 或根结论。本阶段尚未判断其数学可行性/来源与静态环境。根 A/B/C/D、source3/generalKL/globalfar/full17/19/LLT/hW 仍 OPEN。

## 3. 原始来源与实际前置接口

先落盘盲译的报告 SHA256 为 `5747debba18c32313a6aa142fa3adb876f649b47dc10af893d7163729b9bbaf4`，2948 bytes/35行；此后才读 scope 正文和真实 R1。R1 原件 `C:/game/shao/current/oq3/proofs/r1/report.md` 实际 SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。161–188 的支撑能量区间 0≤X²−1≤H 与随机 Bernoulli kernel/纯二元熵给本单元的来源；193–231 的三段充分 gap 与 386–389 的加权负层/远区需求给后续用途。原文 Eq9/10 是一般KL及数据处理陈述，本单元两个类型均未声称它们已成立。

实际 `BinaryEntropyBounds.lean:17–18` 定义
`binaryRelativeEntropy p z = p*Real.log(p/z)+(1-p)*Real.log((1-p)/(1-z))`。
这是纯实函数，标准实数 log0=0，与乘0给端点约定。不能把该定义名字直接换成实际测度KL，不能在 p=0/1 使用内部正分子log拆分。

已接受 U14a 的 `binaryRelativeEntropy_refined_lower` 在 p∈[0,1]、z∈(0,1) 下给 (p−z)²/(2 max p z)≤binaryD；实际 U14b 的 `binaryRelativeEntropy_source_gap` 对 1<q<103/100、50<H<51、R>0且R≠1、可行 p=(qR²−1)/H∈[0,1] 给 (7/200)(R−1)²<binaryD(p,(q−1)/H)。两个完整实际接口已读取；本票第一目标本身只需实际 binaryD 定义和 hL，未偷用该 source 特化作为一般假设或断言一般最优性。

实际 `InverseTilt.lean:26–34` 的公开 `integrable_continuous_of_fixed_bounds`：对实概率μ、μ-AE |x|≤4+sqrt10 和任何真正 Continuous f:ℝ→ℝ，给 Integrable f μ。其证明用固定紧区间上的连续有界与 μ-AE 界，没有要求 f 全局有界，也不只适用于 small tilt。该完整实际类型可用于 x²、(x²−1)/H、指数exp(t(x²−q))、exp(t(x²−1))和凸弦右侧全部连续函数，任意固定实t均可。不能借small-ball估计推广参数，亦不需I/J/样本产品。

## 4. 第一目标：内部与两个端点的有限见证

记 A=1−z>0，B(theta)=A+z exp(theta)。对任意有限实 theta，z>0、exp(theta)>0 即给 B(theta)>0。目标没有要求theta统一或有界；每个 p/z/L 可选自己的有限theta。

**内部 0<p<1。** 令 alpha=p/z>0，beta=(1−p)/(1−z)>0，theta=log(alpha)−log(beta)。分母 z、1−z、1−p 和 beta 均先由严格正性证明非零；然后 exp(theta)=alpha/beta、B(theta)=1/beta>0。合法 `log_inv`/正域log代数给 logB=−logbeta，于是
`theta*p−logB = p logalpha +(1−p)logbeta = actual binaryRelativeEntropy p z`。
这只是真实有限两点函数的代数恒等式。由 hL 严格推出所需测试值>L，既不要求 L≥0，也不除 p−z；p=z 时theta=0、binaryD=0、L<0 也完全保留。

**p=0。** 按真实定义，第一项整体0，binaryD(0,z)=−log A；此处只对正 A 证明 log(1/A)=−logA，不对 log0 进行 exp_log。hL 给 −L>logA，故 E=exp(−L)>A；Delta=E−A>0。取有限 theta=log(Delta/(2z))。其log参数/分母严格正，exp(theta)=Delta/(2z)，故 B(theta)=A+Delta/2∈(0,E)。真实正域log严格单调给 logB<logE=−L，测试值0*theta−logB>L。未使用 theta=−∞ 或把端点上确界误当作可达到的有限最优值。

**p=1。** 真实定义中第二项整体0，binaryD(1,z)=−logz。由hL得 E=exp(−L)>z，Delta=E−z>0。令 u=Delta/(2A)>0，theta=−logu，是有限实数。B(theta)>0，且 exp(−theta)=u、B(theta)exp(−theta)=z+A*u=z+Delta/2∈(0,E)。先正性再 log_mul/log_exp，得到
`theta−logB = −log(B*exp(−theta)) > L`。
只除正A，不对零1−p作内部log公式。没有使用theta=+∞，没有极限交换、DCT或缺失KL缓存。

p∈[0,1] 可按 p=0、p=1、内部三类穷尽；三类均是真有限见证。若 hL 没有严格余量，端点一般只能趋近，当前严格 hL 正是正确条件，不能无条件改成 L=binaryD。

## 5. 第二目标：真实可积、凸弦、对数正域及所有边界

先固定同一 μ/q/H/t，并有 H>0。由一般连续固定界接口建立 x²、常数1/1+H、u=(x²−1)/H、f=exp(t(x²−q))、g=exp(t(x²−1))及 W=1−u+u exp(tH) 的真正 Integrable；均为连续函数，任意实t成立。这样 hsecond 不是不可积Bochner的0总化被误读为真实矩。μ是真概率、非零且有限，先有 f 真可积，再由实际 `MeasureTheory.integral_exp_pos` 得 Z=∫f>0。

可合法用 μ-AE 1≤x²≤1+H 的积分比较（常数和 x² 两侧都真可积、μ质量1），推出 1≤q≤1+H，因 H>0 得 z=(q−1)/H∈[0,1]。这不是来自 q/H 的形式符号或假定它是概率参数。另一方面后续也可从 Z>0 和正系数A0*B上界直接推出B>0，两条路线都合法；实现不得省略所有正性依据。

μ-AE 0≤u(x)≤1。对全实 theta=tH，用全局 exp 凸性、点0和theta、系数1−u和u，得
`exp(theta*u) ≤ (1−u)exp0+u exp(theta) = 1−u+u exp(theta)`。
只使用系数非负及和1，**不**要求 theta≥0，故 t负/零没有失效。H≠0 先于 theta*u=t(x²−1) 的清分母。u可在AE支持外不属于[0,1]，不需要对全x声称凸弦界；W全局连续且真可积，不因AE界缺失而失去积分意义。

`∫u = ((∫x²)−∫1)/H = (q−1)/H = z`，其中 integral_sub 的两项可积已经给出，integral_const 以真实概率质量1简化，再使用 scalar/div 积分公式。对同一AE凸弦，**两侧**g/W真可积先于 `integral_mono_ae`，遂有 ∫g≤1−z+z exp(tH)=B。令 A0=exp(−t(q−1))>0，点态 exp加法恒等式给 f=A0*g，因此真正积分 Z=A0∫g≤A0*B；未用任何tilted measure不可积时为0的总化。

B严格正可显式分类 z=0（B=1）、z>0（z exp(tH)>0且1−z≥0），或由 Z>0、Z≤A0*B、A0>0 直接推出。这还覆盖 z=1。必须在此后才用 log单调得 logZ≤log(A0*B)，再由 A0>0、B>0 的非零门合法 log_mul 和 log_exp，得到精确冻结右侧 −t(q−1)+logB。无 log0 或负对数参数被偷偷消去，也没有 ENNReal∞.toReal。

t=0 时 f=1、Z=1、B=1、结论0≤0；H仍严格正但不除t。q=1/z=0 与 q=1+H/z=1 都允许，B始终正；μ可退化或x²几乎处处常数，目标没有实际正variance/非原子性前提。q没有作为分母，q≤0的可行性由真实矩假设自行排除，不须额外 q>0。没有自然n、样本产品、n0或平方根归一化门被隐含加入。本目标是每个固定实t的比较，不声称未来全部t的共同概率尾常数或紧覆盖已存在。

## 6. 实际固定API与说明文字的名称纠正

- `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:40–63` 实际在**全局 namespace**定义 `strictConvexOn_exp` 与 `convexOn_exp : ConvexOn ℝ Set.univ Real.exp`。文件到228才开始 namespace Real，其236行正是全局 `convexOn_exp.2` 的现成应用。scope路线写 `Real.convexOn_exp.2` 是限定名笔误；应使用实际全局 `convexOn_exp.2`。这是证明API选择，不改变两个完整类型、任何import或数学结论；冻结scope不改，终票明确记录。lead已确认后续实现采用该实际名字。
- `Mathlib/Analysis/Convex/Function.lean:54–56` 的实际 ConvexOn .2 恰要求两点在集合、两个系数非负且和1，然后给 Jensen二点弦不等式。Set.univ 对任意正负theta均覆盖，smul在实数中还原乘法，无需另引一般Jensen积分定理。
- `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:59–61,75–76`：Real.exp_log 需要严格正参数，Real.log_exp 对所有实数成立；103–108显式log0=0/log1=0仅用于真实乘0端点化简。
- 同文件133–145的 Real.log_mul/log_div 要求两个因子/分母非零；log_inv是总化成立，但本推导仍把相关概率/normalizer量先置于正域。147–159的 log_le_log(_iff)/log_lt_log(_iff)要求明确正域，不能把log当作全实单调函数。
- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:792–798` 的实际 `MeasureTheory.integral_exp_pos` 消费 `[NeZero μ]` 和真正 Integrable exp(f)，由support=univ得正积分；μ概率给真实非零/有限。这是一般实函数f的API，不只适用线性指数。
- 同文件261–264的 integral_sub 需要两项真可积；288–297是 actual integral_const_mul/integral_mul_const/integral_div；662–667的 integral_mono_ae 要求两侧均真可积和真实AE≤，990–996的 integral_const 按μ.real univ给常数积分。第5节已逐项建立所需门，即使部分scalar积分公式自身可对总化积分陈述，也不依赖该总化绕开矩/比较假设。

来源数值也独立核过：实际 `SourceStarter.lean:19–20` 定义 sourceU=31/30、sourceEll=Real.log sourceU。真实 `Real.log_lt_sub_one_of_pos` 在 Log/Basic:260–264、以31/30>0且≠1给 sourceEll<1/30；绝非 sourceEll=1/30。若未来另有1<q<103/100，则其正性与此界给 sourceEll*q<103/3000，且7/200−103/3000=1/1500。这只是scope未来来源定位的标准数值核对，不是本单元两个目标新增的iid远区/紧覆盖输出，不必把另一个不在本import闭包的专门sourceEll界定理冒作当前消费依赖。

数学/source/API阶段独立判定支持 CORRECT；尚待最后冻结文件/实际import闭包/现成olean/pins核对。未读作者 future energy/rotation notes、I/J当前proof/receipt或排队其他scope，未实施/运行本目标。

## 7. 最后冻结/实际导入环境核对

数学/source/API阶段报告已先持久化：SHA256 `29f4fa4a3878bb422484a3abbacff5ca728f55fed4d255f91d12ec5148785e44`，12268 bytes/92行；最后才只读核两端scope、实际依赖哈希/导入图、现成olean与pins。当前 EnergyBernoulliMGF.lean 在远端工作树确未创建；本单元没有可声称已核成功的实现、build/Audit/receipt。没有读取当前J的新proof或机械产物。

冻结 scope 本地 `C:/game/shao lean/drafts/oq3/forty-seventh-unit-scope.md` 与 remote `runs/oq3/u17a-20261021/scope.md` 两端实际SHA256均为 `39919380a98af96855ca44ebc8ee8f060892582a3b6dd951cdf731f38c424277`，5892 bytes/39行，未改动。拟上下文是三imports：`Shao.OQ3.SourceBinaryEntropyGap`、`Shao.OQ3.InverseTilt`、`Mathlib.Analysis.Convex.SpecificFunctions.Basic`；namespace Shao.OQ3，open MeasureTheory，noncomputable section。零新公开定义/两个完整类型原样在本票第一节，无新scope/volume/Matrix符号实例需求。

实际递归项目import闭包只有以下 **7个模块**（没有I/J/G/H或任何新energy源），对应既有olean均实际存在。前三个公开承重源 BinaryEntropyBounds/SourceBinaryEntropyGap/InverseTilt 的本地draft与远端工作树字节哈希也逐项匹配：

| 实际项目模块（Shao.OQ3前缀省略） | 实际源SHA256 | 字节/行 |
|---|---|---|
| AtomicMeasure | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` | 6619/139 |
| BinaryEntropyBounds | `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228` | 5574/128 |
| FiniteConstraints | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` | 9679/241 |
| InverseTilt | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` | 8423/174 |
| SourceBinaryEntropyGap | `f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9` | 7616/173 |
| SourceStarter | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` | 13859/337 |
| SummableAtoms | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` | 10641/237 |

实际module→sha256规范字典（JSON sort_keys=True,separators=(',',':')，UTF-8）整体SHA256=`71a04a6618f6bbcded1095c290014218d21fe7c1e66391e2d6f9044de66e14eb`。这些为已接受的实际前置冻结源，不重做它们的成功target/Audit。

拟import源码图还实际可达以下已读库API模块，各自既有olean均核存在：

| 实际库模块（Mathlib前缀省略） | 实际源SHA256 |
|---|---|
| Analysis.Convex.SpecificFunctions.Basic | `809d8e40e5ab931ec4254ae9068e9fb5a4a7c19e95d3fddcc9f4ad81028faef1` |
| Analysis.Convex.Function | `909dc29c14a92dfe5519a0388d58dad48abe02b4947a4c7afb3d473b43d98320` |
| Analysis.SpecialFunctions.Log.Basic | `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97` |
| Analysis.Complex.Exponential | `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146` |
| MeasureTheory.Integral.Bochner.Basic | `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670` |
| MeasureTheory.Measure.Typeclasses.Probability | `00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b` |

指定服务器真实Mathlib HEAD=`807d3836b165983210ee2ecf3cd28f239436949c`。`lean-toolchain`=`leanprover/lean4:v4.36.0-rc1`，29bytes，其SHA256=`d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；实际 lake-manifest.json 3541bytes/117行，SHA256=`40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。共享broker成功只读，host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`；未更改连接或读取凭据。

缓存存在/静态API可行性不是新target已elaboration或内核检查的证明；实现后仍须审完整actualproof、所有private/generated/actualTYPE及最后真实机械产物。本声明gate不假装做过此类未来验证，也没有为确认API而运行Lean/#check。

## 8. 最终独立结论

JUSTIFICATION: **CORRECT。** 第一目标有真实binaryD内部精确代数与p0/p1两种有限见证，严格hL足以提供有限余量，不偷用无穷参数、一般KL或端点log0取消。第二目标先从真实固定AE有界建立所有函数可积与真实正Z；任意正负/零t都可用实际全局exp凸性给AE弦界，真积分单调/真实均值才产生z=(q−1)/H。正常数与B的正性先于log单调/乘法，完整输出含真实可积和正normalizer，H0排除、t0/energy端点/退化μ保留。完整类型、来源定位与固定导入/现成API环境无声明阻塞。

scope路线的 `Real.convexOn_exp.2` 限定名笔误已在第6节透明纠正为实际全局 `convexOn_exp.2`，仅是未来证明API选择；冻结scope/两个完整types/imports保持原样，无需变更声明。来源实际sourceEll严格为log(31/30)<1/30，未替成1/30。

本票仅批准 **U17a声明/source/API门**，不是尚不存在的实现完整proof通过。实际目标只是纯二元熵的有限指数试验与同一概率能量logMGF的充分比较，未给真实iid概率尾、Markov数据处理、source Eq9/10、一般KL/RN、Legendre最优、后续源能量界特化、远区compact finitecover、globalfar、完整17/19、LLT、hW或根闭合。无最弱/最优/新颖性主张；根 A/B/C/D、source3/generalKL/globalfar/full17/19/LLT/hW 均 **OPEN**。

唯一写入的是拥有的新本地报告与随后上传的授权 remote `runs/oq3/u17a-20261021/statement-review.md`。未改source/scope/receipt/旧票/shared/cache，未spawn/Lean/probe/build/recompile/commit、下载原始完整日志或读作者future energy/rotation notes。最终两端SHA另外核验并交lead全文阅读，批准后才进入独立实现流程。
