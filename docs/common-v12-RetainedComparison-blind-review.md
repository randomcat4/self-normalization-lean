# RetainedComparison 最终独立源码语义与证明审查

STATUS: CORRECT（源码数学审查）

本裁决覆盖冻结实现的两个定义、三个公开定理、唯一私有可测性 helper 及全部证明，复用先前独立声明盲译与已接受旧依赖。未发现声明改变、源语义偏离或数学证明缺口。未运行本机或服务器 Lean，未重跑目标编译或传递公理审计；作者回执仅为另行执行记录，不作为本报告的数学依据。本轮只新增本报告及另行明确授权的原 SignedBlock scope 恢复文件，未修改任何实现、现有 scope 或他人文件。

## 冻结绑定与原声明核对

- 实现：C:/game/shao lean/drafts/c12/RetainedComparison.lean，270 行。
  SHA256：fc5b9316c9571465dabc324d57d901da328f9c38c1d9f02a4ac26b8f55687604。
- 冻结提案：C:/game/shao lean/drafts/c12/RetainedComparison-next-scope.md。
  SHA256：fe2969bf94db460176175726853dc71cd4bdb055279623dcff58c38d89eaa23f。
- 独立声明审查：C:/game/shao lean/drafts/c12/RetainedComparison-statement-review.md。
- 原 main.tex SHA256：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- 原 supplement.tex SHA256：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

本轮实际核对实现与 scope 哈希。两定义的真实 bodies 与冻结提案一致；三个完整公共定理签名除空白外逐字比较相等。没有新增前提、放宽闭 cutoff、改事件边界、改路径顺序、换方差/能量或加入分析目标假设。scope 中明确排除的后续 bounded_product_upperCrossing_normal_tail_open_goal 未实现、未引用、未成为新公理。

已接受的 ConditionalIID、RetentionEvent、OrderedSelection、Deletion、RetainedMoments、RetainedSample、RetainedVariance 和 FiniteIID/MeasurablePath 公开接口复用，不重编译或重验其证明。所用 RetainedVariance 冻结 SHA256 为 5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6。

## 全部实际公开定义、量词与零边界

记 Bₓ={u:|u|≤1/x}，ηₓ=retainedCutoffLaw ν x=cond ν Bₓ，μₓ=∫u dηₓ，Vₓ=∫(u−μₓ)²dηₓ，τₓ=√Vₓ。

1. **retainedStandardize（21–24 行）。** 对任意实测度 ν、任意 x,z∈ℝ，定义 Z(z)=(z−μₓ)/τₓ。定义本身没有概率、可积性、正质量或方差前提；零分母使用 Lean 的全定义除法，不带单位方差断言。固定 ν,x 后 μₓ,Vₓ 是常数。
2. **retainedStandardLaw（26–27 行）。** 对相同任意 ν,x，定义实际 ζₓ=map Z ηₓ。没有指定一个“具有标准矩”的抽象概率律；后面的结论计算的是这个固定 pushforward。
3. **retained_cond_transform_path_map_eq_pi（37–50 行）。** 任意 n、带可测结构的 Ω、概率 μ、ν、真实函数族 X:Fin n→Ω→ℝ；要求每个 Xᵢ 可测、iIndepFun X μ、每个 Xᵢ 在 μ 下与 id 在 ν 下 IdentDistrib。再任取固定 s⊆Fin n，m=s.card>0；任取 Borel B 和真实 fiber Aₛ={retentionSet X B=s}，要求 μAₛ≠0；任取可测 g:ℝ→ℝ。结论为整条升序变换路径在 cond μ Aₛ 下的 map，等于 Fin m 上各边缘 map g (cond ν B) 的真实乘积。不是仅坐标同分布，也不是随机保留路径在原 μ 下无条件 iid。没有矩、均值或数值 cutoff 前提。
4. **retainedStandardLaw_moments（70–87 行）。** 任意概率 ν、n,j∈ℕ、x∈ℝ；输入是 x≥2、x⁶≤n、j≤x²/2、u² 在 ν 下可积、∫u dν=0、n∫u²dν=1，以及实际 Hₓ=n∫F(xu)dν≤1。结论为 ζₓ 概率，id、平方、绝对三次均真可积，∫z dζₓ=0、∫z²dζₓ=1，且
   \[
   \frac{\int|z|^3\,d\zeta_x}{\sqrt{(n-j:\mathbb N)}}
   \le\frac{64}{(\sqrt{x^2-j})^3}.
   \]
   n−j 先在 Nat 取减法再转实数。没有输入全局原三矩、正方差、Jensen 或 BE。样本正性、截断质量与方差正性从实际来源条件推出。
5. **retained_cond_upperCrossing_comparison（159–186 行）。** 在第 3 项真实 iid 前提下，任意固定 s、x，并要求第 4 项数值/原矩/预算条件，其中 j=n−s.card；还要求闭 cutoff 的真实固定 fiber A 正质量。输出存在 hn:0<n、hs:0<s.card，且
   \[
   (\operatorname{cond}\mu A)\{a(X)\in C_n(x)\}
   \le\eta_x^{\otimes m}(C_m(y)),
   \]
   \[
   \eta_x^{\otimes m}(C_m(y))
   =\zeta_x^{\otimes m}\{a:R(a)\in C_m(y)\},
   \]
   其中 m=s.card、y=√(x²−j)、R(a)ᵣ=μₓ+τₓaᵣ，Cₘ(y)=upperCrossing hs y。三个概率都是实际 ENNReal 测度值。Cₘ(y) 使用非空前缀 1,…,m 的弱穿越 y√energy≤upperMax，包含零平方和；标准化端必须先恢复 R(a) 才计算同一 raw 事件。

定义虽在 Vₓ=0 时仍有值，所有单位方差与逆恢复结论都只在来源条件导出 Vₓ>0 后成立。第 3 项 hs>0 排除空保留族；第 4、5 项的 n=0、m=0、y=0、Vₓ=0 则由实际条件排除，没有暗加非空或正方差前提。

## 证明一：真实完整条件路径律

**29–31 行**唯一私有 helper 直接证明真实仿射函数可测：id 减常数，再除常数。它不依赖 τₓ≠0，即使零方差时也可测。因此 map 在本模块中的用途确实是可测观测的真实推前，不靠不适用的任意不可测 map 约定。

**51–54 行**调用已接受 iid_retained_cond_retentionSet_eq，得到 νB≠0、cond μ Aₛ 下真实保留坐标独立性，以及每个原始升序坐标在该条件律下与 id 在 cond ν B 下同分布。随后分别从实际非零质量建立 cond μ Aₛ、cond ν B 的概率实例。hs>0 与 hA 被实质使用；没有从空族 hLaw 推断条件边缘概率。

**55–61 行**令 Y(ω)ᵣ=X_{retainedIndex s r}(ω)，G(a)ᵣ=g(aᵣ)。Y 和 G 都逐坐标证明可测。FiniteIID 的完整 path-map theorem 在真实条件概率空间应用，得到
\[
 \operatorname{map}(Y,\operatorname{cond}\mu A_s)
 =(\operatorname{cond}\nu B)^{\otimes m}.
\]
使用的 retainedIndex 是固定严格递增枚举，不是可观测样本依赖的重排。

**62–66 行**通过可测 map_map 复合，再用 pi_map_pi，将整条路径施加 G 的真实推前写为 ∏map g (cond ν B)。该证明使用真实 hI，而没有把逐坐标同分布独自升级为联合乘积。g 只需可测，常值、非单射和不连续可测 g 都允许。

本轮只读核对指定服务器 Mathlib/MeasureTheory/Constructions/Pi.lean:386–401：pi_map_pi 的确要求每坐标 AEMeasurable 和各 mapped marginal 的 SigmaFinite。这里 hg 提供前者，条件概率及其 mapped probability 提供后者。没有隐含的漏前提。

## 证明二：实际 pushforward 的可积性、矩和方差正性

**88–100 行**固定同一实际 η、μₓ、Vₓ、τₓ、Z、ζ。真实 size bounds 推 n≥64，进而 n≥2；从实际 Hₓ≤1 的 cutoff mass bound 得 qₓ≥1/2>0，再建立 η 的真概率实例和 ζ 的映射概率实例。预算仍是 n∫F(xu)≤1，没有换用更强 Rₙ(x)≤1 或另一个截断尺度。

**101–110 行**先从已接受 centered-moment theorem 取得 η 下中心 id、平方、绝对三次的真可积性和中心均值零；再从真实 variance bound 推 Vₓ>0。其后才有 τₓ>0 和 τₓ²=Vₓ。没有在方差可为零的分支上使用除法消去。

**111–122 行**明确计算 Z=(u−μₓ)/τₓ，证明 Z、Z²、|Z|³ 在 η 下可积。前两者由中心一、二矩除常数及 div_pow；三次使用 τₓ>0 得
\[
 |Z(u)|^3=\frac{|u-\mu_x|^3}{\tau_x^3},
\]
再由条件 centered cube 可积性常数缩放。无须 ν 的全局三矩。

**123–128 行**逐个用 integrable_map_measure，将上述真可积性转移到真实 ζ，正确使用 .mpr 方向。指定服务器源码 Function/L1Space/Integrable.lean:355–359 的 API 实际为
\[
 \operatorname{Integrable}(f,\operatorname{map}(Z,\eta))
 \Longleftrightarrow \operatorname{Integrable}(f\circ Z,\eta),
\]
前提是目标 f 在映射律下 a.e. 强可测、Z 在 η 下 a.e. 可测；连续 id/平方/绝对三次和 hZmeas 全部满足。不是依靠 Bochner 全定义积分对非可积函数返回默认值来伪造矩。

**129–149 行**在真可积性已具备后分别使用实际 integral_map 和常数除法，得到
\[
 E_\zeta Z=0,\qquad E_\zeta Z^2=V_x/\tau_x^2=1,\qquad
 E_\zeta|Z|^3=C_c/\tau_x^3,
\]
其中 C_c=Eη|U−μₓ|³。二矩的 div_self 使用已证明 Vₓ≠0；cube 的缩放方向由 τₓ>0 保证。服务器只读核对 Bochner/Basic.lean:1076–1079 的 integral_map：本实现提供了所需的真实 a.e. 可测映射和被积函数 a.e. 强可测性。

**150–153 行**把最后的参数精确化为
\[
 \frac{C_c}{\sqrt{(n-j:\mathbb N)}\,\tau_x^3}
 \le64/y^3,
\]
再调用已接受的同一 retainedSample_lyapunov_bound。没有把 centered cube 换成 raw cube，也未将常数 64 宣称为 Gaussian/BE 误差常数。这个标准化律与第 1 定义的真参数完全一致。

另只读核对 Mathlib Measure/Typeclasses/Probability.lean:124–132 的 map 概率实例，故 100 行 infer_instance 有实际公开实例可用；真实仿射函数的独立可测性证明确保这里仍是所需可测推前。未运行 API #check 或任何 Lean。

## 证明三：弱穿越包含与精确恢复事件

**195–204 行**先证明 s.card≤n，再在 Nat 中用 n−(n−s.card)=s.card 建立 hret。size bounds 给 j<n、n≥64、n−j≥1，随后推 hn、hs；x>0 及 j≤x²/2 严格推出 j<x²。固定删除集为 sᶜ，真正基数为 j，且 univ\sᶜ=s。没有把好集 s 当坏集，或未证合法就把 Nat subtraction 换成实数差。

**205–217 行**Y 是真实升序保留路径；可测性逐坐标证明。第一个公共定理取 g=id 和实际闭 cutoff Bₓ，给整个 Y 的 law 为 ηₓ^{⊗m}。map_apply 在已有可测 weak upperCrossing 上得到事件概率等式 hrawprob。这里调用的是完整 path law，不是边缘同律替代事件 law。

**218–231 行**对每条原始路径应用已接受 chronological deletion，删除固定 sᶜ，并由真实 hcomp/hIcard 把保留路径、长度和阈值识别为 s、m、y。不同正长度证明通过 proof irrelevance 兼容，不改变非空前缀事件。得到全路径集合包含后，在同一真实 cond μ A 下使用 measure_mono，再以 hrawprob 识别 raw product 概率。没有将所求原条件穿越界当作输入。

**232–244 行**从同一来源条件再次取实际 variance positivity，得到 τₓ>0；定义同一实际标准化保留路径 G 和逐坐标恢复映射 R，两者都可测。第一个公共定理取真实 retainedStandardize，得到整条 G 的 law 为 ζₓ^{⊗m}，没有新增标准化 iid 假设。

**245–251 行**用导出的 τₓ≠0，逐坐标证明
\[
 R(G(\omega))=Y(\omega)
\]
对所有 ω 成立。该等式恢复的是整个 raw 路径，先于概率操作；没有只证明 marginals 相同、只恢复终点和，或在零分母处非法消去。

**252–266 行**原始 upperCrossing 的 R 前像可测，随后实际 hstd map_apply 转移该事件。最后用 hrestore 将两个 Ω 事件精确识别，因此 raw product crossing probability 与标准化 product 上恢复后的 raw crossing probability 相等。这个概率等式没有用 BE、Gaussian 或任意尾估计。

## 能量、前缀与全部实际边界

实现不需要另写一个公开 energy 展开引理：右侧事件直接把 R(a) 交给已有原始 upperCrossing，且 hrestore 是完整路径等式，因此其中原始能量和每个前缀都自动保全。其精确数学展开为，对 1≤r≤m，
\[
 S_r(Ra)=r\mu_x+\tau_x S_r(a),\qquad
 Q_m(Ra)=\tau_x^2Q_m(a)+2\mu_x\tau_xS_m(a)+m\mu_x^2.
\]
所以 event 实际包含前缀 drift、完整交叉项和 mμₓ²。没有省略 2μₓτₓSₘ、没有把真实 energy 换成中心 energy、mVar 或 mEZ²，也没有因 ζ 单位方差将随机平方和变成常数。前缀只在 1,…,m，未使用超出长度时错误的 rμₓ 公式。

- Bₓ 的 |u|≤1/x 是闭条件；坏集为严格 |u|>1/x，阈值原子仍保留。
- 穿越是弱 ≥，未换成严格或默认连续分布。零 raw 平方和对应全零 raw 路径，仍在非空前缀 weak crossing 中；其标准化坐标可以不为零，R 的完整恢复不会删掉该分支。
- 第一个 theorem 的非空 hs 和固定正概率 hA 是明确前提；νB≠0 由它们推导。没有空保留集下的共同条件律正常化结论或无条件随机长度 iid 结论。
- 第二、三 theorem 的 n=0、全删空路径、Vₓ=0、τₓ=0 都由来源条件排除。j=0、s=univ、j=x²/2 均允许；j=0 时 y=x，不制造阈值 slack。
- 源 Hₓ≤1 与 x≥2、x⁶≤n 保持原值，没有偷用 main 的 ε/(1+x) cutoff 数值界。仅第一个任意 B 定理可直接用于该不同 cutoff 的固定 all-good path law；标准化矩或比较的粗 cutoff 预算须另行验证。

## 来源对应和最终范围

supplement.tex:82–99 给真实预算/样本量；126–140 给弱 chronological deletion，包含平方和为零；144–209 给固定坏集正概率 fiber、按原顺序保留 law 和 raw 矩。当前模块完成这些对象之间的真实完整 path-law 和概率事件桥接，并给实际标准化 law 的矩。1075–1084 的 BE 输入中心三矩/τ³√m 被正确提供为参数，但那里 BE 的分布函数结论本身没有由本模块证明。

**最终裁决：CORRECT。** 两定义、三定理保全冻结数学声明，全部证明有真实可测/可积依据，正性从实际来源条件推出，weak crossing 包含与标准化恢复事件均忠实。源码未见 sorry/admit/new axiom/unsafe/native_decide 或跨模块 _private 名称。协调者所述 target exit 0、9 声明标准公理审计属于另行服务器证据；本报告不将其表述为本轮自行重跑的内核检查。

结论仍限于真实 conditional raw product 事件及同一事件的标准化表示。Gaussian bounded-random 尾界、Petrov BE 的严格 CDF/区间推论、Mills 比较、square tilt/random denominator 分层、随机删除集平均和大删除界以及完整 C1/C2 均未由此闭合，也未被循环假设。
