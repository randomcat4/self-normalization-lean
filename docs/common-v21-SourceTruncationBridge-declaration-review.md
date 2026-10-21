# SourceTruncationBridge 独立声明审查

STATUS: CORRECT（声明阶段，零定义、八定理）

冻结 scope：C:/game/shao lean/drafts/c12/SourceTruncationBridge-next-scope.md。
SHA256：43c846bcb05d87b9cc4a9e38c28e905286724bc846477118adc12ddbd49d24c5。

本轮先只提取八个 Lean 签名并独立翻译量词，再读完整 scope、原 source 和所需已接受公开定义/声明，最后核算尺度、矩、方差及 Clock 数值。未实施、未运行本机或服务器 Lean、未复跑旧目标、未重审已接受证明，也未修改作者文件。CORRECT 是八条拟议声明及其 source 适用范围的数学裁决；不存在候选 Lean proof 的最终审查或内核认证。

## 一、八个实际签名的独立盲译

全部量化 ν:Measure ℝ、n∈ℕ、实 x,ε，输入 h2:Integrable(z↦z²)ν、x≥0、ε>0。记

    a=1+x， b=a/ε， h=ε/a， B={z:|z|≤h}，
    R=truncationBudget ν n x=n∫F(az)dν，
    H=n∫F(bz)dν， F(w)=w² min(|w|,1)。

以下 P 表示额外的 IsProbabilityMeasure ν；N 表示实际 normalization n∫z²dν=1；M 表示原均值 ∫z dν=0。n 的减乘转实数按每条实际公式解释；条件 law 一律是固定在 x 的真实 ρ=cond ν B。

1. sourceTruncation_reparameterization（scope 96–110）：ν 可为一般 measure，不要求 P、N、M；输入 0<ε≤1，结论为

       1/b=h， retainedCutoffSet b=B，
       retainedCutoffLaw ν b=cond ν B，
       H=truncationBudget ν n (b−1)， R/ε²≤H≤R/ε³。

   条件 measure 的等式不承诺其为概率或 B 有正质量；n=0 合法。预算是 R_n(b−1)，不是 R_n(b)。

2. sourceTruncation_sample_size（124–133）：额外 P、N，0<ε≤1/2、R≤ε³/8；不要求 M，结论 b≥2、b⁶≤(n:ℝ)、64≤n（最后一式为 Nat）、H≤1/8。没有 n>0、R>0 或新 cutoff 的 sample-size 前提。

3. sourceTruncation_tail_budget（143–155）：额外 P，0<ε≤1；不要求 N、M 或小预算，结论为严格尾 T={h<|z|} 的

       n ν.real T≤R/ε³，
       n∫|z|1_T dν≤R/(ε²a)，
       n∫z²1_T dν≤R/(εa²)。

   n=0 合法。tail 是闭保留集 B 的精确补集；原子 |z|=h 仍在 B。

4. sourceTruncation_law_data（168–183）：额外 P、N，0<ε≤1/2、R≤ε³/8，不要求 M，结论 3/4≤ν.real B≤1、IsProbabilityMeasure ρ、ρ-a.e. |z|≤h，以及 z、z²、|z|³、z⁴ 全部在真实 ρ 下可积。正质量、真概率和高矩可积性都是输出。

5. sourceTruncation_paid_moments（194–212）：额外 P、N、M，0<ε≤1/2、R≤ε³/8。令 μ=∫z dρ、m3=∫|z|³dρ、m4=∫z⁴dρ，结论

       n|μ|≤2R/(ε²a)， nm3≤2R/a³， nm4≤h nm3，
       |z−μ|³ 在 ρ 下真可积， Eρ|z−μ|³≤8m3。

   原均值零不等于条件均值零。raw cube 与 centered cube 被分别保留。

6. sourceTruncation_variance_bounds（225–244）：输入第 5 条相同 P、N、M、ε 与 R 条件，令 m2=∫z²dρ、V=variance id ρ，结论

       3/4≤nm2≤4/3， nμ²≤1/4，
       V=m2−μ²=∫(z−μ)²dρ，
       V>0， 1/2≤nV≤4/3。

   没有方差正、条件均值零或 raw m2=variance 前提。

7. sourceTruncation_nearby_payment（256–276）：输入第 5 条相同条件，再量化实 y≥0、|y−x|≤1/a；ρ 仍固定在 x。令 Λ=(1+y)n|μ|+(1+y)³nm3，给

       (1+y)h≤2ε， (1+y)³nm3≤16R， Λ≤20R/ε²，
       Λ Tail(y)≤[20 exp(2) R/ε²] Tail(x)。

   Tail 是已接受真实 standardNormalTail，非代理尾或样本 Gaussian comparison 输入。

8. sourceTruncation_clock_inputs（290–303）：额外 P、N，0<ε≤1/8、R≤ε³/8、y≥0、|y−x|≤1/a；刻意不要求 M。结论

       (1+y)h≤1， 8(1+y)²h²≤1，
       [8(1+y)²]² n∫z⁴dρ≤1/2。

   这是 ClockControl 的三个真实数值输入，不是 clock probability 结论，也未声称 y≥0 已满足其最终概率 theorem 的另一个 y≥2 前提。

## 二、source 参数是否实际提供所列范围

本轮实际读取 main.tex:355–435、546–551、622–640，supplement.tex:522–533、2045–2135、3078–3099、3117–3126。来源冻结哈希：

- main.tex：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- supplement.tex：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

main:372–382 的实际构造是 ε0∈(0,1]、L≥1600、K=8(1+L)，以及

    ε=min{ε0/2,1/[4(K+1)L]}，
    η(u)=min{u³/8,u²η0/40,ρ*/32,1/(4A0)}。

两个 ε 分支均严格正；第一分支给 ε≤1/2。第二分支的分母 4(K+1)L≥6400≥8，确实推出 ε≤1/8。这个更小范围有实际 source 支持；仅凭 ε≤ε0/2、ε0≤1 本来不能推出它，提案没有作该错误推断。

main:389–392 的 D3 实际包含 x≥0 和 R_n(x)<η(ε)，所以真实 source 既给 R<ε³/8，也给 R<ε²η0/40。拟议 hR 使用 ≤ 是合法放松，不是额外强假设。第 7 条因此还能由真实第二分支推 Λ<η0/2，计算为 20R/ε²<η0/2；提案没有把这条小 Λ 预算当作自由结论。

原 ξ=X/(σ√n) 的有限 raw second moment、原均值零和 nEξ²=1 对应 N、M；source 当前条件 law main:546–551 明确是 ξ 在闭 {|ξ|≤h_x} 下的真实条件分布，且条件均值未必零。main:639 的邻域是更小的 1/[2(1+x)]，安全蕴含当前 1/a 邻域；源 y≥γ 且 γ>0 可以提供当前 y≥0。Clock probability 本身仍需 y≥2，不能把数值桥在所有 y≥0 的有效性泛化成概率 lemma 的全 y 适用性。

因此这些 ε、R、邻域限制能由本段实际 D3 proof parameter 构造供给。不过此报告不把 generic N/M 的实例化、D3 membership 或原根定理其它区域自动视为已形式证明。main:395–400 已将 x=0 单独处理；本声明包含 x=0 是合法加强，不声称 D3 分支替代整个原根论证。

## 三、换参、真实 H 和 ε⁻⁶ 样本量付款

本轮核对已接受公开定义：retainedCutoffSet b={|z|≤1/b}，retainedCutoffLaw ν b=cond ν(retainedCutoffSet b)；truncationBudget ν n t=n∫F((1+t)z)dν。由 a≥1、ε>0，有 b>0、1/b=ε/a，从而闭集合和两个真正 condition measure 精确相同。

在第 1 条，一般 measure 的 B 可能零质量或无穷质量，不能声称 cond 为概率；但相同集合下 Mathlib cond 的真实 measure 仍严格相等。h2 使任意实 scale 的 F kernel 真可积。取 c=1/ε≥1，复用已接受 truncationBudget_scale_one_le 给 c²R≤R_n(ca−1)≤c³R。ca=b，所以正是 R/ε²≤H=R_n(b−1)≤R/ε³，不是 R_n(b) 或 H≤R。

在第 2 条，N 排除 n=0，并由真实非负 F 和 normalization 推 R>0；不能先除 R 再解释零预算。ε≤1/2 与 hR 给 0<R≤1/64≤1/16。已接受 TruncationSampleSize 实际中间式是

    (1−R)³ a⁶/R²≤n。

R²≤ε⁶/64，且 (1−R)³≥(63/64)³>1/64。于是

    b⁶R²=a⁶R²/ε⁶≤a⁶/64≤(1−R)³a⁶。

所有分母 ε⁶、R² 都真正正，故 b⁶≤n。另 a≥1、ε≤1/2 给 b≥2，推出 n≥64；H≤R/ε³≤1/8。弱端点 hR=ε³/8 或 ε=1/2 仍有效。

不能只拿旧 theorem 较弱的 a⁶≤n 就推 b⁶≤n：ε<1 时 b⁶=a⁶ε⁻⁶ 更大。提案明确要求使用实际 R-dependent 中间式，故这个关键迁移没有缺口。

## 四、严格原尾、正质量和保留 R 的真实条件矩

### 三条尾预算与全部可积性

若 |w|>ε、0<ε≤1，则分 |w|≤1 与 ≥1，由 F 的真实 cubic/quadratic 公式逐点有

    F(w)≥ε³， F(w)≥ε²|w|， F(w)≥εw²。

取 w=az，a>0，tail |z|>h 等于 |az|>ε。ν 为概率，indicator-one 真可积；原 |z| 的 L1 来自实际 L2/概率，strict tail-one/tail-two 亦有已接受 marked-kernel integrability。F(az) 可积，才能作真实 integral comparison，得到第 3 条三项、精确各分母 ε³、ε²a、εa²。n≥0 只作非负乘数；n=0 全项为零，不需除 n。

### 正 conditioning mass 和真正概率

在 N 和小预算下，n≥1，nq≤R/ε³≤1/8 给 q=ν.real{|z|>h}≤1/8≤1/4。严格 tail 与闭 B 互补、两者可测，概率质量一保证 ν.real B=1−q≥3/4。正质量是推论，足以使真实 cond 成为概率并支持于 B；不是将 cond 任意赋予概率实例。

真实 bounded ρ 使 z、z²、|z|³、z⁴ 都真可积。原 ν 无全局 cube/fourth 也完全允许：仅有界区域内的 marked 原矩用于 condition integral，其 integrability 从原 L2 的 cutoff domination 得到。

### 原均值零给真实漂移，raw cube 保留 R

令 p=ν.real B=1−q，p≥3/4。原 id 真可积，M 给 ∫_Bz=−∫_(Bᶜ)z；真实条件积分公式给

    |μ|≤p⁻¹∫_(Bᶜ)|z|，
    n|μ|≤2R/(ε²a)。

不能只因 M 就称 μ=0。另一方面 B⊆{|z|≤1/a}，在 B 上 |az|≤ε≤1 且 F(az)=a³|z|³，故条件 cube 满足

    nm3≤R/(a³p)≤2R/a³。

这里 R 没有被 H≤1 的粗界抹掉。再由 ρ 真支持得到 m4≤h m3，所有比较双方真可积。真实 centered cube 的 integrability 和 ≤8m3 可直接复用已接受 retainedCutoffLaw_centered_moments，经真实 law 等式运输；它不需要额外 Jensen 假设或把 raw cube 当 centered cube。

raw cube 与 fourth comparison 本身不需要原 M；第 8 条可以使用私有 raw-moment helper，无需把第 5 条未用的 M 误添进公共 Clock 输入。

## 五、raw 二矩、真实 Var 与邻阈值

令 v=n∫_(Bᶜ)z²dν。第 3 条给 v≤R/(εa²)≤ε²/(8a²)≤1/4，且 v≥0。真实 conditional integral、N 给

    nm2=(1−v)/p， 3/4≤nm2≤1/p≤4/3。

paid drift 与小预算还给 n|μ|≤ε/(4a)≤1/8。n≥1、n>0 后可合法计算 nμ²=(n|μ|)²/n≤1/64≤1/4；或者用 |μ|≤h 支付而不除 n。真实概率与 square integrability 给 Mathlib variance 的 identities

    V=m2−μ²=∫(z−μ)²dρ。

因此 1/2≤nV≤4/3，n>0 蕴含 V>0。方差正性不是假设，也不是用 raw m2 正性代替。原 M 在这里确实必要：ν 为点质量 1/√n 时 N 成立，n 大可令 R 很小且全部 retained，但 ρ 仍点质量、V=0；它正好违反 M。

对第 7 条，c=1+y>0、|y−x|≤1/a、a≥1 给 c≤a+1/a≤2a。所以 ch≤2ε、c³nm3≤16R，漂移部分≤4R/ε²，cube 部分≤16R≤16R/ε²，从而 Λ≤20R/ε²。

已接受 standardNormalTail_local_comparison 的实际前提就是 x,y≥0 和 |y−x|≤1/(1+x)，输出 Tail(y)≤exp(2)Tail(x)。Λ 与 20R/ε² 非负、tail 非负，所以可合法乘界得到最后 weighted payment。ρ 一直固定在 x，不随 y 重新截断；没有样本 Gaussian approximation、反向 IdentDistrib 或 tail proxy。

## 六、Clock 输入的常数与缺失 M 是否正当

第 8 条取 c=1+y≤2a、h=ε/a、θ=8c²。原 M 不用于 source raw cube/fourth 上界，因此无需添加；Clock 中心化的是 A² 而非 A。由上述 genuine raw 矩界得

    ch≤2ε≤1，
    8c²h²≤32ε²≤1/2≤1，
    θ²nm4≤64c⁴h nm3
             ≤128ε c³nm3
             ≤2048εR
             ≤256ε⁴
             ≤1/16≤1/2。

每一步只乘非负 c、ε、n、m3 等因子；R 小因子一直保留。ε≤1/8 的端点给 256ε⁴≤1/16，常数充分。若仅知 ε≤1/2，则这条特定粗估计的上界可达 16，不能据此推 1/2；提案如实使用 source 第二 minimum 分支推出的 ε≤1/8，没有假装 ε≤1/2 自行足够。

ClockControl 的第三 theorem 除这些数值还需要真实 bounded iid sample、ρ 概率、支持、raw normalization 和 y≥2。第 4、6、8 条供 scalar-law 的相应输入；sample 的 fixed-event conditioning iid/common law 仍需实际 ConditionalIID 运输，未被本八条标量定理替代。两个坏 clock 事件和全 raw energy 均没有改定义。

## 七、边界及可接受范围

- x=0 给 a=1，无奇点；ε>0 排除零除。ε=1 只属于第 1、3 条允许范围，ε=1/2 属于第 2、4–7 条，ε=1/8 属于第 8 条；相应弱端点均成立。
- 第 1、3 条允许 n=0；normalized 各条由 N 推 n>0，并通过真实 sample-size 链得 n≥64。R=0 在 normalized 前提下不可能，不存在对零预算的除法捷径。
- B 使用 |z|≤h，尾事件 h<|z|。|z|=h 的原子真实保留；F 在 |az|=1 的两公式一致。所有 marked original cube 仅在真实小区域积分，未假设原高矩。
- 第一条只是 cond 等式，可包含 B 质量零/无穷；只有第 4 条以后由实际正质量宣布概率。不能把第一条的一般 measure 情形直接实例化成未证概率。
- 原 M 必要地保留在漂移/正 Var/Λ；raw 四矩 Clock 数值不需要它。Later tilted laws 不等于本固定 ρ，需重证 moments 和 budgets。
- 八条没有量化或证明所有 source γ 比较、γ≤2h、m2≤γ²、nm3≤2r_n；这些若由后续噪声构造消费，须另行供给。它们也不闭合整个 conditional-moment source lemma、Fourier frequency-domain transport、noise/smoothing、严格 CDF、zero-energy 或 C1/C2 根目标。

## 裁决

CORRECT：固定哈希的八条声明数学成立，无需修改签名。真实 cutoff 换参、H=R_n(b−1) 与双向 ε scaling、带 R 的 b⁶样本量付款、真实 conditioning mass/高矩/Var、邻阈值 exp(2) 支付和 Clock θ²nm4 数值均正确；source 实际参数构造确实提供 ε≤1/8、R<ε³/8 等适用条件。

该结论只放行此 scalar-law bridge 的声明阶段。实现仍须完成真实 condition/integral 运输、全部可积与正性、端点及 algebra，再作定向服务器检查、完整声明/语义依赖审计和新的独立 proof 审查；当前没有候选内核证明或原根全覆盖结论。
