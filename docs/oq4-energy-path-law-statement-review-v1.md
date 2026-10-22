# EnergyPathLaw E3 第一叶声明语义核对 v1

STATUS: CORRECT
E3_STATUS: OPEN
ROOT_STATUS: OPEN

本票仅认证原式(7)到冻结声明的源语义、实际路径对象、量词、密度因子、真可积性及边界，不认证证明或实现。未读取新EnergyPathLaw证明/实现、variance证明/实现或独审票，未运行Lean，未操作Git/cache。未读取冻结稿所引接口intake或其他旧审查票替代原源。

## 来源与实际接口读取

原始只读源：
C:/game/shao/current/oq4/energy01.md 第69–77行，特别是第71行的事件上逐坐标闭界、第73–75行式(7)、第77行无需全局二次指数矩。

源SHA256：
2E0387F0A35CA677853E45FFF271CC2FB0E87DB9EE9C6B2F00D3BCF56B51D9E6

本次冻结：
C:/game/shao lean/drafts/oq4/frozen-energy-path-law-v1.md

冻结SHA256：
DCC050F7C229BBE6410DD5B9562BC4F349D6466B2E82CEEB70956DAE7E545899

共享定义/声明只读核对：

- library/Shao/Basic/FinitePath.lean：Path n=Fin n→ℝ；prefixSum按i.val<k求和；energy a=∑i(a i)²。
- library/Shao/Basic/ClosedSurvival.lean：closedStrip h要求全部k≤n的|prefixSum a k|≤h；逐坐标声明abs_coordinate_le_two_mul_of_mem_closedStrip给|a i|≤2h。
- library/Shao/Probability/FiniteIID.lean：samplePath X ω=i↦X i ω；iid_samplePath_map_eq_pi的实际环境包含双方概率测度、各坐标Measurable、iIndepFun及IdentDistrib (X i) id p ν。

未读取这些共享定理的证明体。实际energyTiltedLaw、energyWeight、energyNormalizer沿此前获准的N0/N1冻结定义，不重新定义替代law。

## 1. 前提与路径对象忠实

冻结稿使用实际Π_n(ρ)=Measure.pi(fun _ : Fin n => ρ)，以及同一Shao.Path n上的A=closedStrip h、Q=energy。原源的S0=0在共享closedStrip中被明确包含；h≥1时它与源max_{1≤k≤n}|S_k|≤h一致，并合法保留n=0的空路径版本。

μ=energyTiltedLaw ν h s是真实权重w/Z相对于ν的非负密度测度，T不进入law定义。概率性、权重真可积及Z>0须内部供应，不能列为新输入。

原平方真可积与单位二阶矩足以供应这部分有限归一化：h≥1时闭截断质量有正下界，截断内指数权重有有限上下界。原中心和原第三绝对矩不为式(7)或此有限身份所必需，省略它们是合法局部加强。最终调用既有API时仍须在该弱前提域内完成，不能为适配而回添中心、第三矩或原ν指数矩。

## 2. 密度与精确系数

冻结所列真实积分身份

∫Φ dΠ_n(ν)=exp(−s(n:ℝ)/h²) Z^n (Π_n(μ)).real A

与原式(7)完全一致。归一化因子是Z的自然数n次幂，外部指数是exp(−sn/h²)，符号、n因子及h²分母均正确。

在A内，共享逐坐标界保证每个|a i|≤2h，因此所有闭截断指示均为1，有限乘积权重为exp(sQ(a)/h²)。实际μ的有限π乘积密度需要包含Z⁻n，移项后恰给右侧Z^n；冻结稿明确要求从实际Measure.pi构造交付该身份，没有预设具有所需密度的替代路径law。

上述截断指示的删除只在A内成立，不可推广至整个路径空间。冻结稿在A外令Φ=0并明确禁止该推广，范围正确。最终身份不除以生存概率，故无需A概率为正或生存条件后独立性。

## 3. Φ真可积的有限支配

Φ使用实际闭事件指示和真实Q：

Φ(a)=if a∈A then exp(s(Q(a)−(n:ℝ))/h²) else 0。

在A内，Q≥0且Q≤4(n:ℝ)h²；这个Q上界只在事件内使用，并不是全路径空间的无条件Q上界。|s|≤T、h≥1因此给全空间Φ的有限支配

0≤Φ(a)≤exp(−s(n:ℝ)/h²) exp(4T(n:ℝ))。

A外Φ=0，使同一个正有限常数仍然支配。常数对每个有限n、实s、h≥1均有限，正负s都覆盖；Π_n(ν)是概率测度，所以该常数真正可积。

事件和能量沿共享真实路径可测接口处理，指数复合与闭事件指示随后可测。该机制足以供应真实Bochner实积分；不需要原ν未截断的二次指数可积，也不能靠不可积实积分默认值。Π_n(μ)也是概率，故其A质量有限，转real及非负/实积分转换可在真实有限性下进行。

## 4. iid拉回环境完整

冻结稿沿共享iid_samplePath_map_eq_pi，保留了实际所需环境：

- Ω带可测空间，p为其概率测度；ν为实数上的概率测度。
- X:Fin n→Ω→ℝ，每个X i为Measurable。
- iIndepFun X p。
- 每个坐标满足IdentDistrib (X i) (id : ℝ→ℝ) p ν。

由此得到真实Measure.map(samplePath X)p=Π_n(ν)，再把已证Φ真可积和积分身份拉回。冻结中“各坐标与原ν的IdentDistrib”应按上述实际id表示理解；其允许适配已认证接口的措辞与该完整环境一致。

拉回后的事件仍是closedStrip h (samplePath X ω)，能量仍是energy(samplePath X ω)，不是换成其他最大值、改动时间0或条件law。没有增加假设path law已有密度，也没有对生存后law冒用独立性。源概率空间的原变量矩可由其law表达，冻结不需另添加第三矩或指数矩输入。

## 5. 零时间、弱边界与范围

n=0时，Fin 0坐标族为空，closedStrip只检查S0=0；h≥1使A为全集。Q=0、Φ=1，Π_0(ν)与Π_0(μ)均为空乘积概率，Z^0=1、外部指数为1，所以两边真实等于1。不能使用要求n>0的absMax接口缩减这一范围；冻结稿已明确禁止。

h=1、T=0、s=0、零路径、Q=0、弱闭端点及原子全部保留。s=0时μ通常仍是归一化闭截断law，Z通常不是1；身份中的Z^n不能删除。没有除以Q或忽略全零路径。

本叶不依赖θ、E2方差窗口、精确再中心化、K或生存概率正性。它只供应原式(7)，不供应线性再倾斜反向式(8)、共同二维算子、相对渐近、E4、K/Kv、随机分母或完整E3/OQ4。

## 结论

CORRECT：未发现实际有限π对象、闭事件、能量、Z^n与指数系数、Φ真可积性、n=0、iid拉回前提或范围缺口。可通过E3第一叶声明语义门；证明及最终形式认证另行完成，E3与全部完整根保持OPEN。
