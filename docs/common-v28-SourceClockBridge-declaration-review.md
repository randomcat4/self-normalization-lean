# SourceClockBridge 独立声明审查

STATUS: CORRECT（声明/source 阶段：零定义、三条公开定理）

冻结提案：`drafts/c12/SourceClockBridge-next-scope.md`，本轮实际 SHA256 为 `673ad95d64459843af58dd563696a600f3820c662cd038bf5baff7b419b6877c`，与委派值相同。三条完整签名在实际已有定义下均数学成立，源适用条件能够供给，没有需要修复的前提、量词、事件或常数问题。

已读取 SERVER.md、TEAM.md，并按 math-theorem 的命题/前提保全和声明—来源审查规则执行。这里复用已接受依赖，不重审旧概率/指数估计证明。未读未来实现，未编写实现，未运行本机或服务器 Lean、API smoke 或服务器传输；只写本报告。未改提案、原始稿、共享源、缓存或他人文件，无子实例。本报告不构成候选的内核、全公理或根集成认证。

## 精确输入与实际原源

本轮独立计算、核对并读取相关定义/接口：

| 输入 | SHA256 |
|---|---|
| main.tex | `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` |
| supplement.tex | `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd` |
| 已接受 SourceTruncationBridge，drafts/c12 原件 | `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1` |
| library/Shao/Probability/ConditionalIID.lean | `855c2eb0e560ac9372505f8b41551a9895b9eb753be3ce2b3f3752be845af787` |
| library/Shao/Probability/ClockControl.lean | `c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba` |
| library/Shao/Probability/FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| library/Shao/Basic/FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 已接受 GaussianTail，drafts/c12 原件 | `f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922` |

原源位于 `C:/game/shao/current/c12/`。实际对照 main:372–392（已在前项源桥审查中完整核对）、423–430、440–455、491–499、546–556、624–640、763–782，以及 supplement:836–858、3078–3150、3894–3907。SourceTruncationBridge 使用已验收 drafts 原件与独立完整审查，不因本地 library 仍为 v20 而假定该新模块不存在或另写一份证明。

`samplePath X ω i=X i ω`，`prefixSquares a k` 只取 i.val<k 的真实平方，`energy a=∑i a_i²`。`retainedCutoffLaw` 是实际 Mathlib cond；`ConditionalIID.indep_cond_joint_map_eq_pi` 的前提确有固定坐标事件的非零质量，它的结论是实际条件向量测度等于各真实单坐标条件律的 pi。ClockControl 的公开最终接口已实际读取，要求真概率、iid、共同 law、支持、raw nm2 两界、y≥2 和三条数值门，结论的系数正是 2048√(2π)。

## 三条实际签名的独立语义

统一记 a=1+x>0、h=ε/a、B={z:|z|≤h}、A=⋂i X_i⁻¹(B)、μx=cond μ A、ρ=cond ν B、R=n∫F(az)dν，其中 F(w)=w²min(|w|,1)。原 X 是 μ 下 iid 的已归一化坐标，具有 ν law；这不是 μx 下 iid 的自由假设。

1. **sourceTruncation_conditioned_sample，scope53–74。** μ、ν 为概率，原 X 可测/独立/同分布，原平方真可积，x≥0、0<ε≤1、R≤ε³/8。推出 μ.real Aᶜ≤R/ε³、μ.real A≥7/8、μx 是概率、真实向量 law=ρⁿ，并推出 X 在 μx 下独立及每个真实边缘为ρ。不要求原均值零、nEνz²=1、n>0、ν(B)>0 或条件 iid；这些没有被偷偷当作输入。
2. **sourceTruncation_clock_bad_probability_le，scope84–109。** 再明确加入原 normalization nEνz²=1、原 Eνz=0、ε≤1/8；y≥2 且 |y−x|≤1/(2a)。同一 μx 下，严格半时钟事件 Q_floor(n/2)<1/16 与最终能量落在闭[1/4,2]之外的概率之和，先保留2048√(2π)(1+y)³nm3·Tail(y)，再给32768√(2π)R·Tail(y)，最后给32768√(2π)exp(2)R·Tail(x)。m3 是同一固定ρ的真实 raw绝对三矩。
3. **sourceTruncation_final_clock_probability_le，scope125–148。** 保持第二条原始输入但不量化y；对所有x≥0，最终 bad probability 同时≤4nm4、≤8εR/a⁴、≤[32768√(2π)+1/Tail(2)]R·Tail(x)。前两界是单独方差/切比雪夫结论，最后一界拼接x<2与x≥2，而非低阈值套用第二条。

三个命题的 A、μx、ρ 均在 x 固定后再使用；没有按 y、样本观察或某个坏时钟事件重新条件化。m2=Eρz² 为 raw second moment，μρ 可非零；energy 从未变成∑(X_i−μρ)²。

## 第一条：真实 N_x 正质量、空样本与 iid

闭B与hX保证A、Aᶜ可测，Aᶜ精确为有限并 ⋃i{h<|X_i|}，边界原子|z|=h保留。原 IdentDistrib 的真实map等式给每个尾事件的质量等于ν{|z|>h}，有限并界与已接受 sourceTruncation_tail_budget 给

    μ.real Aᶜ ≤∑i ν.real{|z|>h}=nν.real{|z|>h}≤R/ε³≤1/8。

所有测度在原概率门下有限，因此real质量与有限并/补集换算合法。于是 μ.real A=1−μ.real Aᶜ≥7/8>0，进而μ(A)≠0。**先正质量，后 cond 概率和条件 joint law**；不存在用待证条件iid或概率性反过来证明A正质量的循环。7/8是现有弱小预算的精确直接后果，强于原稿只要求的3/4，合理且非新假设。

在非空Fin n上，任取实际索引i，有A⊆X_i⁻¹(B)。原map law与μ(A)>0推出ν(B)>0，才可安装ρ真概率并用产品测度eval边缘。把既有generic conditional vector theorem取B_i=B，得到真实 joint map=ρⁿ，继而eval恢复每个边缘，现有联合map判据恢复条件独立。这里只复用固定坐标条件化定理，不需要普通iid在任意随机事件条件化后仍iid的错误命题。

n=0时，A=univ、R=0、μx=μ；独立/边缘的∀i声明为空，samplePath取唯一空向量，空产品测度为质量1。scalar ρ可能是零测度，但签名没有声明它是概率，空产品也不依赖其值。因此不需增加n>0或ν(B)>0；实现应先分空样本，再在非空分支安装scalar实例，避免证明工程中误添数学前提。

## 第二条：两个源坏事件、原始输入与常数

原 main:427与499正是固定A=N_x，main:549–554给同一真实ρ及raw Q_j；supplement:841–842的两个事件逐字对应这里的 natural n/2、严格<1/16和最终闭区间的补集。没有弱化成另一半截法、改变<为≤、丢弃边界原子或把raw clock换为中心化能量。

第一条提供μx真概率、条件iid和边缘。已验收 SourceTruncationBridge 在本条N/M/ε/R门下给 n≥64、ρ真概率、真实支持、raw nm2∈[3/4,4/3]和三项数值：

    (1+y)h≤1， 8(1+y)²h²≤1， [8(1+y)²]²nm4≤1/2。

当前邻域1/(2a)≤1/a，故合法消费旧较宽邻域结论。h>0来自ε>0、a>0；y≥2保留了generic clock proof的实际适用范围。所有generic参数均由**原始**输入推得，未将正Var、conditional mean0、原高矩、desired event bound或small moment payment加成前提。

精确调用已接受 ClockControl 后，以同一x法则的 (1+y)³nm3≤16R 相乘，常数2048乘16=32768，R没有被H≤1粗界消掉；Tail(y)≥0。最后用实际standardNormalTail_local_comparison上侧Tail(y)≤exp(2)Tail(x)，乘以32768√(2π)R≥0。第一项还强于原 CΛ_yTail(y)形式，因为Λ_y的drift项非负。

源 main:639还写y≥γ。generic clock论证在y≥2、实际支持/矩门下不需要这个额外条件，故当前声明覆盖更广y并仍覆盖全部源-admissible y。若只为解释源范围，已接受raw bounds与真实方差还给 γ=m3/Var≤(8/3)h≤1/3<2；该解释不意味着此单元形式证明了所有γ比较、noise构造或其它源条件矩结论。不能在实现中把γ直接设为0。

ε≤1/8由真实main:376–377第二个minimum分支及L≥1600供给；不是从ε≤ε0/2≤1/2擅自加强。当前更强标量数值路线避免依赖未形式化的“足够小η0/ε0”或用待证Λ界作输入的循环。

## 第三条：小 x 与所有 x 的最终时钟支付

令Q=∑i X_i²，所有期望/方差都在同一μx下。ρ支持有界，故各z²有真实L2（四矩仅在ρ下，不在原ν全局）。通过真实IdentDistrib把二/四矩运输到各原坐标，平方复合保持独立，有限和给

    Eμx Q=nm2∈[3/4,4/3]，
    Varμx Q=n Varρ(z²)=n(m4−m2²)≤nm4。

这只用实际独立有限和方差和切比雪夫；即使不采用特定库名，也可由中心化平方和展开、不同坐标协方差为0证明，无需假设Q与坐标独立或引入外部渐近结果。未来实现仍要实际给L2和所调用Mathlib定理的前提，当前声明审查没有编译认证API名字。

若Q<1/4，而EQ≥3/4，则EQ−Q>1/2；若Q>2，而EQ≤4/3，则Q−EQ>2/3≥1/2。因此正确的**闭好区间之补集**包含于{|Q−EQ|≥1/2}；不是反向包含，也没有把端点1/4、2计入bad。真实L2切比雪夫给bad≤4Var(Q)≤4nm4。

已接受原R支付给nm4≤h·nm3≤2εR/a⁴，故bad≤8εR/a⁴。因a≥1、0<ε≤1/8、R≥0，该界对全部x≥0还≤R。对0≤x<2，实际尾反单调与Tail(2)>0给

    bad≤R≤[1/Tail(2)]R Tail(x)。

不需数值近似Tail(2)，也未除R、m3或n。对x≥2，第二条取y=x，邻域差为0、原law不变；最终bad是两个非负项之一，所以bad≤32768√(2π)R Tail(x)，此处无需exp(2)。两个正系数之和统辖两支，正是第三条显示常数。x=0属于切比雪夫分支且完全合法；x=2可属大分支，两边界均覆盖。不能用一条只对y≥2的指数clock theorem代替上述小x论证。

## 无循环假设、实施门与结论范围

- 真实原 normalization是nEνz²=1，原二矩为1/n；原均值零是M输入，不是ρ均值零。第二/三条保留M以消费已接受scalar接口，并未更改源假设。
- 条件化后的样本iid/同law从固定事件与原iid推得；坏时钟概率、conditional原点矩/高矩可积、n正性和Clock数值均是输出或已接受原输入的推论，未把目标藏进接口。
- y变化时N_x、μx、ρ均不变；没有生存条件化、按样本选择、permutation或后续square/exponential tilt。晚块整体signed payment仍需已接受LindleySignedBlock，其const1整体估计不能改成逐项绝对值求和损失。
- 第三条只支付source sandwich中的b_x。平滑noise及其矩、确定性sandwich、Fourier频率域、untruncated bad-large、解平滑收缩与完整C1/C2根未关闭。第二条的显式y≥2也必须原样保留。
- 此为零定义三声明的CORRECT裁决，作者尚未实施。实施后需定向服务器目标、全部模块归属的public/private/generated声明公理门、签名/源哈希、禁用项扫描及新的独立完整proof审查。不得把本报告或提案中的分析当作Lean成功。

JUSTIFICATION: 实际N_x补集有限并预算先建立正质量；正确处理n=0后，generic真条件law给条件iid。精确两个raw坏事件消费已接受ClockControl，系数与R支付正确。最终clock以独立平方和的真实方差与切比雪夫单独覆盖小x，再以Tail(2)>0和y=x大分支拼接统一常数。源参数、量词、事件端点和条件均值均保全；无需修改冻结签名。
