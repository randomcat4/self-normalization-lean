# EnergyLinearPathLaw E3 第二叶声明语义核对 v1

STATUS: CORRECT
E3_STATUS: OPEN
ROOT_STATUS: OPEN

本票仅核对原式(8)到冻结声明的实际有限π密度、反向身份、有限夹界、可积性、iid拉回和范围，不认证证明或实现。未读取EnergyPath作者新证明/实现/审稿票或E2endpoint新产物，未运行Lean，未操作server/Git/cache。

## 来源与读取绑定

原始只读源：
C:/game/shao/current/oq4/energy01.md 第78–83行。

第80行式(8)为P_{h,s}(A_h)=L^n Ẽ[1_{A_h}exp(−θS_n)]；第83行强调终点指数控制及始终使用同一个绝对部分和事件。冻结的全实t有限身份在t=θ时准确供应该式，但不直接认证第83行的相对渐近。

源SHA256：
2E0387F0A35CA677853E45FFF271CC2FB0E87DB9EE9C6B2F00D3BCF56B51D9E6

本次冻结：
C:/game/shao lean/drafts/oq4/frozen-energy-linear-path-law-v1.md

冻结SHA256：
54678CA7ADBDCFAF007F34B1637693F2B70E6E73A15D69A761BF88F52E601091

对象沿此前获准的实际energy/linear-law及共享FinitePath、ClosedSurvival、FiniteIID定义与声明。未读取冻结稿所引接口intake或其他审查票替代原源。

## 1. 对象、弱前提与全实t量词

冻结稿保持同一实际μ=energyTiltedLaw ν h s、μ_t=energyLinearTiltLaw ν h s t、L=energyLinearNormalizer ν h s t，及实际Π_n=Measure.pi、Path n=Fin n→ℝ、A=closedStrip h、S=prefixSum a n。

原square真可积、单位二阶、ν概率与h≥1、T≥0、|s|≤T足以供应实际能量law的概率和闭支持。后续线性指数在该闭支持上对全部实t真正可积；无需原中心、原cube、M、K、θ、方差下界或原ν指数矩。省略原源已有但有限身份不使用的条件是合法局部加强。

实际概率、L>0、指数可积性和路径事件可测性必须内部供应；冻结没有把这些结论或路径密度作为新输入。law本身不依赖T或是否已经中心化。

## 2. 全路径线性密度与归一化方向

实际μ_t相对于μ的单步密度是exp(tx)/L。有限π乘积密度因此应为

exp(tS(a))/L^n，

其中S(a)=prefixSum a n=∑i a_i。指数符号、终点与n次幂均正确，冻结要求从同一真实withDensity和Measure.pi构造证明或实例化。

该线性乘积身份可以对全部路径成立，因为此处比较的是μ_t与已经构造好的μ，单步相对密度没有新的截断指示。它不允许把原ν到μ的能量截断指示在全路径空间删除。冻结稿明确区分了这两件事，未发生无条件删除错误。

密度的实/ENNReal表示和测试积分转换仍需实际正性、有限性及真可积接口；不能先定义另一个具有所需密度的替代路径law。这里n为任意自然数，空乘积也在范围内。

## 3. F_t真可积及精确反向身份

冻结定义

F_t(a)=if a∈A then exp(−tS(a)) else 0。

同一个A在k=n处给|S(a)|≤h，因此在A内

exp(−|t|h)≤exp(−tS(a))≤exp(|t|h)。

全路径F_t非负且由正有限常数exp(|t|h)支配；A外为零。Π_n(μ_t)是真实概率，所以F_t真正可积。事件和终点沿实际共享可测对象处理，不需原ν未截断指数矩。

反向身份

(Π_n(μ)).real A=L^n ∫F_t dΠ_n(μ_t)

方向正确。使用上述实际密度时，exp(tS)与exp(−tS)相消，剩余L⁻n；移项后正好是L^n而非其倒数。L>0和L^n>0须由已有law接口内供，冻结没有通过总实积分默认值或生存概率归一化来制造身份。

## 4. 不除生存概率的有限夹界

事件内的指数上下界给

L^n exp(−|t|h)(Π_n(μ_t)).real A
≤(Π_n(μ)).real A
≤L^n exp(|t|h)(Π_n(μ_t)).real A。

因L^n>0，乘法方向不变。下界和上界指数的符号、绝对值以及h系数均正确，没有遗漏n或多加n：使用的是终点|S_n|≤h，而不是逐坐标累加得到的较粗nh。

此夹界不除以任何生存质量，故允许(Π_n(μ_t)).real A=0。该情形身份及夹界仍有效，无需条件化law或稀有事件概率正性，也不使用生存条件后的独立性。

## 5. iid拉回环境

沿共享iid_samplePath_map_eq_pi，μ_t侧真实拉回需要：

- Ω带可测空间，p为概率测度，μ_t已内部证明为概率；
- X:Fin n→Ω→ℝ，∀i, Measurable (X i)；
- iIndepFun X p；
- ∀i, IdentDistrib (X i) (id : ℝ→ℝ) p μ_t。

此时Measure.map(samplePath X)p=Π_n(μ_t)，可把F_t真实可积性和相应积分拉回。μ侧的概率可用目标law改为μ的同一个共享map桥拉回，环境相同。

两侧拉回各自使用其真实目标law；不应要求一个样本族同时具有μ与μ_t两种不同边缘law，也不需要在两侧样本之间新增耦合。冻结稿允许适配既有桥，并未作这种错误要求。

拉回事件始终是相同closedStrip h，终点是prefixSum n。没有改成其他最大值事件、添加均值平移或假设path law有密度。独立性来自原无条件iid环境，不是生存后的独立性。

## 6. 零参数、闭边界与后置范围

n=0时，A为全集，S=0、F_t=1、L^0=1，空乘积概率质量为1，反向身份和两侧概率均为1。有限夹界成为exp(−|t|h)≤1≤exp(|t|h)，同样有效，不要求n>0。

t=0时L(0)=1、μ_0=μ为真实测度身份，F_0=1_A；反向式退化为同一概率，有限夹界两端相等。正负t、h=1、T=s=0、零路径、弱闭端点和原子均保留。

本叶不选择θ、不要求t已中心化，也不输出n/h条件下的相对渐近。它不供应共同二维算子、E4、K/Kv、随机分母或完整E3/OQ4。第一EnergyPathLaw最终门前不实施本叶的边界与当前仅statement性质一致。

## 结论

CORRECT：未发现全实t实际π密度、F_t真可积性、反向归一化方向、有限夹界、零质量、iid环境或n=0/t=0/闭原子范围缺口。可通过E3第二叶声明语义门；证明和最终形式认证仍待后续完成，E3与全部完整根保持OPEN。
