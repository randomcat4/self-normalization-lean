# OQ4 E3 联合极限薄叶：固定原律、同一中心参数与零质量安全的相对传递 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E3_STATUS: OPEN
ROOT_STATUS: OPEN

来源为固定 oq4/energy01.md 第71–83行式(7)–(8)，并使用第7–24、47–58行共同常数与矩条件；sourcecommit35d4580b61e22e7145f47730045a09874ef93259，文档SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。只读intake translation/energy-joint-transport-intake-v1.md 不是本冻结的认证。

拟新 Shao/OQ4/EnergyJointTransport.lean。唯一新承重内容是将既有有限共同乘法路径界接成真实联合极限。必须使用真实 energyTiltedLaw、energyLinearTiltLaw、energyNormalizer、energyLinearNormalizer、energyPathIntegrand、Measure.pi 与 Shao.closedStrip，禁止替换成任意抽象概率数或假设密度。EnergyRelativePathBounds 完成作者、独立、负责人最终门禁前，不启动本叶作者证明或实现；当前只开来源语义门。

## 固定输入与对象

固定 M,T≥0，C=energyE2Constant M T、H=energyE2Threshold M T、P=energyE1Constant T。随后固定一个实 Borel 概率律 ν，原平方及绝对三次方真正可积，原均值∫x dν=0、原点二阶矩∫x²dν=1、β=∫|x|³dν≤M。所有序号 j 使用同一个 ν；倾斜律可随 j 改变，不能把原律默换为任意三角阵。

对任意 h,s:ℕ→ℝ，前提仅为 Tendsto h atTop atTop 和 ∀j,|s j|≤T。h 的早期值允许小于 H、为零或负；共同有效尾部 H≤h j 必须从 h→∞ 内部导出，不得新加对所有 j 的高度阈值。

存在同一个 θ:ℕ→ℝ，且在 ∀长度序列 n:ℕ→ℕ 之前选择，使最终对 j 有

energyE2Conclusion ν M T (h j) (s j) (θ j) ∧
∀m:ℕ, energyRelativePathConclusion ν M T (h j) (s j) (θ j) m。

θ j 只按 ν,M,T,h j,s j 选取，不观察任何 m 或后续长度序列 n；不要求唯一、可测或连续的选择。阈值之前可以约定 θ j=0，不在无效早期声称归一化律为概率或对数有真实归一化意义。全部真正概率性、归一化正性、三种矩可积性、精确中心化及有限路径可积性由既有接口在共同尾部内部供应。

对任意长度序列 n:ℕ→ℕ，仅再假设 Tendsto (fun j => (n j:ℝ)/(h j)^3) atTop (𝓝 0)。不加 n→∞ 或 n/h²→∞。

记 μ_j=energyTiltedLaw ν (h j) (s j)，μθ_j=energyLinearTiltLaw ν (h j) (s j) (θ j)，Z_j=energyNormalizer ν (h j) (s j)，L_j=energyLinearNormalizer ν (h j) (s j) (θ j)。令 Π_j(λ)=Measure.pi(fun _ : Fin(n j) => λ)，A_j=Shao.closedStrip(n:=n j)(h j)，

p_j=(Π_j(μ_j)).real A_j，r_j=(Π_j(μθ_j)).real A_j，

I_j=∫a, energyPathIntegrand (h j) (s j) a ∂Π_j(ν)。

所有这些均为真实定义；I_j 是原 ν 的能量加权积分，不能当成 s≠0 时原 ν 的无权生存概率。有限误差沿用透明定义

e₂_j=energyRelativePathError2 M T (n j) (h j)=C/(h j)+C*(n j:ℝ)/(h j)^4，
e_j=energyRelativePathError M T (n j) (h j)=P*M*(n j:ℝ)/(h j)^3+e₂_j，
δ₂_j=exp(e₂_j)−1，δ_j=exp(e_j)−1。

## 冻结结论

同一 θ 序列对全部上述 n 序列同时给出：

1. 真正确定性的联合极限 e₂_j→0、e_j→0、δ₂_j→0、δ_j→0，指数两端 exp(±e₂_j)→1 和 exp(±e_j)→1。误差和 δ 在共同有效尾部非负，不能把早期负高度值的符号当作前提。

2. 最终对 j，I_j integrable 的实际被积函数可积，有限界

exp(−e₂_j)*r_j≤p_j≤exp(e₂_j)*r_j，
exp(−e_j)*r_j≤I_j≤exp(e_j)*r_j，

并给出零质量安全的真正相对误差

|p_j−r_j|≤δ₂_j*r_j，|I_j−r_j|≤δ_j*r_j。

因此对每个 η>0，最终 |p_j−r_j|≤η*r_j 且 |I_j−r_j|≤η*r_j；也可以另外返回等价的 exp(±η) 乘法夹逼。误差尺度必须保留 r_j，不能仅返回绝对差趋零。若 r_j=0，上述界直接强制 p_j=I_j=0；没有任何除以生存概率的步骤，也不声称无条件比值→1。

3. 原文第83行的归一化和终点支付应作为同一 θ 的明确推论返回：

(n j:ℝ)*log L_j→0，|θ j|*(h j)→0，L_j^(n j)→1，
(n j:ℝ)*(log Z_j−(s j)/(h j)^2)→0，
exp(−(s j)*(n j:ℝ)/(h j)^2)*Z_j^(n j)→1。

L_j、Z_j 在有效尾部的真正正性必须由既有实际 law 接口推出；不得由 Lean 对非正数 totalized log 的值伪造幂与指数恒等式。阈值前所有实值表达式只是有限前段扩展，不影响极限，不供应真实概率声明。能量归一化误差仍由 E1 的 P*β*n/h³ 与 β≤M 支付，不在有限 j 把因子设为1。

4. 提供对真实 iid 实现的转接：在每个 j，原 ν、μ_j、同一 μθ_j 的有限 iid 样本可位于三个不同概率空间；仅要求各自可测、iIndepFun、逐坐标 IdentDistrib 为指定实际边缘。由现有有限 samplePath-map/integral 等式，将 p_j,r_j,I_j 精确替换为实际样本事件概率及原 ν 下样本能量积分，传递同一相对误差界。θ 不能因选择样本或长度而改变，不增加跨 j、跨空间独立或耦合条件。可采用单独的逐 j 等式转接辅助定理与联合极限总入口组合，不重新证明共同概率基础。

允许把确定性极限、尾部选择、任意满足 E2 的 θ 辅助结论和 iid 转接拆成必要公开引理，但最终存在型总入口必须内部选择 θ，保留先 θ 后所有 n 的量词与全部实际对象。公开定理数以后由实际源码测量，不把定义或条目数当作新增原始义务。

## 边界与开放范围

n j 可以恒零、取有界值或任意变化；h j 早期零/负/阈值下、s=0、T=0、弱闭端点原子、全零路径及零生存概率均保留。M<1 的分布类可空，不添加 M≥1。s=0 时 μ_j 仍是实际截断再归一化律，不先删除 Z_j 幂。始终使用同一个绝对部分和 closedStrip 事件，不以累计均值漂移移动边界。不要求原 ν 有界支持、指数矩、四阶矩、密度、对称或非格点。

本叶只关闭式(7)–(8)在上述联合尺度的标量相对传递，不关闭式(9)–(10)共享双变量算子/微分共轭、killed 边界误差、反射账本、K/Kv、条件能量 E4、随机分母或完整 E3/OQ4 根；不把 E4 的最终正性和 n/h²→∞ 倒灌进来。

全部 Lean/重计算仅指定服务器；作者唯一 emit，独立 target no-o 与完整原 source 全部 getModuleIdxFor?=none 无名称/namespace过滤，独立 actual-import 全部已冻结 OQ4 共存及模块所有权/命名空间并集公理审计，负责人 import-only 复核。禁 sorry/admit/new axiom/unsafe/native_decide，标准三公理白名单不变。冻结后不得静默改前提、共同常数、事件、原律或量词；canonical 窗口另由负责人释放。
