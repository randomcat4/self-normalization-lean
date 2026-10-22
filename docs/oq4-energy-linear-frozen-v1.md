# OQ4 E2 首叶：实际线性倾斜 law 与有限积分族冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
E2_STATUS: OPEN
ROOT_STATUS: OPEN

源为固定 shao@35d4580b61e22e7145f47730045a09874ef93259 的 oq4/energy01.md E2 式(5)及第61–62行的实际指数族对象；源SHA2562e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。拟新 Shao/OQ4/EnergyLinearTiltLaw.lean，仅绑定已冻结 EnergyTiltedLaw 的真实 law，不建立/修改公共泛化，不改任何旧源。

## 对象与前提

ν为ℝ上Borel概率测度，x²、|x|³真正ν可积，∫x²dν=1。T≥0、h≥1、|s|≤T，令 μ=energyTiltedLaw ν h s，必须使用N1真实定义、概率性及μ-a.e.闭支持|x|≤2h。首叶不要求原中心、M、K、未知θ或方差下界；如果中间结论可省略不需的三阶条件，其加强必须仍覆盖本域，不得引入新分布条件。

对全部实t定义真实积分族及测度（law/积分族定义不含T、M、K）：

L(t)=∫exp(t*x)dμ，
A1(t)=∫x*exp(t*x)dμ，A2(t)=∫x²*exp(t*x)dμ，B3(t)=∫|x|³*exp(t*x)dμ，
dμ_t=L(t)⁻¹ exp(t*x)dμ，m(t)=A1(t)/L(t)。

建议名 energyLinearNormalizer、energyLinearFirstNumerator、energyLinearSecondNumerator、energyLinearThirdNumerator、energyLinearTiltLaw、energyLinearMean。μ_t必须是实际非负密度测度；只能重用实际μ，不得改成任意具有所需矩的新抽象law。t可正可负，没有小参数限制。

## 冻结结论

1. 对每个实t，exp(tx)、x exp(tx)、x² exp(tx)、|x|³ exp(tx)真正μ可积；L,A1,A2,B3为这些真实积分。所有可积性由同一μ的闭支持内部供应，不能要求原ν具有任何指数矩，不能将μ-a.e.有界性误写为全实轴逐点有界性。
2. 证明显式归一化界
   exp(-2*h*|t|)≤L(t)≤exp(2*h*|t|)，从而L(t)>0；所需μ概率和支持由N1内部供，不将L正性或这些界列为新输入。
3. 真实μ_t为概率测度，且μ_t-a.e.|x|≤2h。
4. 对每个Borel集A，μ_t.real A=(∫_A exp(tx)dμ)/L(t)。对每个Borel实函数f，若x↦f(x)exp(tx)真正μ可积，则f真正μ_t可积且∫f dμ_t=(∫f exp(tx)dμ)/L(t)。不用不可积实积分的默认值，不要求泛化到任意不可积f或联合参数kernel。
5. 真实id、x²、|x|³对μ_t可积，并分别给出∫x dμ_t=A1/L=m(t)、∫x²dμ_t=A2/L、∫|x|³dμ_t=B3/L，调用第1项的实际加权可积性。
6. t=0时L(0)=1、μ_0=μ（真实测度等式），m(0)=∫x dμ。后者一般不为零，首叶不得声称中心化；s=0时μ仍是纯截断归一化law，一般不等于原ν。

所有结论沿同一ν,h,s及实际μ量化；没有原ν有界支撑、密度、对称、非格点、无原子、全局第四矩或线性/二次指数矩前提。保留h=1、T=0、s=0、t=0、正负t、零点及±2h的全部原子。

## 后置范围与认证

本叶子不证明L/A1/m/logL的参数导数，不给共同方差区间、端点异号、θ存在、精确均值零或选定θ处的h⁻⁴ logL和最终矩界。不将首叶概率/支持误当作方差正下界。E2/E3/E4、K/Kv、随机分母与完整OQ4仍OPEN；E1已有本线验证但main整合待root。

作者不得改前提；先匿名数学proof冻结后API实施，声明语义门通过后才server。所有Lean仅指定server、作者唯一emit新目标olean、27旧OQ4+source body及最终28实际共同import、按所有owner新声明审计；独立无-o/完整source全部getModuleIdxFor?none与父全模块owner/公理门。禁sorry/admit/newaxiom/unsafe/native_decide，仅允许标准三公理。
