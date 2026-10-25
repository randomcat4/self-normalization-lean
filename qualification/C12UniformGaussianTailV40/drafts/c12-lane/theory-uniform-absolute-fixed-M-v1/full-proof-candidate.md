# Unit220：统一绝对误差与任意固定上阈值的精确装配

本文是已先行冻结的新数学范围候选，作者为C12主实例。它复用已完成独立数学审阅的216、217及218实际装配，只证明取消固定16的两个承重步骤：一个统一的正态尾多项式界，及随后固定M的常数量词。它尚未独审、尚无本单元Lean或公理资格。既有219固定16形式声明、旧源码、审查和服务器回执全部保持原样。

## 1. 命题与量词

固定支撑系数eta=1/100。存在同一个数值epsilon>0、epsilon<=1/8，以及数值CA,KD>0，先于所有概率律、n、x和实际布朗运动选择，使下述结论成立。rho为实际中心化单位方差概率律，|Z|<=B且0<B<=sqrt(n)/(100x)，n>0、x>=1/2，beta=E|Z|^3、delta=beta/sqrt(n)，delta*x^3<=epsilon。令A为实际完整平方和wall下的正时间弱绝对最大值事件，D为同一路径的两面弱命中交事件；令A_B、D_B为实际Brownian对应事件，两面命中时间可不同，不固定先后次序。则

    |P(A)-P_B(A_B)|<=CA*delta,
    |P(D)-P_B(D_B)|<=KD*delta.

没有x的上界，没有预算正下界，没有残差/非残差条件，没有对称性、密度或非格点假设。进一步，对每一个先固定的实数M>=1/2，选出只依赖M的CF(M)>0，在选择rho、n、x、Brownian律之前，使同一epsilon与同一CA对1/2<=x<=M给出

    |P(D)-P_B(D_B)|<=CF(M)*delta*(1+x)^3*Psi(x).

实际归一化律为map(z |-> z/sqrt(n))rho，结论仍包括它自己的精确R0=delta、Rx=delta*(1+x)^3。绝对结论统一于所有x，带Psi的相对结论只对每个预先固定的M断言；不宣称CF对所有M统一。

## 2. 统一的多项式正态尾界

令c=(sqrt(2*pi))^(-1)>0，Kpsi=1+16*c/3。已验收GaussianTail.standardNormal_mills_bounds对x>=0给

    Psi(x)<=(4/3)*phi(x)/(1+x),
    phi(x)=c*exp(-x^2/2).

因1+x>0，可乘得

    (1+x)^3*Psi(x)<=(4/3)*c*(1+x)^2*exp(-x^2/2).

由(x-1)^2>=0，(1+x)^2<=2*(1+x^2)。设t=x^2/2>=0。实指数的基本凸性界exp(t)>=1+t给

    (1+x^2)*exp(-x^2/2)=(1+2*t)*exp(-t)
      <=2*(1+t)*exp(-t)<=2.

上式只乘正数；exp(-t)*exp(t)=1。因此(1+x)^2*exp(-x^2/2)<=4，进而

    0< (1+x)^3*Psi(x) <=16*c/3 < Kpsi.

严格正性使用字面Gaussian右尾在每个有限x处严格正。这里没有假定某个未提供的四阶矩接口，也没有取一个依赖x的隐式上确界。

## 3. 自己的预算与全阈值C1绝对界

从已验收original_one_sided_relative_error_iid选择数值rhoStar>0、rhoStar<=1/16、C1>0，取epsilon=min(rhoStar/27,1/8)。这个选择完全不依赖M。

对所有x>=1/2，(1+x)/x<=3，且(1+x)B/sqrt(n)<=3/100<1。真实truncationF从未截断，故当前rho的归一化律精确有R0=delta、Rx=delta*(1+x)^3、h0=4*n*R0^2=4*beta^2。它们是积分恒等式，不是移用另一个原始律的预算域。所有所需可积矩从有界支撑得到；单位方差导出beta>=1、B>=1、delta>0及n>=2500。

Rx<=27*delta*x^3<=rhoStar，故p=3的真实C1适用分支成立。对实际同一产品律和符号s=1或-1，完整合法C1给

    |P(U_s)-2*Psi(x)|<=C1*delta*(1+x)^3*Psi(x)
      <=K1*delta,  K1=C1*Kpsi>0.

这一步取代218中唯一依赖x<=16的K1=C1*17^3/2。两个符号来自C1明确s参数，不把rho等同于反射律。delta<=8*epsilon<=1，因此delta^2<=delta。

## 4. 精确复用的实际支付及全阈值绝对装配

216已独立完整数学审阅的结论对所有x>=1/2、上述有界中心化rho及任何实际可测cap<=kappa_h0给同一个实际I/U/D保留项绝对值及负区间overshoot账单，预算KB*delta，KB为先于rho、x的数值。217已独立完整数学审阅的结论在相同全阈值范围给每个实际域在真实h0截止以后的全部future supremum费用KT*delta^2。其真实全后缀、closed strip端点、实际最终能量wall、2/32U走廊、boundedPhi停止积分与genuine L1均保持，不产生新的生产者假设。

218第三节通过实际closed-CDF、显式g_x层积分、Gaussian反射和真实零能量概率给出的初始完成界本就对任意x>0成立：

    |E V0^s-(1-2*Psi(x))|<=(KS+16)*delta.

原halfline初始完成在Q=0时为0，弱命中在Q=0时成立，严格存活失败，恰好支付所列16*delta；该原子不能丢弃。故同一实际半线终值与初始完成的host gap为KG*delta，其中KG=K1+KS+16，现在KG也独立于x的上界。

选择同一个nu=kappa_h0。energy_cutoff_data提供真实固定完整路径下的标签揭示停止性及cap条件；不是自然iid最终能量wall停止性。实际Brownian核、FY导数、统一导数界与source_parts_measurable_integrable提供所有真实可测性和genuine L1。所有这些完整前提、来源与接口，在218第四节独立审阅中已覆盖，均未使用x<=16。此处只用新的KG值。

精确消费source_three_domain_overshoot_transfer与mask=1，仍得

    |P(A_n^I)-E V0^I| <= (3*KB+3*KT+2*KG)*delta,

因为terminal费用KT*delta^2<=KT*delta。已验收original_iid_actual_interval_initial_cdf_budget对任意x>=0给|E V0^I-P_B(strict interval survival)|<=KI0*delta。取字面补集，得到冻结第一结论，令

    CA=3*KB+3*KT+2*KG+KI0>0.

这只是给全阈值一致的绝对误差，未由绝对界推导无界x上的Psi相对误差。旧区间初始、actual IID/revealLaw重排、全rank账单及strict/weak等号分配均照旧，不重证也不改写旧qualified producer。

实际U_+并U_-恰为A，交恰为D；Brownian有同样容斥，两个一壁概率都是2Psi(x)。因此

    |P(D)-P_B(D_B)|<=2*K1*delta+CA*delta=KD*delta,
    KD=2*K1+CA>0.

对于实际Q=0，n>0保证正时间也有0>=x*sqrt(Q)，两个单壁及绝对最大值都弱命中；严格存活全失败。容斥恒等式包含这些样本而无需概率零论证。Brownian正阈值下的两壁时间可以分别选择。这关闭全阈值绝对命题的全部新范围。

## 5. 任意预先固定M的相对比较

固定任意有限实数M>=1/2，再选择CF(M)=1+KD/Psi(M)>0。Psi(M)>0保证这是有限数值；CF在rho、n、x、Brownian律之前选择，epsilon、CA、KD及所有生产者常数则已经在M之前固定。

对1/2<=x<=M，字面右尾单调性给Psi(x)>=Psi(M)>0，且(1+x)^3>=1。故

    KD*delta <= (KD/Psi(M))*delta*(1+x)^3*Psi(x)
      <=CF(M)*delta*(1+x)^3*Psi(x).

结合第四节即得冻结第二命题，以及同一个CA的绝对最大值界和第三节精确预算身份。M=16时恢复218范围；任何今后由Root固定的大阈值X0>=1/2，都可以先代M=X0再选择该固定段比较常数，不再要求证明X0<=16。

## 6. 资格与承重边界

这项扩展直接对接原文d:fixed的“绝对比较加固定X0转换”承重位置。它允许主证明的X0在大阈值指数常数选定后取值，同时保留epsilon在X0之前的量词。Root的大阈值带记录权重条带/实际正overshoot支付仍独占且未被本绝对界替代；全参数C2/C12仍OPEN。

新的取消16和固定M量词尚需独立完整数学范围审阅；可以精确复用216/217/218已审覆盖，并完整审阅本稿全部新论证。既有219的冻结声明没有变化，也未授权其实现optionalM。本文没有新Lean源文件、没有本单元服务器检查或公理审计；214/其他源码的旧成功不能充作220形式资格。
