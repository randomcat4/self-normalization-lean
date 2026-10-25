# Unit216：全辅助阈值的实际保留项与负区间项支付

## 1. 精确数学声明与资格边界

取真实布朗运动B及其真实Brownian桥噪声律Q。取均值零、二阶矩一的实际增量律rho，满足|Z|≤Bcap几乎处处，Bcap>0。设n≥1，x≥1/2，Bcap≤√n/(100x)，β=E|Z|³，δ=β/√n，h0=4β²。取任意ν:Path_n×LabelPerm_n→N，使每个标签截面可测且逐点ν(a,σ)≤energyCutoff(a,h0,σ)。这里不要求ν为停止秩，也不要求ν独立于任何后缀。

令F_J为同一Q的eventCompletionKernel，FY_upper/lower为实际halflineDerivative，FY_interval为同一Q的intervalDerivative。对J∈{I,U,D}定义

    L_J(a,σ,r)=sourceRetainedRemainder J F_J FY_J a x ν(a,·) r σ，
    O_I(a,σ,r)=sourceSeparatedOvershoot I FY_I a x ν(a,·) r σ。

定义同一真实revealLaw(rho^n)下的非负账单

    Bill=Σ_{r=0}^{n−1} (|L_I|+max(−O_I,0)+|L_U|+|L_D|)。

存在数值常数C>0使Bill可测、真正可积且E Bill≤Cδ。实际actualDoubleRetained=L_I−L_U−L_D，因而Σ_r|actualDoubleRetained|以及Σ_r actualDoubleRetained也真正可积，并有EΣ_r|actualDoubleRetained|≤Cδ、|EΣ_r actualDoubleRetained|≤Cδ。

这是一份完整数学候选，消费unit214的新范围闭strip和unit215的精确后缀支付。214/215正在独审，并非已经获得服务器资格；所有旧具体producer按v98精确源哈希复用。本稿不声称整个固定阈值比较、正分离overshoot、真实terminal、P_CC或原始C2已经关闭。没有把目标概率预算加为根定理前提。

## 2. 实际状态和两类局部物理producer

在r<n、r<ν、sourceAlive J成立的状态，令

    w=x√Q_n，y=S_r，T=Q_n−Q_r，z=S_n，b=实际下一标签值。

所有和与平方和来自同一重排完整路径，故b²≤T。ν≤κ_h0与r<ν给T≥h0>0。sourceAlive的定义含完整终点在所监测域内部、从0到r的严格生存和Q_n>0；因此相应局部核的正性及内部前提都已付清。若T−b²=0，其余未来坐标全零，精确有y+b=z，这是局部producer的可达零时前提。

对每一符号s，设w_s=w−sy、M_s=|b|+(s(z−y))_+，并令

    Pi_J=Σ_{s∈walls(J)} exp(−((w_s−M_s)_+)²/T)，D=1+|z−y|/√T。

区间实际物理producer采用已验收BridgeIntervalImageResolved.actual_interval_retained_bound。它已从真实布朗桥像核证明，而不是要求本稿假设某个自由核的Taylor性质。其所有前提逐项由上述实际状态满足；通过同一源函数及导数识别可得

    |L_I|+max(−O_I,0)≤KI·(|b|/√T)³ D³ Pi_I，
    KI=2·compensatedProfileConstant+40。

SourceSeparatedOvershoot中的localRetainedRemainder在小能量跨越时使用同一projectionIncrement，未跨越或大能量分支保留实际b；它与IntervalGaussianLocal.retainedRemainder逐分支相同。其localSeparatedOvershoot为−(b−projection)·[1−(b+projection)(z−y)/T]·FY；取负部后恰为IntervalGaussianLocal.negativeOvershoot。跨越定义包含等号；内部y保证不可能同时跨两面墙。源generic区间模块现有完整识别适用于任意x>0，其x≤1仅用于后续Gaussian网格，不用于这些局部等式。这里使用C2实际producer补齐其前提，不重做旧的像核证明。

半线局部producer直接采用已验收SourceActualLocalProfileBudget.actual_halfline_retained_rank_domination，常数KH=8000100。该公开声明只要求x>0、h0>0和逐点cap≤κ_h0，不要求x≤1、x≥16、预算下界或停止性。

为统一写法，G_J(a,r)表示已存在rankGaussianWeight(h0,x,walls(J),false)。它保留同一个真实最终能量wall，严格前缀生存、实际mark及完整后缀。上述两式在活动分支精确转为

    |L_I|+max(−O_I,0)≤KI G_I(reorder(a,σ),r)，
    |L_U|+|L_D|≤KH [G_U+G_D](reorder(a,σ),r)。

在不活动分支原物理值为零，不等式由G非负成立。区间前缀生存是两半线生存的交，而Pi_I为两壁profile的和，故逐点G_I≤G_U+G_D。于是每rank账单≤(KI+KH)(G_U+G_D)。先在这里移除cap，之后才可使用完整路径iid重排；没有声称cap与mark独立。

## 3. 全部可测性和真正可积性先于费用相加

实际eventCompletionKernel、halflineDerivative及intervalDerivative的可测性均有已验收接口。区间导数由实际BridgeIntervalImageResolved.spatial_hasDerivAt提供SourceActualIntervalProfileBudget.actual_interval_kernel_data的真实正则输入；半线则由真实桥反射接口给出。有限前缀条件和可测ν截面，因此L_J、O_I及Bill可测。标签置换群有限且使用离散可测空间，截面可测足以推出联合可测。

fixed_gaussian_weight_measurable_bound对任意x、h0给G的可测性及逐点界

    0≤G_J≤card(walls(J))·(1+√t)³，t=n−r。

它只用实际mark²≤T、|d|≤√(tT)及每个指数≤1；不带x≤1。因而有限n下全部G及总和已被有限常数控制，是真正L1。重排函数可测，iid随机完整置换后仍是原始rho^n；对其推前保持真正可积性及积分。物理账单随后由前一节逐点支配得到真正L1，而不是由希望成立的E Bill值反推可积性。

有些原始状态Q_n=0时sourceAlive为假，且h0>0使κ_h0=0，故ν=0；物理值和G均为零。所有分母在选中的T≥h0上才使用。闭原子和零能量没有被删除为“几乎必然不发生”。

## 4. 早rank费用

r<n/2时t=n−r>n/2。两半线profile各≤1，生存指示≤1，因此

    G_U+G_D≤2·1_{T≥h0}|b|³T^(−3/2)D³。

完整iid重排和实际后缀投影将每rank积分运输到rho^t下首个真实mark。Unit215早网格给总积分≤4CEδ，所以此范围的EΣ(G_U+G_D)≤8CEδ。r=0含在这里；n偶数时r=n/2不在此范围，避免中点重复。

## 5. 晚rank：真实闭条带的layer-cake推导

令n≤2r且r<n，固定完整实际后缀u，长度t=n−r≥1，T=energy(u)、d=sum(u)、b=firstValue(u)。若T<h0则G为零。否则T>0，b²≤T，令M=|b|+|d|≤√T D。

对任一实际监测符号s，半线前缀生存A_s使w_s=x√(T+Q_r)−sS_r>0，并且M_s≤M。因此其profile≤exp(−((w_s−M)_+)²/T)。对任意w_s>0，精确有

    exp(−((w_s−M)_+)²/T)
      =∫_{z≥0} (2z/T) exp(−z²/T)·1_{w_s≤M+z} dz。

当w_s≤M时积分为1，否则下端点为w_s−M；闭/严格积分端点不改变实参数Lebesgue积分，所以离散前缀原子没有造成误差。

固定后缀后的前r坐标仍是原始rho^r；不将真实wall视为停止边界。A_s且w_s≤v蕴含同一真能量的闭条带事件

    maxWithZero(s•prefix)≤wall，wall−v≤sS_r≤wall。

Unit214的新真实闭strip适用于同一rho、全样本参数n、x≥1/2、晚rankr、q=T和v≥0，故其概率≤CS(v+β)²/r。这里q来自完整固定后缀，不重抽或平均替代。

所有layer-cake函数非负可测，Tonelli合法；第三节还已给整体L1，所以后续普通Fubini也有正当性。积分密度k_T(z)=(2z/T)e^(−z²/T)满足∫_0∞k_T=1、∫_0∞z²k_T=T，均由u=z²/T直接换元。用(M+z+β)²≤4M²+4β²+2z²，得

    E_prefix[1_{A_s}profile_s]
      ≤CS(4M²+4β²+2T)/r
      ≤6CS D²(T+β²)/r。

最后一步用M²≤TD²、D≥1。两个符号相加给12CS D²(T+β²)/r。乘上原始mark³T^(−3/2)D³即得

    E_prefix[G_U+G_D]
      ≤12CS·1_{T≥h0}|b|³T^(−3/2)D^5·(T/r+β²/r)。

符号−1使用Unit214在实际−rho推前下的结论，未将rho与−rho认作同一律。profile中的(s d)_+被保守增大为|d|，因而两符号均正确。

## 6. 真正后缀费用和整笔账单

晚rank与整数t∈[1,⌊n/2⌋]一一对应，r=n−t。在Unit215中，支撑已证明rho在√r尺度无截断：R_r=β/√r、h=h0、R0=δ。因此刚得到的晚费用精确由其p=5网格支付，总积分≤12CS CLδ。该网格的真实mark平均在其余所有后缀因子对全部标签对称之后进行；没有对未来部分抽样或条件ν制造独立性。

合并两个rank范围、物理逐点支配和完整路径推前，得到

    E Bill≤(KI+KH)(8CE+12CS CL)δ≤Cδ，
    C=1+(KI+KH)(8CE+12CS CL)>0。

所有常数由已固定的布朗桥核常数和统一strip/网格常数构成，先于rho、n、x选择。这个证明没有δ的小量前提或指数下界，因而覆盖固定阈值段所需的任意小预算。

actualDoubleRetained的透明定义是I−U−D。逐项三角不等式给Σ|actualDoubleRetained|≤Bill；所需可测性和真正L1继承自Bill。有限和范数及Bochner积分范数不等式给最后两项绝对/有符号支付。没有把它误写成U+D−I，也不把这个局部绝对估计当作原始doubleCrossing比较。

## 7. 已关闭的数学消费范围和下一承重依赖

若214/215的独立审阅成立，本完整推导提供全辅助阈值x≥1/2下实际I/U/D保留项和负区间overshoot的Cδ数学账单。正式接受还需实现新精确声明、独立完整实际TYPE/FULLVALUE覆盖和服务器内核/递归公理证据；当前没有新Lean源码或执行。

正分离overshoot总账、h0截止处的真实terminal误差、初始完成与固定段比较仍需分别接合。已有原始scalar/interval initial接口可按精确作用域复用，不能把Root大阈值自适应terminal或residual预算无条件套到这里。完整P_CC还要将这个固定段与已验收nonresidual及新的actual residual组合，所有预算必须来自其自己的实际辅助律。

研究根C2/C12仍OPEN；Root共享原始律桥保持其独占范围。本文的意义是完成真实物理量到现有支付的数学连接，而不新造ordinary网格或复制既有布朗桥导数证明。
