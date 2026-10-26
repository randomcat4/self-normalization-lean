# Unit217：实际h0截止处的全阈值terminal包络

## 1. 精确声明

取实际布朗运动的桥噪声律Q。取rho为均值零、二阶矩一的增量概率律，|Z|≤Bcap几乎处处，Bcap>0。固定n≥1、x≥1/2、Bcap≤√n/(100x)，β=E|Z|³，δ=β/√n，H=h0=4β²。令P=rho^n，κ=energyCutoff(a,H,id)。对任意实际监测域I（upper/lower/interval）令

    F=eventCompletionKernel I Q，
    terminal(a)=1_{sourceAlive I a x n id}，
    Dκ(a)=max_{κ(a)≤j≤n}|sourceValue I F a x j id−terminal(a)|。

存在数值常数C>0，使Dκ可测、真正可积、0≤Dκ≤1，且E_P Dκ≤Cδ²。相同结论在实际revealLaw(P)下对每个路径自己的κ(a,σ)、sourceValue(...,σ)和terminal成立。

本文取C=30000CS+100，CS为unit214新真实闭strip常数。unit214/215仍处数学独审/后续kernel资格阶段；本文是一份明确消费这些接口的完整数学候选，不宣称已得到Lean资格或完整P_CC。特别不调用只对x≥16残差成立的Root自适应大H terminal。

## 2. 真实几何、可测性和大δ分支

β有限、β≥1、Bcap≥1来自同一rho的有界支撑及单位方差。支撑尺度给10000x²Bcap²≤n，故n≥2500，特别n≥4。Unit215已证明同一rho的实际完整截断预算R0=δ，源通用截止h=4nR0²=H。

κ是0,…,n内首次真实剩余能量严格小于H的秩。有限个实际二次多项式的严格比较使κ可测，κ≤n保证最大值的有限集合非空。实际源核、alive有限前缀事件可测，故Dκ可测；真实源值及terminal均在[0,1]内，故Dκ≤1，先获得真正L1。

若δ≥1/2，直接有E Dκ≤1≤4δ²≤Cδ²。后面只处理δ<1/2，因此可消费通用backward raw producer要求的R0≤1/2。没有把大δ或小n隐含删掉；给定本声明的支撑与方差已经排除n<2500。

## 3. 复用实际反向停止数据

精确调用v98已验收SourceTerminalEnvelope.actual_backward_terminal_raw_data，参数为rho、n≥4、sigmaSq=1、R0=δ、H=h及m=0。其raw生产者没有阈值x前提。

设L=⌊n/2⌋，NH为从最后坐标反向累计实际平方和首次达到H的秩，未达到时取L；N=max(0,NH)=NH，r=n−N。定义

    U=Q_n−Q_r，J=max_{0≤ell≤N}|S_{r+ell}−S_r|，
    Ebad={最后L坐标的实际平方和<H}。

producer给出所有这些量的可测性、U及J²的真正可积性，1≤N≤L，r≥n/2，以及

    E N≤7H，E U=E N≤7H，E J²≤16 E N≤112H，
    P(Ebad)≤12H/n。

在Ebad之外，κ=r+1；这里m=0且NH≥1，故raw头中的if NH≤m分支不发生。首次正向剩余能量严格低于H与反向首次达到H的对应保留平方和等于H的情况，未把等号改掉。

因此逐点有

    Dκ≤1_{Ebad}+D_r，
    D_r=max_{r≤j≤n}|sourceValue_j−terminal|。

Ebad外来自[κ,n]⊆[r,n]；Ebad内来自Dκ≤1、D_r≥0。没有要求r是正向停止秩。

## 4. 实际pointwise corridor：使用已验收的真实常数

精确调用已验收actual_source_terminal_corridor_envelope，其前提对所有x≥0成立。该实际producer给D_r≤1，U=0时D_r=0；U>0时给

    D_r≤1_{sourceAlive at r} Σ_{s∈walls(I)}
       [1_{0<w_s≤2J}+2exp(−w_s²/(32U))·1_{w_s>2J}]，
    w_s=x√Q_n−sS_r。

这里刻意保留真实源中的系数2和分母32U；不使用论文中更紧的分母2U。所有后续常数按这个较松但已验收的包络重算。

这个逐点结论保持源核在所有j上的actual future completions、同一最终平方和wall与实际terminalIndicator；未用独立布朗运动替换任何原始坐标。U=0与Q_n=0时无需除法。

## 5. 对完整停止后缀的合法条件积分

N是反向平方和的有限停止秩。精确调用已验收actual_backward_stopped_suffix_integral，参数m=0。对每个t≤L，事件N=t由完整最后t坐标决定，其selectedSuffix条件包含首次达到H的严格/闭边界。它提供的是对每个可测、有界Phi的实际积分恒等式；并不声称任意随机条件事件都保持前缀iid。

取Phi_t(v,b)为拼接实际前缀v∈Path_(n−t)、完整后缀b∈Path_t之后，从确定r=n−t到n的上述实际D_r。它可测且|Phi_t|≤1，所以接口的所有条件满足。固定b后U=energy(b)、J为该后缀的正向最大绝对部分和，均不随前缀v变化。条件前缀正好是原始rho^(n−t)。

selectedSuffix指标在前缀积分之外保留。对U=0，Phi_t=0。对U>0，下一节在每个实际固定b下估计前缀积分。最后用该精确停止后缀恒等式相加，而不把随机N当成独立样本长度。

## 6. 闭条带支付两部分包络

固定完整后缀，r=n−t≥n/2，q=U。对任一实际监测符号s，alive前缀加0<w_s≤v包含在unit214的真实闭条带事件内，因而

    P_prefix(alive,0<w_s≤v)≤CS(v+β)²/r，v≥0。

只要求该符号的一面生存即可；区间alive更强。unit214的参数正是本声明的n,x,r,q和同一个rho，支持及单位方差前提无需改变。即使固定后缀的能量随机性决定N，source积分恒等式已先把它合法固定。

近走廊部分因此≤CS(2J+β)²/r≤CS(8J²+2β²)/r。

对远部分先删除w_s>2J的非负指示。对w>0，

    exp(−w²/(32U))=∫_{v≥0}[v/(16U)]exp(−v²/(32U))1_{w≤v}dv。

该非负密度的总质量是1，二阶矩为32U。Tonelli及闭条带给

    2 E_prefix[1_alive exp(−w_s²/(32U))]
      ≤(2CS/r)∫density(v)(v+β)²dv
      ≤CS(128U+4β²)/r。

两个部分相加，每个符号的费用≤CS(8J²+128U+6β²)/r≤CS(8J²+128U+2H)/r。最多两面墙，r≥n/2，得到

    ∫Phi_t(v,b)dP_r(v)≤(4CS/n)(8J_b²+128U_b+2H)。

闭条带保留等号；layer-cake参数使用Lebesgue积分，所以原子阈值不产生漏项。负号只使用真实−rho推前对应，不假设rho对称。

## 7. 总费用、常数和真实重排版本

应用第五节停止后缀积分恒等式，乘selectedSuffix后对t求和。N=t是实际不交划分，U_b、J_b正是第三节的实际U、J。因此

    E D_r≤(4CS/n)(8 E J²+128 E U+2H)
           ≤(4CS/n)(896H+896H+2H)
           =7176CS H/n。

加异常事件，E Dκ≤(7176CS+12)H/n=(28704CS+48)δ²。它被Cδ²控制，C=30000CS+100同时覆盖第二节的大δ分支。常数只依赖统一CS，在law、n、x之前固定。

由完整iid坐标重排不变性，实际(a,σ)在revealLaw下的整条重排路径仍有P的分布。能量、sourceValue、terminal与该路径自己的energyCutoff逐点运输为identity-order的相同对象，所以Meas/L1及同一个积分结论精确运输到revealLaw；未把κ替换为平均秩。

这给出任意I在κ_h0处的整个未来supremum误差，尤其包含单个|sourceValue_κ−terminal|。原始paper d:OW所需E=Cδ²正由这一精确范围提供，但仍待214/215及本消费证明的独立/形式资格。正分离overshoot、初始完成和fixedcentered装配仍须逐项接合，C2/C12保持OPEN。没有执行Lean、AX、上传或服务器计算，也没有改动Root的共享Probability模块。
