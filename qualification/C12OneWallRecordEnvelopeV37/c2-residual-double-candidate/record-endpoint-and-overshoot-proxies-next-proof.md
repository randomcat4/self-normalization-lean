# 连续下一概率依赖：actual record endpoint tails与三类overshoot proxies

本稿继续原supp5353–5429、5500–5595的实际概率链，0formal/Lean/AX，不改原19文件/两公开候选。
物理gradient ratio由A负责；本稿只闭合真实iid非负proxies，绝不将目标overshoot概率/积分当新前提。

## 1. 实际bounded raw law的任意参数Bennett尾

rho为实概率，EX=0、EX²=1、AE |X|≤B，beta=E|X|³≥1，B≥1。
对任意lambda≥0，实际指数级数逐项用|X|≤B，得到

  log Eexp(lambda X)≤(exp(lambda B)−1−lambda B)/B²。

原矩都可积且指数在support上有界，故逐项/极限交换可由有界收敛支付；
也可直接用exp二阶Taylor的积分余项在[-B,B]比较，得到同一个点态二次上界。
真实有限product的指数最大界在lambda=B^(−1)log(1+Bh/N)给，对N≥1、h≥0，

  P(max_{k≤N}S_k≥h)≤T_N(h)，
  T_N(h)=exp(−h/(2B)log(1+Bh/N))。                              (BT)

这里(1+t)log(1+t)−t≥(t/2)log(1+t)由对差求导及t=0证明。
没有theta B小量条件；这是处理实际很早crossing所需的合法广参数尾，非新HasLaw假设。

## 2. 普通record矩及其actual endpoint tail

D_N=(S_N−max_{0≤k<N}S_k)_+。已有准确cycle identity给
E D_N=E S_N^+/N≤1/sqrt(N)。固定最后增量b>0并reverse前N−1块，
record要求closed survival≥−b，D_N≤b。消费已qualified Strip ordinary survival，
E D_N²≤C E[b_+²(b_++beta)]/sqrt(N)≤Cbeta/sqrt(N)，N≥2；
N=1直接E D_1²≤1≤beta。于是

  E(D_N²+beta D_N)≤Cbeta/sqrt(N)。                              (RM0)

对h≥max(8B,sqrt(N))，进一步有

  E[(D_N²+beta D_N);S_N≥h]
   ≤Cbeta/sqrt(N) exp(−h/(8B)log(1+Bh/N))。                     (RMT)

平方项：给定最后b>0（b≤B≤h/8），reverse前块必须survive≥−b且terminal至少h−b≥7h/8。
其首次hit h/4处至多h/4+B≤3h/8，所以余段必须再上升至少h/2。
前一weighted-survival稿已从实际ordinary survival支付固定level hit概率≤C(b+beta)/h；
随后真实独立余段的有限最大尾由(BT)给≤T_N(h/2)，统一覆盖全部remaining lengths≤N。
所以E[D_N²;S_N≥h]≤Cbeta/h T_N(h/2)。
h≥sqrt(N)，且log(1+t/2)≥.5log(1+t)，给(RMT)平方项。
一阶项只用实际rotation-invariant endpoint mark：
E[beta D_N;S_N≥h]=(beta/N)E[S_N^+;S_N≥h]≤beta/sqrt(N)T_N(h)^(1/2)，
比所需尾更强。N=1的tail为空，因为h≥8B而|X|≤B。

## 3. 实际closed record-strip的概率与endpoint尾

固定全长度n>0、x≥1、j≤n、suffix能量U≥0，
F_j=S_j−x sqrt(max(Q_j+U,n/2))。假设xB/sqrt(n)≤eta0=1/200。
其平方坐标clip到[-B,B]而linear sum不clip的全局延拓，各单坐标斜率[1/2,3/2]。
在任意给定补块后，长度k>0第一块的closed interval宽v浓度≤C(v+beta)/sqrt(k)：
直接消费iid_strong_monotonicity_concentration，对真实normalized map X/sqrt(k)，
H(z)=2F_ext(sqrt(k)z)/sqrt(k)满足H更新减coordinate全局monotone；
旧头的2*interval length+80R与R≤beta/sqrt(k)逐字给此实际估计。

j≥2时拆两个长度k,l≈j/2的真实相邻块，D_j≤D_l(Bblock)。固定末块，first-block interval
宽为D_l，(RM0)于是给

  E[D_j;0≤F_j≤D_j]≤Cbeta/j。                                   (RS)

若j≥12、A≥max(24B,3sqrt(j))，三个连续块A1,A2,B0的长度均在[j/4,j/2]。
S_j≥A必有一个block sum≥A/3。若rare在A1，给定A1、B0后浓集A2，
成本≤C/sqrt(|A2|) E(D_B0²+beta D_B0)P(S_A1≥A/3)
≤Cbeta/j T_|A1|(A/3)。交换A1/A2给第二支。
若rare在B0，浓集A1后用(RMT)，h=A/3≥8B且≥sqrt(|B0|)。
用log(1+t/3)≥(1/3)log(1+t)，三支统一得到

  E[D_j;0≤F_j≤D_j,S_j≥A]
   ≤Cbeta/j exp(−A/(72B)log(1+AB/j))。                          (RSE)

原F、任意真实U、closed strip及endpoint等号都保留；没有替换随机energy为均值。

## 4. 全部很早one-wall record-strip proxy的数值Gaussian付款

先固定eta0=1/200，d0=eta0/sqrt(2)，

  gamma0=min(1/2,d0²,exp(−400sqrt(2)eta0))>0，
  X0=max(16,sqrt(3/gamma0),sqrt(200sqrt(2)eta0))。

随后取原bounded-centered data，n≥1、x≥X0、B≤eta0 sqrt(n)/x，
delta=beta/sqrt(n)、delta(1+x)³≤exp(−3x²)。所有以下C只依赖已先定数值。
对原同一路径j=1,...,n，actual suffix权W_{n−j}为前稿half-cutoff普通W，
a=x sqrt(Q)、F_j^actual=S_j−a。定义

  ES_j=D_j W_{n−j}1_{Q≥n/2}1_{0≤F_j^actual≤D_j}。

它的prefix strip在high Q上等于上述clamped F_j。且S_j≥a、Q>0与S_j²≤jQ_j≤jQ
逐点推出j≥x²，故x≥X0确保每个非零early项j≥12，不新增时间前提。
令A=x sqrt(n/2)，则A≥3sqrt(j)、A≥24B对j≤gamma0n成立。
(RSE)给定真实suffix后均匀适用，Wsum给E W_{n−j}≤C/sqrt(n)。
将72适当放宽为100，其成本≤Cbeta/(j sqrt(n))
 exp(−A/(100B)log(1+AB/j))。

函数log(1+cB)/B在B>0递减（log(1+t)≥t/(1+t)），所以代Bmax=eta0 sqrt(n)/x合法。
令gamma=j/n≤gamma0、q=x²/(200sqrt(2)eta0)≥1，
log(1+d0/gamma)≥.5log(1/gamma)由gamma≤d0²给，因而指数≤gamma^q。
J=floor(gamma0n)时n^(−q)sum_{j≤J}j^(q−1)≤(J/n)^q≤gamma0^q≤exp(−2x²)。
因此

  E sum_{j≤gamma0n} ES_j≤Cdelta exp(−2x²)。                      (EARLYO)

没有harmonic log(n)；J=0时和为空；不合法的小j已由实际energy几何排除。

## 5. 既往相反墙命中的actual second-wall proxy

令P_j^-={∃1≤k≤j,S_k≤−a}，同一个真实wall a=x sqrt(Q)，定义SO_j=ES_j1_{P_j^-}。
前稿low-full-energy proxy已给E sum D_jW1_{Q<n/2}≤Cdelta exp(−2x²)，可无条件付low Q。
很早high-Q项由(EARLYO)支付，不需要该hit mask。
对j≥gamma0n，theta0=2x/sqrt(n)。在原same-path lower-hit与upper strip上，
L_j≥S_j+2a≥3a≥3x sqrt(n/2)。故

  E_prefix[D_j;highQ,strip,P_j^-]
   ≤exp(−3sqrt(2)x²) E_prefix[D_j exp(theta0 L_j);clamped strip]。

前一实际smallballot(B)给后者≤Cbeta/n(1+x)^5
 exp(.506jtheta0²+Cjtheta0³beta+Ctheta0B)，统一于给定实际suffix。
.506jtheta0²≤2.024x²，3sqrt(2)−2.024>2.2；
jtheta0³beta≤8delta x³≤8、theta0B≤2eta0均为数值，
再用sum E W_t≤Csqrt(n)，得到late成本≤Cdelta(1+x)^5 exp(−2.2x²)≤Cdelta Psi(x)。
合并early/lowQ即给所有同路径second-wall strip proxy的Cdelta Psi(x)预算。

## 6. 删除crossing label后的actual bad-displacement proxy（结构cutoff前）

沿用已交第二公开候选的同一K=2^64、H=Kbeta²(1+x)^6、m=ceil(H)。
它已数学证明h0≤H/2、m≥4、m≤n/4及真实future rare weight期望≤Ct^(−1/2)Psi(x)，t≥m。
对j=r+1，b=X_r（属于prefix长度j的最后一坐标），U、d'是严格之后的真实suffix。
定义bad label事件|b+d'|≥(3x/2)sqrt(b²+U)，并明确加静态结构guard t=n−j≥m、U≥H/2。
在此guard下删除mark的Cauchy几何给|d'|≥sqrt(9x²/4−1)sqrt(U)。
这是真实必要事件；删除后才只依赖suffix，不能事先把原bad事件因子化。

用(RS)给prefix actual first-wall strip成本≤Cbeta/j，统一于suffix U；
乘actual rare W_t再积分，当j≥gamma0n时成本≤Cbeta Psi(x)/(j sqrt(t))。
求和t^(−1/2)≤2sqrt(n)给C_gamma delta Psi(x)。
其余很早项和low-full-Q可删bad/结构masks，分别已由(EARLYO)/(LFO)支付。
所以这个明确静态cutoff前bad-displacement strip proxy总成本≤Cdelta Psi(x)。
将guard从t≥m/U≥H/2识别到实际tau前状态必须消费C12真实AdaptiveRevealCutoff接口；
本稿不增加任意tau或目标omitted budget前提，也不重复其148/149producer。

## 7. 坏first-interval projection的纯cubically weighted wall-gap proxy

对r∈[0,n−1]令T_r,d_r,b_r为真实old suffix，A_r为前稿普通cutoff cubic mark。
wall gap w_r=a−S_r，strict upper alive A_r^+，定义

  N_r=A_r 1_{|d_r|≥(3x/2)sqrt(T_r)}1_{A_r^+}1_{0<w_r≤|b_r|}。

early r<n/2时删alive/gap，用已交第二候选actual rare q3 grid，得≤Cdelta A_x≤Cdelta Psi(x)。
late r≥n/2时分G_r={Q_r≥r/2}。good prefix由已完成(WCDF)在theta=0、v=|b_r|给实际概率
≤C(|b_r|+beta)²/r≤C(T_r+beta²)/r≤5CT_r/(2n)，在T_r≥h0上逐点成立。
所以good成本由已交actual late rare q1 grid支付≤Cdelta Psi(x)。
在G_r^c上删所有alive/gap/bad masks，只有此prefix-low-energy mask与suffix A_r分离；
它的exp(−c/delta²)概率乘实际unsummed cubic grid≤C，
原residual Gaussian吸收给≤Cdelta exp(−.8x²)≤Cdelta Psi(x)。
因此E sum N_r≤Cdelta Psi(x)。

这精确支付物理negative interval overshoot若被已有projection界支配到该cubic/gap proxy时的概率账。
该物理source-value/endpoint/status支配不在本稿当作新假设；其符号与large-step/zero-time范围须Root核对。

## 接受与剩余范围

所有proxies由真实有限sum/energy/max、Borel guards、正能量cutoff构成且由原support实际有界，故Integrable为输出。
原zero energy分支全为0、closed crossing/record strip端点保留；同一label seed/AE原族运输只用已qualified iid reorder/map。
低Q mask绝不误作独立；只在cycle不变或Cauchy的未mask平方期望中使用真prefix/suffix独立。
固定X0很大仍是原source可选通用数值；本稿没有解决1/2≤x<X0的固定窗或宣称原根闭合。
当前仅后续完整数学草稿，未冻结Lean头/执行/独审。actual physical regular ratio由A推进，
retained/overshoot proxy精确识别、tau后omitted预算、初值BV与完整flags/stopping/telescope装配仍需各实际接口。
