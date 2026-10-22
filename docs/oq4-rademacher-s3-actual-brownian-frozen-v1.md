# OQ4 原S3：实际Brownian基准的最小汇总冻结命题 v1

STATUS: FROZEN_FOR_FRESH_SOURCE_REVIEW
AUTHORITY: OQ4_LEAD
INTAKE_STATUS: SOURCE_INTAKE_ADOPTED
UNIT_KIND: DERIVED_ASSEMBLY
NEW_RAW_LEAF_INCREMENT: 0
SOURCE_RAW_DENOMINATOR_DELTA: 0
PROOF_STATUS: NONE
LEAN_STATUS: NONE
IMPLEMENTATION_AUTHORIZATION: NONE
UPSTREAM_U1_FORMAL_STATUS: PENDING
UPSTREAM_S2_FORMAL_STATUS: OPEN
ACTUAL_BROWNIAN_INTERFACE_OWNER: ROOT
ACTUAL_BROWNIAN_INTERFACE_STATUS: PENDING
S3_S4_S5_DA1_DA2_STRICT_COSETS_SPECTRUM_ROOT_STATUS: OPEN
SOURCE_REVIEW_STATUS: PENDING

本文件由OQ4 lead冻结S3的实际对象、定义域、全部量词、固定依赖和待证输出；作者不得增加、删减、弱化或重新解释前提。只组合固定实际S2接口与原冻结题所指的实际Brownian首项等价，不新增原始raw叶或总分母。下列极限、正性和代数桥全部在结论侧，不得变成自由假设。当前仅授权全新来源审查，证明、Lean和共享实现均未授权。

来源intake 013748edbd842f5e84c6c6b5bc6b220c73d1210e7bb96797ccd0f7057ad35fcd/13231B和候选56bed942992031803c5a97b53460414052b3ce92a71235bf58fe4d62a2dc9589/13566B均由lead完整读取并核验原字节；两原件保持不变。本文件采用其全部有限对象、S3-DOM、S3-ALG、S3-MAIN及排除范围，另立冻结身份；不将该intake或候选当作数学证明。

## 1. 来源、强度与固定依赖

唯一原谱来源为 C:/game/shao/current/oq4/c01/spectrum01.md，commit 35d4580b61e22e7145f47730045a09874ef93259，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b，4306 bytes：

- 11–12、24–37行固定弱胞元、实际概率、零时间、a/rho。
- 38–56行给S2及其原双尺度。
- 60行固定lambda=π²/8、x=h/sqrt(n)。
- 65–67行给本冻结唯一主目标S3。

实际Brownian原输入为 C:/game/shao/current/oq4/frozen01.md，SHA256 ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a，1491 bytes：第3行定义U=sup_{0≤t≤1}|B_t|；第9行只给

P(U≤x)~(4/π)*exp(-π²/(8x²))。

spectrum01.md第61行保留的原文较强表述是

P(U≤x)=(4/π)*exp(-lambda/x²)*(1+O(exp(-8lambda/x²)))。

已核对的原冻结题没有该相对指数速率。本文不把它当作给定或已认证输入，也不删改原文。S3只消费实际首项等价在x↓0的相对误差趋零及其所需最终正性；不需要上述较强O率。若将来另用较强率，须由root补齐实际Brownian定理和来源，本冻结不交付它。

固定S2接口为 C:/game/shao lean/drafts/oq4/frozen-rademacher-s2-assembly-v1.md，SHA256 c59971859b432bf312d5c1d65ca82d0a02254c06d4d56833322364f87f69146e，8318 bytes；消费其F0及Q1实际对象输出，不消费S2证明。按lead本轮派发：S2数学相对于固定实际U1已过新鲜审查，U1 formal仍PENDING，S2 formal未关闭；实际共享B/U/首项tail Lean接口由root负责且PENDING。本文不能将冻结声明或这份来源intake当作上述正式接口已关闭的证据。

## 2. 全部有限格点参数与同一实际S2对象

量化全部m:ℕ、1≤m，全部h:ℝ、(m:ℝ)≤h<(m:ℝ)+1，全部n:ℕ，包含0。记

H_m=(m:ℝ)+1，N_n=(n:ℝ)，
a_m=Pair.amplitude m，rho_m=Pair.rho m，
eps_mn=Pair.epsilon m n，R_mn=Pair.remainder m n，
u_m=Scalar.u m，q_m=(Real.tan u_m)²，
A_mn=a_m*rho_m^n。

这里Pair:=Shao.OQ4.RademacherSpectralPairing、Scalar:=Shao.OQ4.RademacherScalarBounds。A_mn是固定S2第40行B_mn的别名，只为避免与Brownian过程B混名，数学对象及归一化分母不变。

固定ν_R=Shao.OQ4.RademacherCosine.law及其law_isProbabilityMeasure，产品概率与杀死质量为

p(n,h):=(Measure.pi(fun _:Fin n=>ν_R)).real(@Shao.closedStrip n h)，
K(n,h):=@Shao.OQ4.killedMass ν_R law_isProbabilityMeasure h n 0，
D(m,n,h):=p(n,h)/A_mn。

p是从0出发的实际Rademacher产品测度弱事件，不能按谱和定义。固定S2 F0的全部时间身份和正分母继续保留：

a_m>0，0<rho_m<1，A_mn>0，
p(n,h)=K(n,h)，
p(n,h)=A_mn*(1+eps_mn*q_m+R_mn)，
D(m,n,h)=K(n,h)/A_mn=1+eps_mn*q_m+R_mn。

R仍是实际Pair.remainder的有限normalizedTerm和加zeroMode/A；不是自由R。n=0时p=K=1，偶m中心项及0^0=1照样保留，不能因后继对数只在正时间使用而删去。m=1、m=2、全部奇偶及整数弱端点h=m保留；H不是h或独立实参数。

已获准公开透明定义与冻结S2第52–58行固定相容：

u_m=π/(4H_m)=Pair.alpha m 0，
z_m:=Scalar.z m=π/(2H_m)=Pair.beta m 0，
a_m=(1/H_m)*(cos u_m/sin u_m)=Scalar.a m，
rho_m=cos z_m=Scalar.rho m，
eps_mn=(-1:ℝ)^(n+m)。

Pair的导入cotangent由获准S1透明值cos/sin解释。这些不作为新的等值假设，也不重新要求Scalar的Taylor估计；本S3不消费SCA1/SCA2展开或n/h³尺度。

## 3. 实际Brownian对象：固定原输入与root尚缺契约

B、U始终指原冻结题的同一实际Brownian基准：

U=sup_{0≤t≤1}|B_t|，
b_U(x):=P_B(U≤x)。

P_B表示该实际Brownian概率律，不能由OQ4另选一个任意函数、抽象尾函数、任意分布或自由随机变量替代。Rademacher与Brownian仅比较各自边际概率；本冻结不增加耦合或独立性假设。

本轮没有获准或已提供的actual B/U/P_B Lean公开名称、类型、透明定义或首项tail定理。root必须交付/明确以下接口后才能进行忠实形式对接：

- 实际概率空间/概率律、原布朗基准B及标准尺度归一化；不能任意缩放B并仍保留4/π及lambda=π²/8。
- 实际U的可测实随机变量表示及其与sup_{0≤t≤1}|B_t|的精确身份。若用可测版本或a.s.身份，root须给不改变该事件概率的实际桥；本冻结不选择或实现版本。
- 对全部实x，b_U(x)确为该实际事件的实值概率；若形式层采用ENNReal事件概率或分布函数，须给对应Measure.real及概率有限性/可测性的公开桥。
- 对同一实际b_U、常数4/π及lambda的正侧小x首项等价：第4节的明确消费契约。此为原输入的待落实实际外部接口，不是一个可自由实例化的尾假设。

这些是root pending的来源/对象依赖，并非本S3目标可更换的数学前提。不能把“设F满足一个尾等价”作为本冻结的替代结论。本文不创建共享Brownian定义、实现或公理，也不假定已存在某个未见的正式名称。

## 4. 实际首项等价的最小消费语义

lambda:=π²/8。对x>0，定义明确确定性主项及实际规范化量：

g(x):=(4/π)*Real.exp(-lambda/x²)，
T_U(x):=b_U(x)/g(x)。

T_U不是自由函数：它必须逐字使用上述实际b_U与显示的g。实际首项等价的消费语义为

∀e:ℝ, 0<e →
  ∃d:ℝ, 0<d ∧
    ∀x:ℝ, 0<x → x<d →
      |T_U(x)-1|<e。

即x从正侧趋0时T_U(x)→1。该量是原等价的透明派生消费接口，不是本S3新增自由输入。root需要的是同一实际Brownian等价的已审公开声明；本冻结不把其正确性宣称为已证明或形式认证。

需要交付的合法性/便利消费输出为g(x)>0（x>0），以及存在d_pos>0，使0<x<d_pos时b_U(x)>0、T_U(x)>0。该局部正性应从实际等价消费中实际获得，或由root提供更强且真实的已证正性接口；不能先把它作为自由假设。S3不要求b_U对每个正x的全局正性，也不需要b_U(0)的任何值。

## 5. 任意序列：全k数据与唯一渐近前提

任取m_,n_:ℕ→ℕ及h_:ℕ→ℝ，要求每个k均

1≤m_k，
(m_k:ℝ)≤h_k，
h_k<(m_k:ℝ)+1。

全部对象取第2节实际函数；记H_k=H_{m_k}、N_k=(n_k:ℝ)、a_k、rho_k、eps_k、R_k、q_k、A_k、p_k、K_k、D_k。唯一渐近前提为

H_k→+∞，
t_k:=N_k/H_k²→+∞。

准确量词是：每个实数T，分别存在自然阈值K_H(T)、K_t(T)，其后H_k≥T、t_k≥T。无单调性、奇偶、指定子列、N/h³、DA1/DA2或更强尺度前提。全部k的胞元条件不弱化为最终合法，也不把早期n_k=0排除。

全k均有h_k≥1、H_k≥2、a_k>0、rho_k>0、A_k>0、p_k=K_k及S2有限身份。S2的D_k=p_k/A_k在全部k有正分母；p_k是否可作真实log的自变量则留待最终正性输出。

普通数学的x_k=h_k/sqrt(N_k)只在N_k>0处使用。在形式语言中可以用同一显示式的Real.sqrt和全域Real除法书写一个全k原始项xhat_k；n_k=0时其形式值按Real除零约定为0，仅是有限前缀的总函数记法，不给原x一个新的概率解释，不改变h、p或弱事件。冻结的实际Brownian比较与概率log均只在下节正时间尾段声明。

可在全部k定义正的确定性主项

G_k:=(4/π)*Real.exp(-lambda*N_k/h_k²)，

因h_k≥1，这里的实数除法全部合法。G_k不是新的概率分母过程，而是g在实际x_k上的尾段重写。若使用xhat总项，则W_k:=b_U(xhat_k)/G_k是全k明确实际Brownian规范化量；其除数全部k正，但不声称早期W_k正，也不使用b_U(0)的信息。

## 6. S3-DOM：必须给出的尾段域与尺度输出

在第5节且仅有的两尺度前提下，冻结要求：

- h_k→+∞，N_k/h_k²→+∞。
- 存在K_time，使每个k≥K_time有1≤n_k、N_k>0、Real.sqrt(N_k)>0；此时x_k=h_k/Real.sqrt(N_k)>0。
- x_k→0且最终保持正，即正侧趋0；准确地∀d>0，∃K_d，∀k≥K_d，0<x_k<d。若用xhat全项，则同一尾段xhat_k=x_k。
- 真实Brownian规范化量沿该尾段满足T_U(x_k)→1；等价消费形式是W_k→1及尾段W_k=T_U(x_k)。
- 存在K_pos≥K_time，使每个k≥K_pos有p_k=K_k>0、D_k>0、b_U(x_k)>0、T_U(x_k)>0。
- 在同一尾段，全部实际商p_k/b_U(x_k)、K_k/b_U(x_k)、D_k、T_U(x_k)都正，概率log有普通实数意义；不依赖Real.log(0)或实数除零的形式值。

D_k→1及log(D_k)→0取固定S2 Q1的实际输出，并保留其U1正式pending依赖；不得换成一个新“归一化比趋1”的假设。T_U(x_k)→1及最终Brownian正性是实际首项等价经本序列的消费输出，也不得改成可自由给定的W、F或趋零误差。

## 7. S3-ALG：需要的定义与对数桥声明，不给证明

在全部m≥1弱胞元参数且n≥1处，所有h、H、N、sqrt、a、rho均取实际定义。冻结需要内部实际核对以下桥；它们都在结论/派生侧，不是自由假设：

N>0，sqrt(N)>0，(sqrt(N))²=N，h>0，
x=h/sqrt(N)>0，x²=h²/N，1/x²=N/h²，
g(x)=(4/π)*exp(-lambda*N/h²)=G，
log(rho^n)=N*log(rho)，
log(g(x))=log(4/π)-lambda*N/h²，
log(a)-log(4/π)=log(π*a/4)。

含p或b_U的对数身份仅在p>0及b_U(x)>0的尾段使用。令

C_k:=lambda*N_k/h_k²
      +N_k*Real.log(rho_k)
      +Real.log(π*a_k/4)，

则在同一合法尾段须给出精确身份

Real.log(p_k/b_U(x_k))-C_k
 =Real.log(D_k)-Real.log(T_U(x_k))。

K_k可由p_k=K_k使用同一身份，不另计概率过程。幂rho^n使用自然指数；N是同一n的实数强制转换，不能换成Real.rpow或独立实时间后略过桥。π、a、rho及g的正性来自固定域和真实定义，不得通过log_abs或总函数log的取值把非法概率对数改成另一个目标。

这些只是所需声明清单，没有给代数推导、极限推导或Lean实现。主项C保留原h分母；不能将h替换成H，不能提前使用S4的Taylor/格点位移。

## 8. S3-MAIN：唯一核心渐近目标

对第5节的任意三条序列，按第6节实际正性尾段解释，要求

Real.log(p_k/b_U(h_k/Real.sqrt(N_k)))
 -[lambda*N_k/h_k²
   +N_k*Real.log(rho_k)
   +Real.log(π*a_k/4)]
 →0。

即对每个e:ℝ、e>0，存在K_e≥K_pos，使全部k≥K_e该显示式各概率log均合法且绝对值<e。用K_k替换p_k是同一实际概率的消费形式，不新增核心义务。

如需形式全k序列，可直接以第5节xhat及Real.log总函数书写同一显示项；其目标必须同时交付S3-DOM并给与普通正性尾段公式的eventual相等。两种写法只差有限前缀的形式解释，不能藉此前缀改造b_U、补假设n_k≥1全k或引入自由延拓F。最终K_e可依赖该三序列和e；本冻结没有指定收敛速率或绝对误差常数。

该目标是原65–67行S3的明确o(1)解释。它不声称p_k/b_U(x_k)→1，也不要求其有有限极限；未减去C_k的对数比可以具有原S4/S5所讨论的其他行为。这里不交付S4、S5、DA1/DA2或一般OQ4。

## 9. 原行映射、有限前缀与后续门

| 输出/接口 | 原行或固定来源 | 精确边界 |
| --- | --- | --- |
| 实际p、K、a/rho/D/R及全部有限端点 | 原5–7、11–12、24–37；冻结S2第31–68行 | 全m≥1、全部弱胞元、全部自然时间，n=0中心项保留 |
| 双尺度及S2实际D/log消费 | 原38–56；冻结S2第88–108行 | 只H→∞与N/H²→∞，正式U1/S2依赖pending |
| 实际U、b_U与首项等价 | frozen01第3、9行 | root实际对象/公开定义与tail接口pending；不是自由Brownian尾前提 |
| 指数O来源差异 | spectrum第60–61对照frozen01第9行 | 只保留并登记；不借强率 |
| x与sqrt桥、尾段域 | 原60行和双尺度 | 早期n=0不删，n≥1及x正/趋0在结论侧 |
| S3实际中心化log极限 | 原65–67行 | 原h保留，lambda=π²/8、系数4/π原样；只给o(1) |
| 最终正性、实际规范化量与精确log桥 | 原S3消费所需的derived便利输出 | 原文未逐项写出；透明列出，不增加raw叶 |

上述为一个derived assembly，raw叶增量和原始来源总分母变化均0。本冻结的下一门为全新来源语义审查；通过后才另派匿名数学证明与独立验证。正式U1/S2、root实际Brownian公开对象及首项tail接口、形式实现和独立审查各门分别保留；不能以自由尾函数或额外正性/收敛假设绕过。当前数学推导与形式化均NONE。

本文件只冻结数学对象及输出，不为lead或后继角色作统一的零曝光声明。intake的实际读取和动作披露保持在其不可变原件；后继作者与审查者的输入隔离另按派发逐项记录。旧原文、候选和intake字节不改；本次冻结未执行Lean、Git、共享实现或数学证明。S3、S4、S5、Brownian、strict、cosets、Spectrum与root全部OPEN；DA1/DA2的其他任务状态不能作为本S3的数学前提。
