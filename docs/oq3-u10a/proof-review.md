# U10a 完整独立声明、来源与证明审查

## 第一阶段：actual三定义及五完整签名盲译（先落盘）

本节只提取实际GaussianBoundaryConstant.lean的三个公开定义体、五个完整公开签名及导入/作用域；在读取本次实现/私有项、scope/R1/旧票及作者receipt/Audit之前落盘。源码实测SHA256=`c44d13d42da6711f9eec44313fb27b363513b7e75aeb83c1df79708157e65f5a`，282行。actual导入CorrectedScaleContinuity、GaussianIntegral、ImproperIntegrals、Integral.Prod；namespace Shao.OQ3、open MeasureTheory、noncomputable section。此前声明上下文存在，本次仍重新从actual翻译。

三个定义：gaussianBoundaryWeight(kappa,d)是Lebesgue限制积分，在闭二次集合{z:−(z/kappa)²≤d}上积分exp(−z²/2)/sqrt(2pi)；gaussianBoundaryProfile(ell,kappa,d)=exp(−ell*d)乘weight；boundaryKappa(q,mu)=sqrt(q)/(4sqrt(transverseVariance(mu)))。三者任意输入总化，物理正域由下述前提提供。

1. 对每个kappa>0、所有实d，weight在d≥0时等于1；d<0时等于2/sqrt(2pi)乘exp(−z²/2)在开半线z>kappa sqrt(−d)上的积分。包括d=0；开闭端点须真实零测。
2. 对每个ell>0、kappa>0且2ell<kappa²，profile作为实d函数真正Integrable（实Lebesgue测度）。
3. 相同严格正域下，全实线真实积分∫profile(d)dd=kappa/(ell sqrt(kappa²−2ell))。需证明联合/切片可积后才作Bochner换序，不能利用总化积分0。
4. 对任意q>0和任意Measure ℝ的mu，若S=actual normalVariance(mu)>0、D=det actual parabolaCovariance(mu)>0，则boundaryKappa(q,mu)²=qS/(16D)。没有概率或可积输入；应核是否为实际transverseVariance=D/S的纯标量代数结论。
5. 对每个ell>0、q>0、任意mu，若S>0、D>0及R=S−(32ell/q)D>0，则(1/sqrt(S))∫profile(ell,boundaryKappa(q,mu),d)dd=actual correctedInverseScale(ell,q,mu)。应由实际正前提推出kappa>0、gap>0及所有根号/逆分母非零，核对常数及正根符号。

待核整个282行含stdGaussian/kernel及全部私有/生成项、真实高斯归一化与两尾、联合可积先于Fubini、每个正域/实际协方差与校正定义；之后才机械核验。当前无完整裁决，根A/B/C/D全部OPEN。

## 第二阶段：冻结与R1来源对应

盲译落盘后读取scope及旧声明票，实测SHA分别为`e294a49d155254fb3f375e6f04251fdaa51e03143c0fde0c4471c66212c56ba2`和`b02b1168511c6065ad2f65202e5aca54281f672dcd444f0c4b288df87061bc1a`。三个actual公开定义体与五完整类型逐项按空白规范化独立比较，8/8完全相同；导入/作用域一致。

真实R1 411–444逐行读取，SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。413–421的g为1/标准Gaussian两尾，kappa=sqrt(q)/(4tau)，F=exp(−ell d)g；431–443的(20)及kappa²/corrected方程与当前五目标对应。实际transverseVariance为D/S=tau²，S=Var(normalValue)，Delta是Cov(X,X²)矩阵；候选没有把tau²直接当作tau，也没有以任意替代矩阵代替真实协方差。声明范围不包含(19)有限层LLT、全层极限或后续Euler–Maclaurin/实际hW。

## 第三阶段：全部实际证明、私有辅助与固定库数学

已逐行审读全部282行，含stdGaussian/gaussianBoundaryKernel两个私有定义、七个私有定理及全部局部辅助。以下独立数学判定在读取本次Audit TYPE、作者receipt/Audit源和机械结论之前落盘：CORRECT，未发现数学或source缺口；生成常量实际TYPE与机械绑定随后核对。

1. 30–50行stdGaussian恰为标准密度。stdGaussian_integrable先把指数写为−(1/2)z²，用真实正系数Gaussian可积定理，再除常数。integral_stdGaussian从实际Gaussian积分取得sqrt(pi/(1/2))，化为sqrt(2pi)并以其严格非零相除，真实归一为1。虽然库integral_gaussian对b≤0另有总化分支，本次系数1/2>0且真实可积先已证明，不借总化积分。
2. 52–106行piecewise目标：d≥0时−square≤0≤d，边界集合确为全集，含d=0。d<0令a=kappa sqrt(−d)>0、a²=kappa²(−d)，由kappa²>0合法乘除，原闭二次不等式等价a²≤z²，再按z正负得Iic(−a)∪Ici(a)。ha>0保证两半线不交。stdGaussian真实全可积给两限制可积，合法setIntegral_union。实际Lebesgue反射接口把左Iic(−a)积分变为右Ioi(a)下stdGaussian(−z)，偶性化为stdGaussian(z)；另一Ici端点通过Lebesgue单点零测改为Ioi。最终真实二倍右尾及2/sqrt(2pi)系数正确。
3. 108–119行kernel为闭可测曲边界上的indicator乘exp(−ell*d)stdGaussian(z)，非负证明对indicator两支完整处理；不需额外概率或正kappa才能非负。
4. 121–134行固定任意z的d切片：ell>0使指数斜率−ell<0，先用真实右半线IntegrableOn，再用有限实端点值/Lebesgue零原子换Ioi到Ici，乘stdGaussian(z)并以measurableSet_Ici转indicator的真实Integrable。此辅助甚至允许任意kappa；没有把每切片可积偷当联合可积。
5. 136–160行先对每个固定z计算真实切片积分：下限−(z/kappa)²，指数半线值为exp(ell(z/kappa)²)/ell，乘stdGaussian后为exp(−(1/2−ell/kappa²)z²)/(ell sqrt(2pi))。field_simp只在hk≠0下改写指数；ell>0支持指数半线值。该逐点公式不要求gap，只是切片值，未冒称此时z方向一定可积。
6. 162–185行联合可积证明次序严格正确：先由gap及kappa²>0得b=1/2−ell/kappa²>0；边界由连续函数≤构成闭可测集合，body连续，得到真实联合AEStronglyMeasurable。消费integrable_prod_iff时，第一个门是前述每z切片Integrable；第二门将kernel范数以真实非负性改成本身，逐点切片积分恰为严格正b的Gaussian，故真实可积。联合Integrable在任何Fubini调用之前完成。
7. 187–204行profile辅助以可测indicator及integral_const_mul绑定另一实际边缘积分∫z kernel(z,d)=exp(−ell d)weight；等式对任意输入成立，不依赖错误的未证明Fubini。公开profile_integrable由已经联合可积的kernel.integral_prod_right取得，再用实际边缘等式AE改写；积分方向与库接口一致。
8. 206–231行公开完整积分：先持有hprod，再把profile改为z边缘，用实际hprod作Fubini交换前提，之后才代入d切片公式与Gaussian积分。b>0和G=kappa²−2ell>0均从实际gap取得。hroot用sq_eq_sq₀的两个非负门，平方化sqrt(pi/b)=sqrt(2pi)kappa/sqrt(G)，然后用hk、b、G非零验证有理式；没有丢负号或错选平方根。最终除ell及正sqrt常数取得kappa/(ell sqrt(G))，是真完整全实线积分。
9. 233–239行boundaryKappa_sq仅消费真实transverseVariance=D/S定义，hD/hS使其正；sqrt(q)²=q及sqrt(D/S)²=D/S后得到qS/(16D)。S/D的非零由正假设给出。这里是任意mu的纯正实标量代数，不需要额外概率/矩可积门，也不宣称任意mu无条件满足这些正前提。
10. 241–279行把actual S/D/R/k定义在同一mu上，正假设先给k>0。由k²=qS/(16D)及q,D非零得G=k²−2ell=qR/(16D)>0，故公开Gaussian积分的gap被真实满足。hid给S*G=k²R，再以两边非负的sq_eq_sq₀及真实S/G/R正根得到sqrt(S)sqrt(G)=k sqrt(R)。代入完整积分，最后只在k、ell、sqrt(R)非零时消去，恰得actual(ell sqrt(R))⁻¹。常数4/16/32、sigma=sqrt(S)和正根符号全部保持，未重新定义协方差或修正常数。

本次只读核对的固定库实际接口及SHA：GaussianIntegral.lean115–117/210–221（`4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c`）分别给正b真实可积与Gaussian积分；ImproperIntegrals.lean77–80/102–107（`1527f79047df49f816995ad879a8cfa9e6655f8c8a2c1e0342bf780890a894e7`）要求负指数斜率并给真实半线可积/积分。Integral/Prod.lean230–243/341–343/471–483（`8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05`）明确要求联合可测+切片可积+范数边缘可积，Fubini要求联合Integrable，证明已逐门满足。Measure/Lebesgue/Integral.lean89–92（`8fa19186f554100cee2b450ba3faef3e84c0407734a3068e442093d2b9ff4ea4`）实际integral_comp_neg_Ioi方向是右Ioi下f(−x)=左Iic(−a)下f，和本实现反射相符。Integral/IntegrableOn.lean932–967（`d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2`）核实端点有限门；Bochner/Set.lean693–721（`e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75`）核实零单点的开闭积分相等。Algebra/Order/GroupWithZero/Basic.lean748–749（`28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c`）sq_eq_sq₀确要求两实数非负，实际两次均已消费，未以仅平方相等代替带符号相等。

继承语义：本单元的概率分析全在实Lebesgue上，mu仅通过已审实际S、D和transverseVariance进入最后两项正域代数。U7对实际概率原子族的真实可积、协方差和Var(Y)绑定及U11d v2正radicand/尺度定义保持，不把variance.toReal总化用作高斯可积或额外概率结论。根A/B/C/D仍OPEN。

## 第四阶段：全部48个实际owned TYPE逐项审查

数学阶段先落盘，然后只读取实际服务器Audit.log中的DECL/TYPE及完整续行，分1–24、25–48两批读完，没有先读取receipt或机械结论。下表保持真实枚举序号，每一项均已审读实际类型，不由计数推测生成项。所有公开名省略`Shao.OQ3.`；`P.`代表实际私有前缀`_private.Shao.OQ3.GaussianBoundaryConstant.0.Shao.OQ3.`。另作唯一缩写：I=`integral_gaussianBoundaryProfile`，C=`gaussianBoundary_constant_eq_corrected`，G=`gaussianBoundaryWeight_eq_piecewise`，L=`P.integral_gaussianBoundaryKernel_slice`。

生成类型记号均保留其实际前提：N_m指任意[Zero α][OfNat α m][NeZero m]下命题等式(m=0)=False；M指[Mul M][Zero M][NoZeroDivisors M]及a≠0、b≠0下(a*b=0)=False；P_N指[MonoidWithZero M][IsReduced M]、n:ℕ及a≠0下(a^n=0)=False；P_Z指[GroupWithZero G]、n:ℤ及a≠0下(a^n=0)=False；Z指[AddMonoidWithOne R][CharZero R]、n:ℕ下((↑n+1)=0)=False。它们均为有条件的通用简化定理，未将数值非零/幂非零假设静默删去。

|#|实际常量|实际TYPE核对|
|---|---|---|
|1|I._simp_1_5|P_N。|
|2|I|∀ell,kappa，ell>0、kappa>0、2ell<kappa²→∫profile=kappa/(ell sqrt(kappa²−2ell))，无削弱正域。|
|3|I._simp_1_1|N_2。|
|4|gaussianBoundaryProfile_integrable|同三正域→真实Integrable(profile) volume。|
|5|P.stdGaussian.eq_1|∀z，stdGaussian z=exp(−z²/2)/sqrt(2pi)。|
|6|P.gaussianBoundaryKernel.eq_1|∀ell,kappa,v，kernel=闭边界indicator(exp(−ell v.2)*stdGaussian v.1)v。|
|7|G._simp_1_4|∀α,x,a,b，(x∈a∪b)=(x∈a∨x∈b)。|
|8|C._simp_1_6|P_Z。|
|9|L._simp_1_3|N_3。|
|10|P.integral_stdGaussian|∫stdGaussian=1，无参数或额外假设；实际归一化已独立核证。|
|11|L._simp_1_5|M。|
|12|P.gaussianBoundaryKernel_slice|∀ell,kappa，ell>0→∀z，真实d切片Integrable volume，kappa任意，符合半线分析。|
|13|G|∀kappa>0、d，weight=if d≥0 then1 else真实二倍开右Gaussian尾，符号/端点同冻结。|
|14|I._simp_1_3|N_4。|
|15|L._simp_1_7|P_Z。|
|16|P.gaussianBoundaryKernel_nonneg|∀ell,kappa,z,d，0≤kernel(z,d)，无遗漏域条件，密度/indicator确非负。|
|17|gaussianBoundaryProfile|ℝ→ℝ→ℝ→ℝ。|
|18|I._simp_1_7|Z。|
|19|G._simp_1_5|∀[Preorder α],b,x，(x∈Iic b)=(x≤b)。|
|20|L._simp_1_2|N_2。|
|21|C._simp_1_2|N_3。|
|22|L._simp_1_8|Z。|
|23|L._simp_1_6|P_N。|
|24|C|∀ell,q,mu，ell/q/S/D/R均>0→(1/sqrt(S))∫profile(ell,boundaryKappa q mu)=actual correctedInverseScale；无虚增概率/可积输入。|
|25|gaussianBoundaryWeight|ℝ→ℝ→ℝ。|
|26|P.gaussianBoundaryKernel_profile|∀ell,kappa,d，∫z kernel(z,d)=profile(ell,kappa,d)，任意输入的实际边缘恒等式。|
|27|boundaryKappa._proof_1|(3+1).AtLeastTwo，数值4实例证明。|
|28|C._simp_1_3|N_4。|
|29|P.stdGaussian_integrable|真实Integrable stdGaussian volume。|
|30|L|∀ell,kappa，ell>0、kappa>0→∀z，∫d kernel(z,d)=exp(−(1/2−ell/kappa²)z²)/(ell sqrt(2pi))；没有错误的z可积无gap声明。|
|31|P.gaussianBoundaryKernel_integrable|ell>0、kappa>0、2ell<kappa²→真实联合Integrable kernel (volume.prod volume)。|
|32|C._simp_1_4|M。|
|33|L._simp_1_4|N_4。|
|34|C._simp_1_5|P_N。|
|35|gaussianBoundaryProfile.eq_1|∀ell,kappa,d，profile=exp(−ell d)*weight。|
|36|boundaryKappa_sq|∀q,mu，q/S/D>0→kappa²=qS/(16D)，与actual定义的纯代数一致。|
|37|I._simp_1_4|M。|
|38|gaussianBoundaryWeight.eq_1|∀kappa,d，weight=实际闭二次集合限制的标准密度积分。|
|39|gaussianBoundaryWeight._proof_1|(1+1).AtLeastTwo，数值2实例证明。|
|40|I._simp_1_6|P_Z。|
|41|boundaryKappa|ℝ→Measure ℝ→ℝ。|
|42|P.gaussianBoundaryKernel|ℝ→ℝ→(ℝ×ℝ)→ℝ。|
|43|G._simp_1_1|∀α,x，(x∈Set.univ)=True。|
|44|C._simp_1_1|N_2。|
|45|C._simp_1_7|Z。|
|46|P.stdGaussian|ℝ→ℝ。|
|47|G._simp_1_6|∀[Preorder α],b,x，(x∈Ici b)=(b≤x)。|
|48|I._simp_1_2|N_3。|

独立逐项分类：5定义（3公开、2私有），43定理（5公开、7私有、31生成）。31生成项是上表25个通用有条件简化定理、4个定义方程、2个数值实例证明；未假定存在未出现的boundaryKappa.eq_1，也未遗漏实际L._simp_1_8等项。所有生成TYPE都是正确定义/逻辑/代数简化，不含新分析结论或隐藏假设。完整TYPE审查支持前述CORRECT；接下来才核作者机械证据。

## 第五阶段：最后读取的作者门与真实机械证据

仅在全部前述阶段后读取本地U10a-receipt.json，随后实际读取指定服务器run的Audit源、receipt、Audit公理/计数、build元数据，并逐份核真实源码。作者receipt状态为`AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW`，其作者门不替代本报告独立数学与TYPE判定。

实际worktree=`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，branch=`feat/oq3-gaussian-constant`，HEAD=`06e64c476169bedc9b87446af79e23c7a5ded6e4`；status仅`?? Shao/OQ3/GaussianBoundaryConstant.lean`。本地、真实worktree、真实run快照三处source SHA均为`c44d13d42da6711f9eec44313fb27b363513b7e75aeb83c1df79708157e65f5a`，12700字节/282行。run scope与statement快照SHA分别为第二阶段所列冻结值。源码独立扫描无CR、无尾空白、无sorry/admit/axiom/unsafe/native_decide/implemented_by。

实际承重17份project源在本地与服务器逐份核hash，全部与冻结receipt及已完整独立审查源码一致：

|依赖|实测SHA256（本地=服务器）|
|---|---|
|U1 FiniteConstraints|`800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`|
|U2 SourceStarter|`0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d`|
|U3a SummableAtoms|`0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b`|
|U3b AtomicMeasure|`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`|
|U4 InverseTilt|`c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`|
|U6a AtomProjection|`0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22`|
|U6c ResonanceArithmetic|`cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b`|
|U3c FiniteStageMeasure|`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`|
|U8 FiniteNormalSpan|`0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de`|
|U11b AtomicTailControl|`ec528d9af8b475f1db8a78c93ab917d754365d280027a86be2823825b19c2f79`|
|U9a SampleBoundary|`7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2`|
|U11c AtomicProductControl|`6f886635f2201e04d1004a4f4b3b4058d406be3a283f716b70f1ce1cfaa5775f`|
|U5a PositiveRate|`8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b`|
|U7 RegularCovariance|`0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`|
|U11d CorrectedScaleContinuity v2|`b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8`|
|共享FinitePath|`898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`|
|共享FiniteIID|`d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`|

真实run=`/root/rivermind-data/shao-lean-20261021/runs/oq3/u10a-20261021`。本地与远端receipt SHA均为`e12e61664d01a9867c85b579a4c98f4303c4b12d9d10245f39ea7d14bea10033`（4593字节）；Audit.lean实际SHA=`f1c041250f889f7a55874089783e45f820ccde2089a6713cb58951e12d61fca1`（1750字节）；Audit.log实际SHA=`168147492eb12182dbf6c9e2d6560b5c9b1b2e99c9bedaf8f9c975eae582f2f4`（10677字节）；build-03.log实际0字节、SHA=`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。既有实际receipt记录build和Audit命令exit0；本次只核已有记录/产物，未重跑并不虚称观察新执行。真实目标olean为840360字节，SHA=`660eb79a3737d0de5389d75d20e3fdd0658da79f78d9801ccba6f69ab740c80c`。

Audit源完整覆盖八个公开stem及模块整个私有前缀，检查五冻结目标存在且是theorem，拒绝新axiom，并对每项Lean.collectAxioms的传递集合实施propext/Classical.choice/Quot.sound白名单。真实log全部48项AXIOMS只含白名单，末尾实际为`U10A_FROZEN_THEOREMS 5`、`U10A_ALL_THEOREMS 43`、`U10A_ALL_DECLARATIONS 48`、`U10A_AXIOM_GATE PASS`。已先逐项读完全部48TYPE，未把PASS计数当作数学审查。

真实toolchain文件与实际版本输出一致：leanprover/lean4:v4.36.0-rc1，Lean commit=`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Lake=`5.0.0-src+c9afcdd`；manifest及mathlib实际HEAD均为`807d3836b165983210ee2ecf3cd28f239436949c`。没有本地Lean、成功目标重编、Audit重跑、raw log下载、源码/旧报告修改、commitPR或spawn。

STATUS: CORRECT

JUSTIFICATION: actual三定义/五完整目标签名与冻结源对应一致；全部282行、两个私有定义、七个私有定理、31生成项以及全部48实际TYPE独立审查无缺口。标准密度真可积且归一化，闭二次集合确为两个不交半线，反射/零端点给真实两尾；每个指数半线切片和严格正系数Gaussian范数边缘先建立联合Integrable后才Fubini。实际全线积分及正根/分母消去正确，q/S/D/R正域真实支持kappa与校正逆尺度恒等式。随后真实source/17传递源码/pins/build记录及48项公理Audit全部绑定；该CORRECT为独立完整判定，不由作者门代替。不声称源(19)、有限LLT、全层极限、尖点展开、实际hW或根闭合；根A/B/C/D全部OPEN。

交付：本报告完成后上传为上述run/proof-review.md并另行核远端SHA；自身SHA通过交付消息提供，不嵌入正文。
