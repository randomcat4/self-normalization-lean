# U19c SourceLogPartitionDerivatives 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 一、唯一完整TYPE及全部let的独立盲译

本轮仅先提取scope70的Lean fence，独立翻译并持久化；未读取本候选scope说明／作者路线／mechanical图／未来notes。前置模块上下文存在，但不把其已有结论自动当成此完整导数目标的证明。0publicDEF，以下完整保留TYPE。

```lean
theorem source_log_partition_first_and_second_derivatives
    (q : ℝ) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    let K : (Fin 2 → ℝ) → ℝ := fun theta =>
      Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)
    let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
    let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
    let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
      (pr 0).smulRight (q / 4) + (pr 1).smulRight q
    let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
      ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
    HasFDerivAt K gradient theta0 ∧
      HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0
```

逐量词／类型／let依赖独立盲译：

1. 任取实q，不假设qwindow或q>0。
2. 任取w:AtomicIndex→ℝ，并要求全部w_i≥0。
3. 全部k:Fin4，实际w_i*constraintFeature sourceEll(fixedAtom i)k真HasSum到constraintTarget q k。
4. 无手工IsProbabilityMeasure、Integrable、正Z或可微性假设。
5. 无基点／全部原子严格正、正方差、det>0或非退化假设。
6. P在结论内let为同w/sourceEll的实际originalMeasure。
7. K不是新public定义，只是此结论内局部实函数。
8. K的定义域为Fin2→ℝ，值域ℝ。
9. K(theta)是标准实log乘同P上的真实exp(theta0*x+theta1*x²)实积分。
10. 这个theta 0/1是参数坐标，不是下面固定theta0的名称。
11. 固定theta0局部定义为![8*sourceEll,−sourceEll]。
12. D局部定义为actual parabolaCovariance(atomicMeasure w)。
13. pr(i)是连续线性坐标投影：(Fin2→ℝ)→L[ℝ]ℝ。
14. gradient是同参数空间到ℝ的连续线性映射。
15. gradient=(pr0).smulRight(q/4)+(pr1).smulRight(q)。
16. smulRight须按真实库类型读取，不能误作参数点或梯度坐标向量本身。
17. hessian是从参数空间到其连续线性对偶空间的连续线性映射。
18. hessian由全部i,j:Fin2的双重有限和给出。
19. 每项为(pr i).smulRight((pr j).smulRight(D i j))。
20. 该类型旨在给一个有序双线性型，而不只是2×2数值矩阵。
21. 第一结论：K在同实际theta0有Fréchet导数gradient。
22. 第二结论：真实函数theta↦fderiv ℝ K theta，在同theta0有Fréchet导数hessian。
23. 它比单方向二阶导数、单点二阶Peano展开或“存在某个Hessian”更强。
24. 第二结论须真正控制theta0附近的fderiv函数，不能只知道K在theta0的导数值。
25. 全部P/K/theta0/D/pr/gradient/hessian由同w/q固定，无量词交换或更换law。
26. K中的实积分与log均总定义，proof须排除非可积归0和log0总化后才解释为真实log配分。
27. 退化mu或D=0在type中未排除，真导数结论仍须覆盖。
28. 结论不宣称root公共K/globalRate/domK或鞍点全局性质已定义／闭合。

后续门：实际CLM及smulRight的双线性方向；共同邻域上的dominated integral导数、operator-norm真可积主控和AE可测性；邻域正配分与真实局部梯度公式；同theta0下归一化weighted original moments=同π矩，真L²方差协方差；最后才graph/cache/pins/hash。当前检查点不是批准。

## 二、冻结声明、真实来源与本门裁定范围

以上60行／3971B盲译检查点原字节保留，其SHA256为32d655cb37970530dfe02e2835becb78f43d39be0dd9833208476bd75f215edf；页首IN_PROGRESS是历史检查点状态，最终裁决见末节。
本轮随后全文读取scope70，并核其唯一fence与上述完整TYPE逐字相同；没有把scope路线、既有statement通过或作者候选metadata当作证明。
这是0publicDEF／1publicTHM的声明、来源、实际API及静态环境审查。当前无实现，故本票不宣称target已elaborate、kernel检查、build或Audit通过。

R1真实原件report.md的140–145行给P=π反向指数倾斜，并明确按exp(8ell X−ell X²)倾回π。
R1的147–153行给EπX=q/4及同一个theta0=(8ell,−ell)的鞍点坐标；真实约束第四行给EπX²=q。
R1的239–245行明确Delta=Covπ(X,X²)，sigma²=VarπY；故声明的Hessian必须是同一π的特征协方差，不能换成P的协方差。
R2真实原件38–45行把W=(X,X²)、K(theta)=log E exp(theta·W)、m=∇K及Delta=∇²K写为同一对象，支持本TYPE的字面解析。
R1原件SHA256为3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662；R2为572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。
这里无qwindow／basepos的声明比源正则鞍点应用更一般，但只是有界law的导数恒等式，不把正定性、全局极值或唯一性推广到退化law。
所有let都在真实hw/hm之后由同w/q确定；没有存在参数选择、隐含蕴含前件或caller任选Hessian的真空漏洞。

## 三、概率、真积分、正配分及同一倾斜法则

1. 由hm在k=0及constraintFeature的第一分量1、constraintTarget的第一分量1，真实获得HasSum w 1；这是普通实可和，不是tsum默认值。
2. AtomicMeasure.lean39–42的atomicMeasure_isProbabilityMeasure消费hw及该HasSum，产出同π=atomicMeasure w的真概率。
3. AtomicMeasure.lean86–94的atomicMeasure_constraints消费全部四个真实HasSum；第四行给真实Integrable X²及EπX²=q。
4. AtomicMeasure.lean96–113的atomicMeasure_mean由第四行减第二行，给真实Integrable X及EπX=q/4，不需要严格正原子或qwindow。
5. InverseTilt.lean36–55先证明exp(−ellY)真Integrable和Z>0，再给originalMeasure的IsProbabilityMeasure；本门不把不可积时tilted=0的总定义分支当作概率。
6. InverseTilt.lean57–60给同P的AE固定界1≤|x|≤beta，beta=4+sqrt10；π的对应界由AtomicMeasure.lean51–55给出。
7. InverseTilt.lean26–34的公开integrable_continuous_of_fixed_bounds明确消费真概率、AE固定界与真实Continuous f，给同law上的Integrable f。
8. 因而任意固定实theta、任意自然数j，x↦x^j*exp(theta0*x+theta1*x²)在P上连续且真Integrable；不是仅在theta0小球里可积。
9. A(theta)=积分exp(theta·(X,X²))在每一个实theta都真有限。MeasureTheory.integral_exp_pos在Integral/Bochner/Basic.lean792–799消费Integrable exp与概率所给NeZero，产出A(theta)>0。
10. 之后才允许Real.log A(theta)、A(theta)的逆和商的分析解释；不使用log0、非可积积分归0或无穷toReal。
11. InverseTilt.lean116–127的公开originalMeasure_retilt给P.tilted(ellY)=π；129–147给真前向指数可积及A(theta0)=Z^-1。
12. 在theta0，8ell*x−ell*x²=ell*normalValue x，符号与真实normalValue=8x−x²一致，没有把反向倾斜符号带进正向K。
13. 这条路径只需hw≥0及hm；不调用PositiveRate中需全w>0的严格熵结论，也不跨模块引用任何private helper。

## 四、完整Fréchet微分的可实现分析门

取Theta=Fin2→ℝ，L=Theta→L[ℝ]ℝ；设pr_i为真实连续线性投影。每一个参数点theta*都分别作以下构造，而不只在theta0计算形式导数。
记M_j(theta)=E_P[X^j exp(theta0 X+theta1 X²)]，j=0,1,2,3,4；其中下标theta0/theta1在本式只是theta的两个坐标，固定鞍点仍写theta0=(8ell,−ell)。
为避免这项排版歧义，也可把指数始终写作theta(0)*X+theta(1)*X²；下述A=M_0。
对j=0,1,2，实际点态导数候选为
F'_j(theta,x)=pr_0.smulRight(x^(j+1)*exp(theta(0)x+theta(1)x²))+pr_1.smulRight(x^(j+2)*exp(theta(0)x+theta(1)x²))。
它是Theta→Lℝℝ的真实CLM，不是只有两个坐标数或单方向导数。
ContinuousLinearMap.proj／proj_apply在PiProd.lean234–239给真实坐标投影；ContinuousLinearMap.Basic.lean696–702的smulRight实际作用为c(h)•f。
参数函数theta↦theta(0)*x+theta(1)*x²是连续线性映射，故其hasFDerivAt及ExpDeriv.lean353–355的HasFDerivAt.exp、FDeriv/Mul.lean300–304／353–355的常数乘规则给上述真实HasFDerivAt。

我独立核对一个不依赖额外C²／紧族输入的共同邻域主控如下。
固定theta*，取同一个参数球s=ball(theta*,1)，R=‖theta*‖，p_i=‖pr_i‖，B=(p_0*beta+p_1*beta²)*(R+1)。
对theta∈s及同一AE事件|x|≤beta，由连续线性映射le_opNorm、‖theta‖≤R+1及三角不等式，真实有theta(0)x+theta(1)x²≤B。
因此对全部theta∈s，同时有
‖F'_j(theta,x)‖≤C_j=(p_0*beta^(j+1)+p_1*beta^(j+2))*exp B。
C_j是有限非负实常数，先于该邻域内全部theta／全部AE样本固定；它不是逐theta选择的主控。
此估计只用beta>1、abs_pow和真实算子范数；Bilinear.lean451–457的norm_smulRight_apply给张量CLM范数的准确乘积并以le_opNorm证明上界。
P为真概率，所以constant C_j真Integrable。参数球与同一AE支持事件均不依赖样本逐点另选。
对每theta，F_j(theta,·)是实连续函数，故AEStronglyMeasurable且真Integrable；固定theta*的F'_j由两个实连续系数乘固定CLM再相加，故AEStronglyMeasurable。
同一C_j及Integrable.of_bound还独立给F'_j(theta*,·)真Integrable，之后才可交换CLM取值与积分或拆分其两个项。
点态HasFDerivAt对所有实x和所有theta成立，因此也满足共同AE x之后∀theta∈s的强顺序；没有把∀theta的各自AE集合非法交换为共同AE事件。

实际ParametricIntegral.lean206–212的hasFDerivAt_integral_of_dominated_of_fderiv_le完整消费：
- s∈nhds theta*；
- 参数最终AEStronglyMeasurable F_j；
- F_j(theta*,·)真Integrable；
- F'_j(theta*,·) AEStronglyMeasurable；
- ∀AE x,∀theta∈s,‖F'_j(theta,x)‖≤bound x；
- bound真Integrable；
- ∀AE x,∀theta∈s,真实HasFDerivAt。
其实现213–226以共同球及实际MeanValue Lipschitz估计归约到dominated局部Lipschitz积分微分；不是只给标量deriv版本。
上述各门均可由当前假设实际生产。结果在每个theta*给HasFDerivAt M_j (积分F'_j(theta*,·)) theta*。
Bochner/ContinuousLinearMap.lean70–76的integral_comp_comm／integral_apply明确消费CLM值函数真Integrable；219–223的integral_smul_const及真实积分加法可把导数识别为
M'_j(theta)=pr_0.smulRight(M_(j+1)(theta))+pr_1.smulRight(M_(j+2)(theta))。
由此只需j=0,1,2的三个一阶积分微分命题，但它们在全部theta成立；所需原始矩最多四阶，均已真可积。

## 五、先建立邻域梯度公式，再微分真实fderiv

Real.log的Fréchet接口是Log/Deriv.lean150–152的HasFDerivAt.log，导数为A(theta)^-1 • A'(theta)，显式要求A(theta)≠0。
这里用已证明的严格A(theta)>0，不靠该接口只要求非零便略去log的概率解释。
FDeriv/Basic.lean414–423的HasFDerivAt.fderiv／fderiv_eq把每个theta的真实HasFDerivAt转换成真实fderiv函数公式。
于是对全部theta（因此也在theta0的同一个邻域）有
fderiv ℝ K theta = R_1(theta) • pr_0 + R_2(theta) • pr_1，R_j=M_j/A。
这一步必须在证明第二个HasFDerivAt之前完成；单在theta0算出gradient数值不足以得到第二结论。
实际商可用FDeriv/Mul.lean719–721的hasFDerivAt_inv'与HasFDerivAt.comp，再用该文件206–210的HasFDerivAt.mul生产，所有分母为真实A(theta0)>0。
不需要假称有一个未核定的同名HasFDerivAt.div快捷接口，也不需额外导入标量MGFAnalytic模块。
在theta0，按上述真实M'_j，得到
R'_1(h)=h0*(R_2−R_1²)+h1*(R_3−R_1*R_2)，
R'_2(h)=h0*(R_3−R_2*R_1)+h1*(R_4−R_2²)。
此处各R_j均在同theta0取值，导数来自真正商法则而非形式期望符号。
FDeriv/Mul.lean127–129的HasFDerivAt.smul_const适用于值域L，给theta↦R_j(theta)•pr_(j−1)的导数R'_j.smulRight(pr_(j−1))。
有限和规则给CLM值梯度函数的真实Fréchet导数；与全邻域fderiv公式的函数外延相等后即得到所要求的HasFDerivAt(fun theta=>fderiv ℝ K theta)。
这条路线不以Peano二阶值展开、单方向二阶导数、存在一个未指定Hessian或caller输入C²代替目标。

## 六、归一化矩与actual covariance的精确绑定

对j=0,1,2,3,4，P上的x^j exp(theta0·(x,x²))均真Integrable，π上的x^j也由固定界真Integrable。
MeasureTheory.integral_tilted在Measure/Tilted.lean230–232的实际命名空间为全局MeasureTheory；用同一originalMeasure_retilt和正A(theta0)给
R_j(theta0)=M_j(theta0)/A(theta0)=E_π[X^j]。
它是归一化weighted original moment，不是未归一化M_j直接等于π矩，也不是P的原始矩。
由实际HasSum约束R_1=q/4、R_2=q，故第一真实Fréchet导数正是TYPE所指定gradient。
π为真概率，AE |X|≤beta和|X²|≤beta²；LpSeminorm/Basic.lean631–633的MemLp.of_bound给真实MemLp X 2 π及MemLp(X²)2 π。
这两个L²门先于Variance.lean226–228的variance_eq_sub及Covariance.lean54–65的covariance_eq_sub。
因此D00=R_2−R_1²，D01=R_3−R_1*R_2，D11=R_4−R_2²；D10=D01由RegularCovariance.lean20–24的真实矩阵定义逐字相同。
没有把variance对非L²的总化值当作方差公式；x³/x⁴也确有可积性，不只是符号矩。

真实hessian(h)(k)=Σ_i,j h_i*k_j*Dij。
从梯度求导先得到k0*R'_1(h)+k1*R'_2(h)，四项展开正是h0*k0*D00+h1*k0*D01+h0*k1*D01+h1*k1*D11。
所以外层i是参数导数方向h，内层j是线性泛函被作用方向k，满足冻结TYPE；两个交叉项依真实D10=D01对齐，没有转置／丢失2因子。
该目标既不求逆D，也不除detD、q或方差；退化D、零基点权重不会造成非法清分母，q的实际可行域不需偷偷加在声明里。
hw/hm若在某些q无模型，命题仍是正常全称条件式；本票未声称任意q都存在满足它们的w。

## 七、实际API公开可达与静态环境门（数学后核）

本轮在指定服务器以taskset -c 14-17独立扫描这三个确切imports的真实源文件。未读作者scanner／candidate JSON，也未运行Lean／API probe。
扫描剥除嵌套块注释、行注释与字符串；识别普通import、public/private modifier和public meta import；传统非module源普通import按公开处理。
physical遍历全部内部import；public遍历仅公开边；只在Shao／Mathlib内部展开，Lean/Batteries等外部节点停止，并分别计数，不冒称其内部依赖已展开。
实际physical为8 Shao＋2777 Mathlib＋211外部停止节点=2996；public为2531内部＋189外部停止节点=2720。
全部8＋2777内部节点source及对应olean存在，缺项0；这是静态存在性，不是本target成功编译或全cache内容不变证据。
已核公开可达：CLM PiProd／Basic、Operator.Bilinear、FDeriv.Basic／Congr／Mul、ExpDeriv、Log.Deriv、ParametricIntegral、Bochner.ContinuousLinearMap、LpSeminorm.Basic、Variance／Covariance及Measure.Tilted。
本轮没有重新跑U19a／B、root KL或root任何成功import smoke／build／Audit；新target图只独立扫描一次。

8项目前置canonical相对路径键→实际SHA256（本地draft与服务器源逐项一致）：
- Shao/OQ3/AtomicMeasure.lean: 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39
- Shao/OQ3/FiniteConstraints.lean: 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0
- Shao/OQ3/FiniteStageMeasure.lean: 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1
- Shao/OQ3/InverseTilt.lean: c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811
- Shao/OQ3/PositiveRate.lean: 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b
- Shao/OQ3/RegularCovariance.lean: 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853
- Shao/OQ3/SourceStarter.lean: 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d
- Shao/OQ3/SummableAtoms.lean: 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b
排序canonical相对路径键、UTF8 compact JSON的独立SHA256=07ac7a5a474ea797a09196c33283033d7200dec1693cd15350e53abb6f39181a。
Current C144／U19a146／U19b148不是此target的import，不因它们已接受便把其private helper视为可调用API。

## 八、冻结及行政事实

local／remote scope70同37行7667B，SHA256=66a18870fa58a2f4ca0853c5fe9ac0f6d27b292972a8feb6f6c089c0c502d6b9。
报告内完整TYPE与该scope fence逐字一致；scope的三imports／namespace／open/scopes／noncomputable上下文足以解释现有CLM、矩阵和导数记号。
服务器实际Mathlib HEAD=807d3836b165983210ee2ecf3cd28f239436949c。
lean-toolchain SHA256=d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4。
lake-manifest.json SHA256=40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。
本次实际Git观察：branch feat/oq3-source-geometric-scale，HEAD0e29e2642e22edf7da734817a2fc8909a304a4b8，status--short为空。
U19c SourceLogPartitionDerivatives.lean／run Audit.lean／receipt.json实际均不存在；不把未来source、分支、proof或内核结果预报为既有事实。
root随后v37行政整合不改变当前冻结scope／8项源／pins；本报告仍绑定实际B148 checkout，不fetch/rebase/reset以吸收新基线。
本门未启动任何Lean、probe、重编译或重跑Audit／smoke；未修改source、scope、旧票、共享cache、pins或其他工作者文件。

## 九、最终裁决与直接承重边界

STATUS: CORRECT

JUSTIFICATION: 完整公开TYPE与真实源的逆倾斜梯度及Covπ(X,X²) Hessian含义一致。hw/hm真实产生同π/P概率、全部真指数／多项式可积及每参数严格正配分；当前公开积分微分API在共同参数邻域可由明确的AE统一算子范数常数主控满足。全参数一阶公式先识别真实fderiv K，再对归一化矩的CLM值梯度求导，确实可得到第二个完整Fréchet导数，所有四个系数经同一实际倾斜法则与真L²矩识别为所指定D，无新增手工解析假设、非退化前提或private依赖。当前静态imports与缓存无缺项，未发现需修订的声明或环境阻塞。

原target→消除义务：R1鞍点的实际梯度／Hessian身份，此声明要求并可在现有环境证明其真实Fréchet解析内容；不是一阶值计算或二阶形式多项式包装。
直接consumer：root统一canonical K的同law鞍点／Hessian身份桥，随后把U19b已有字面几何常数等式接到同一D；本模块保持0publicDEF，不与root定义竞争。
剩余：尚无本target实现或kernel/Audit凭据；完整actual proof、所有private/generated实际TYPE及传递公理仍须下一独立proof门审。root canonical K/domK/扩展值sup桥、均值映射局部逆、全局鞍点性质和A/B/C/D原始组装均不由本声明门闭合；general KL9/10亦未声称。全部root A/B/C/D保持OPEN。
