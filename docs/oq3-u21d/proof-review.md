# U21d CompactTiltCovarianceSpectrum 完整独立证明审查

STATUS: IN_PROGRESS

## 不可改写的actual全所属TYPE盲审前缀

本前缀先只读取实际7项owner TYPE及全部续行，不读实现、receipt、作者证明说明或旧声明票解释。下录实际类型是本次独立逐义核查的起点；当前不据其存在便判断证明正确。0公开DEF，下面逐项保全7项THM。

```text
DECL _private.Shao.OQ3.CompactTiltCovarianceSpectrum.0.Shao.OQ3.bounded_parabola_memLp
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (M : ℝ),
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ M) → MeasureTheory.MemLp (fun x => x) 2 mu ∧ MeasureTheory.MemLp (fun x => x ^ 2) 2 mu
AXIOMS [propext, Classical.choice, Quot.sound]

DECL _private.Shao.OQ3.CompactTiltCovarianceSpectrum.0.Shao.OQ3.quadratic_variance_eq
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  MeasureTheory.MemLp (fun x => x) 2 mu →
    MeasureTheory.MemLp (fun x => x ^ 2) 2 mu →
      ∀ (xi eta : ℝ),
        ProbabilityTheory.variance (fun x => xi * x + eta * x ^ 2) mu =
          xi ^ 2 * Shao.OQ3.parabolaCovariance mu 0 0 + 2 * xi * eta * Shao.OQ3.parabolaCovariance mu 0 1 +
            eta ^ 2 * Shao.OQ3.parabolaCovariance mu 1 1
AXIOMS [propext, Classical.choice, Quot.sound]

DECL _private.Shao.OQ3.CompactTiltCovarianceSpectrum.0.Shao.OQ3.variance_lower_of_measure_lower
TYPE ∀ (mu nu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.IsProbabilityMeasure nu]
  (f : ℝ → ℝ),
  MeasureTheory.MemLp f 2 mu →
    MeasureTheory.MemLp f 2 nu →
      ∀ (m : ℝ),
        0 ≤ m → ENNReal.ofReal m • mu ≤ nu → m * ProbabilityTheory.variance f mu ≤ ProbabilityTheory.variance f nu
AXIOMS [propext, Classical.choice, Quot.sound]

DECL Shao.OQ3.parabolaCovariance_pos_of_weakCramer
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (M : ℝ),
  0 ≤ M →
    (∀ᵐ (x : ℝ) ∂mu, |x| ≤ M) →
      ∀ (beta c R : ℝ),
        0 < c →
          (∀ (xi eta : ℝ),
              R < √(xi ^ 2 + eta ^ 2) →
                ‖Shao.OQ3.jointCharacteristic mu xi eta‖ ≤ 1 - c * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)) →
            0 < Shao.OQ3.parabolaCovariance mu 0 0 ∧
              0 < Shao.OQ3.parabolaCovariance mu 1 1 ∧
                0 < (Shao.OQ3.parabolaCovariance mu).det ∧
                  ∀ (xi eta : ℝ),
                    xi ≠ 0 ∨ eta ≠ 0 →
                      0 <
                        xi ^ 2 * Shao.OQ3.parabolaCovariance mu 0 0 +
                            2 * xi * eta * Shao.OQ3.parabolaCovariance mu 0 1 +
                          eta ^ 2 * Shao.OQ3.parabolaCovariance mu 1 1
AXIOMS [propext, Classical.choice, Quot.sound]

DECL _private.Shao.OQ3.CompactTiltCovarianceSpectrum.0.Shao.OQ3.quadratic_variance_upper._simp_1_1
TYPE ∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), (a ^ m) ^ n = a ^ (m * n)
AXIOMS []

DECL _private.Shao.OQ3.CompactTiltCovarianceSpectrum.0.Shao.OQ3.quadratic_variance_upper
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (M : ℝ),
  0 ≤ M →
    (∀ᵐ (x : ℝ) ∂mu, |x| ≤ M) →
      ∀ (xi eta : ℝ),
        ProbabilityTheory.variance (fun x => xi * x + eta * x ^ 2) mu ≤ (M ^ 2 + M ^ 4) * (xi ^ 2 + eta ^ 2)
AXIOMS [propext, Classical.choice, Quot.sound]

DECL Shao.OQ3.exists_compact_tilted_covariance_spectral_bounds
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (M : ℝ),
  0 ≤ M →
    (∀ᵐ (x : ℝ) ∂mu, |x| ≤ M) →
      ∀ (K : Set (ℝ × ℝ)),
        IsCompact K →
          ∀ (u0 v0 beta c R : ℝ),
            0 < c →
              (∀ (xi eta : ℝ),
                  R < √(xi ^ 2 + eta ^ 2) →
                    ‖Shao.OQ3.jointCharacteristic (mu.tilted fun x => u0 * x + v0 * x ^ 2) xi eta‖ ≤
                      1 - c * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)) →
                have mu0 := mu.tilted fun x => u0 * x + v0 * x ^ 2;
                have D0 := Shao.OQ3.parabolaCovariance mu0;
                ∃ m,
                  0 < m ∧
                    m ≤ 1 ∧
                      have lambdaMin := m * D0.det / (D0 0 0 + D0 1 1);
                      have lambdaMax := 2 * (M ^ 2 + M ^ 4) + 1 + lambdaMin;
                      0 < lambdaMin ∧
                        lambdaMin < lambdaMax ∧
                          0 < m ^ 2 * c / 2 ∧
                            ∀ p ∈ K,
                              have mup := mu.tilted fun x => p.1 * x + p.2 * x ^ 2;
                              MeasureTheory.IsProbabilityMeasure mup ∧
                                (∀ᵐ (x : ℝ) ∂mup, |x| ≤ M) ∧
                                  MeasureTheory.MemLp (fun x => x) 2 mup ∧
                                    MeasureTheory.MemLp (fun x => x ^ 2) 2 mup ∧
                                      ENNReal.ofReal m • mu0 ≤ mup ∧
                                        (∀ (xi eta : ℝ),
                                            lambdaMin * (xi ^ 2 + eta ^ 2) ≤
                                                xi ^ 2 * Shao.OQ3.parabolaCovariance mup 0 0 +
                                                    2 * xi * eta * Shao.OQ3.parabolaCovariance mup 0 1 +
                                                  eta ^ 2 * Shao.OQ3.parabolaCovariance mup 1 1 ∧
                                              xi ^ 2 * Shao.OQ3.parabolaCovariance mup 0 0 +
                                                    2 * xi * eta * Shao.OQ3.parabolaCovariance mup 0 1 +
                                                  eta ^ 2 * Shao.OQ3.parabolaCovariance mup 1 1 ≤
                                                lambdaMax * (xi ^ 2 + eta ^ 2)) ∧
                                          ∀ (xi eta : ℝ),
                                            R < √(xi ^ 2 + eta ^ 2) →
                                              ‖Shao.OQ3.jointCharacteristic mup xi eta‖ ≤
                                                1 - m ^ 2 * c / 2 * (√(xi ^ 2 + eta ^ 2)).rpow (-beta)
AXIOMS [propext, Classical.choice, Quot.sound]
```

## 独立完整量词／假设／结论盲译及待核门

1. bounded_parabola_memLp是私有定理：对任意真实实概率mu、任意有限实M，仅从AE |X|≤M同时推出X和X²在同mu下真MemLp2。实际TYPE没有M≥0前提；实现须从真支配或概率非空性处理负M，不能暗加。
2. 两个MemLp中的指数均是2，第二函数是X²；不是只证明X²真L¹或另一个代理law。
3. quadratic_variance_eq是私有定理：对同mu真概率，输入X/X²各真L²，任意xi/eta，实际Var(xiX+etaX²)恰为actualD的二次型，系数为xi²、2xi eta、eta²。
4. 必须在真实方差／协方差展开前使用这些L²门，核D01与交叉项方向及2因子，不能只靠形式矩阵名称。
5. variance_lower_of_measure_lower是私有定理：mu和nu都是真概率，f在两律下真L²，m≥0且ofRealm•mu≤nu，推出m Var_mu f≤Var_nu f。
6. 这个实际TYPE允许m=0，也允许m作为任意非负有限实数；它没有输入两均值相同。不能把不成立的无条件variance测度单调当证明，须核真实中心校正／平方可积和有限实标量转换。
7. 第一公开定理保留真概率mu、M≥0、AE界及任意实beta/c/R和c>0。没有手工cov正定、正原子或非退化前提。
8. hWC是实际jointCharacteristic、字面欧氏sqrt(xi²+eta²)及真实rpow；R、beta可以负。外区真实相位及正半径选择须独立核，不能靠零频率或不恰当rpow0。
9. 结论同时给同mu D00>0、D11>0、actualdet>0，及全部非零实方向actual二次型>0。
10. M=0仍在类型内；必须让输入不相容的情形自然推出，不能除M、xi或eta。
11. generated quadratic_variance_upper._simp_1_1是宇宙多态通用Monoid恒等式：forall a,m,n,(a^m)^n=a^(m*n)。没有Measure、概率、M实界或协方差假设。
12. 该生成项实际AXIOMS[]，不能按生成名字猜为旧parabolaCovariance等式，也不能统一写全部项都依赖三公理。
13. quadratic_variance_upper是私有定理：同真概率mu、M≥0及AE界，任意xi/eta的真实投影方差≤(M²+M⁴)(xi²+eta²)。
14. 这个实际helper比冻结公开上界的2(M²+M⁴)+1+lambdaMin更强。须核实际Cauchy／平方支配因子，不能只复用粗略因子2路线而忽略helper强度。
15. 第二公开定理对同基础mu/M、任意紧K、任意实参考u0/v0/beta/c/R及c>0成立。输入只给参考真实quadratic tilt上的WC。
16. let mu0固定为mu.tilted(u0X+v0X²)，D0固定为其实际协方差；参考不要求属于K，也不输入参考概率或可积。
17. 存在同一个实m>0且m≤1先于全部p、xi、eta。不能从不同生产者分别取m再混代。
18. 内部lambdaMin=m detD0/(D000+D011)，lambdaMax=2(M²+M⁴)+1+lambdaMin；分母、det正性和实际矩阵对称必须生产而非假设。
19. 输出全局lambdaMin>0、lambdaMin<lambdaMax及m²c/2>0，K空时这些仍必须成立。
20. 每个p∈K令mup=同mu的实际quadratic tilt；须输出真概率、同M AE界、X/X²真MemLp2。
21. 每个mup还输出ofRealm•mu0≤mup、actualD_mup二次型的共同lambdaMin/lambdaMax双界，以及same beta/R的actualWC新常数m²c/2。
22. 这些输出都在同m内，不许另选law或假装倾斜后均值不变；不要求p联合可测因为没有对p积分。
23. 外部hWC没有beta≥0/R≥0，故已有只接非负符号的标准化consumer不能被提前当本定理证明。
24. 所有tilt均须先真exp Integrable、正normalizer和概率，排除不integrable时tilted零测度总化捷径。
25. 真L²到真平方／乘积可积须先于积分线性、variance展开、测度积分单调和实标量化；不允许以∞.toReal或不可积积分默认0完成。
26. 全7实际TYPE中4私有、2公开、1生成，0DEF；当前显示6项标准三公理，生成通用pow_mul无公理。最终须将实际owner覆盖与全源码联合核，不凭namespace前缀漏项。
27. 必查实际det/trace恒等式、正trace后清分母，及公开lambdaMax余量；包括zero frequency、K空、参考不在K、M0、m0helper、beta0/R0和任意负beta/R。
28. 此前缀只保全实际陈述与独立疑点，不是最终proof结论，也不将scope或作者准备状态当证明。

--- END IMMUTABLE ACTUAL-TYPE BLIND PREFIX ---

## 最终独立裁决与审查顺序

STATUS: CORRECT。

本报告先保全实际7项owner完整TYPE／公理及独立盲译，再读完整285行实现、冻结scope80、R2原件和实际承重公开库，最后才读receipt、build／Audit与行政记录。上方143行／10542B盲审前缀原字节保留；SHA256 a7c9bbccdedc66b6770bdd0ee211023d2c86d59b668fb322448555b467eda94b。开头IN_PROGRESS为历史检查点，最终裁决在本节及报告末尾。

本裁决是实际实现的完整proof／来源／owner-TYPE／机械绑定审查，不沿用旧声明CORRECT便批准，也不以作者receipt里的数学叙述或kernel成功代替逐义验证。没有发现需要修订的数学、类型、概率／可积或环境缺口。

## 1. 精确冻结对象及来源对应

实际实现为Shao.OQ3.CompactTiltCovarianceSpectrum，完整285行／14942B，SHA256 99b8b9b20f1860ddd7890d8b4d317825ce76572e1c0d209d6843340a33b0c634。本地draft、remote ownworktree和run/source-01.lean字节一致。0公开DEF，2公开THM，4私有THM，1生成THM。

冻结scope80为eightieth-unit-scope.md，83行／7782B，SHA256 b30cd580532e687dc5bc385a06965281e93ea55cc8160363824c5ed70d655b83。逐空白归一化比较两条actual公开完整签名均匹配冻结TYPE；原有mu概率、M/hM/hb、任意实beta/R、参考参数、K紧性、全部let和合取范围均未改变。

实际第1–2行精确imports仍为CompactTiltWeakCramer和RegularCovariance；第12–15行namespace/open/scoped Matrix ENNReal NNReal/noncomputable与冻结环境一致。没有新公共定义、caller谱界、正原子、K非空或参考属于K等输入。

R2原件C:/game/shao/current/oq3/proofs/r2/report.md，SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55，已读38–60、74–76、83–92、343–373行。第38–60行要求actual倾斜协方差的统一谱(2)，第83–92行消费它完成真实线性标准化，第343–369行从单点WC与紧倾斜测度下界生产same-beta族WC。

本节点在同一个实际mu0和所有实际mup上生产明确共同谱界。它消除标准化消费者所需的一项真实前提，来源拟合为充分标准界；不宣称谱常数最优、beta阈值最优或一般无界情形已有相同测度下界。R2第371–373行对无界情形的保留没有被本实现删去。

## 2. 私有bounded_parabola_memLp：第17–27行

第20–22行直接对真实连续id及AE norm界调用MemLp.of_bound，得到同mu下X真L²。固定Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean第631–633行实际API只需IsFiniteMeasure、AEStronglyMeasurable和有限实C的AE范数界，不要求额外C≥0。

因此这个私有TYPE未列M≥0不是隐藏错误。其API实际以C≤|C|传给memLp_const；即使M负，给定AE范数界仍是合法输入。公开目标仍保留冻结hM；不存在删除公开假设或从空概率测度偷取结果。

第23–25行在每个满足|x|≤M的点用abs_pow和pow_le_pow_left₀得到|x²|≤M²。其单调门从0≤|x|及该点上界得到，不需要除M。第26–27行以真实连续平方函数再调用of_bound，生产X²真L²。

两输出均是实际mu上的MemLp2，而非X²仅L¹，也不是另一law。后续所用integrable_sq真门由Mathlib/MeasureTheory/Function/L2Space.lean第42–43行MemLp.integrable_sq生产。

## 3. 私有quadratic_variance_eq：第29–45行

第36–40行按RegularCovariance.lean第20–24行实际定义展开：D00=Var X，D01=D10=Cov(X,X²)，D11=Var(X²)。

第41行先将h1/h2真实L²通过const_mul生产两个投影项L²，才用ProbabilityTheory.variance_fun_add。固定Variance.lean第263–274行的实际加法定理要求这两个真L²门，内部用真实covariance线性及对称性展开。

第42–44行分别用variance_const_mul和covariance_const_mul_left/right，最后ring整理，精确得到xi²D00+2xi eta D01+eta²D11。交叉方向是同一个Cov(X,X²)，两个标量各一次，没有转置、负号或2因子错误。

variance_const_mul及covariance标量公式本身可有总化版本，但此处其所有操作对象已由输入真L²覆盖；证明没有靠不可积方差／协方差默认值完成实际二次型身份。

## 4. 私有variance_lower_of_measure_lower：第47–65行

该helper实际是两真实概率law上的方差比较。第52行z定义为nu真实均值；hnu真L²在有限概率下保证其L¹，故z不是不可积积分默认0。

第53–54行先以两律各自的hmu/hnu减去真L²常数，得到g=f-z在mu/nu下均真L²。两均值不被假设相等。

第55–60行对mu上的g调用真实variance_eq_sub，再用variance_sub_const hmu.aestronglyMeasurable z把Var_mu(g)还原为Var_mu(f)。因此
  Var_mu(f)=∫(f-z)²dmu-(∫(f-z)dmu)²≤∫(f-z)²dmu。

固定Variance.lean第226–228行variance_eq_sub要求真概率及真L²；第254–256行variance_sub_const在真概率下合法。实现均已满足，且使用的是非负真实均值平方。这是完整中心校正，未误用“variance对测度无条件单调”。

第61–62行调用Bochner/Basic.lean第621–637行integral_mono_measure：小测度为ofReal(m)•mu，大测度为nu；平方逐点非负，且hgnu.integrable_sq先给大测度下真实可积。实际API内部也从mono_measure取得小测度下真实可积。

第63行integral_smul_measure把左积分换为(ofReal m).toReal倍真实积分，再以hm:m≥0合法toReal_ofReal，得到m系数。m为有限实数，ofReal m≠∞；没有利用一般∞标量的积分总化分支。m=0同样合法，helper不除m。

第64行用hnu.aemeasurable的variance_eq_integral，将右侧精确写成∫(f-E_nu f)²dnu。第65行用hm保持乘法方向，再传递第61行比较，完成m Var_mu f≤Var_nu f。

以上各真实平方可积、方差展开和积分单调门先于相应操作。没有把两law的中心混同，也不需要未声明的RN导数、SFinite额外输入或共同均值。

## 5. 私有quadratic_variance_upper及其生成项：第67–97行

第72–74行先生产X/X²和F=xiX+etaX²真L²。第77–82行从AE |X|≤M依次得到X²≤M²、X⁴≤M⁴，所有平方单调门均有非负底数。

第83–85行使用真实非负平方(xi*x²-eta*x)²，精确给出二维Cauchy恒等式差：
  (xi²+eta²)(x²+x⁴)-(xi*x+eta*x²)²=(xi*x²-eta*x)²≥0。

因此第86–88行得到更强的F²≤B*(xi²+eta²)，B=M²+M⁴，不需要粗略因子2。此处不是把冻结公开上界的2B误用于更强helper。

第89–92行先有hf.integrable_sq和常数函数真实Integrable，才用integral_mono_ae并以概率总质量1消去常数积分。第93–97行在真L²后variance_eq_sub减去非负均值平方，得Var F≤B*(xi²+eta²)。

实际generated quadratic_variance_upper._simp_1_1的完整TYPE为∀{M:Type u}[Monoid M](a:M)(m n:Nat),(a^m)^n=a^(m*n)，AXIOMS[]。它对应第82行←pow_mul的通用简化，含完整宇宙和Monoid实例，不是实M界、概率前提或旧协方差定义式。

私有上界hM在源码未显式使用，因为本证明从实际AE界及偶次幂即可；保留冗余输入与冻结公开门一致，unused提示不造成语义缺口。

## 6. 第一公开定理：第99–180行

第113行先取得真L²，第118–119行同mu上的F真L²。第120–124行若不能Var F>0，则用variance_nonneg与not_lt推出真实Var F=0，再以ae_eq_integral_of_variance_eq_zero hf得到F=E_mu F AE。

固定Variance.lean第162–172行的零方差AE定理确实要求MemLp2，并在内部先证明中心平方的真实Integrable；本实现实际提供hf。没有把不可积时Var总化为0当退化证据。

第125–129行由xi≠0∨eta≠0和平方严格正生产rho=sqrt(xi²+eta²)>0。第130–131行T=(|R|+1)/rho>0，先正分母后除法；未除M、xi或eta。

第132–138行以sqrt_mul(sq_nonneg T)、sqrt_sq(hT.le)及非零rho消去除法，精确得到新欧氏半径sqrt((Txi)²+(Teta)²)=|R|+1。这是真实实数距离，非圆周距离或错误Pi最大范数。

第139–143行在F=E_mu F的同一AE集上展开实际jointPhase，完成Txi*x+Teta*x²=T F(x)，从而相位AE等于真实常数exp(i T E_mu F)。

实际JointNonlattice.lean第20–24行的jointCharacteristic就是该jointPhase的真实复Bochner积分；第29–35行已公开证明任意频率相位在真实概率下真Integrable，范数恒为1。因此第144–151行integral_congr_ae及概率常数积分不是不可积积分默认0捷径。

第152–154行Complex.norm_exp_ofReal_mul_I给实际特征模=1。第155–157行由le_abs_self R和+1使半径严格大于任意实R；R负或0均无遗漏。

第158–160行在真实严格正半径上使用Real.rpow_pos_of_pos，固定Pow.Real.lean第116–117行对任意实指数均成立。因此c>0给严格正缺口，对任意beta（含0或负）都不需要额外符号假设。

第161–163行将actual hWC代入该真实外区频率，与模1和正缺口矛盾。第164行通过已核私有quadratic_variance_eq还原actual二次型，得到所有非零方向hpos。

第165–169行设实际a,b,d，于(1,0)/(0,1)生产a>0、d>0。第170–176行在(-b,a)取值，因a>0方向真实非零，得到a*(a*d-b²)>0并以a正排除错误符号分支，推出a*d-b²>0。

第177–180行用Matrix.det_fin_two和actualD10=D01的定义相等性将该严格值绑定actualdet。四个公开合取均实际完成；没有把det>0单独当任意矩阵正定，顺序是先全部方向正再det。

第一目标hM未显式使用是本证明更弱前提也能工作的冗余binder，不是被删去的输入。M0时WC与退化概率不相容，证明仍全程合法，无除M或隐藏正原子。

## 7. 第二公开定理：第182–282行

第215–216行mu0／D0精确为冻结let。第217–218行先调用已接受公开quadratic_exp_integrable_of_ae_abs_le mu M hM hb u0 v0，再由isProbabilityMeasure_tilted生产参考真实概率。

已独立读TiltedMeasureDomination.lean第17–34行的实际证明：连续exp的固定AE有限界给真实Integrable，任意实u/v均可；不是局部小参数结论。固定Tilted.lean第126–136行在NeZero mu与真实指数可积后用integral_exp_pos生产正normalizer并证明倾斜总质量1。基础真概率给NeZero。

第219–220行用tilted_absolutelyContinuous及实际AbsolutelyContinuous.ae_le把原AE |X|≤M转移给mu0。第221行继而生产参考X/X²真L²，第222–224行消费第一公开定理，得到同D0的a/d/det正性及trace>0。

第225–227行用actual D0对称和det_fin_two产生det公式，而非引入任意辅助矩阵。第228–229行只一次调用公开exists_compact_tilted_weakCramer_bound，取同一m、hm、hm1、hnewc和全族hfamily。

已读实际CompactTiltWeakCramer全部94行及完整公开TYPE，其输入正是本mu/M/hb/K/hK/参考参数/beta/c/R/hWC；任意实beta/R合法。它的m=min(m0,1)同时给真实测度下界、平方模缺口和rawWC。当前实现既未另选m，也未重新选择mu0或law。

第230–235行lo=m*detD0/traceD0，B=M²+M⁴，hi=2B+1+lo。只有在hm>0、hdet>0、htrace>0后才div_pos生产lo>0；B≥0后线性整理给lo<hi。常数和m全在p与频率之前固定。

第236–245行对每个p∈K建立actual mup。第239–240行同样先任意参数exp真实Integrable再真概率，第241–243行同AE界及两个L²。hfamily p hp在第244行给同m的真实hdom和hwc；_hgap不被重复证明或当新输入。

第245行输出的概率实例、AE、L²、hdom及最终WC均属于这个同mup。参考(u0,v0)不要求在K；没有任何Nonempty K抽取。

第247–251行rr是xi²+eta²≥0；q0/qp分别是actual D0/D_mup同系数二次型。第252–257行ring核实真实恒等式
  trace(D0)*q0-det(D0)*rr=(D000*xi+D001*eta)²+(D001*xi+D011*eta)²。

第258–263行在已经严格正的htrace后用div_le_iff₀，非负两平方推出(detD0/traceD0)*rr≤q0。未提前清不明符号分母，也未假设谱下界。

第264–270行生产两law上的同一个F真L²，再调用私有variance_lower_of_measure_lower mu0 mup ... m hm.le hdom。通过两个真实quadratic_variance_eq还原m*q0≤qp。这就是经过合法中心校正的下界，不是假定倾斜均值相同。

第272–277行把lo*rr精确重排为m*((det/trace)*rr)，以同hm.le保持乘法方向，再传递实际方差下界，得到冻结lambdaMin谱下界。

第278–282行先调用已核更强私有upper得qp≤B*rr，再由hB≥0、hlo>0得B≤hi，乘rr≥0合法放宽到qp≤hi*rr。冻结lambdaMax的额外2与+1得到完整保留，没有以helper较强输出替换公开类型。

至此每个p∈K的真实prob／AE／L²／measure lower／共同谱双界／same-beta rawWC全在同一个m内完成。没有caller谱、原子正性、参考归属K或参数联合可测输入。

## 8. 边界及真实量词总核

K空：第217–235行仍先生产参考真概率、D0正性和同m全局正lambda，不依赖p存在；hfamily的共同m来自接受生产者的紧集min处理。因此空K输出非真空的全局正性成立。

M0：所有证明保留它，不除M；WC若与该支撑退化矛盾由第一定理的真实AE常数论证给出。私有bounded helper甚至不需要hM，负M假设的逻辑处理也不破坏公开定理。

beta/R任意实：第一定理只在严格正半径用rpow严格正；第二定理消费159只需sqrt底数rpow非负。没有把标准化consumer169所需的beta/R非负门偷偷加入当前证明。

xi=eta=0：谱双界两边均0，rr≥0允许0；只有第一条非零方向严格正分支需要rho>0。m=0允许于私有方差比较helper，但主输出严格m>0来自同159生产者。

参考不在K、退化caller未手给SPD、每个倾斜均值不同、所有有限实中心均完整保留。没有积分／variance总化、∞.toReal、log0、分母0或非负平方换方向的捷径。

## 9. 全部actual owner TYPE与传递公理覆盖

先读的actual-types.txt完整99行／5853B，SHA256 5b1f060217abea8a6d7459e0934cf6f6af54ab9e68a5e32f75102c47c60bf270，已原样保全在盲前缀。随后从server audit.log选取全部DECL／TYPE完整续行／AXIOMS逐项比较，7条规范空白后完全一致，无⋯或…省略。

实际7项逐项结论为：

1. private bounded_parabola_memLp：实际TYPE为任意M及AE支撑生产两个真L²；第17–27行实现匹配；公理[propext,Classical.choice,Quot.sound]。
2. private quadratic_variance_eq：两个实际L²输入到同mu实际二次型身份；第29–45行匹配；标准三公理。
3. private variance_lower_of_measure_lower：两实际概率／两真L²／m≥0及测度下界到方差比较；第47–65行匹配；标准三公理。
4. public parabolaCovariance_pos_of_weakCramer：完整任意beta/R及四合取，actual TYPE匹配冻结；第99–180行完成；标准三公理。
5. generated private quadratic_variance_upper._simp_1_1：宇宙多态∀Monoid的pow_mul，完整实例／自然数参数已读；第82行简化来源；AXIOMS[]。
6. private quadratic_variance_upper：真实概率／支撑到更强B谱上界；第67–97行完成；标准三公理。
7. public exists_compact_tilted_covariance_spectral_bounds：全部mu0/D0/m/lambda/mup长let与合取已读；第182–282行完成；标准三公理。

总计7owned=7THM=2public+4authored private+1generated；0DEF。不是7项都依赖完整三公理，生成项没有公理。没有预猜旧namespace parabolaCovariance.eq_1或按名称前缀遗漏所属常量。

已读实际Audit.lean全部45行：它通过env.getModuleIdxFor?及env.header.moduleNames精确匹配owner Shao.OQ3.CompactTiltCovarianceSpectrum，对所有所属常量逐项拒绝isAxiom并collectAxioms白名单检查，再报告全部计数。不是只审两个public的命名列表。

完整285行正文与该owner枚举联合检查，没有额外隐藏DEF／private／生成义务；没有sorry/admit、新axiom、native_decide、unsafe、implemented_by或证明设置弱化。

## 10. 机械证据（数学判断之后）

实际run目录为/root/rivermind-data/shao-lean-20261021/runs/oq3/u21d-20261021；真实日志文件名为小写audit.log。本审查只读取server上的所需TYPE／摘要及hash，没有把完整原始build／Audit日志复制为本地文件。

源本地draft、remote worktree和source-01.lean均为285行／14942B、99b8b9b20f1860ddd7890d8b4d317825ce76572e1c0d209d6843340a33b0c634；scope两端b30cd580...655b83一致；actual-types两端5b1f0602...60bf270一致。正式receipt两端135行／7122B、76dfbe0bd2a3590f635c2f5a694cf9d445e8da18dada1e3fa0551e032b377da5一致。

作者首次完整strict build01 exit0，5.446220692s；唯一完整285行source快照，无失败、partial或成功重跑。build-history.json SHA256 8ea36d8be3cf2f449098080de84bf21e29c441110f4d4ba24e12cd1d725aaed7仅一条COMPLETE_SUCCESS记录，源hash与当前一致。

build-01.log实际28行／1433B，SHA256 9bf40faca95d17d491f79dcc23a03e481bc1a3190916b4f620408460419f625b，非空。真正4条warning为第68和101行hM未显式引用，以及217和239行letI风格提示；提示文字内部再出现warning:不另算警告。没有error或coded error。没有为清理style而修改／重跑成功源。

首owner Audit exit0，5.512016213s；Audit.lean 45行／1961B、SHA f7bbfd69e07ace9cd69873798bcd839cd654543650980cc08ddcdc57e7c38863；audit.log 98行／5961B、SHA c9e6f8a849d04f0c62e875b99d51fa8e3694d65a6b1c9ea9cb629e38f47b17ae。现有摘要为0冻结DEF、2冻结THM、7全THM／全声明、AXIOM_GATE PASS，与实际逐项读取一致。

Audit打印选项仅pp.deepTerms true／pp.maxSteps1000000，用于完整TYPE输出，不是proof设置。记录的构建／Audit均CPU14–17、native memory8192MiB、j4、autoImplicit=false；没有ulimit-v或外部CPU0–9／80GiB任务干预。

正式prerequisite-hashes.json 18项／1917B，文件SHA acbcb4647dcf10974d8874e6972453cd8d5a1d1c51c9fbccd954e4db0bf5ac2e；规范相对路径键compact SHA e03503582ed63f55f9629bcbea056930e068049a2ad4df885c6399bee290659a，独立重算与声明门接受的v42子字典相同。本门复用已接受18前置闭包、对象、pins和cache证据，不重新扫描Mathlib／稳定源或重哈希旧对象。

## 11. 分支及preflight真实历史

当前实际分支feat/oq3-compact-tilt-covariance-spectrum，HEAD 7832c37251145161d095daac02e3506db90b3910，为正式v42接受checkpoint。git status仅本新Shao/OQ3/CompactTiltCovarianceSpectrum.lean untracked，没有本模块commit或PR。

preflight-history.json 10行／478B，SHA 4b9b1da54a06c3a0497b157067f029ff2ed06cedcbf16961998ac48f1fcdf56d，保存初次git for-each-ref的partial component selector返回0导致guard失败。其时未switch／写source／启动Lean，不能把它计为build失败或partialsource。

随后branch-created.json SHA4ebf5958bef705fa85cf90c95c71776fc8523be720d99df3cf1a0361be1ee53d保存以原权威77字典加169逐项核78refs后正常建branch的记录：parent/head均7832...，all78_preserved=true、no_merge_rebase_reset=true，并保留完整78项旧ref字典。当前HEAD／分支实际观察与该记录一致。

没有重写169、旧159或其他冻结head；此处从v42正常新branch的事实与声明门早先169旧树缺159源的观察不冲突。未复制cache、切换依赖版本、重跑root gate或新增Lean检查。

## 12. 原目标→已消除义务→直接consumer→仍剩范围

本实现实际消除的是：从同一有界基础law和一个真实参考quadratic tilt的WC，生产同一紧倾斜族的真实概率／L²／共同协方差谱(2)及同m²c/2原始WC。常数明确且独立于p和频率；不再把实际谱作为caller手工输入。

直接consumer为已独立接受PR169的uniform_covariance_whitened_moments_weakCramer。未来在诚实保留该consumer的beta／R条件后，本节点的actual谱与159的WC可供实际白化、均值0、协方差I、统一欧氏矩和标准化WC装配。当前模块没有提前调用或改写169接口，也没有把单个helper包装宣称为整根完成。

本节点不是完整bounded C的联合装配／root正式验收；这仍是后续直接承重工作。一般unbounded B其余分析、D、均值逆、未声明Hessian桥、Edgeworth／胞重建／Laplace或远概率结论没有由本节点自动完成。A已正式v40 CLOSED；169当前仍pending root，B/C/D OPEN，不提前关闭。

最终STATUS: CORRECT。两冻结公开完整目标在实际285行实现中均真实证明，4私有helper及1生成项已逐义核，全部7owner TYPE／传递公理和首次机械历史一致；没有发现需要修订的数学或环境缺口。

收尾约束：本报告稳定上传并核双端后，本reviewer停止，不启动下一单元／研究／写入；不自行commit或PR。整个审查没有启动Lean／Audit／probe、修改生产源／scope／旧票／receipt／共享缓存或触及外部任务。最终交付时所有工具调用均已闭合，无本reviewer后台工具或写入在途。
