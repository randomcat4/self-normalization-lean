# U21d CompactTiltCovarianceSpectrum 独立声明／来源／API审查

STATUS: IN_PROGRESS

先行不可改写盲译前缀：只读取冻结scope80两个Lean fence的两imports／两完整TYPE与header；未读说明、来源、作者路线、receipt或候选metadata。此门只审声明／来源／静态环境，不是实现／proof门。

## 完整环境与两TYPE保全

拟模块Shao.OQ3.CompactTiltCovarianceSpectrum；namespace Shao.OQ3；open MeasureTheory；open scoped Matrix ENNReal NNReal；noncomputable section。0公开DEF／2公开THM。

```lean
import Shao.OQ3.CompactTiltWeakCramer
import Shao.OQ3.RegularCovariance
```

```lean
theorem parabolaCovariance_pos_of_weakCramer
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic mu xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    0 < parabolaCovariance mu 0 0 ∧
      0 < parabolaCovariance mu 1 1 ∧
      0 < (parabolaCovariance mu).det ∧
      ∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        0 < xi ^ 2 * parabolaCovariance mu 0 0 +
          2 * xi * eta * parabolaCovariance mu 0 1 +
          eta ^ 2 * parabolaCovariance mu 1 1

theorem exists_compact_tilted_covariance_spectral_bounds
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ) (hc : 0 < c)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    let D0 : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance mu0
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      let lambdaMin : ℝ := m * D0.det / (D0 0 0 + D0 1 1)
      let lambdaMax : ℝ := 2 * (M ^ 2 + M ^ 4) + 1 + lambdaMin
      0 < lambdaMin ∧ lambdaMin < lambdaMax ∧ 0 < m ^ 2 * c / 2 ∧
        ∀ p ∈ K,
          let mup : Measure ℝ := mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
          IsProbabilityMeasure mup ∧ (∀ᵐ x ∂mup, |x| ≤ M) ∧
            MemLp (fun x : ℝ => x) 2 mup ∧
            MemLp (fun x : ℝ => x ^ 2) 2 mup ∧
            (ENNReal.ofReal m • mu0 ≤ mup) ∧
            (∀ xi eta : ℝ,
              lambdaMin * (xi ^ 2 + eta ^ 2) ≤
                  xi ^ 2 * parabolaCovariance mup 0 0 +
                    2 * xi * eta * parabolaCovariance mup 0 1 +
                    eta ^ 2 * parabolaCovariance mup 1 1 ∧
                xi ^ 2 * parabolaCovariance mup 0 0 +
                    2 * xi * eta * parabolaCovariance mup 0 1 +
                    eta ^ 2 * parabolaCovariance mup 1 1 ≤
                  lambdaMax * (xi ^ 2 + eta ^ 2)) ∧
            ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
              ‖jointCharacteristic mup xi eta‖ ≤
                1 - (m ^ 2 * c / 2) *
                  Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

## 独立逐量词／实际对象／边界盲译

1. 第一目标对同一实概率mu、有限实M≥0及其真实AE |X|≤M成立，另有任意实beta/c/R和c>0。
2. 只有c要求严格正，第一目标没有beta≥0或R≥0；不能在证明时默加这两条件。
3. hWC给同mu实际jointCharacteristic在字面欧氏半径sqrt(xi²+eta²)>R的全频率上界1−c*rho^(−beta)。
4. 结论是同mu实际parabolaCovariance的两个对角严格正、真实det严格正，且每个非零(xi,eta)的实际协方差二次型严格正。
5. 没有手给正原子／非退化／hCovPos。必须从真实bounded积分与WC排除非零居中二次式AE常数；不能只用variance总化非负。
6. 第一目标的真L²／积分／AE零平方门须由M界生产，不能用旧固定4+sqrt10界接口套任意M。
7. M=0及任意beta/R都保留；若原假设不相容，可由真实证明推出，不能除M或把0频率当捷径。
8. 第二目标仍以同实概率mu和同M AE界为基础，K是任意紧的实参数对子集，允许空K。
9. u0/v0是任意实参考参数，不要求(u0,v0)∈K；beta/R仍是任意实，c>0。
10. hWC只给参考真实mu.tilted(u0X+v0X²)上的实际特征模界，不给整个族WC，也不输入参考tilt概率。
11. let mu0为这个同mu的真实quadratic tilt，D0为mu0的实际parabolaCovariance；不能另选reference law或手给矩阵。
12. 结论先存在同一实m>0且m≤1，之后所有lambda及族门都用这个m。
13. lambdaMin=m*detD0/(D000+D011)，分母是真实参考协方差trace；它不是自由正数，必须先生产trace/det正性。
14. lambdaMax=2(M²+M⁴)+1+lambdaMin，明确比lambdaMin严格大；没有按p、频率另选常数。
15. 全局输出lambdaMin>0、lambdaMin<lambdaMax、m²c/2>0。即使K空，这些全局性质也不可真空交付。
16. 每个p∈K固定实际mup=mu.tilted(p1X+p2X²)，而不是从hWC重新选择的law。
17. 每个mup要输出真概率、同M真实AE支持界，以及X/X²各真MemLp2；这些都不是调用者前提。
18. 还输出实际测度序ENNReal.ofReal(m) • mu0≤mup，m须与WC常数及lambdaMin中的m同一。
19. 对全部实频率输出lambdaMin*rho²≤实际Cov_mup二次型≤lambdaMax*rho²；同一组常数在全部p与频率外固定。
20. 最后在原R外输出实际mup的全频率WC，same beta，精确新常数m²c/2；不能拿只给测度下界的另一个m代入。
21. hWC没有要求beta/R正，故负幂的真实非负／正性和取外区频率时需逐项核，不可机械消费只接beta≥0的别模块。
22. 盲审疑点：tilted在不integrable时可能总化为零；必须独立生产任意quadratic exp真Integrable、正normalizer和参考／族真概率，再谈covariance。
23. 盲审疑点：不同概率的均值不同，variance不因测度序而无条件单调。需要真实同函数在mup中心的非负平方积分，或等价合法分解，才能由测度下界得协方差二次型≥m倍参考。
24. 盲审疑点：detD0/traceD0真能控制参考最小二次型吗；需完整实二维对称正定代数，不把det>0单独当任意矩阵正定。
25. 盲审疑点：2(M²+M⁴)+1+lambdaMin的上界因子需由同M真实矩／中心化variance展开支持，不能比较不同中心的函数后省略误差项。
26. 真有限ENNReal标量、实数coercion／toReal及积分单调的全部真实可积门须核；没有∞.toReal假正性。
27. 不需要对p联合可测，因为不对p积分；紧性只用于生产共同测度下界的现有producer，不应偷加K非空。
28. 本模块的直接消费者是已接受169实际白化／标准化矩与WC，当前输入输出不声称完整C或B/D关闭。
29. A已v40正式关闭，B/C/D OPEN。此声明还没有Lean源／Audit／构建／新分支，不能预报kernel PASS。

--- END IMMUTABLE BLIND PREFIX ---
## 最终裁决与版本绑定

STATUS: CORRECT — 独立声明／来源／公开API／静态环境门通过；尚无本模块实现或kernel验收。

上方99行／7088B盲译前缀完整原样保留，其SHA256为f89d0820e821420cc4eb65eac7fe60a7e5f5014bd066e932d4a3840cc6203e4e。开头IN_PROGRESS是该历史检查点状态；本节为完成审查后的最终裁决。

冻结scope80实际83行／7782B，SHA256 b30cd580532e687dc5bc385a06965281e93ea55cc8160363824c5ed70d655b83。两完整TYPE、两imports及Matrix／ENNReal／NNReal作用域如盲前缀所录。没有修改scope、加强假设、补入隐含非空性或变更参数。

以下结论来自实际定义、接受生产者与固定Mathlib正文的独立审查，不以scope路线、候选metadata、作者准备状态或旧CORRECT标签代替数学。

## 一、真实来源及本声明消除的义务

R2原件C:/game/shao/current/oq3/proofs/r2/report.md的SHA256为572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。已对照§2第38–60行、74–76行、83–92行及§5第343–373行。

原文用实际二阶协方差及其统一谱界完成线性标准化，并把单点弱Cramér界传到紧倾斜族。本声明保留同一真实mu、参考倾斜mu0及各mup，生产这些实际协方差的共同严格谱界；它没有把自由矩阵或自由特征函数族当作这些对象。

第一条从真实WC排除非零线性／二次投影的退化，因而生产同mu的D严格正定。第二条使用已接受的紧倾斜测度下界与WC生产者，再生产明确lambdaMin／lambdaMax和同一族真实L²门。它是原文标准化所需的充分、可消费界，不宣称最优谱常数或新颖性。

root-contract相应紧倾斜／测度下界／WC义务与该解释一致；原B的分析义务不因本声明被视为完成。

## 二、第一条：由实际WC得到实际协方差严格正定

1. mu是真概率且|X|≤M AE，M是有限实数。连续的X、X²及其任意固定线性组合均真可测；有界概率门给出真MemLp2，继而给出其平方、交叉项及居中平方的真实可积性。此处不调用只适用于固定4+sqrt10支撑的接口。

2. 实际RegularCovariance.lean第20–24行的parabolaCovariance是[[Var X,Cov(X,X²)],[Cov(X,X²),Var(X²)]]。对F=xi*X+eta*X²，实际variance_fun_add、variance_const_mul及covariance_const_mul在上述L²门后给出
   Var_mu(F)=xi² D00+2 xi eta D01+eta² D11。
   两个交叉项使用同一实际协方差及其对称性，没有转置或系数2遗漏。

3. 真实variance非负。若某非零(xi,eta)的该二次型为零，Mathlib/Probability/Moments/Variance.lean第162–172行ae_eq_integral_of_variance_eq_zero的真实MemLp2前提已满足，因此F=mu[F] AE。这里不是从总化Var或不可积平方推AE结论。

4. 令r=sqrt(xi²+eta²)>0，并取T=(|R|+1)/r>0。经真实sqrt平方及正标量恒等式，(T*xi,T*eta)的欧氏半径恰为|R|+1>R，且该半径严格正。没有除xi、eta或M，也没有把零频率代替外区频率。

5. 在这组频率，实际jointPhase AE等于常数exp(i*T*mu[F])。概率积分将该常数保留，真实复指数模为1，故实际jointCharacteristic的模等于1。

6. hWC则使该模≤1-c*(|R|+1)^(-beta)<1。严格性来自c>0及Real.rpow_pos_of_pos对严格正底数、任意实指数的适用性。因此beta或R不要求非负。该矛盾排除了每个非零方向的零方差。

7. 在(1,0)、(0,1)取值得a=D00>0、d=D11>0。令b=D01=D10；在(-b,a)取值，得到a*(a*d-b²)>0。由a>0及Matrix.det_fin_two的实际定义得det D=a*d-b²>0。使用的是同一个对称D，绝非“任意矩阵det>0便正定”。

第一条四个合取均由实际输入推出。M=0时输入WC与退化概率不相容，以上证明仍合法；无需除M、正支撑或手工非退化假设。

## 三、第二条：先真倾斜概率，再消费同一个m

实际公开TiltedMeasureDomination.lean第17–34行quadratic_exp_integrable_of_ae_abs_le接受任意实M≥0、真实概率mu及同一AE界，给出任意实u/v的exp(uX+vX²)真实Integrable。其证明使用真实连续／有界指数，未要求参数在某小球。

因此参考mu0及每个mup的指数均真可积，且由非零概率测度上的正指数得到严格正normalizer。实际Measure/Tilted.lean第126–136行isProbabilityMeasure_tilted在该门后给真概率，不能落入不integrable时tilted=0的总化分支。

实际Tilted.lean第280–281行tilted_absolutelyContinuous及Measure/AbsolutelyContinuous.lean第175–186行AbsolutelyContinuous.ae_le把原mu的AE |X|≤M传给mu0和mup。每个倾斜律上的X/X²真MemLp2随之成立。参考(u0,v0)可在K外，不影响这些任意参数结论。

已独立读实际CompactTiltWeakCramer.lean全部94行，其第17–37行公开exists_compact_tilted_weakCramer_bound的完整类型正接收本scope的输入：任意实beta/R、c>0、同M及同参考mu0。该公开生产者一次给出
  ∃m, 0<m ∧ m≤1 ∧ 0<m²*c/2 ∧ ∀p∈K, ofReal(m)•mu0≤mup ∧ 实际模平方缺口 ∧ 实际WC。

本声明只需一次destruct该存在。其同一个m用于测度下界、lambdaMin和最终WC的新常数m²c/2，不能另选一个仅满足某一分支的m。

该实际生产者第38–45行保留min(m0,1)，并先给参考真概率；第56–57行先给每个mup真概率。第77–91行的WC分支只用真实rpow非负性，不要求beta/R符号。没有把另一个只接受beta≥0的标准化定理提前套在本scope上。

K空时，此m的正性及≤1仍由生产者的紧集处理与min构造给出；参考D0的正性来自第一条和参考hWC，不是从K内抽取一个p。不存在隐藏Nonempty K或(u0,v0)∈K前提。

## 四、真实测度序到方差下界：必须保留中心校正

不同概率律的均值不同，不能直接写“variance随测度单调”。下面的真实积分比较提供所需门。

固定p∈K和任意xi/eta，记nu=mup、alpha=mu0、F=xi X+eta X²、z=nu[F]。两律都已是真概率且有同M界，所以F、F²和(F-z)²在两律下均真实可积。

由ofReal(m)•alpha≤nu及非负居中平方，Bochner/Basic.lean第621–637行integral_mono_measure可用于f=(F-z)²。其必要门是较大测度nu下f非负及真Integrable；两者先已建立。得到
  Var_nu(F)=∫(F-z)² dnu ≥ ∫(F-z)² d(ofReal(m)•alpha)=m*∫(F-z)² dalpha。

标量测度是有限实m的ofReal倍，m>0给非负；integral_smul_measure及ENNReal.toReal_ofReal把系数变为真实m。没有∞.toReal、无条件积分单调或缺少可积性的跨测度操作。

在alpha真概率下先有平方、线性、常数各项真可积，才展开并使用积分线性：
  ∫(F-z)² dalpha=Var_alpha(F)+(alpha[F]-z)² ≥ Var_alpha(F)。

因此q_Dnu(xi,eta)≥m*q_D0(xi,eta)。它容许均值变化，也不把参考均值强加给整个倾斜族；这是同一中心平方积分论证，而非不成立的无条件方差单调性。

## 五、明确det/trace下界和上界常数逐项核算

第一条作用于真实mu0后，a=D000>0、d=D011>0、delta=det D0>0；trace tau=a+d>0。令b=D001=D010。真实二维对称代数恒等式为
  tau*q_D0(xi,eta)-delta*(xi²+eta²)
    =(a*xi+b*eta)²+(b*xi+d*eta)² ≥0。

只有在tau>0后才清分母，得到q_D0≥(delta/tau)*(xi²+eta²)。与上一节同m比较合并，恰为本TYPE的lambdaMin=m*delta/tau。三个正因子／分母先成立，所以lambdaMin严格正，不依赖某个p或频率。

对每个nu=mup，真实MemLp2后Variance.lean第226–228行variance_eq_sub给
  Var_nu(F)=nu[F²]-nu[F]² ≤nu[F²]。

在原AE支撑转移后逐点有
  F²≤2*xi²*X²+2*eta²*X⁴
     ≤2*(xi²*M²+eta²*M⁴)
     ≤2*(M²+M⁴)*(xi²+eta²)。

所有多项式先真Integrable，再对nu真概率积分；故q_Dnu≤2*(M²+M⁴)*(xi²+eta²)。将非负余量(1+lambdaMin)*(xi²+eta²)加入即得到TYPE中的lambdaMax上界。

lambdaMax-lambdaMin=2*(M²+M⁴)+1>0，包括M=0时也成立。这个严格上界常数不来自未知tilted均值，不漏掉中心校正；中心项在真实variance_eq_sub中以非正平方被合法丢弃。

最终m²c/2>0和WC来自同一公开生产者。两个常数、同m及统一WC均在全部p和频率之前固定，输出的谱界正是实际D_mup二次型，不是Pi最大范数或任意代理矩阵。

## 六、实际API、可达性与边界总核

已针对承重步骤读固定Mathlib实际正文：Variance.lean第143–150、157–172、204–210、226–228、263–274行；Covariance.lean第54–65、75–78、113–140行；Bochner/Basic.lean第621–637行；Tilted.lean第126–136、280–291行；AbsolutelyContinuous.lean第175–186行及Pow.Real的正底数rpow正性接口。

实际variance_fun_add、variance_const_mul和covariance_const_mul消费真实L²门；ae_eq_integral_of_variance_eq_zero消费真MemLp2而非仅形式variance=0；variance_eq_sub在真概率及真MemLp2后使用。上文已逐项给出这些门的来源。

MemLp.of_bound、memLp_const及连续函数的真实AE可测性足以在有限概率中建立所有固定多项式的L²／L¹门。积分中的常数中心均是固定有限实数；不会把参数积分或联合可测性强加给p。

所有所需生产接口均为公开常量。本审查未以别模块privatehelper作可调用API，也不需要新增import、未缓存模块、未证cosine恒等式或新的公理。

边界结论如下：K空仍生产正lambda；参考参数不在K也合法；M0不导致除零；beta0和任意负beta均保留；R0和任意负R均通过严格正外区频率论证；xi=eta=0的非严格谱双界两边为0；第一条只在非零方向要求严格正。

测度比较及正系数均先于实数coercion／除法；lambdaMin分母是已生产严格正trace。没有以0除总化、tilted=0总化或tsum／积分默认值完成目标。

## 七、静态环境与正式接受树绑定（数学门之后）

机械核对最后进行。冻结scope两端83行／7782B及SHA b30cd580532e687dc5bc385a06965281e93ea55cc8160363824c5ed70d655b83一致。本模块CompactTiltCovarianceSpectrum.lean在本地draft和remote worktree均尚不存在；没有其Lean、Audit、构建或实现分支。

实际当前工作树是已发布PR169的feat/oq3-covariance-whitening，HEAD c06e026254837782a706bcde0b8c7218c7f71eb4，git status为空。该冻结分支早于159整合，因此其中没有CompactTiltWeakCramer源文件；初次定向header读取真实记录了这一点，没有把缺源伪报为已可达。

本scope计划从正式接受v42 checkpoint 7832c37251145161d095daac02e3506db90b3910正常新建分支，因此后续静态源码可达性按该接受Git树逐模块git show核查。没有切换、重写或复制169工作树，也没有fetch/reset/merge/rebase。

实际正式绑定依据是coordination/integration-v42/gate-result.json的source_files_sha256字典和accepted-head.json；前者具有295项正式源记录，后者确认accepted head 7832c37251145161d095daac02e3506db90b3910。未把不存在的本地receipt.json当作证据文件。

按两个实际seed在该接受树独立进行小型Shao header DFS，共18模块；规范相对路径键子字典compact SHA256为e03503582ed63f55f9629bcbea056930e068049a2ad4df885c6399bee290659a，与正式源字典一致。没有依作者candidate JSON正文作图谱证明。

关键链为CompactTiltWeakCramer→CharacteristicMeasureDomination→CompactTiltDomination→ProductMeasureDomination→TiltedMeasureDomination；前者同时经FiniteFarArc接JointNonlattice／FiniteNormalSpan。RegularCovariance→FiniteStageMeasure／PositiveRate→InverseTilt→AtomicMeasure→SummableAtoms。余下共同底层为AtomProjection、ResonanceArithmetic、SourceStarter、FiniteConstraints。

关键接受源码绑定：CompactTiltWeakCramer SHA87d4560d0a896d7094e17153b2286408b509b605719977ee443cd688ba8b5544；TiltedMeasureDomination SHA5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b；RegularCovariance SHA0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853。

定向对象检查只补核8项本门新需要的现成olean路径：CharacteristicMeasureDomination、CompactTiltDomination、CompactTiltWeakCramer、FiniteFarArc、FiniteNormalSpan、ProductMeasureDomination、ResonanceArithmetic、TiltedMeasureDomination，均存在。其余10项路径沿已完成U21c门复用；未重复稳定对象hash、完整Mathlib闭图、pins、root gate或成功smoke。

没有运行Lean／#check／probe／build／Audit，没有创建缓存／复制对象／升级依赖或改设置。所有remote项目读取均限定taskset -c 14-17；外部CPU0–9／80GiB任务未触碰。只有本新报告有写入与授权上传。

## 八、直接消费者及明确剩余

已接受PR169的CovarianceWhitening要求真实概率、L²及实际统一谱门，并在原source非负beta/R条件下生产实际白化、均值0、协方差I、欧氏支撑／自然矩和标准化WC。本模块正补其紧倾斜族谱门生产者；未来组合时仍须逐项实例化169诚实的beta/R前提，不能因本声明支持任意实beta/R而删改169接口。

本门没有证明本新模块的Lean实现；作者后续仍须实际完成上述积分、代数和全部声明的elaboration，并接受独立proof审查。本门也未把169 pending root状态提前改成整根验收。

本声明本身不生产完整C装配、一般B分析结论、D结论、实际均值逆或未声明的最优谱界。A已正式v40关闭；B/C/D仍OPEN。冻结scope的历史上下文保留，不作倒改。

最终STATUS: CORRECT。两个完整TYPE在原输入、实际法则、所有量词与边界下均数学成立；实际公开API及计划接受v42执行环境有充分可行路径，未发现必须修订的声明或环境缺口。此裁决仅授权进入实现，不等于证明实现已通过。
