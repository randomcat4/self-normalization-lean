# U19b SourceGeometricScale 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 一、先行完整TYPE盲译检查点

只读取冻结scope69的唯一完整Lean fence并在本节独立翻译；尚未读scope说明、数学路线、R1／root解释或本候选机械图材料。0公开DEF、1公开target。此前已接受模块上下文存在，但本类型的几何恒等式在本轮尚未获准。

```lean
theorem source_corrected_scale_geometric_identity
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
    let x0 : ℝ := Real.sqrt q / 4
    let a0 : ℝ := q / 4
    let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
    let curvature : ℝ := 2 * (-sourceEll) / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
    0 < D.det ∧ 0 < curvature ∧
      0 < sourceEll * Real.sqrt D.det * Real.sqrt curvature ∧
      correctedInverseScale sourceEll q (atomicMeasure w) =
        (sourceEll * Real.sqrt D.det * Real.sqrt curvature)⁻¹
```

逐量词／let绑定独立翻译：

1. 任取实q，要求严格1<q<103/100。
2. 任取w:AtomicIndex→ℝ，每个实际w_i≥0。
3. 对每个i:Fin4，基点分支w(Sum.inl i)严格正。
4. 不要求全部新增无限原子也严格正；它们允许为0。
5. 对全部k:Fin4，w_i*constraintFeature sourceEll (fixedAtom i) k具有真正HasSum。
6. 此级数的和指定为同一个constraintTarget q k。
7. target没有额外输入手工概率、均值、方差、det非零或曲率正性。
8. 以下五个let表达式都是结论内部定义，不能当作调用方自由选择的量。
9. D是atomicMeasure w之实际parabolaCovariance，类型Matrix(Fin2)(Fin2)ℝ。
10. x0是标准实数平方根sqrt(q)除以4。
11. a0是同q除以4。
12. v是Fin2→ℝ的实际二向量![1,2*a0/(x0²)]。
13. curvature是实际表达式2*(-sourceEll)/(x0²)+dotProduct v(D⁻¹*ᵥv)。
14. 矩阵逆是固定库的D⁻¹；type没有先输入D可逆。
15. dotProduct使用同v两侧，矩阵向量乘法也是该同D的逆。
16. 结论第一合取项为真实D.det>0。
17. 第二合取项为上述明确curvature>0。
18. 第三合取项为sourceEll*sqrt(D.det)*sqrt(curvature)>0。
19. 第四合取项将现有correctedInverseScale(sourceEll,q,atomicMeasure w)等同于该正几何常数的逆数。
20. 因而本命题不只给总化逆数的形式等式，还必须生产三项实质正性。
21. 全部量都来自同一个w/q/sourceEll，不能在几何因子与校正常数之间切换measure或中心。
22. 所有q/x0²/矩阵det分母、平方根与逆数在证明点须真实合法。
23. 仅由D.det>0并不能对任意矩阵自动推出所需曲率正性；必须消费实际协方差结构和source参数。
24. 这里没有导出真实全局率函数、Hessian定义、domK或扩展supremum。
25. 原型作用只能在后续来源核查后判定，不能把这个代数表达式直接命名为已证明的真实Hessian。

后续独立门：实际mu概率和L²／可积矩、基点正性、D对称和实际normalVariance身份，矩阵逆非奇异门，x0/a0/v正确简化、曲率正性及sqrt乘法正域，最后才scope/pins/hash/cache。当前检查点不构成CORRECT票。


## 二、盲译后来源、量词及实际数学审查

本节在56行完整TYPE独立盲译已持久化后追加；此时已读完整scope69、R1真实239–257及431–443、实际CorrectedScaleContinuity/RegularCovariance公开定义与必要证明，以及固定Mathlib矩阵逆／平方根主API。未读作者implementation/future/candidate笔记或scanner JSON；尚未读取本候选图/hash/cache元材料作数学依据。没有U19b实现，以下是声明可实现性审查，不预报kernelPASS。

### 来源与根契约边界

R1 239–257明确实际Δ=Covπ(X,X²)、S=Varπ(Y)、Λ1=S/detΔ−32ell/q>0。431–443的continuous constant满足v_corr²=ell²*(S−32ell*detΔ/q)，其逆正是现有correctedInverseScale。原R2 report23及313–314也写v_corr=−t0*sqrt(detΔ)*sqrt(Λ1)。冻结scope的literal几何曲率是2t0/x0²+vᵀD⁻¹v，t0=−sourceEll，x0=√q/4，a0=q/4；本type需把它真实识别为同一个R1 Λ1，而非人为定义新常数。

此type无新DEF，所有let由同w/q构成，D不是调用者给的任意det正矩阵，x0/a0/v/curvature不是可自由选择的见证。它只对actual atomicMeasure的矩阵作字面几何恒等式；root canonical K的Hessian=该D、源参数为真实鞍点、globalRate/domK/扩展值桥仍需root独立证明。不得从本代数票反向宣称K可微或root所有鞍点前提已闭。

### 真概率／矩／基点正质量及非退化

1. hm0因constraintFeature首行1、constraintTarget首行1，真实给HasSum w1；与hw≥0用公开atomicMeasure_isProbabilityMeasure建立mu=atomicMeasure w真概率。不是从裸tsum1或未可和totalization取概率。
2. 公开atomicMeasure_ae_bounds给mu下真实1≤|X|≤β=4+√10。可用公开integrable_continuous_of_fixed_bounds对X、X²、四次幂和全部中心多项式给真Integrable；也可直接MemLp.of_bound分别用β和β²给X/X²真MemLp2。因此本D的方差／协方差来自真实可积矩，不是evariance.toReal或实Bochner非可积时0值。
3. 实际parabolaCovariance定义RegularCovariance20–24恰D=!![A,B;B,C]，A=VarX、B=Cov(X,X²)、C=Var(X²)，故D10=D01定义性rfl。未把均值矩阵或正标量det替代整个实际协方差矩阵。
4. fixedAtom(inl i)=baseAtom i，公开atomicMeasure_real_singleton w hw i真实给mu.real{baseAtom i}=w(inl i)>0。基点权和单点质量之间不存在额外未证RN或finite-index漏门；hm0先保证mu概率/所有质量有限。
5. 公开parabolaCovariance_det_pos(mu,hb,hbasemass)109–130生产d=detD>0，不要求新增原子全正。其已接受实际证明从centered_parabola_integral_pos的真可积平方、AE零值在正原子取点，使用−1、1、2三个不同基点排除非零二次式；再取明确二向量产生det正。不是“任意det>0就等于正定”的错误逆推。
6. 同实际hb下normalVariance_eq_covariance132–155给真实S=64A−16B+C。其实现先真X/X²可积、线性计算EY，再把Y的中心平方映射到centered_parabola_integral_eq；后者先保证三种中心乘积真Integrable才展开协方差。无需调用不在本import计划里的NormalTangentGaussian或别模块private lemma。

### q/x0/a0及几何系数

7. q>1给q>0、sqrtq>0。Real.sq_sqrt(q≥0)给(sqrtq)²=q；由x0=sqrtq/4得x0>0及x0²=q/16>0。4、16、q和x0²都在清分母前真实非零。
8. a0=q/4，所以2a0/x0²=(q/2)/(q/16)=8，v=![1,8]。第一分量确为1，第二分量8，不是把normal方向(8,−1)误当边界切向；D仍Cov(X,X²)的原坐标序。
9. 2*(-ell)/x0²=−32ell/q。负号和32因子均由literal2t0和x0²=q/16产生，不用源ℓ≈1/30数值代换。sourceEll>0是公开真实log(31/30)>0。

### 实际2×2逆矩阵及二次型

10. 固定Mathlib `Matrix.inv_def`不是抽象任意Inv：NonsingularInverse.lean166–171定义A⁻¹=Ring.inverse(det A)•adjugate A，奇异时归零。此处先由步骤5得d>0／d≠0；因此使用该逆不依赖奇异总化。Real上的Ring.inverse_eq_inv给真实1/d。
11. `Matrix.adjugate_fin_two`372–376精确给adjD=!![C,−B;−B,A]（利用实际D10=D01）。Matrix.mulVec/dotProduct在Fin2有限求和可展开为两项，系数/行列顺序独立核对如下：

`D⁻¹ *ᵥ ![1,8] = ![(C−8B)/d,(8A−B)/d]`，
`dotProduct ![1,8] (D⁻¹*ᵥ![1,8])=(C−8B+8(8A−B))/d=(64A−16B+C)/d=S/d`。

12. 全部除d的代数清分母用d.ne'，有限求和的展开无需新积分／可积前提；真实S身份则来自步骤6。该式没有转置误用，也没有把D⁻¹与元素逐项倒数混淆。
13. 因而type内部literal curvature确等于S/d−32ell/q。此等式不以root Hessian为前提，且无法仅对任意非对称矩阵从det>0推出；实际对称性、S身份和v系数是关键。

### 真曲率与尺度正性、最后精确恒等式

14. 公开atomic_curvature_pos230–257的完整输入恰当前qwindow/w≥0/hbase/4HasSum，无手工radicand或variance前提。它真实给S/d−32ell/q>0，所以literal curvature>0。其承重证明从sourceEll<1/30和q/(32*transverseVariance)>1/30、真实S/det正及真实方差界产生，不是把所求正性作为假设。
15. 令κ=curvature。d>0、κ>0，先正分母d后有dκ=S−(32ell/q)d>0；同结果也可用公开source_atomic_corrected_radicand_pos138–155验证。目标没有允许在负radicand上依靠sqrt0总化。
16. sourceEll>0、sqrt d>0、sqrtκ>0，故literal几何常数G=sourceEll*sqrt d*sqrtκ>0，真实证明第三合取项；不是仅因取逆后存在实数而忽略G零值。
17. 固定Real.sqrt_mul以d≥0为门给sqrt(dκ)=sqrt d*sqrtκ。结合dκ=S−(32ell/q)d得到`sourceEll*sqrt(S−(32ell/q)d)=G`。再对同实数两边取逆并展开existing correctedInverseScale20–22，恰得第四合取项，所有参数/measure完全同一。
18. 平方根乘积不需要错误的绝对值删去或平方反推符号：两个sqrt按标准非负支取值，三个因子已严格正；因此不会把正几何尺度错配成其负值或总化逆0。

### 全量词／端点／消费者核对

q窗口严格保留，q=0和x0=0本来不在前提内，proof不能非法约分；这里正性已由hq0生产。新增权允许零和无限可和支撑，但4基点严格正始终保证非退化；因此可消费有限stage含J0，也可消费最终无限法则。J不是此target参数，不能凭该适用性声称已构造一个新stage family。4行HasSum用同sourceEll、fixedAtom及constraintTarget q，既非finite-sum替代也非额外Summable w输入。

根契约的几何公式与actual corrected constant的同law正域身份，在上述完整路径下数学正确且可实现。单一import中的已接受公开API足够，不需新增手工det/curvature/Hessian/可微/全局优化假设，也不需修改类型或扩大正性门。声明CORRECT仍只批准此完整类型和实现可行性，不能预批准未来实现、private/generated obligations或Lean机械验收。

## 三、已独立核验的固定库/API可见性语义

实际server读NonsingularInverse.lean146–180：Matrix.inv实例要求[Fintype n][DecidableEq n][CommRing α]，Fin2/ℝ标准实例满足；inv_def170无额外隐式“已提供Invertible”门。实际Adjugate372给2×2交叉负号，Ring.inverse_eq_inv426在GroupWithZero（ℝ适用）给数值逆。实际Sqrt177的sq_sqrt要求0≤q，365的sqrt_mul要求第一因子≥0，正域步骤全部明确。

实际导入项目API完整type已逐项读：CorrectedScaleContinuity existing definition及source_atomic_corrected_radicand_pos；RegularCovariance实际D/S定义、centered平方积分及正性、det_pos、normalVariance_eq_covariance和atomic_curvature_pos。它们的概率／AE／单点正门逐项由当前hw/hm/hbase生产，不需要跨模块private访问；矩阵范数Elementwise scope在当前type没有出现，先前U11d范数实例修复不会被误当本type的隐藏norm实例。


## 四、数学核验之后的实际公开图／cache／hash／pins绑定

最后仅对本新候选的exact单一import做一次独立静态源码图扫描；没有重复U19a成功构建、root KL/import smoke或旧全cache哈希。扫描器在reviewer只读server输入中临时运行，处理嵌套注释/字符串、module默认可见性、public/private及meta import，不读取作者候选scanner、candidate JSON或未来notes。所有内部源存在性与olean存在性均只读，未执行Lean或写cache。

唯一import=`Shao.OQ3.CorrectedScaleContinuity`。独立physical17Shao+2747Mathlib=2764内部节点、211外部停止叶；public17Shao+2440Mathlib=2457内部节点，加189外部停止叶=2646。source缺项0、olean缺项0；外部Lean/其他package叶只计停止边界，不冒作已展开源码。canonical source-relative path键排序紧凑17源map SHA=`a1f4b5aa595cc437fb511345cdcd4b9d3471b3f88bcc50fbc7ea90247e421766`，由当前实际源fresh重算。

必要公共节点RegularCovariance/AtomicMeasure/InverseTilt/SourceStarter、Mathlib.LinearAlgebra.Matrix.NonsingularInverse/Adjugate、Algebra.GroupWithZero.Units.Basic、Analysis.Real.Sqrt和Probability.Moments.Variance均真实public可达。SourceGlobalExponentialTests(U19a)、SourceFixedLawRemainder(C)、NormalTangentGaussian均不在本物理闭包；数学路径只用上文已核的RegularCovariance公开接口，未错误消费不可见后继或别模块private。

17项目源实际hash表如下；关键local已读取文件CorrectedScaleContinuity/RegularCovariance/AtomicMeasure/InverseTilt/SourceStarter同时fresh核SHA与server一致：

| canonical项目相对路径 | SHA256 |
| --- | --- |
| Shao/Basic/FinitePath.lean | 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb |
| Shao/OQ3/AtomProjection.lean | 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22 |
| Shao/OQ3/AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| Shao/OQ3/AtomicProductControl.lean | 6f886635f2201e04d1004a4f4b3b4058d406be3a283f716b70f1ce1cfaa5775f |
| Shao/OQ3/AtomicTailControl.lean | ec528d9af8b475f1db8a78c93ab917d754365d280027a86be2823825b19c2f79 |
| Shao/OQ3/CorrectedScaleContinuity.lean | b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8 |
| Shao/OQ3/FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| Shao/OQ3/FiniteNormalSpan.lean | 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de |
| Shao/OQ3/FiniteStageMeasure.lean | 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1 |
| Shao/OQ3/InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| Shao/OQ3/PositiveRate.lean | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |
| Shao/OQ3/RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| Shao/OQ3/ResonanceArithmetic.lean | cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b |
| Shao/OQ3/SampleBoundary.lean | 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2 |
| Shao/OQ3/SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| Shao/OQ3/SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| Shao/Probability/FiniteIID.lean | d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b |

本地scope与remote run/scope.md均34行6372B，SHA=`fba06a40b1db81cfdb8dec02b8bb9bd5887a3b64b484e6491d7082c73477b2cf`。原件R1 report.md SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`；补充只读原R2 report.md SHA=`572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`，其v_corr公式仅用于来源一致性，不把R2其他分析假设导入本target。

指定server实际Mathlib Git HEAD=`807d3836b165983210ee2ecf3cd28f239436949c`；lean-toolchain为leanprover/lean4:v4.36.0-rc1，文件SHA=`d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest SHA=`40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。当前所需Fin2/ℝ矩阵inverse实例、有限求和、标准实sqrt和covariance APIs均公开/缓存现成，未发现需显式新增import或变更type的环境阻塞。但没有U19b Lean elaboration或目标proof的成功凭据，不能据此预称kernelPASS。

最后实际Git branch=`feat/oq3-source-global-exponential-tests`，HEAD=`5d14dbdb619fd7d2eb97ec31e049053de53be871`，status干净，仍是已发布U19a冻结head；local/remote SourceGeometricScale.lean不存在，U19b run的Audit.lean/receipt.json不存在。尚未B新branch/source/probe，保持冻结声明门边界；此前正常U19a发布不是B源漂移。C144f698和U19a146均不是B的import，root共享K/Hessian/率函数所有权未被跨越。

本review所有server项目命令taskset CPU14–17只读，没有Lean/#check/probe/build/rebuild/spawn/cachewrite/commit/pub/fetch/rebase/reset/retarget或raw完整log下载，未触外部CPU0–9/80GiB任务或全局资源。仅写新的本地报告及授权remote对应报告，旧scope/票/源/pins/shared文件原样保留。rootv36已接受17前置的行政说明不代替上面的独立数学和静态图核验。

## 五、最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: scope69唯一完整type数学正确，全部let对象都来自同一实际atomicMeasure。完整4HasSum生产真概率和可积矩，基点权严格正生产真实单点正质量并给detD>0；q窗口确保x0正和全部q/x0²分母合法。实际2×2对称协方差逆二次型为S/detD，v第二分量8与2t0/x0²=−32ell/q正确，公开atomic_curvature_pos生产真正曲率正性。detD*curvature恰existing corrected radicand，正sqrt乘法和ell>0给实际几何尺度正性及其逆与existing correctedInverseScale的精确同law身份。没有依赖奇异inverse/sqrt总化或手工Hessian/curvature前提，实际单一import/API/实例/cache足够，未发现声明或环境修复需求。

这是独立声明／来源／API准许，不是未存在实现的预先证明票。后续需重新审实际public type、完整proof/private/generated、actual TYPE／传递axioms和真实成功机械门；本票不授权改变冻结前提。直接消费者为root literal source saddle constant与C实际余项尺度的桥，在root另证其canonical Hessian=actual covariance、鞍点参数与supremum等之后使用。一般KL9/10、root K/domain/globalRate/扩展值桥及全部根装配仍独立OPEN，无最优性或新颖性声明。

根A/B/C/D保持OPEN。先行56行完整盲译检查点原字节前缀保留，前部IN_PROGRESS是历史状态，最终以本节为准。lead全文读本完整final前不应实施B；review未修改任何作者/旧票/共享文件。
