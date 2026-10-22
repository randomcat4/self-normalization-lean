# U20d SourceCanonicalSaddle 完整独立证明审查

STATUS: IN_PROGRESS

## 不可改写 actual TYPE 盲审前缀

本前缀只从当前实际源码提取完整公开TYPE，尚未读取本次171行证明体、Audit／actual TYPE输出或receipt。
此前声明审查上下文已经存在；此处重新独立解释实际TYPE，不以旧CORRECT或作者构建成功代替本次proof审查。
本模块0公开DEF，唯一公开合取target如下。

```lean
theorem source_canonical_saddle_hessian_and_scale
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w
      (fun i => (hw i).le)
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    ∃ lift : (Fin 2 → ℝ) → bivariateMGFDomain P W,
      (∀ theta, (lift theta : ℝ × ℝ) = (theta 0, theta 1)) ∧
      let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
      let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
      let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
      let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
      let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
        (pr 0).smulRight (q / 4) + (pr 1).smulRight q
      let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
        ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
      let x0 : ℝ := Real.sqrt q / 4
      let a0 : ℝ := q / 4
      let s0 : ℝ := 8 * sourceEll
      let t0 : ℝ := -sourceEll
      let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
      let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
      let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
      let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
      (∀ theta, K theta =
        Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
      HasFDerivAt K gradient theta0 ∧
      HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
      (∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < dotProduct u (D *ᵥ u)) ∧
      0 < x0 ∧ q = a0 ^ 2 / x0 ^ 2 ∧ s0 = -2 * a0 * t0 / x0 ^ 2 ∧ t0 < 0 ∧
      lambda0 = saddleRate sourceEll q w ∧ 0 < lambda0 ∧
      0 < D.det ∧ 0 < lambda1 ∧ 0 < vCorr ∧
      correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹
```

### 完整量词与独立所需门

1. q为同一个任意实数，1<q<103/100。
2. w为同一个AtomicIndex权重，全部严格正；不是另取一个存在族。
3. 全部Fin4约束是w乘实际fixedAtom特征的真实HasSum。
4. P固定为originalMeasure sourceEll w，TYPE内部letI由hw非负化与hm0生产真概率。
5. W固定为(x,x²)，canonical domain是真实二次指数可积域。
6. 结论先存在覆盖整个Fin2实参数空间的domain-valued lift。
7. lift的底层实对逐theta等于(theta 0,theta 1)，不能仅局部或换参数。
8. K为同P/W canonical logMGF在lift上的拉回，不是自由新定义。
9. 必须先证明整个ambient K等于字面log指数积分函数。
10. 只有鞍点数值相等不能转移一阶，更不能转移fun theta=>fderiv K theta的导数。
11. theta0是Fin2向量![8sourceEll,−sourceEll]。
12. D是真atomicMeasure w下parabolaCovariance，不是原P的未倾斜协方差。
13. pr_i是真连续线性坐标投影；gradient为h↦(q/4)h0+qh1。
14. hessian是h↦[k↦Σij h_i k_j D_ij]的真实嵌套CLM。
15. 第二个HasFDerivAt针对实际fderiv函数，不能用形式偏导／Peano二阶代替。
16. 对所有u≠0的dotProduct u(D*ᵥu)必须严格正，不仅detD>0。
17. 正base权重须先变成同π下真实正singleton质量，配合概率／有界／真积分门。
18. 非零Fin2向量须真实给u0≠0或u1≠0，才能消费中心二次式严格性。
19. D的对称交叉项和二重求和方向须与实际Hessian一致。
20. q>0先给x0=sqrtq/4>0及x0²非零，再作所有除法恒等式。
21. a0=q/4，s0=8sourceEll，t0=−sourceEll，目标要求q=a0²/x0²和s0=−2a0t0/x0²。
22. t0<0必须由真实sourceEll>0给出。
23. lambda0为当前K及当前theta0形成的canonical测试值，须绑定为同saddleRate且严格正。
24. U20c domain witness与当前lift theta0只给同底层对时，须正确绑定Subtype或展开同一个canonical log。
25. 正率必须消费真实严格权重与ell≠0门，不由有限率恒等式自动推正。
26. v为![1,2a0/x0²]；lambda1含实际矩阵逆D⁻¹和2t0/x0²。
27. 应先生产真实detD>0排除奇异逆总化，再与公开几何接口的同一表达式匹配。
28. vCorr=(-t0)sqrt(detD)sqrt(lambda1)需要每项正，最后correctedInverseScale为同vCorr逆。
29. 所有q/w/P/D和几何参数均在同一量词域中，不得重选law／矩阵／曲率。
30. 待核whole hK如何在两个HasFDerivAt内部转移，不能只重写目标值。
31. 待核所有locals和实际generated声明；不能按Shao.OQ3 namespace猜owner而漏掉别namespace常量。
32. 待核跨模块只消费public API，不能调用private inverse或AE原子helper。
33. 本TYPE只到theta0处导数，不给邻域C2、均值映射逆或最终根A装配。
34. 所有原A/B/C/D仍OPEN，本盲前缀不预报完整proof／kernel裁决。

--- END IMMUTABLE BLIND PREFIX ---

## 实际完整证明与来源审查（receipt之前）

严格顺序记录：先仅提取当前公开完整TYPE，持久化90行5685B盲前缀，SHA256 `63f2d79e889268a797335ff3bfc90b2250160839d75cc5bad8f0a10cd3a2d3f9`；之后才读实际171行全部源码、scope75、R1 141–159／239–257／431–443和实际公开直接生产者。全proof逐行审完后才读取全部actual DECL／TYPE，receipt和构建账留最后。没有读取作者implementation／future／candidate／scanner笔记。

### 1–18／19–57行：来源、作用域与完整实际目标

精确四imports是SourceCanonicalRate、SourceLogPartitionDerivatives、SourceGeometricScale、PositiveRate；namespace Shao.OQ3，open MeasureTheory Shao.Probability，scoped Matrix Topology BigOperators。没有竞争canonical定义、额外axiom或新公开DEF。

R1 141–159把原P于(8ell,−ell)倾斜回同π，并给a=q/4、x0=√q/4和正Lambda0；239–257明确Delta是π下Cov(X,X²)且严格正定，Lambda1=S/detD−32ell/q>0；431–443将校正常数绑定为ell²(S−32ell detD/q)的正根。当前公开TYPE实际使用P的canonical log、同π的D和相同系数，未把原P协方差误作倾斜Hessian。

19–57行完整目标与冻结scope一致：q窗口、严格w、全部HasSum、内部P概率生产、整个ambient lift／K、真实梯度／fderiv二阶、完整∀非零u二次型正定、标量鞍点、正率、det／lambda1／vCorr正及真实correctedInverseScale倒数都保留。没有输入这些结论，未把同law性质变成可真空成立的前件，也不声称只凭局部凸性得到全局率。

### 58–69行：实际质量／双概率与全域lift

58行hw0逐点由严格正转非负；59–60行用feature／target的首分量1和mul_one把hm0精确还原为真实HasSum w 1，非总化tsum。61–64行P／W定义与TYPE相同；62行公开originalMeasure_isProbabilityMeasure消费hw0／hs生产P真概率，63行公开atomicMeasure_isProbabilityMeasure生产同w的π真概率。后者是下面实际矩／正定性的必要门，不能只给P概率。

65–66行仅一次消费source_canonical_rate_unique_minimizer q hq0 hq1 w hw0 hm，解构得到同P/W全域hdom、全部域内正配分／literal log的hlog、thetaStar底层身份、达到值htest，其余全局比较尾部在本模块无需重复输出。没有另选q、w或π。

67–68行lift(theta)是实际subtype构造：底层对(theta0坐标,theta1坐标)，成员证明通过真实hdom=univ与mem_univ；不是从域外总化log构造假成员。69行底层坐标身份rfl。这里theta0坐标指theta 0，而非固定鞍点被错误代入；整个Fin2实参数空间均覆盖。

### 70–105行：全部let身份、whole hK与真正二阶转移

70–85行K、theta0、D、pr、gradient、hessian及全部几何量逐体等于TYPE；86–94行change仅展开这些let，将剩余目标完整重述，没有删弱任何合取。

95–98行hK是完整函数等式K=(fun theta=>log∫exp(theta0坐标*x+theta1坐标*x²)dP)，由funext theta及(hlog(lift theta)).2给出。hlog中的底层pair经明确lift构造可定义性还原为ambient两个坐标。不是只有K(theta0)的一个数值等式，也没有对子类型采用新拓扑求导。

99行实际公开source_log_partition_first_and_second_derivatives消费同q/w/hw0/full4hm；其公共TYPE161–177的P、literal K、Fin2 theta0、actual D、pr和双和hessian与此逐体一致。100–105行先rw[hK]，包括在fun theta=>fderiv ℝ K theta内重写整个函数，再分别exact hd.1／hd.2；所以真正保留导函数的Fréchet导数，而非只求方向二阶。

该接受生产者的真实语义已在独立U19c完整proof审查：任意参数exp／weighted moments真Integrable、正partition在log前建立，全参数第一导数给整个fderiv等式后才求二阶；同P retilt归一化矩还原到同π，真实MemLp x和x²先于variance／covariance矩公式，两个交叉项与双重CLM方向完整一致。本节点没有额外手给C2、Hessian或另一个测度的矩。

### 106–130行：真实非零向量的完整严格二次型

106–107行由atomicMeasure_ae_bounds取真实固定上界。108–111行hbp把baseAtom i改写为fixedAtom(Sum.inl i)，再用atomicMeasure_real_singleton w hw0得到质量恰为w(Sum.inl i)，最后消费严格hw；不是把抽象权重正性直接当作measure.real正性。

112–120行对任意u≠0分解坐标非零：若u0=0且u1也0，则ext i／fin_cases覆盖Fin2全部索引，simp_all得u=0，与hu矛盾；否则直接给第一坐标非零。没有假设两个坐标都非零，也没有把全函数非零偷换成任意一个坐标非零。

121–122行真实公开centered_parabola_integral_pos在同π概率、hb和hbp下给中心二次式平方积分严格正，再用公开centered_parabola_integral_eq还原为u0²D00+2u0u1D01+u1²D11。两个API的生产体先建立中心多项式真Integrable再作积分线性／零积分推出AE零；正原子−1、1、2排除非零二次式。不是variance.toReal总化造成假正性，且本源未跨模块引用其private AE helper。

123行hsym为真实D构造中两次同一Cov(X,X²)的定义性相等D10=D01。124–128行展开Matrix.mulVec、dotProduct和两个Fin.sum_univ_two，代hsym后ring得精确二次型身份。129–130行实际用heq重写目标并exact hp；这是完整∀u≠0正定结论，不是det>0替代正定定义。

### 131–147行：真实正q分母与标量鞍点

131–132行q>1给q>0，sqrt_pos和除正4给x0>0。133–136行先用Real.sq_sqrt hq.le合法算x0²=q/16。137–146行只在hq.ne'明确给q≠0后field_simp，得到q=a0²/x0²以及s0=−2a0t0/x0²；常数16／4与8ell因子精确。没有利用q=0／x0=0总化倒数或错误取消sqrt。147行由真实sourceEll_pos给t0<0。

### 148–158行：绑定同一个domain见证与正lambda0

148–150行hlift0以Subtype.ext证明lift theta0=thetaStar。目标底层pair的左侧化简为(8ell,−ell)，而hthetaStar给thetaStar底层恰为这个pair；取.symm方向正确。只比较底层值并用子类型外延消去证明差异，不另取鞍点或law。

151–155行展开lambda0／K，rw hlift0把canonical log精确移到同thetaStar；再在实际达到值htest中rw hthetaStar还原线性参数。exact htest给当前lambda0=saddleRate sourceEll q w，符号为8ell·q/4−ell·q−K(theta0)，没有把P和π的配分混用。

156–158行先rw hvalue，再消费公开saddleRate_pos sourceEll q sourceEll_pos.ne' w hw hm。它实际需要ell≠0和全部严格权重，当前门完整交付；正率不是由候选有限值或canonical率名字自动推出。源正normalizer和严格log门已在该接受producer中落实。

### 159–168行：实际D／lambda1／vCorr的几何接口与全部返回

159–160行公开source_corrected_scale_geometric_identity接同q窗口、w／hw0、四base严格质量和完整hm。161–164行change将其真实D／x0／a0／v／curvature展开为本TYPE的同D与lambda1；t0=−ell，故项2t0/x0²精确对应公共曲率。没有借用其private inverse_tangent_quadratic作为新API。

实际接受几何producer先证明同π detD>0，再用q正得v第二分量8及−32ell/q因子、真实Var(Y)协方差身份和正曲率，最终通过正det的sqrt_mul证明correctedInverseScale倒数身份；不是奇异逆／负根式总化。本模块消费的hgeo.1／.2.1就是这些真实正det／正lambda1，非caller假设。

165–166行refine按顺序返回whole hK逐点值、真实一阶／二阶、hposdef、所有标量方程、ht0、hvalue／hlambda0以及hgeo正性。167–168两目标只展开vCorr、t0并用neg_neg将−t0精确还原为sourceEll，分别交付hgeo.2.2.1的正乘积和hgeo.2.2.2的真实scale等式，最后各合取无遗漏。170–171仅结束section／namespace。

全171行及所有local已读；源码无authored private DEF／THM或额外递归。生成声明不能凭源码表面或namespace猜测，下一节按真实module owner逐项核10项TYPE，之后才读取receipt／构建证据。数学阶段未发现CRITICAL GAPS。

## 全部10个实际所属TYPE／生成项／公理

上述proof和必要实际API全部审完后，独立读取服务器actual-declarations.txt全部77行4636B，SHA256 `44761c849e7db83f4698362a93d8a8d68fa1805071bff76b73e5a64b73c5a655`。完整选块原样保存在下，保留主TYPE的全部let、量词、长续行以及生成项的universe／typeclass／非零假设。

```text
DECL Shao.OQ3.source_canonical_saddle_hessian_and_scale._simp_1_7
TYPE ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ), a ≠ 0 → (a ^ n = 0) = False
AXIOMS [propext]
DECL Shao.OQ3.source_canonical_saddle_hessian_and_scale._simp_1_8
TYPE ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ), a ≠ 0 → (a ^ n = 0) = False
AXIOMS [propext, Classical.choice, Quot.sound]
DECL Shao.OQ3.source_canonical_saddle_hessian_and_scale._simp_1_5
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4], (4 = 0) = False
AXIOMS [propext]
DECL Shao.OQ3.source_canonical_saddle_hessian_and_scale
TYPE ∀ (q : ℝ),
  1 < q →
    q < 103 / 100 →
      ∀ (w : Shao.OQ3.AtomicIndex → ℝ) (hw : ∀ (i : Shao.OQ3.AtomicIndex), 0 < w i)
        (hm :
          ∀ (k : Fin 4),
            HasSum (fun i => w i * Shao.OQ3.constraintFeature Shao.OQ3.sourceEll (Shao.OQ3.fixedAtom i) k)
              (Shao.OQ3.constraintTarget q k)),
        let P := Shao.OQ3.originalMeasure Shao.OQ3.sourceEll w;
        have W := fun x => (x, x ^ 2);
        ∃ lift,
          (∀ (theta : Fin 2 → ℝ), ↑(lift theta) = (theta 0, theta 1)) ∧
            have K := fun theta => Shao.Probability.bivariateLogMGF P W (lift theta);
            have theta0 := ![8 * Shao.OQ3.sourceEll, -Shao.OQ3.sourceEll];
            have D := Shao.OQ3.parabolaCovariance (Shao.OQ3.atomicMeasure w);
            have pr := fun i => ContinuousLinearMap.proj i;
            have gradient := (pr 0).smulRight (q / 4) + (pr 1).smulRight q;
            have hessian := ∑ i, ∑ j, (pr i).smulRight ((pr j).smulRight (D i j));
            have x0 := √q / 4;
            have a0 := q / 4;
            have s0 := 8 * Shao.OQ3.sourceEll;
            have t0 := -Shao.OQ3.sourceEll;
            have v := ![1, 2 * a0 / x0 ^ 2];
            have lambda0 := s0 * a0 + t0 * q - K theta0;
            have lambda1 := 2 * t0 / x0 ^ 2 + v ⬝ᵥ D⁻¹.mulVec v;
            have vCorr := -t0 * √D.det * √lambda1;
            (∀ (theta : Fin 2 → ℝ), K theta = Real.log (∫ (x : ℝ), Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
              HasFDerivAt K gradient theta0 ∧
                HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
                  (∀ (u : Fin 2 → ℝ), u ≠ 0 → 0 < u ⬝ᵥ D.mulVec u) ∧
                    0 < x0 ∧
                      q = a0 ^ 2 / x0 ^ 2 ∧
                        s0 = -2 * a0 * t0 / x0 ^ 2 ∧
                          t0 < 0 ∧
                            lambda0 = Shao.OQ3.saddleRate Shao.OQ3.sourceEll q w ∧
                              0 < lambda0 ∧
                                0 < D.det ∧
                                  0 < lambda1 ∧
                                    0 < vCorr ∧
                                      Shao.OQ3.correctedInverseScale Shao.OQ3.sourceEll q (Shao.OQ3.atomicMeasure w) =
                                        vCorr⁻¹
AXIOMS [propext, Classical.choice, Quot.sound]
DECL Shao.OQ3.source_canonical_saddle_hessian_and_scale._simp_1_4
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3], (3 = 0) = False
AXIOMS [propext]
DECL Shao.Probability.bivariateLegendreRate.congr_simp
TYPE ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ μ_1 : MeasureTheory.Measure Ω) (e_μ : μ = μ_1) [inst_1 : NeZero μ]
  (W W_1 : Ω → ℝ × ℝ),
  W = W_1 →
    ∀ (z z_1 : ℝ × ℝ),
      z = z_1 → Shao.Probability.bivariateLegendreRate μ W z = Shao.Probability.bivariateLegendreRate μ_1 W_1 z_1
AXIOMS [propext, Classical.choice, Quot.sound]
DECL Shao.OQ3.source_canonical_saddle_hessian_and_scale._simp_1_9
TYPE ∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ), (↑n + 1 = 0) = False
AXIOMS [propext]
DECL Shao.OQ3.source_canonical_saddle_hessian_and_scale._simp_1_3
TYPE ∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2], (2 = 0) = False
AXIOMS [propext]
DECL Shao.Probability.bivariateLogMGF.congr_simp
TYPE ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [inst_1 : NeZero μ] (W : Ω → ℝ × ℝ)
  (θ θ_1 : ↑(Shao.Probability.bivariateMGFDomain μ W)),
  θ = θ_1 → Shao.Probability.bivariateLogMGF μ W θ = Shao.Probability.bivariateLogMGF μ W θ_1
AXIOMS [propext, Classical.choice, Quot.sound]
DECL Shao.OQ3.source_canonical_saddle_hessian_and_scale._simp_1_6
TYPE ∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀] [NoZeroDivisors M₀] {a b : M₀},
  a ≠ 0 → b ≠ 0 → (a * b = 0) = False
AXIOMS [propext]
```

主TYPE10–52选块与盲前缀／冻结TYPE逐项一致：严格w与full4hm、同P/W、全域lift、整个K恒等、两个真实HasFDerivAt、完整非零u正定、正x0与两鞍点代数、t0负、lambda0等率且正、真实det／lambda1／vCorr正和最终scale身份齐全。打印器把let部分打印为have，并隐藏IsProbability／NeZero证明参数；实际源25–29和58–63中概率生产完整，不是遗漏caller前提。

七个_simp生成类型逐项语义：_1_3／_1_4／_1_5分别在Zero／OfNat及明确NeZero 2／3／4下给数字非零命题等于False；_1_6在NoZeroDivisors和两个真实非零因子下给乘积非零；_1_7在MonoidWithZero／IsReduced和a≠0下给全部自然数次幂非零（不暗需n>0）；_1_8在GroupWithZero和a≠0下给全部整数幂非零；_1_9在AddMonoidWithOne／CharZero下给自然数cast n+1非零，不需要假设任意实数序列有序。每项完整前提均在实际TYPE，不从名称推测更强无条件结论。

另外两个生成项真实位于Shao.Probability命名空间：bivariateLegendreRate.congr_simp要求真实measure相等、W相等、z相等并有NeZero原μ，右端实例随e_μ传递，结论只是同一canonical EReal值的同余；bivariateLogMGF.congr_simp在同μ／W的真实domain subtype上由theta相等给log值相等。二者不提供任意measure／参数之间的自由等式，不额外生产概率或最小值。它们虽不在Shao.OQ3 namespace，实际owner仍属本模块，不能漏查，也不意味着改写了root共享源码。

我随后末阶段实读Audit.lean：21–25行遍历env.constants并以env.getModuleIdxFor?的header.moduleNames精确判owner==Shao.OQ3.SourceCanonicalSaddle，不按namespace／stem筛选；26行拒绝新axiom，27–30行collectAxioms递归检查全部传递公理。31行每项打印DECL／完整TYPE／AXIOMS，32–40行统计。实际计数0 DEF／1 frozen THM／10 ALL THM／10 ALL DECL，即1public+9generated、0authoredprivate。

公理不是“一律三项”：_1_3／4／5／6／7／9共6项仅propext；主定理、两个congr_simp、_1_8共4项为[propext, Classical.choice, Quot.sound]。全10项实际公理都在标准白名单内，无新axiom／sorryAx，覆盖全部所属生成常量。没有把别命名空间2项或universes／typeclasses省略掉。

## 最后机械绑定及验收历史

### 精确source／scope／类型

当前本地源码、remote worktree源码、run源码快照均171行8038B，SHA256 `24200d85b6c4d13862ab166da8c7e6221ef87601216a125d5e8dc3260d0a7941`。冻结scope75实际70行6940B，SHA256 `d38dd216682cb45f1bffe2641c441d6e4ca08affa320c272e77740821a516c5f`；完整公开TYPE含letI hm0证明与scope白空格规范比较PASS。

声明终票198行SHA256 `eaec9cc1f96d67fdb56f7fe59e00c1af4c92661081ea2ba252e958208b32b435`及其101行盲前缀为历史接受门，不代替本次proof。R1原件仍绑定`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。当前proof source没有新增公开定义或跨模块private调用，没有source settings weakening。

### 唯一完整构建和首owner Audit

build-history.json实际28行1940B，SHA256 `c9367ed26540fa2b5719cc5a0669ec32bfa5cf36f44044b409ff68b630ba02e9`；恰一次完整源build01、exit0、5.8963729s，是当前冻结源首次成功。没有失败／partial／probe／proof repair／源修改或成功重跑。

build-01.log实际28行1504B，SHA256 `37a061bb7b717aac10835e80298aac8802f89c1be827d05f55d990b63f18fcd8`，非空。选读实际诊断确认6条style／instance warning、0error：62／63各一实例建议，141／146各unused `<;>`及unnecessary sequence两条，共2+2+2=6。它们不是数学／kernel错误；没有为了无warning而重编成功源，也没有把linter提示中的可关闭说明当作已修改设置。

首次actual-owner Audit exit0、5.0320519s；Audit.lean41行1780B SHA256 `30aa733636ba8f49ae96e4d8aba70942e5e11fe7f1919af0c89f831853076fcf`；Audit.log82行4752B SHA256 `1c49550b55ad2158fddcd7cba7a77b98f90ea46a786fe4245fda93a69b1dc7e3`。全部实际TYPE／公理和owner机制已独立核查，不以末行PASS代替。

构建记录为native -M8192／-j4／-DautoImplicit=false、taskset -c 14-17。复用U20c已独立核查的single-root import-view（manifest d060d63c06c0dcd5da7469194ac2016cfd98ed06982c32251acf2eb14c489c20），在lake env之后让view成为首个Shao root、保留其余Lake路径；对象仅符号链接只读引用，没有copy cache或写接受root目录。该环境不再使用v1已撤回的并列Shao逐模块fallback推断。

### 正式receipt、25前置源和git

数学／所有actualTYPE审查之后才读取正式receipt.json，219行11216B，SHA256 `0d20d7daf0dda654e48baf1eab18b48feffaff687f254a30106acd825cc02104`。状态AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW与本次独立终审先后相符；nonclaims明确保留邻域C2、均值局部逆、root A组装及其他根，未提前声称U21a已实现。本报告不使用作者route或receipt描述作为数学依据。

prerequisite-hashes.json正式27行2650B，SHA256 `a5f2b8d3549f9cdef4f66e0cf600b2f6e1f4698359b2f921ed64542c2608160d`，25 canonical相对源路径。仅末阶段对其当前own源做fresh hash绑定，不符／缺项0，独立compact重算`a2bc1daeb0e36fb2393964fd1e113b073b30ddf3419439097c29d2c7915a4867`，与声明阶段由接受字典并集独立得到的25项相同。没有重扫完整physical／public图、重验pins／对象／缓存hash或重复成功smoke。

当前branch `feat/oq3-source-canonical-saddle`，HEAD `7dcf60695c046d0d89e96b92ccd25604e444cfe9`，tree `0acb4f35dc49de4f27250df50bfd32838eb51d01`，status仅`?? Shao/OQ3/SourceCanonicalSaddle.lean`。从已接受PR156正常新分支，旧冻结heads仍为行政保存历史；本review未merge／reset／rebase／fetch／retarget／commit／pub，也不把旧源／票重写。

固定Lean v4.36.0-rc1／Mathlib807d3836b165983210ee2ecf3cd28f239436949c沿已通过声明／root v38绑定；本门按指示未重哈希稳定pins。所有远程项目读取均taskset14–17，未启动Lean或heavy任务、未动外部CPU0–9／80GiB及全局资源；原始完整日志留服务器，只读取实际声明选择和小诊断／机械摘要。

## 最终完整独立裁决及义务边界

STATUS: CORRECT

绑定冻结scope75完整SHA、当前171行24200d85完整SHA、全部10实际module-owner TYPE及公理、首次build01／Audit。完整source、所有locals、生成类型、真实公共API消费、原文语义及末阶段机械绑定均通过独立审查，未发现CRITICAL GAPS。此裁决不由声明票或kernel PASS单独推出。

原target→本节点实际消除：同一源P/q/w上的整个canonical ambient lift／K literal身份、真实一阶梯度和真正fderiv二阶、同π actual D的完整非零二次型正定、正q下标量鞍点方程、同canonical测试lambda0=saddleRate>0、实际det／lambda1／vCorr正以及correctedInverseScale=vCorr⁻¹。直接consumer是root A在U20b同一个最终w/q/P上同时消费U20c全局率唯一极小结论与本鞍点／Hessian／常数适配，保持真实有限乘积概率和同律余项见证。

剩余：本节点只给theta0处梯度／二阶，不声称整个邻域C2、均值映射邻域逆、统一far率间隙／概率界、标准化WC或Edgeworth；root A最终装配及原B/C/D等仍分别待闭，全部原A/B/C/D仍OPEN。U21a仍声明正确而DEFERRED_UNIMPLEMENTED，未纳入proof接受计数，也不声称一般KL9/10、最优beta或整体OQ3完成。

90行5685B盲前缀SHA256 `63f2d79e889268a797335ff3bfc90b2250160839d75cc5bad8f0a10cd3a2d3f9`逐字保留。初始IN_PROGRESS是落盘历史，本节CORRECT为完整proof终裁。本报告外未修改source／scope／receipt／Audit／旧票／shared／cache／pins或任何他人文件，没有新agent／chat／Lean／commit／PR；仍待lead整份final全文读取后才接受／发布。
