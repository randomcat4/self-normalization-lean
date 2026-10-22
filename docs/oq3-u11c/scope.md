# OQ3-U11c：原子律的有限重积期望误差

冻结候选v1，PROPOSED；尚未实现。拟文件 `Shao/OQ3/AtomicProductControl.lean`，导入 `Shao.OQ3.AtomicTailControl`、`Shao.OQ3.SampleBoundary` 和已有缓存 `Mathlib.MeasureTheory.Integral.Pi`，namespace Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，499–520。沿实际同一固定原子支撑，直接用权重L1证明n重积下有界可测期望差，再接U9a的真实似然权重上界和U11b尾界。这给(28)所需比较误差的直接证明路线，不依赖测度TV新缓存，不把weight L1重新命名为TV。

## 冻结候选声明

```lean
theorem atomicMeasure_integrable_of_atom_bound (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (B : ℝ) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hf : ∀ i, |f (fixedAtom i)| ≤ B) :
  Integrable f (atomicMeasure w)

theorem atomicMeasure_integral_sub_le (w v : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hsw : Summable w) (hsv : Summable v) (B : ℝ) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hf : ∀ i, |f (fixedAtom i)| ≤ B) :
  |(∫ x, f x ∂atomicMeasure w) - (∫ x, f x ∂atomicMeasure v)| ≤
    B * atomicMassL1 w v

theorem atomic_iid_integral_sub_le (w v : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hsw : HasSum w 1) (hsv : HasSum v 1) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (f : Shao.Path n → ℝ) (hf : Measurable f)
    (hbound : ∀ z : Fin n → AtomicIndex, |f (fun i => fixedAtom (z i))| ≤ B) :
  |(∫ z, f z ∂Measure.pi (fun _ : Fin n => atomicMeasure w)) -
      (∫ z, f z ∂Measure.pi (fun _ : Fin n => atomicMeasure v))| ≤
    B * (n : ℝ) * atomicMassL1 w v

theorem finite_limit_iid_integral_tail_le (ell : ℝ) (hell : 0 ≤ ell) (q : ℝ)
    (p : Fin 4 → ℝ) (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hl : ∀ i, 0 ≤ limitingBase ell p r i) (hj : ∀ i, 0 ≤ finiteBase ell p r J i)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B) (f : Shao.Path n → ℝ) (hf : Measurable f)
    (hbound : ∀ z : Fin n → AtomicIndex, |f (fun i => fixedAtom (z i))| ≤ B) :
  |(∫ z, f z ∂Measure.pi (fun _ : Fin n => atomicMeasure (limitingMass ell p r))) -
      (∫ z, f z ∂Measure.pi (fun _ : Fin n => atomicMeasure (finiteMass ell p r J)))| ≤
    B * (n : ℝ) * compensationTailConstant ell * (∑' j, r (J + j))

theorem finite_limit_likelihood_tail_le (ell : ℝ) (hell : 0 ≤ ell) (q : ℝ) (hq : q ≤ 2)
    (p : Fin 4 → ℝ) (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hl : ∀ i, 0 ≤ limitingBase ell p r i) (hj : ∀ i, 0 ≤ finiteBase ell p r J i)
    (n : ℕ) :
  |(∫ z, (sourceTail q n).indicator (fun z => Real.exp (-ell * normalDeviation q z)) z
      ∂Measure.pi (fun _ : Fin n => atomicMeasure (limitingMass ell p r))) -
    (∫ z, (sourceTail q n).indicator (fun z => Real.exp (-ell * normalDeviation q z)) z
      ∂Measure.pi (fun _ : Fin n => atomicMeasure (finiteMass ell p r J)))| ≤
    Real.exp (11 * ell * (n : ℝ)) * (n : ℝ) * compensationTailConstant ell *
      (∑' j, r (J + j))
```

零定义、五公开目标。首两条允许任意非负可和权重，不假设概率；它们的可积性来自实际原子级数绝对可和，不能依赖不可积积分总化为零。首两条不要求f全局可测，因为该可数原子测度下既有integrable_atomicMeasure_iff涵盖任意原子值函数。第三条起显式要求HasSum质量为1和真实可测性，构造两个实际概率律及其有限产品，任何积分交换都须真实可积。hbound只需在共同原子n元组上成立，不能把似然函数错误视为全实路径上有界。n=0须包括。

预计逐坐标替换/Fubini证明第三条：每一步比较一个原子积分，先验证有界可积与参数积分；其余坐标保持概率，逐步累积n个B*L1。不能以乘积积分在不可积时的总化零分支代替Fubini。第四条的limitingMass/finiteMass非负与质量1必须从hl/hj/hr、hM/hc与既有HasSum约束实际推出，非奇异门此时真实消费；ell>=0和hs支持U11b。第五条的可测性来自sourceTail_measurable和normalDeviation连续，原子支撑上界用fixedAtom_normalValue_lower→normal_likelihood_weight_bound以及indicator非负绝对值界。

这直接完成源(28)比较误差所需的权重版结论：乘sqrt(2*pi*n)后得到显式Cn比较误差，不需要在本模块引入TV符号。Mathlib TV采取完整变化范数，若后续陈述成TV仍须独立桥与归一化。此单元不证明源(27)产品精确换测度、不证明逆倾斜原律的TV、不证明(30)常数连续性、LLT/尖点/实际witness。根A/B/C/D仍OPEN，p/q/ell在r/J/n前固定。
