# OQ3-U7：真实协方差正定、横向方差与正曲率

冻结候选v1，PROPOSED；未实现，须独立声明审查。拟文件 `Shao/OQ3/RegularCovariance.lean`，导入U3c、U5a与固定 `Mathlib.Probability.Moments.Variance`。命名空间Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。该固定库的covariance/variance定义已只读确认，两个模块缓存实际存在。

来源R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，238–258行。Delta是倾斜律pi下(X,X²)的真实协方差，sigma²=Var_pi(Y)，transverseVariance在下文表示源的tau²（不是tau），因而严格曲率比较是q/(32*transverseVariance)>1/30>ell。

一般概率mu的紧支撑保证所有用到的多项式和乘积真正可积，不能依赖方差由无穷值toReal得到0的总化分支。正基点集合中-1、1、2已足以排除非零二次多项式为AE常量；可消费全部四基点正质量，最终对每个真实有限阶段和极限律都须从实际w质量建立此条件。严格正二次型须先与实际Delta的三个元素绑定，不能预设其正定。

## 待冻结导出声明

```lean
def parabolaCovariance (mu : Measure ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![ProbabilityTheory.variance (fun x : ℝ => x) mu,
      ProbabilityTheory.covariance (fun x : ℝ => x) (fun x : ℝ => x ^ 2) mu],
    ![ProbabilityTheory.covariance (fun x : ℝ => x) (fun x : ℝ => x ^ 2) mu,
      ProbabilityTheory.variance (fun x : ℝ => x ^ 2) mu]]

def normalVariance (mu : Measure ℝ) : ℝ :=
  ProbabilityTheory.variance normalValue mu

def transverseVariance (mu : Measure ℝ) : ℝ :=
  (parabolaCovariance mu).det / normalVariance mu

theorem centered_parabola_integral_eq (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (a b : ℝ) :
  (∫ x, (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2 ∂mu) =
    a ^ 2 * parabolaCovariance mu 0 0 +
      2 * a * b * parabolaCovariance mu 0 1 + b ^ 2 * parabolaCovariance mu 1 1

theorem centered_parabola_integral_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i})
    (a b : ℝ) (hne : a ≠ 0 ∨ b ≠ 0) :
  0 < ∫ x, (a * (x - ∫ y, y ∂mu) + b * (x ^ 2 - ∫ y, y ^ 2 ∂mu)) ^ 2 ∂mu

theorem parabolaCovariance_det_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i}) :
  0 < (parabolaCovariance mu).det

theorem normalVariance_eq_covariance (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) :
  normalVariance mu = 64 * parabolaCovariance mu 0 0 -
    16 * parabolaCovariance mu 0 1 + parabolaCovariance mu 1 1

theorem normalVariance_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i}) :
  0 < normalVariance mu

theorem transverseVariance_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i}) :
  0 < transverseVariance mu

theorem transverseVariance_le_variance_id (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hbase : ∀ i : Fin 4, 0 < mu.real {baseAtom i}) :
  transverseVariance mu ≤ ProbabilityTheory.variance (fun x : ℝ => x) mu

theorem atomic_id_variance (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  ProbabilityTheory.variance (fun x : ℝ => x) (atomicMeasure w) = q - q ^ 2 / 16

theorem sourceEll_lt_one_div_thirty : sourceEll < (1 : ℝ) / 30

theorem atomic_transverse_bounds (q : ℝ) (hlo : 1 < q) (hhi : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < transverseVariance (atomicMeasure w) ∧
    transverseVariance (atomicMeasure w) ≤ q - q ^ 2 / 16 ∧
    (1 : ℝ) / 30 < q / (32 * transverseVariance (atomicMeasure w))

theorem atomic_curvature_pos (q : ℝ) (hlo : 1 < q) (hhi : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < normalVariance (atomicMeasure w) / (parabolaCovariance (atomicMeasure w)).det -
    32 * sourceEll / q

theorem exists_source_finite_and_limit_regular_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (atomicMeasure (limitingMass sourceEll p r)) ∧
      0 < normalVariance (atomicMeasure (limitingMass sourceEll p r)) ∧
      0 < (parabolaCovariance (atomicMeasure (limitingMass sourceEll p r))).det ∧
      (0 < normalVariance (atomicMeasure (limitingMass sourceEll p r)) /
        (parabolaCovariance (atomicMeasure (limitingMass sourceEll p r))).det - 32 * sourceEll / q) ∧
      ∀ J : ℕ, IsProbabilityMeasure (atomicMeasure (finiteMass sourceEll p r J)) ∧
        0 < normalVariance (atomicMeasure (finiteMass sourceEll p r J)) ∧
        0 < (parabolaCovariance (atomicMeasure (finiteMass sourceEll p r J))).det ∧
        (0 < normalVariance (atomicMeasure (finiteMass sourceEll p r J)) /
          (parabolaCovariance (atomicMeasure (finiteMass sourceEll p r J))).det - 32 * sourceEll / q)
```

三定义、十二目标。第1条把第2条严格正二次型与真实协方差矩阵绑定，覆盖源的正定性含义；没有把det>0单独当成任意矩阵正定。normalVariance是sigma²，transverseVariance是tau²，不能对tau²再次误平方。源kappa²/2=q/(32tau²)只使用该正确分母。

方差toReal定义的失真风险须以实际有界L²/连续可积证据消除；不允许从不存在的积分假定推出AE常量。允许用积分非负/零条件或正确方差零判据，在三个正基点排除非零居中二次式。

横向上界可由严格正sigma²和实际恒等式 Var(X)*sigma²-det(Delta)=(8Var(X)-Cov(X,X²))²建立；该代数恒等式必须连接真实积分，不能把它预设为假设。q>1给严格的1/30下界，sourceEll=log(31/30)<1/30独立证明。有限/极限最终家族仍共用同一p/q/eps，在全部r/J/n之前固定。

本单元不证明全局正尾极小唯一性、实际二元累积母函数的微分、LLT、曲边界常数、尖点、产品TV或对角。不得把本单元的Lambda1正性和已有正KL当成源第3节完整极小性论证已经完成。根ABCD仍OPEN。
