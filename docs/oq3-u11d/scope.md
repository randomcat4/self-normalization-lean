# OQ3-U11d：矩连续性与修正常数的正尾预算

冻结修订v2，PROPOSED（v1保留为历史）；尚未实现。拟文件 `Shao/OQ3/CorrectedScaleContinuity.lean`，导入 `Shao.OQ3.AtomicProductControl`、`Shao.OQ3.RegularCovariance` 和已有缓存 `Mathlib.Analysis.Matrix.Normed`，namespace Shao.OQ3，open MeasureTheory，open scoped Matrix Matrix.Norms.Elementwise，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，239–257、438–443、523–529。源v_corr²=ell²*(S−32ell D/q)，ell>0、S−32ell D/q>0时其正根逆为下面定义。此单元给真实原子矩连续性、正域稳定以及在未来整条质量序列之前取得的正尾cap。

## 冻结候选声明

```lean
def correctedInverseScale (ell q : ℝ) (mu : Measure ℝ) : ℝ :=
  (ell * Real.sqrt (normalVariance mu -
    (32 * ell / q) * (parabolaCovariance mu).det))⁻¹

theorem atomic_power_integral_sub_le (w v : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hsw : HasSum w 1) (hsv : HasSum v 1) (k : ℕ) :
  |(∫ x : ℝ, x ^ k ∂atomicMeasure w) - (∫ x : ℝ, x ^ k ∂atomicMeasure v)| ≤
    (4 + Real.sqrt 10) ^ k * atomicMassL1 w v

theorem exists_atomic_covariance_radius (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsw : HasSum w 1) (eta : ℝ) (heta : 0 < eta) :
  ∃ delta : ℝ, 0 < delta ∧ ∀ (v : AtomicIndex → ℝ),
    (∀ i, 0 ≤ v i) → HasSum v 1 → atomicMassL1 v w < delta →
      ‖parabolaCovariance (atomicMeasure v) - parabolaCovariance (atomicMeasure w)‖ < eta ∧
      |normalVariance (atomicMeasure v) - normalVariance (atomicMeasure w)| < eta

theorem source_atomic_corrected_radicand_pos (q : ℝ) (hlo : 1 < q) (hhi : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hbase : ∀ i : Fin 4, 0 < w (Sum.inl i))
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < normalVariance (atomicMeasure w) -
    (32 * sourceEll / q) * (parabolaCovariance (atomicMeasure w)).det

theorem exists_atomic_corrected_scale_radius (ell : ℝ) (hell : 0 < ell) (q : ℝ)
    (hq : 0 < q) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hsw : HasSum w 1)
    (hR : 0 < normalVariance (atomicMeasure w) -
      (32 * ell / q) * (parabolaCovariance (atomicMeasure w)).det)
    (eta : ℝ) (heta : 0 < eta) :
  ∃ delta : ℝ, 0 < delta ∧ ∀ (v : AtomicIndex → ℝ),
    (∀ i, 0 ≤ v i) → HasSum v 1 → atomicMassL1 v w < delta →
      0 < normalVariance (atomicMeasure v) -
        (32 * ell / q) * (parabolaCovariance (atomicMeasure v)).det ∧
      |correctedInverseScale ell q (atomicMeasure v) -
        correctedInverseScale ell q (atomicMeasure w)| < eta

theorem exists_corrected_scale_future_tail_cap (ell : ℝ) (hell : 0 < ell) (q : ℝ)
    (hq : 0 < q) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hj : ∀ i, 0 ≤ finiteBase ell p r J i)
    (hR : 0 < normalVariance (atomicMeasure (finiteMass ell p r J)) -
      (32 * ell / q) * (parabolaCovariance (atomicMeasure (finiteMass ell p r J))).det)
    (eta : ℝ) (heta : 0 < eta) :
  ∃ cap : ℝ, 0 < cap ∧ ∀ (s : ℕ → ℝ),
    (∀ j, 0 ≤ s j) → Summable s → (∀ j : Fin J, s j.val = r j.val) →
    (∀ i, 0 ≤ limitingBase ell p s i) → (∑' j, s (J + j)) < cap →
      0 < normalVariance (atomicMeasure (limitingMass ell p s)) -
        (32 * ell / q) * (parabolaCovariance (atomicMeasure (limitingMass ell p s))).det ∧
      |correctedInverseScale ell q (atomicMeasure (limitingMass ell p s)) -
        correctedInverseScale ell q (atomicMeasure (finiteMass ell p r J))| < eta
```

一个定义、五公开目标。k=0包括。所有真正的原子矩积分须先从共同有界支撑与真实概率门保证可积；不能以不可积variance/covariance/integral的总化值证明连续性。预计以原始一至四阶矩表示实际covariance及normalVariance，再用有限维多项式连续性和实际U11c原子积分L1界给半径；不能把弱收敛在无共同矩支配时当作矩收敛。本处共同原子支撑有固定紧界，恰提供该支配。

correctedInverseScale对任意输入定义为总化表达式，只有声明中明确的ell>0与正radicand邻域才消费为实际正根逆。不能在sqrt=0/分母0处宣称连续。第三目标由已审U7的det>0与curvature正性相乘给源族正域，不需要新全局鞍点主张。

最后目标的cap在整条未来s之前取得。参照律只取r的前J项，r无需Summable；hc/hM/hj/hr真正给该finiteMass概率，hR给正域。任意未来s须与同一前缀逐项相同、非负可和且实际limit旧质量非负；hM/hc又给limit质量1。由前缀相等得finiteMass ell p s J=finiteMass ell p r J，再用U11b L1<=C(ell)*完整未来s尾与generic正半径，cap可取delta/C(ell)>0。该顺序使cap只需参照有限前缀：用于U11a时可给u:Fin J→ℝ零延拓作为r，而非用尚未构造的无限s决定cap。

此处严格的点态有限参考radicand正性不能从一条未知极限的收敛来倒推。源应用可先用第三目标和有限源族的正旧质量/约束取得hR；limitingBase非负由既有同一p/q/eps预算提供。cap存在只是(30)的正预算门，不声称已构造实际LLT/witness、尖点展开或最终固定P的对角序列；根A/B/C/D保持OPEN。

## v2显式范数修复

实际首轮elaboration发现v1导入没有任何Matrix Norm实例，签名中的矩阵范数未明确而无法elaborate。v2增加固定已缓存Normed导入并明确Elementwise作用域，矩阵范数为最大元素绝对值（两层有限sup），与既有Pi拓扑相容；不是行和算子范数。五个声明的文本量词/假设/结论和定义体保持不变，只明确此前未指定的范数实例。v1原文件和原声明审查保留，v2须再次独立声明审查后才继续实现。
