# Frozen actual source growing-microtime sum tail

Root fully read all three mathematical candidate documents once. Approved original supplement908-920 scope: actual fixed-x conditional iid law, nonzero conditional mean, uncentered true raw2 clock and original lambda0=32(1+y). Before any original law, choose L2>0 and 0<epsilon0<=1/(192sqrt(L2+1)). Literal C=2exp17 is fixed. Original nearby payment gives Lambda<=1/2; gamma<=2hcut<=2h_y; the true quadratic exponent is <=2/9, so total <=17. Fin0 empty tail/energy and Fin n actual product laws retained.

Owner /root/common_growing_microtime_chernoff_candidate; only new Shao/Probability/SourceGrowingMicrotimeTail.lean plus assigned drafts/c12-growing-microtime outputs. Existing accepted SourceGrowingTiltParameterPayment and all other source/object/cache inputs read-only. Three private plus one public complete heads below frozen literally; zero new global/private definitions. Additional private helper THEOREMS are allowed with complete final source/type/AX review, superseding the candidate local-have-only restriction. No changed assumptions/constants/newpublicheads/newdefinitions without full literal addendum before implementation.

All Lean/heavy designated server only, pinned versions/read-only package view, CPU10-13/root-heavy.lock/M8192/j4/autoImplicitfalse; first whole-source success emits original-o and directrc captured immediately. Newsource UTF8LF firstwrite. Failed attempts preserved; successful checks/old producers/old native DAGs not replayed. Fresh author-independent full source-to-statement/proof/all actual private/generated types/values/transitiveAX required. AX whitelist propext/Classical.choice/Quot.sound; no sorry/admit/newaxiom/unsafe/native_decide. This is a source tail producer, not localized-noise derivative or C1/C2 root closure. Continue necessary next source dependency after each complete part.

```lean
import Shao.Probability.SourceFourierScale
import Shao.Probability.FiniteIID
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Shao.Probability

private theorem smt_one_step_exp
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 ≤ h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (theta : ℝ) (htheta : |theta| * h ≤ 1) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    Integrable (fun a : ℝ => Real.exp (theta * a)) nu ∧
      (∫ a : ℝ, Real.exp (theta * a) ∂nu) ≤
        Real.exp (|theta| * |mu| + 2 * theta ^ 2 * raw2)

private theorem smt_product_exp_energy
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 ≤ h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (theta : ℝ) (htheta : |theta| * h ≤ 1) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
    let S : Shao.Path m → ℝ := fun a => Shao.prefixSum a m
    let Q : Shao.Path m → ℝ := fun a => Shao.prefixSquares a m
    Integrable Q pi ∧
      (∫ a : Shao.Path m, Q a ∂pi) = (m : ℝ) * raw2 ∧
      Integrable (fun a : Shao.Path m => Real.exp (theta * S a)) pi ∧
      (∫ a : Shao.Path m, Real.exp (theta * S a) ∂pi) ≤
        Real.exp ((m : ℝ) * |theta| * |mu| +
          2 * theta ^ 2 * ((m : ℝ) * raw2))

private theorem smt_product_abs_tail
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 ≤ h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (m : ℕ) (theta r : ℝ)
    (hthetaPos : 0 < theta) (hr : 0 < r)
    (htheta : theta * h ≤ 1) :
    let mu : ℝ := ∫ a : ℝ, a ∂nu
    let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
    let S : Shao.Path m → ℝ := fun a => Shao.prefixSum a m
    pi.real {a : Shao.Path m | r ≤ |S a|} ≤
      2 * Real.exp ((m : ℝ) * theta * |mu| +
        2 * theta ^ 2 * ((m : ℝ) * raw2) - theta * r)

theorem sourceTruncation_growing_microtime_abs_tail
    (L2 epsilon0 : ℝ) (hL2 : 0 < L2)
    (hepsilon0 : 0 < epsilon0)
    (hepsilon0Bound : epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)))
    (nu0 : Measure ℝ) [IsProbabilityMeasure nu0] (n : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) nu0)
    (hnorm : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu0) = 1)
    (hmean : (∫ a : ℝ, a ∂nu0) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ epsilon0 / 2)
    (hR : Shao.truncationBudget nu0 n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 2 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x)))
    (m : ℕ) (hm : m ≤ n) :
    let nu : Measure ℝ := ProbabilityTheory.cond nu0
      {a : ℝ | |a| ≤ epsilon / (1 + x)}
    let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
    let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) nu
    let gamma : ℝ := m3 / V
    let T : ℝ := (m : ℝ) * raw2
    let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => nu)
    let C : ℝ := 2 * Real.exp 17
    T ≤ L2 * gamma ^ 2 →
      Integrable (fun a : Shao.Path m => Shao.prefixSquares a m) pi ∧
      (∫ a : Shao.Path m, Shao.prefixSquares a m ∂pi) = T ∧
      pi.real {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|} ≤
        C * Real.exp (-4 * y ^ 2)

end Shao.Probability
```

Proof-local planned lets (not new definitions):

```lean
let hcut : ℝ := epsilon / (1 + x)
let h : ℝ := epsilon0 / (1 + y)
let mu : ℝ := ∫ a : ℝ, a ∂nu
let R : ℝ := Shao.truncationBudget nu0 n x
let Lambda : ℝ := (1 + y) * (n : ℝ) * |mu| +
  (1 + y) ^ 3 * (n : ℝ) * m3
let lambda0 : ℝ := 32 * (1 + y)
```
