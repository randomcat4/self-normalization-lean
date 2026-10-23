# Root exact freeze: actual short-time integrals and remaining-clock sums

Root fully read all three complete declarations and the entire source/payment contract, original main LF724–745 and supplement LF624–650/LF2655–2698. Author common_marked_outside_author is authorized next to implement new Shao/Probability/SourceShortTimeGrid.lean. Preserve the actual R and T*R integrability at zero and exact 7/3 and (15/14)*y² constants, the actual conditional-law clock T_i=(n-i)*m2, all-real-power comparison with explicit 2^|a|, exact finite index guards and the absolute discrete R/TR bounds including the final y² improvement.

Empty index sets and reversed/degenerate integration intervals are covered without a nonempty assumption. Positive m2/gamma and m2<=gamma² must come from actual source data. The windows are genuinely disjoint half-open intervals before integral summation; no arbitrary grid or integral estimate is supplied as a premise. Existing exact source-law evidence is reused. This closes a real analytic time dependency only; summing the actual regional norms and identifying true kernel/probability contributions remain subsequent obligations. One complete independent final source/proof/all-owned semantic review and exact server kernel/transitive-axiom evidence suffice for the frozen module. Continue the next source consumer immediately after this unit.

drafts/c12-cone-derivatives/short-time-grid-candidate-declarations.md SHA256 72bdee7fd23d370a7bdc4adc717f9f8fdb62ae0db5a783994dd9903d0fd95e34

# Actual short-time integrals and conditional remaining-clock sums

State: AWAITING_ROOT_FREEZE; no new production source or Lean gate started.
Proposed module: Shao.Probability.SourceShortTimeGrid.

```lean
import Shao.Probability.SourceFourierScale
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
theorem sourceShortTime_R_integrals (y : ℝ) (hy : 0 < y) :
    let R : ℝ → ℝ := fun T => 1 + Real.sqrt y * T ^ (-(1 / 4 : ℝ))
    IntegrableOn R (Set.Ioo 0 (y ^ 2)) ∧
      IntegrableOn (fun T => T * R T) (Set.Ioo 0 (y ^ 2)) ∧
      (1 / y ^ 2) * (∫ T in Set.Ioo 0 (y ^ 2), R T) = (7 / 3 : ℝ) ∧
      (1 / y ^ 2) * (∫ T in Set.Ioo 0 (y ^ 2), T * R T) = (15 / 14 : ℝ) * y ^ 2

theorem sourceTruncation_remainingClock_power_integral_comparison :
    ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
      ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
        (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
        (∫ z : ℝ, z ∂ν0) = 0 →
        ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
          Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
          ∀ L2 y a : ℝ, 2 ≤ L2 → 0 < y →
            let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
            let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
            let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
            let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
            let J : Finset ℕ := (Finset.range (n + 1)).filter
              (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
            IntegrableOn (fun t : ℝ => t ^ a) (Set.Icc (L2 * gamma ^ 2 / 2) (y ^ 2)) ∧
              m2 * (∑ i ∈ J, T i ^ a) ≤
                (2 : ℝ) ^ |a| * (∫ t in Set.Icc (L2 * gamma ^ 2 / 2) (y ^ 2), t ^ a)

theorem sourceTruncation_shortClock_R_sums :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ L2 y : ℝ, 2 ≤ L2 → 0 < y →
              let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
              let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
              let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ρ) / variance (id : ℝ → ℝ) ρ
              let T : ℕ → ℝ := fun i => ((n - i : ℕ) : ℝ) * m2
              let J : Finset ℕ := (Finset.range (n + 1)).filter
                (fun i => n / 2 < i ∧ L2 * gamma ^ 2 ≤ T i ∧ T i < y ^ 2)
              let R : ℝ → ℝ := fun t => 1 + Real.sqrt y * t ^ (-(1 / 4 : ℝ))
              m2 / y ^ 2 * (∑ i ∈ J, R (T i)) ≤ C ∧
                m2 / y ^ 2 * (∑ i ∈ J, T i * R (T i)) ≤ C * y ^ 2
end Shao.Probability
```


drafts/c12-cone-derivatives/short-time-grid-source-contract.md SHA256 7049483e3c6388775e287a1179cc81233777a6219e1808aa7dbb6c024fc20048

# Short-time integrals and actual remaining-clock sums — source contract

Original main LF724–745 (equation Rintegrals/3.46), supplement LF624–650
and LF2655–2698. The exact main R integrals are 7/3 and (15/14)y² after
factoring y^-2. Supplement's five regional time integrals are converted to
actual remaining-index sums on T_i=(n-i)m2 using disjoint grid windows.

The complete three statements in short-time-grid-candidate-declarations.md
are proposed unchanged for SourceShortTimeGrid. No production gate has begun.
Read-only original supplement SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd;
main is the same immutable original source in C:/game/shao/current/c12/main.tex.

The first theorem proves true Lebesgue integrability and exact integrals of
the source R(T,y)=1+sqrt(y)*T^(-1/4) and T*R(T,y) on (0,y²), including the
improper endpoint at zero. It does not assume any antiderivative or integral.

The second theorem uses the actual conditional source law and exact clock.
All probability, integrability, positive m2, gamma>0 and m2<=gamma² payments
come from accepted SourceTruncationBridge/SourceFourierScale and original
normalization, mean, cutoff and budget premises. L2>=2 is exactly the grid
condition. For each selected index, T_i>=L2*gamma²>=2m2, so its actual window
(T_i-m2,T_i] lies inside [T_i/2,T_i] and the global integration interval
[L2*gamma²/2,y²]. The actual half-open grid windows are disjoint. A proof must
pay disjointness and positivity/integrability before summing the true interval
integrals. The power comparison holds for every real a with the explicit
2^|a| factor; it is not a supplied bound or arbitrary grid hypothesis.

The selected finite set includes exactly 0<=i<=n with n/2<i, the original
lower time guard and strict upper y² guard. Natural n/2<i for integer i agrees
with the source real inequality. An empty range when y² is below the lower
cutoff is legitimate and must be handled. There is no new nonempty assumption.

The third theorem pays the actual m2-weighted discrete R and T*R sums, with
one absolute constant chosen before every raw source, clock or spatial scale.
It consumes the exact first theorem and actual window comparison for powers
0,-1/4,1,3/4; lower-cutoff interval integrals are bounded by the positive full
integrals. It retains the y² improvement in the T*R sum. No pointwise D/W or
probability envelope is a premise.

These are actual analytic time dependencies for the completed Region1/2
norm producers. Next consumer will sum the true two-dimensional post-IBP
norm integrals with original raw n|mu| and n*m3 coefficients, then extend to
the other regions and actual whole-u IBP assembly. The original source choice
h=epsilon0/(1+y), explicit cutoff h_x<=h, low kappa and outside smallness
payments remain separate adapters. No norm bound is identified with a
probability contribution, and no C1/C2 root closure is claimed.
