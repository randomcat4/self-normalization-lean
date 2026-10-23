# Unit105 frozen source interfaces — SparseProjectionLaw

Planning frozen before implementation. Ten declarations: two literal definitions and eight theorem types. Source p53 §3, actual G=A+ηd_B. All six analytic theorems keep α>0 and the same selection Core. Full x and N fixed before every q>0.

Reuse the exact P35.noiseLaw = cond volume Icc[-1,1], its honest L1/zero mean/second moment1/3; product it independently with the actual signedshift tag law. No specialized P35 category coefficient enters this law.

```lean
def sparseGBaseMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure (ℝ × (ℕ × Bool)) :=
  Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)

def sparseG (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (z : ℝ × (ℕ × Bool)) : ℝ :=
  z.1 + sparseSignedShift α x N z.2

theorem sparseGBaseMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseGBaseMeasure α x N)

theorem measurable_sparseG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseG α x N)

theorem integrable_sparseG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (sparseG α x N) (sparseGBaseMeasure α x N)

theorem integral_sparseG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseG α x N z ∂(sparseGBaseMeasure α x N)) = 0

theorem integrable_sparseG_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun z => (sparseG α x N z) ^ 2) (sparseGBaseMeasure α x N)

theorem integral_sparseG_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, (sparseG α x N z) ^ 2 ∂(sparseGBaseMeasure α x N)) =
    (1 / 3 : ℝ) + ∫ w, (sparseSignedShift α x N w) ^ 2 ∂(sparseSignedLabelMeasure α x N)

theorem integral_sparseG_sq_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (1 / 3 : ℝ) ≤ ∫ z, (sparseG α x N z) ^ 2 ∂(sparseGBaseMeasure α x N)

theorem integrable_sparseG_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseG α x N z| ^ q) (sparseGBaseMeasure α x N)
```

The square formula requires actual product L1, both square L1 and cross-product L1 before integral splitting/Fubini. Meanzero requires honest G L1. The lower bound follows from the nonnegative actual shift square integral. No G symmetry/exponential moment/jointGZ/iid/encoding/kernel/trueR/events/tails claim; P53/OQ6/RS2 OPEN. Unit104 independent final acceptance is still pending, so implementation remains ungranted. The main lead designed these interfaces; the independent reviewer must not author their proofs.


Freeze identities remain MD3542b802dc27064d1825a383c98bf3e39841f0132065f49fee82401844b2b2d8 / JSON97738d5d5efd5554f746cf2bba91612318d3e322a9fc7541cc1ebb1cc2377ad9. Final canonical source SHA256 3e335bcb21f2510c611743770f8eb9682642bcc11091f6a751ddd54420b981b1,10256B. One explicit official Integral.Prod import was added for an observed compiler closure gap; all10mathematical contracts and assumptions are unchanged.
