# Unit106 frozen actual product population

Main lead read the complete original p53.md, especially §3, and freezes these exact17 declarations (3literaldefs/14theoremtypes) before implementation. Use independently grouped (A,B,eta) and (C,epsilon) blocks. The first block is the actual Unit105 uniform-noise/signedshift law, the second is the actual Unit103 signed-amplitude law on an independent copy of the completed labels/signs. The source law is fixed before q/tau and sampling.

```lean
def sparsePopulationMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    Measure ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) :=
  (sparseGBaseMeasure α x N).prod (sparseSignedLabelMeasure α x N)

def sparsePopulationG (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)) : ℝ :=
  sparseG α x N z.1

def sparsePopulationZ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)) : ℝ :=
  sparseSignedAmplitude α x N z.2

theorem sparsePopulationMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparsePopulationMeasure α x N)

theorem sparsePopulationG_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationMeasure α x N).map (sparsePopulationG α x N) =
    (sparseGBaseMeasure α x N).map (sparseG α x N)

theorem sparsePopulationZ_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationMeasure α x N).map (sparsePopulationZ α x N) =
    (sparseSignedLabelMeasure α x N).map (sparseSignedAmplitude α x N)

theorem measurable_sparsePopulationG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparsePopulationG α x N)

theorem measurable_sparsePopulationZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparsePopulationZ α x N)

theorem sparsePopulationG_indep_Z :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ProbabilityTheory.IndepFun (sparsePopulationG α x N) (sparsePopulationZ α x N)
    (sparsePopulationMeasure α x N)

theorem integrable_sparsePopulationG_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparsePopulationG α x N z| ^ q) (sparsePopulationMeasure α x N)

theorem integrable_sparsePopulationZ_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparsePopulationZ α x N z| ^ q) (sparsePopulationMeasure α x N)

theorem integral_sparsePopulationG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparsePopulationG α x N z ∂(sparsePopulationMeasure α x N)) = 0

theorem integral_sparsePopulationZ_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ z, sparsePopulationZ α x N z ∂(sparsePopulationMeasure α x N)) = 0

theorem integral_sparsePopulationG_sq_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (1 / 3 : ℝ) ≤ ∫ z, (sparsePopulationG α x N z) ^ 2 ∂(sparsePopulationMeasure α x N)

theorem integral_sparsePopulationZ_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ z, (sparsePopulationZ α x N z) ^ 2 ∂(sparsePopulationMeasure α x N)

theorem integrable_sparsePopulationZ_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Integrable (fun z => Real.exp (τ * |sparsePopulationZ α x N z| ^ α))
    (sparsePopulationMeasure α x N)

theorem integral_sparsePopulationZ_exp_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ z, Real.exp (τ * |sparsePopulationZ α x N z| ^ α) ∂(sparsePopulationMeasure α x N)) ≤ (5 / 4 : ℝ)
```

This pays actual component marginal laws, G/Z independence, positive-order moments, finite zero means, second-moment nondegeneracy and the full0<tau<=1 feature exponential bound. Every moment statement requires honest underlying first/square L1; these are available only after qualified105 and103 source-bound acceptance. Ganalytictypes and strictZsquare retain alpha>0/sameCore; Zmean/allq/exp needalpha>0only. No Gsymmetry/kernel/realencoding/iid/positiveR/events/conditionalestimates/tails is certified. P53/OQ6/RS2 OPEN. No separateSOURCEcontext is automatic under currentstreamlinedpolicy.


Original freezeMD69fb31cff3c7b7d7534bd3ce0cf2ac9c3f152264c94ce4b633909f308a6f05a7/contractsJSON3d4927cc02dd702b6747f1ba0fae1b98f7199f04f248a1695c027725c99e84f5 unchanged. Canonicalsource e8783d2b2a7d75f60cb1ef1fe8e4c805a4c524f519a4292ff4e5dc084da6401d /10098B. Qualifiedexact105/103dependencies are reused.
