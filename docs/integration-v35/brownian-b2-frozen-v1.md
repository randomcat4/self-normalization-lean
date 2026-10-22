# Brownian B2 root freeze v1

Independent review CORRECT: brownian-route-review-v1.md/json. Original actual Brownian B1 objects and IsBrownianReal inputs unchanged.

Route SHA256 596ba300939b539e470e8d3a48b294d090e0a8a1e26c143abf0ba7b6c7c4ff16
Statement proposal SHA256 d929bd9e124348b8a1705e25079653be33c51472bcd7fe7f40f6f6e1bff9b90b

The exact definitions and theorem statements in the reviewed proposal are frozen, with module and namespace assignment as follows (reviewer explicitly approved):
- Shao.Probability.BrownianSup namespace for all shared adapters.
- M: Shao/Probability/RademacherGrid.lean owns radMeasure, radSurvival, coarseStrip, coarseProbability; rademacher_max_fourth_tail and rademacher_coarse_comparison.
- G: Shao/Probability/BrownianGridBridge.lean imports M and certified BrownianSup; owns gridTime, brownianGridEvent, brownianGridProbability; rademacher_coarse_tendsto_brownian_grid and brownian_dyadic_grid_tendsto_probability.
- Root S: Shao/Probability/BrownianFirstTerm.lean owns firstTerm exactly (4/Real.pi)*Real.exp (-(Real.pi^2/8)/x^2); rademacher_eventual_firstTerm_envelope, actual_brownian_firstTerm_envelope, actual_brownian_firstTerm. Root may separate finite spectral proof into BrownianSpectralEnvelope.lean to minimize imports without changing statements.
- Additional derived public conclusion (reviewer approved): actual_brownian_eventually_positive : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < x → x < δ → 0 < probability B P hB x ∧ 0 < probability B P hB x / firstTerm x.

No weakened assumptions, no desired probability/CLT/modulus premise, no new axiom or proof stub. Private helpers allowed only with complete proofs; additional public interfaces require review before freeze. Entire target remains OPEN until all actual nodes independently reviewed and integrated.
