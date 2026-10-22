# Proposed exact declarations v1

STATUS: PROPOSED_FOR_INDEPENDENT_STATEMENT_REVIEW
IMPLEMENTATION: NONE
LEAN_CHECKS: NONE
PROPOSED_MODULE: Shao/Probability/BrownianSup.lean (root dedicated worktree shared-brownian-v34)
AUTHOR: root/brownian_author

The statements below freeze the actual object and the smallest genuine probability bridge. The code blocks are a declaration specification, not compilable proof stubs. Auxiliary private/generated declarations may be needed, but no additional mathematical assumptions may be introduced.

```lean
namespace Shao.Probability.BrownianSup
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

-- One fixed, explicit countable dense exhaustion; no abstract selector premise.
noncomputable def rationalTime (n : ℕ) : ℝ≥0 :=
  ⟨max 0 (min 1 (((Encodable.decode ℚ n).getD 0 : ℚ) : ℝ)),
    le_max_left _ _⟩

noncomputable def grid (n : ℕ) : Finset ℝ≥0 :=
  insert 0 ((Finset.range n).image rationalTime)

variable {Ω : Type*} [MeasurableSpace Ω]
variable (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)

noncomputable def pathSup (ω : Ω) : ℝ :=
  sSup ((fun t : ℝ≥0 => |B t ω|) '' Set.Icc 0 1)

noncomputable def traceSup (ω : Ω) : ℝ :=
  ⨆ n : ℕ, |B (rationalTime n) ω|

def fullStrip (x : ℝ) : Set Ω :=
  {ω | ∀ t ∈ Set.Icc (0 : ℝ≥0) 1, |B t ω| ≤ x}

def finiteStrip (n : ℕ) (x : ℝ) : Set Ω :=
  {ω | ∀ t ∈ grid n, |B t ω| ≤ x}

noncomputable def gaussianFinite (n : ℕ) (x : ℝ) : ℝ :=
  (ProbabilityTheory.BrownianReal.projectiveFamily (grid n)).real
    {v | ∀ t, |v t| ≤ x}

variable [IsProbabilityMeasure P]
variable (hB : ProbabilityTheory.IsBrownianReal B P)

theorem traceSup_aemeasurable : AEMeasurable (traceSup B) P

-- U is explicitly a measurable version of the actual Brownian supremum.
noncomputable def U : Ω → ℝ :=
  (traceSup_aemeasurable B P hB).mk (traceSup B)

noncomputable def probability (x : ℝ) : ℝ :=
  P.real {ω | U B P hB ω ≤ x}

theorem measurable_U : Measurable (U B P hB)

theorem U_ae_eq_pathSup : U B P hB =ᵐ[P] pathSup B

theorem U_le_ae_iff_fullStrip :
  ∀ᵐ ω ∂P, ∀ x : ℝ,
    U B P hB ω ≤ x ↔ ω ∈ fullStrip B x

theorem probability_eq_fullStrip (x : ℝ) :
  probability B P hB x = P.real (fullStrip B x)

theorem finiteStrip_nullMeasurable (n : ℕ) (x : ℝ) :
  NullMeasurableSet (finiteStrip B n x) P

theorem finiteStrip_probability_eq_gaussian (n : ℕ) (x : ℝ) :
  P.real (finiteStrip B n x) = gaussianFinite n x

theorem tendsto_gaussianFinite (x : ℝ) :
  Tendsto (fun n : ℕ => gaussianFinite n x) atTop
    (𝓝 (probability B P hB x))

-- Same probability for any other actually certified standard Brownian motion.
variable {Ω' : Type*} [MeasurableSpace Ω']
variable (B' : ℝ≥0 → Ω' → ℝ) (P' : Measure Ω')
variable [IsProbabilityMeasure P']
variable (hB' : ProbabilityTheory.IsBrownianReal B' P')

theorem probability_eq_probability (x : ℝ) :
  probability B P hB x = probability B' P' hB' x

end Shao.Probability.BrownianSup
```

Parameter binder order above is semantic. Implementation can make B/P implicit where Lean elaboration requires it, without changing quantified objects. The numerical enumeration is auxiliary; all public probabilities are identified with the original full continuous-time weak event for every x. The same a.e. set supports all x in U_le_ae_iff_fullStrip.

## Full source-bound target (OPEN, not assumed or implemented by this node)

With exactly the same B,P,hB,U,probability and no further probability premises:

```lean
noncomputable def firstTerm (x : ℝ) : ℝ :=
  (4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) / x ^ 2)

-- Ultimate required theorem, NOT an axiom/hypothesis/public stub in implementation:
∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ x : ℝ, 0 < x → x < δ →
    |probability B P hB x / firstTerm x - 1| < ε
```

After proving that exact theorem, positivity of firstTerm and the same actual probability/ratio for sufficiently small positive x must be derived. No relative O(exp(-8λ/x²)) is included. Merely defining firstTerm and proving positivity or consequences conditional on the ultimate display would not close this target.

## Review contract

Independent reviewer must judge semantic fidelity and truth of this finite-approximation declaration set, separately from the ultimate asymptotic. In particular test all x≤0, the n=0 grid={0}, a.e.-only continuity, a.e.-only coordinate measurability, the literal full event versus measurable version, and enumeration exhaustiveness. No desired probability estimate is present among assumptions. Implementation waits CORRECT and explicit root scheduling authorization for any Lean command.
