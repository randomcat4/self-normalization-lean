# OQ3 U22BC / unit136 — frozen actual segment, parabola and affine scaling Lipschitz bounds

FROZEN before implementation, OQ3 lead author, math-theorem (no math-ultra). Independent complete semantic/proof/all-owned-type/value/recursive standard3 axiom review mandatory before qualification. Three public theorems, no global definitions.

Source-bound use: BA's literal six parametrized arcs are four straight segments and two shifted parabolic graphs. The actual source normalization is w ↦sqrt(n)•E(w-y). This unit proves these geometry/Lipschitz primitives; it does not assume a desired Gaussian boundary probability or any root theorem.

Exact planned imports: Mathlib.Topology.MetricSpace.Lipschitz, Mathlib.Analysis.SpecialFunctions.Sqrt, Mathlib.Analysis.Normed.Operator.ContinuousLinearMap. Norm on real pairs is the existing maximum norm. Pins/resources unchanged (server only CPU14–17, max1heavy, -M8192 -j4 -DautoImplicit=false, read-only packages).

Exact complete declarations:
```lean
theorem affine_segment_lipschitz
    (a b dx dq : ℝ) :
    LipschitzWith (Real.toNNReal (max |dx| |dq|))
      (fun t : ℝ => (a + t * dx, b + t * dq))

theorem parabola_segment_lipschitz
    (a dx level shift M : ℝ) (hM : 0 ≤ M)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, |a + t * dx| ≤ M) :
    LipschitzOnWith (Real.toNNReal (|dx| * max 1 (2 * M / level ^ 2)))
      (fun t : ℝ => (a + t * dx, (a + t * dx) ^ 2 / level ^ 2 - shift))
      (Set.Icc (0 : ℝ) 1)

theorem standardized_lipschitz_arc
    (n : ℕ) (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (f : ℝ → ℝ × ℝ) (K : NNReal)
    (hf : LipschitzOnWith K f (Set.Icc (0 : ℝ) 1)) :
    LipschitzOnWith (Real.toNNReal (Real.sqrt (n : ℝ) * ‖E‖ * (K : ℝ)))
      (fun t : ℝ => Real.sqrt (n : ℝ) • E (f t - y))
      (Set.Icc (0 : ℝ) 1)
```

Every displayed parameter universally quantified. The first theorem is global on real t and permits any signed/zero dx,dq. The second's explicit point-range bound hpos is weaker geometric data, to be proved from actual clipped-cell endpoints in a subsequent consumer; it does not assume a Lipschitz/tube conclusion. hM is explicit. Real division is total; level=0 is permitted for this pure polynomial/division geometry statement, with max1 keeping the first-coordinate bound. No physical probability claim at level0. Empty interval cannot arise for Icc01, but dx=0/M=0/shift arbitrary all covered. The third permits n=0 and any continuous linear map including the zero map, so no invertibility or positive-n hypothesis is hidden; actual frontier transport will separately require the physical n>=1 and E equivalence. K : NNReal, and Real.toNNReal encodes explicit nonnegative real constants.

Proof routes: exact affine differences and max-norm; difference of squares factored as (x-y)(x+y), with |x+y|<=2M, and nonnegative-square division monotonicity; actual linear operator norm and scalar norm with the exact subtraction cancelling y. Author may use local names x=a+t*dx etc with these exact values, but must not change the three frozen functions or constants.

OPEN: derive uniform six-arc constants from source grid widths/clipped endpoints and physical window, exact affine/homeomorphism frontier transport, actual six-arc Gaussian tube consumer/finite union interface and h=n^-3, uniform whitening family, anchors/disjoint partition, actual Edgeworth and exterior. OriginalB/D OPEN; accepted corrected fixed-lawA and bounded compact-tiltC scope retained. All original p54/strictWC/external-attribution constraints unchanged. No silent premise change.

