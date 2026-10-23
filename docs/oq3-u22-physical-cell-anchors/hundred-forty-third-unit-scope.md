# OQ3 U22BJ / unit143 — frozen exact half-open grid partition

FROZEN before implementation. math-theorem/no math-ultra. OQ3 lead author; independent complete newsource/proof/eachactualownedfulltype/everylocalvalue/recursive standard3 actual-owner audit required. Two public theorems/no global definitions. All server-only resources/pins/read-onlycache rules unchanged.

Source-bound purpose: repair01 section3 needs an EXACT disjoint cell partition for possibly atomic sample laws. Half-open Ioc rectangles give exact coverage and disjointness while preserving every physical closed-window point. BI142 supplies closure-rate anchors separately. This unit must construct the actual integer coordinate index and the actual 2D cell family, not assume an exact partition or atomlessness.

Exact imports planned: Mathlib.Algebra.Order.Floor.Ring; Mathlib.Topology.Instances.Real.Lemmas. Both pinned primaryobjects observedavailable; no projectdependency/sourceedit or cachehydration. Int.ceil_eq_iff at pinnedFloor/Ring:667 has exact lowerstrict/upperweak bounds; negative coordinateindices must remain signed integers.

Exact complete declarations, including ALL statement local values:
```lean
theorem real_ioc_grid_index_iff
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (i : ℤ) :
    x ∈ Set.Ioc ((i : ℝ) / (n : ℝ)) (((i : ℝ) + 1) / (n : ℝ)) ↔
      i = Int.ceil ((n : ℝ) * x) - 1

theorem actual_parabola_half_open_grid_partition
    (n : ℕ) (hn : 1 ≤ n) (level a0 rho : ℝ) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
        Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    (⋃ k : ℤ × ℤ, cell k) = V ∧
      Pairwise (fun i j : ℤ × ℤ => Disjoint (cell i) (cell j))
```

All parameters universal. n>=1 is explicit; x any real and i any INTEGER, including negative indices and gridline values. The unique index is ceil(n*x)-1: a gridline x=i/n belongs to the preceding cell's CLOSED upper endpoint. The endpoints are literal real casts of signed i divided by positive n. No zero-boundary-mass, density, Gaussian law, rate, cell nonempty or finite-index hypothesis.

The 2D V is the literal CLOSED physical window with BOTH weak parabolic inequalities and absolute-value wall. Allreal level/a0/rho permitted as pure setgeometry; level0 totaldivision and empty V/rho<0 cases remain well-defined. The family cell(k) is exactly the source half-open integer grid rectangle intersected with V; no clipped Ioc L R substitution. Pairwise means disjoint for all distinct integer pairs. Union equality includes ALL points of V, with no almost-everywhere qualification.

Proof route: multiply 1D endpoint bounds by positive n, use Int.ceil_eq_iff for ceil(n*x)=i+1 and integer subtraction to derive the index iff. For union coverage, explicitly choose k=(ceil(n*w.1)-1,ceil(n*w.2)-1); the two coordinate iff statements prove actual membership. Every unionmember lies in V by construction. If two cells share a point, the same two index formulas force equality of both coordinates, contradicting distinctness. Localproof V/cell must exactly equal frozenvalues; local k and pointindices use the exact formulas above.

OPEN: finite active-cell enumeration for compact actual V, valid finite analytic rate patch at BI closureanchors, exact weighted probability reconstruction/summation, actual uniform covariance whitening/cellfamily, actualsampleEdgeworth/exterior and originalB/D. This unit proves only exact setpartition, not probability estimates or rateanchors. AcceptedfixedlawA/boundedcompacttiltC scopes/p54/strictWC/externalattribution unchanged. No silent declaration/premise changes.

