# OQ3 U22BM / unit146 — frozen quantitative actual active-grid cardinality

FROZEN before source. math-theorem/no math-ultra. Two public theorems, zero definitions; everyNEWproof/type/localvalue requires fresh independent full review + recursive actual-owner standard3AX. Server-only CPU14–17/max1/native8192MiB/j4/autoImplicitfalse/pins/read-onlycache unchanged.

Source-bound purpose: report/r2 section3 cellcount and section4 summation need a quantitative O(n²) number of actual nonempty window cells, not just a finite proxy family. BK144 gives explicit finite exactcover/active-index containment; this unit supplies an explicit constant depending only on fixed physical window parameters and a bound on the ACTUAL active set.

Exact imports: Shao.OQ3.ParabolaFiniteGridCover; Mathlib.Data.Set.Card. Qualified BK sourceb9303194ada7248223e0b98947d71db21a66117c0ee07cba563e31c2d8b87178, complete qualifiedreport00ea72556d773f38448f49c169f2c8c20251a4c08d7b796ba91b8eaa99871a99 all135lines parentread. Only oldconsumedcomplete signatures/values/hashscopequalification read; oldproof/checks reused.
Pinned Data.Set.Card cached object available. Read primary Int.card_Icc_of_le (Data/Int/Interval:115), Int.ceil_mono/le_ceil/ceil_lt_add_one (Floor/Ring:659/794), Finset.card_Icc_prod (Interval/Finset/Defs:748), Set.ncard_le_ncard (Set/Card:682) and Set.ncard_coe_finset (:693).

Exact full declarations including ALL statement-local values:
```lean
theorem real_ioc_grid_interval_cardinality_bound
    (n : ℕ) (hn : 1 ≤ n) (lo hi : ℝ) (hle : lo ≤ hi) :
    ((Finset.Icc (Int.ceil ((n : ℝ) * lo) - 1)
      (Int.ceil ((n : ℝ) * hi) - 1)).card : ℝ) ≤
        (hi - lo + 2) * (n : ℝ)

theorem actual_parabola_active_grid_cardinality_bound
    (n : ℕ) (hn : 1 ≤ n) (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
        Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
    0 < C ∧ {k : ℤ × ℤ | (cell k).Nonempty}.Finite ∧
      ({k : ℤ × ℤ | (cell k).Nonempty}.ncard : ℝ) ≤ C * (n : ℝ) ^ 2
```

First result counts the literal FINSET of signed integer grid indices between ceil(n*lo)-1 and ceil(n*hi)-1 for allreal lo<=hi and n>=1. It includes both endpoint indices, even at exact gridlines/negative indices. No positivity of coordinates or integral endpoints is assumed.
Second uses exactly actualclosedV/Iocgridcell from BJ/BK, no atomic-boundary exclusion. C is explicitly (2rho+2)*(M²/level²+rho+2), M=|a0|+rho. It is positive for rho>=0 and independent of n; real totaldivision level0 remains valid puregeometry. n>=1 explicit. Cardinality is Set.ncard of the actual set of indices whose literal cell is nonempty, paired with actual finiteness so zero-for-infinite conventions cannot conceal anything. No cardinality/finitefamily/desiredbound premise.

Proof route: use the integer interval cardinal formula under ordered ceilings, cast its exact count to reals, bound the upper ceiling by n*hi+1 and the lower by n*lo, giving count < n*(hi-lo)+2 <= n*(hi-lo+2) for n>=1. For actualcells use BK's explicit product-order K, identify it with the coercion of the corresponding Finset.Icc, and its cardinality as product of the two 1D interval counts. Apply the helper to [a0-rho,a0+rho] and [-rho,M²/level²], both ordered using rho>=0 and squared-quotient nonnegativity; multiply nonnegative bounds and rearrange to C*n². BK active-subset inclusion gives actual activefiniteness and ncard monotonicity. All proof-local F/K/R values must retain these explicit actual box bounds and be fully reviewed.

OPEN: uniform true covariance whitening/parameter-family constants; actual-sample Edgeworth, weighted exact reconstruction/cell summation and full exterior/root B/D. BG/BH local Gaussian h=n^-3 rate and BL finite true-rate chartanchors are separate qualified/current producer scopes, not sampleprobability conclusions. Accepted fixed-law A/bounded compact-tilt C, p54/strictWC/externalattribution unchanged.
