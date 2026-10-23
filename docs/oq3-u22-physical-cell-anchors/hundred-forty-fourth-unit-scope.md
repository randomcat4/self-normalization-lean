# OQ3 U22BK / unit144 — frozen actual compact window and finite grid cover

FROZEN before implementation. math-theorem/no math-ultra. OQ3 lead author; mandatory fresh independent complete review of all NEW source/proofs/everyactualownedfulltype/allvalues and recursive ALLactualowner standard3 axiom audit. Three public theorems, zero global definitions. Server-only CPU14–17/max1 heavy/native8192MiB/j4/autoImplicitfalse; pins/read-onlycache unchanged.

Source-bound purpose: original repair01 section3 and report cell reconstruction require a finite exact family of actual physical-window cells, rather than an assumed finite proxy partition. BJ143 first establishes exact all-integer half-open partition including atoms. This unit derives the physical window's explicit bounding box, its compactness and an explicit finite signed-integer box containing every actual nonempty cell; restriction to that box still covers V exactly and remains disjoint.

Exact imports planned: Shao.OQ3.ParabolaHalfOpenGridPartition; Mathlib.Data.Int.Interval. BJ source3697b75f71e2006786177e315a69c52a440c1d9d489e9eda36a1e8315420c8ed has author firstkernel/allownerAX PASS and fresh independent review active; final qualification must wait for its full report. Only its two complete declarations and literal values are consumed; no oldgate replay. Pinned Data.Int.Interval object available; Set.finite_Icc and product LocallyFiniteOrder at Order/Interval/Finset/Defs:508/736 read, as well as Int.ceil_mono at Floor/Ring:659, square order at Ring/Abs:119.

Exact complete declarations including EVERY statement local value:
```lean
theorem actual_parabola_window_bounded_box
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    V ⊆ Set.Icc (a0 - rho) (a0 + rho) ×ˢ
      Set.Icc (-rho) ((|a0| + rho) ^ 2 / level ^ 2)

theorem actual_parabola_window_isCompact
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    IsCompact {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}

theorem actual_parabola_finite_half_open_grid_cover
    (n : ℕ) (hn : 1 ≤ n) (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
        Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    let K : Set (ℤ × ℤ) := Set.Icc
      (Int.ceil ((n : ℝ) * (a0 - rho)) - 1,
        Int.ceil ((n : ℝ) * (-rho)) - 1)
      (Int.ceil ((n : ℝ) * (a0 + rho)) - 1,
        Int.ceil ((n : ℝ) * ((|a0| + rho) ^ 2 / level ^ 2)) - 1)
    K.Finite ∧ {k : ℤ × ℤ | (cell k).Nonempty} ⊆ K ∧
      (⋃ k ∈ K, cell k) = V ∧
      Pairwise (fun i j : ℤ × ℤ => Disjoint (cell i) (cell j))
```

All real parameters are universal with explicit rho>=0; n>=1 only in finite grid theorem. level=0 remains permitted under total real division as pure geometry, with no physical positive-tail claim. V is the identical closed window with BOTH parabolic weak inequalities. Bounding-box intervals are closed; cell is literal Ioc×Ioc∩V, preserving all boundary points without atomlessness, density or nullity premise. K is the explicit closed interval in the product order on ℤ×ℤ (componentwise bounds). Its lower/upper indices are exactly ceil(n*coordinatebound)-1; may be negative. Empty V/cells are permitted. K can contain empty cells and is not asserted minimal.

Proof route: from |a-a0|<=rho derive the first coordinate interval and |a|<=|a0|+rho. Square/order and nonnegative level² yield a²/level²<=M²/level²; the two window inequalities plus square nonnegativity give q∈[-rho,M²/level²]. V is closed by continuity of absolute/polynomial/fixed-division functions, hence a closed subset of the compact explicit box. For each nonempty actual cell choose its genuine point w; BJ's exact index iff and monotonicity of ceil applied to the bounding coordinates give k∈K. Set.finite_Icc on integer product supplies actual finiteness. BJ's all-integer exact partition restricts to K using the just-proved nonempty-cell containment; reuse its full pairwise disjointness. Do not replace K or physical/window definitions silently.

OPEN: a quantitative O(n²) cardinal estimate, finite true analytic rate/tilt patch at BI closure anchors, actual uniform covariance whitening, sample Edgeworth, exact weighted probability reconstruction/cell summation, full exterior and original B/D. Compactness/finite exact set cover alone do not prove any probability approximation or root result. Accepted fixed-law A, bounded compact-tilt C, p54 repairs, strict WC and external-result attribution unchanged.
