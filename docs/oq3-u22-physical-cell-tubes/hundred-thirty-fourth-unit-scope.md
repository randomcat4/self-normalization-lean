# OQ3 unit134 / U22ba — six literal compact arcs for the actual cell

Original B target: repair01.md section2eq5, actual window-truncated cell boundary. Direct consumer: uniform scaled affine Lipschitz producers and finite-arc Gaussian tube assembly. Freeze before implementation. This theorem must CONSTRUCT six literal maps, prove compactness of their actual [0,1] images, and prove they cover the actual frontier using AZ; it must not assume a frontier cover or discard endpoint/sample atoms.

Exact statement below. The grid remains Ioc×Ioc and the a-window closed. Clipped max/min endpoints preserve the distinction. All real parameters and empty/degenerate/reversed grid/window cases are in scope; parameter representation for any point of a closed interval must handle equal endpoints explicitly rather than divide by zero. Polynomial maps and division by fixed real level² are globally continuous even at level0 using standard real operations. Later physical probability consumers retain all original positive-domain/saddle premises. No global definition,1 public theorem; the six complete curve values are local statement data frozen here.

```lean
theorem actual_parabola_window_cell_six_compact_arcs
    (aL aR qL qR level a0 rho : ℝ) :
    let L : ℝ := max aL (a0 - rho)
    let R : ℝ := min aR (a0 + rho)
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let curve : Fin 6 → ℝ → ℝ × ℝ := ![
      (fun t => (L + t * (R - L), qL)),
      (fun t => (L + t * (R - L), qR)),
      (fun t => (L, qL + t * (qR - qL))),
      (fun t => (R, qL + t * (qR - qL))),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2)),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho))]
    (∀ i : Fin 6, IsCompact (curve i '' Set.Icc (0 : ℝ) 1)) ∧
      frontier A ⊆ ⋃ i : Fin 6, curve i '' Set.Icc (0 : ℝ) 1
```

The four straight arc images and two parabolic graph images may include harmless extra points outside the truncated cell. Only actual frontier containment is concluded. Uniform O(1/sqrt(n)) Lipschitz bounds after the actual sqrt(n)*E affine map, exact affine/homeomorphic frontier transport, finite-union tube bound, h=n^-3, whitening/cell-family constants/partition/anchors/Edgeworth and original B/D remain OPEN. Previously accepted A/C scope is retained. No silent declaration or assumption change.
