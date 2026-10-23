# OQ3 unit133 / U22az — actual window-truncated half-open cell frontier

Original B target: repair01.md section2eq(5) actual geometric producer, consuming the qualified literal AL parabolic strip V. Direct consumer: six actual parameter arcs, uniform affine Lipschitz transport, AY finite-arc Gaussian tube and AX. See u22-window-cell-boundary-note.md: the actual AL truncation has two parabolic graphs; do not silently reuse the source's one-graph/five-arc assertion for a different set.

Exact declarations frozen before implementation. The first theorem is a continuous-inequality sandwich theorem, not an assumed frontier or probability bound: the open strict region is inside A, and A is inside the closed non-strict region. The proof must derive closure/interior implications and actual equalities on its six potential boundaries. The second theorem must establish that sandwich for the LITERAL half-open grid rectangle intersected with the literal actual chart window. In particular the a-window is closed, the grid has open left endpoints, and clipping by max/min must retain all actual endpoint cases without discarding sample atoms. No desired boundary cover appears in its premises.

These purely geometric formulas are meaningful for arbitrary real parameters (Lean real division by zero remains its standard total operation). Proving them without level/rho positivity does not remove source positivity, covariance or regular-saddle assumptions from any original root: later actual probability consumers must retain their previously qualified physical-domain premises. Empty/degenerate/reversed intervals must be covered rather than excluded silently. No global definition is added;2 public theorems.

```lean
theorem parabola_strip_cell_frontier_of_sandwich
    (aL aR qL qR level rho : ℝ) (A : Set (ℝ × ℝ))
    (hinside : {w : ℝ × ℝ | aL < w.1 ∧ w.1 < aR ∧ qL < w.2 ∧ w.2 < qR ∧
      0 < w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 < rho} ⊆ A)
    (houtside : A ⊆ {w : ℝ × ℝ | aL ≤ w.1 ∧ w.1 ≤ aR ∧ qL ≤ w.2 ∧ w.2 ≤ qR ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}) :
    ∀ w ∈ frontier A,
      ((w.1 = aL ∨ w.1 = aR) ∧ qL ≤ w.2 ∧ w.2 ≤ qR) ∨
      ((w.2 = qL ∨ w.2 = qR) ∧ aL ≤ w.1 ∧ w.1 ≤ aR) ∨
      (aL ≤ w.1 ∧ w.1 ≤ aR ∧
        (w.2 = w.1 ^ 2 / level ^ 2 ∨ w.2 = w.1 ^ 2 / level ^ 2 - rho))

theorem actual_parabola_window_cell_frontier
    (aL aR qL qR level a0 rho : ℝ) :
    let L : ℝ := max aL (a0 - rho)
    let R : ℝ := min aR (a0 + rho)
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    ∀ w ∈ frontier A,
      ((w.1 = L ∨ w.1 = R) ∧ qL ≤ w.2 ∧ w.2 ≤ qR) ∨
      ((w.2 = qL ∨ w.2 = qR) ∧ L ≤ w.1 ∧ w.1 ≤ R) ∨
      (L ≤ w.1 ∧ w.1 ≤ R ∧
        (w.2 = w.1 ^ 2 / level ^ 2 ∨ w.2 = w.1 ^ 2 / level ^ 2 - rho))
```

The conclusion locates actual frontier points on four effective straight edges or two explicit parabolic graphs. Parameterizing each entire compact arc and proving uniform scaled Lipschitz constants, exact affine frontier transport, finite-arc tube assembly, partition/anchor selection and the actual Edgeworth probability comparison remain OPEN. Original B/D stays OPEN and accepted A/C scopes remain unchanged. Frozen declarations and mathematical assumptions may not be changed silently.
