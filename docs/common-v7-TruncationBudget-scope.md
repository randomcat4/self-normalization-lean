# Truncation budget: scalar integrand API proposal

Status: exact definition plus fifteen theorem declarations frozen by the
coordinator on 2026-10-21; implementation authorized in the Basic layer.

Read source scope only:

- `C:/game/shao/current/c12/main.tex`: Lemma `h:lem:truncatedbudget`, around line 320.
- `C:/game/shao/current/c12/supplement.tex`: its proof around line 961, and the
  tail/truncated-moment estimates at lines 188–203.

The first component belongs in `Shao/Basic/TruncationBudget.lean`: it contains
only deterministic scalar real analysis, with no paths or probability law.
The scalar function is the source's actual `F`, not an abstract surrogate.

## Exact proposed declarations

Every declaration is in namespace `Shao`, with `autoImplicit false`.

```lean
def truncationF (z : ℝ) : ℝ := z ^ 2 * min |z| 1

theorem truncationF_nonneg (z : ℝ) : 0 ≤ truncationF z

theorem truncationF_neg (z : ℝ) : truncationF (-z) = truncationF z

theorem continuous_truncationF : Continuous truncationF

theorem truncationF_of_abs_le_one (z : ℝ) (hz : |z| ≤ 1) :
    truncationF z = |z| ^ 3

theorem truncationF_of_one_le_abs (z : ℝ) (hz : 1 ≤ |z|) :
    truncationF z = z ^ 2

theorem truncationF_le_sq (z : ℝ) : truncationF z ≤ z ^ 2

theorem truncationF_le_rpow (z p : ℝ) (hp2 : 2 ≤ p) (hp3 : p ≤ 3) :
    truncationF z ≤ Real.rpow |z| p

theorem truncationF_scale_le_one (c z : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c ^ 3 * truncationF z ≤ truncationF (c * z) ∧
      truncationF (c * z) ≤ c ^ 2 * truncationF z

theorem truncationF_scale_one_le (c z : ℝ) (hc : 1 ≤ c) :
    c ^ 2 * truncationF z ≤ truncationF (c * z) ∧
      truncationF (c * z) ≤ c ^ 3 * truncationF z

theorem truncationF_mono_abs (z w : ℝ) (hzw : |z| ≤ |w|) :
    truncationF z ≤ truncationF w

theorem truncationF_mono_scale (a b z : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    truncationF (a * z) ≤ truncationF (b * z)

theorem truncationF_scaled_decomposition (a z : ℝ) (ha : 0 < a) :
    truncationF (a * z) =
      a ^ 3 * (if |z| ≤ 1 / a then |z| ^ 3 else 0) +
        a ^ 2 * (if 1 / a < |z| then z ^ 2 else 0)

theorem truncationF_tail_one (a z : ℝ) (ha : 0 < a) :
    a * (if 1 / a < |z| then |z| else 0) ≤ truncationF (a * z)

theorem truncationF_tail_two (a z : ℝ) (ha : 0 < a) :
    a ^ 2 * (if 1 / a < |z| then z ^ 2 else 0) ≤ truncationF (a * z)

theorem truncationF_truncated_three (a z : ℝ) (ha : 0 < a) :
    a ^ 3 * (if |z| ≤ 1 / a then |z| ^ 3 else 0) ≤ truncationF (a * z)
```

The large-observation identity is stated under `1 ≤ |z|`, which includes the
source's strict large region and agrees with the small-region identity at
`|z|=1`. The moment indicators retain exactly the source's disjoint convention:
small `≤ 1/a`, large `> 1/a`. Scaling below one explicitly allows `c=0`.
The real exponent in `truncationF_le_rpow` is literally `Real.rpow`; `p=2`
and `p=3` are included. No moment or integrability assumption is hidden in
these purely pointwise declarations.

## How this connects to the actual source budget

For the source's normalized variable `ξ=X/(σ√n)`, the budget is
`R_n(t)=n E[F((1+t)ξ)]`, not a new scalar substitute.

1. Integrating `truncationF_le_rpow` at `z=(1+t)ξ` and factoring the
   nonnegative deterministic coefficient gives
   `R_n(t) ≤ (1+t)^p n E|ξ|^p = β_(n,p)(1+t)^p`.
   This still needs a separately checked measure/integral layer.
2. The two scale inequalities integrate without changing their constants.
   Applying them with `c=(1+t)/(1+x)∈[1/2,2]` gives the source's factors
   `1/8` and `8`, after the scalar ratio bounds are separately established.
3. `truncationF_scaled_decomposition`, integrated with `a=1+t`, is exactly
   the source's retained third moment plus tail second moment decomposition.
4. Integrating the three marked pointwise inequalities bounds, respectively,
   `a n E[|ξ|;|ξ|>1/a]`, `a² n E[ξ²;|ξ|>1/a]`, and
   `a³ n E[|ξ|³;|ξ|≤1/a]` by `n E F(aξ)`.
   For the supplement's cutoff `1/x`, `x>0`, monotone scaling gives
   `F(xξ)≤F((1+x)ξ)`. Therefore `R_n(x)≤1` yields exactly the displayed
   tail bounds `n E[|ξ|^r;|ξ|>1/x]≤x^(-r)` for `r=1,2`, and the
   truncated third-moment bound `≤x^(-3)`.
5. `truncationF_le_sq` supplies the actual domination
   `F((1+t)ξ)≤(1+T)²ξ²` for `0≤t≤T` after monotone scaling; together with
   scalar continuity this prepares, but does not prove, dominated-convergence
   continuity of `R_n`.

## Explicitly deferred

No measure-level continuity, strict increase, limit at infinity, normalization
`n E ξ²=1`, integrated budget comparison, Lyapunov lower bound, or complete
Lemma `h:lem:truncatedbudget` is claimed by this first component. These are the
next batches and require their own frozen assumptions and integral interfaces.

Implementation must keep the pinned server toolchain and compile only the new
module on the server. No shared-cache writes, existing-source edits, `sorry`,
`admit`, new axioms, `unsafe`, or `native_decide` are permitted.

## Implementation and designated-server receipt

All sixteen frozen declarations are implemented in
`drafts/c12/TruncationBudget.lean`, with the corresponding remote source at
`workspaces/lead-c12/Shao/Basic/TruncationBudget.lean`.

After sourcing the pinned activation script and changing to `lead-c12`, the
actual targeted command was:

```text
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/Basic/TruncationBudget.olean Shao/Basic/TruncationBudget.lean
```

The first compilation exited 0 with empty stdout and stderr. Upload and check
were combined into one SSH exec, transmitting only this author's source on
stdin. The output olean belongs to this worktree; no shared package cache was
written. The pinned toolchain is `leanprover/lean4:v4.36.0-rc1`, with mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`.

Server and local source SHA256:

```text
70cf7e33d458b847ea94cfa5bd8dce59a9dc3cb0ef632140a0f55fca8ded71bd
```

A separate designated-server `lake env lean --stdin` import ran `#print axioms`
on the definition and all fifteen theorems. Every one returned exactly
`[propext, Classical.choice, Quot.sound]`, with exit code 0. Source scanning
found none of the prohibited proof placeholders or bypasses.

Current status: the complete frozen **pointwise integrand component** is
mechanically checked. Independent blind source-to-statement and proof review
are pending. The measure-level budget assertions listed under “Explicitly
deferred” remain open; this receipt does not certify complete Lemma 3.1.
