# Truncation budget: measure-level integral component proposal

Status: the current definition plus seventeen theorem declarations were frozen
by the coordinator on 2026-10-21; implementation is authorized in the new
`Shao/Probability/TruncationIntegrals.lean` module.

The definition is the original budget of the true normalized law `ν`,
`R_n(t)=n ∫ F((1+t)z) dν(z)`. The Basic integrand is the frozen source function
`Shao.truncationF`; it is not replaced by a moment or a surrogate.

## Measure and integrability contract

Use an arbitrary `ν : Measure ℝ`. No probability, finite-measure, or sigma-finite
instance is needed for the first integral inequalities: the sole standing
moment premise is `Integrable (fun z : ℝ => z ^ 2) ν`. In the source, `ν` will be
the normalized variable's actual probability law; constructing this law and
checking its normalization are outside this component.

Every integral comparison will carry actual integrability proofs for both
sides. In particular the truncated third moment requires no global third moment.
The one genuinely additional premise for the `p`-moment comparison is integrability
of `z ↦ Real.rpow |z| p`. There is no use of a nonintegrable Bochner integral's
default value to justify a bound.

`n : ℕ` includes zero. No result below divides by `n`. A cutoff scale `a` or `x`
is divided only under an explicit strict-positivity premise. The definition
extends to every real `t`, while monotonicity is asserted only on `[-1,∞)`;
the original source uses `[0,∞)`.

## Exact proposed declarations

Namespace `Shao`; `open MeasureTheory`; `autoImplicit false`.

```lean
noncomputable def truncationBudget (ν : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * ∫ z : ℝ, truncationF ((1 + t) * z) ∂ν

theorem integrable_truncationF_mul (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) :
    Integrable (fun z : ℝ => truncationF (a * z)) ν

theorem integrable_truncation_tail_one (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℝ => if 1 / a < |z| then |z| else 0) ν

theorem integrable_truncation_tail_two (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℝ => if 1 / a < |z| then z ^ 2 else 0) ν

theorem integrable_truncation_small_three (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℝ => if |z| ≤ 1 / a then |z| ^ 3 else 0) ν

theorem integral_truncation_tail_one_le (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    a * (∫ z : ℝ, if 1 / a < |z| then |z| else 0 ∂ν) ≤
      ∫ z : ℝ, truncationF (a * z) ∂ν

theorem integral_truncation_tail_two_le (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    a ^ 2 * (∫ z : ℝ, if 1 / a < |z| then z ^ 2 else 0 ∂ν) ≤
      ∫ z : ℝ, truncationF (a * z) ∂ν

theorem integral_truncation_small_three_le (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) (ha : 0 < a) :
    a ^ 3 * (∫ z : ℝ, if |z| ≤ 1 / a then |z| ^ 3 else 0 ∂ν) ≤
      ∫ z : ℝ, truncationF (a * z) ∂ν

theorem truncationBudget_nonneg (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t : ℝ) :
    0 ≤ truncationBudget ν n t

theorem truncationBudget_mono (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (s t : ℝ)
    (hs : -1 ≤ s) (hst : s ≤ t) :
    truncationBudget ν n s ≤ truncationBudget ν n t

theorem truncationBudget_scale_le_one (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c ^ 3 * truncationBudget ν n t ≤
        truncationBudget ν n (c * (1 + t) - 1) ∧
      truncationBudget ν n (c * (1 + t) - 1) ≤
        c ^ 2 * truncationBudget ν n t

theorem truncationBudget_scale_one_le (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t c : ℝ) (hc : 1 ≤ c) :
    c ^ 2 * truncationBudget ν n t ≤
        truncationBudget ν n (c * (1 + t) - 1) ∧
      truncationBudget ν n (c * (1 + t) - 1) ≤
        c ^ 3 * truncationBudget ν n t

theorem truncationBudget_local_comparison (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x t : ℝ)
    (hx : 0 ≤ x) (ht : 0 ≤ t) (hxt : |t - x| ≤ (1 + x)⁻¹) :
    (1 / 8 : ℝ) * truncationBudget ν n x ≤ truncationBudget ν n t ∧
      truncationBudget ν n t ≤ 8 * truncationBudget ν n x

theorem truncationBudget_decomposition (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t : ℝ) (ht : -1 < t) :
    truncationBudget ν n t =
      (1 + t) ^ 3 * ((n : ℝ) *
        ∫ z : ℝ, if |z| ≤ 1 / (1 + t) then |z| ^ 3 else 0 ∂ν) +
      (1 + t) ^ 2 * ((n : ℝ) *
        ∫ z : ℝ, if 1 / (1 + t) < |z| then z ^ 2 else 0 ∂ν)

theorem truncationBudget_le_rpow_moment (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (t p : ℝ)
    (ht : 0 ≤ t) (hp2 : 2 ≤ p) (hp3 : p ≤ 3)
    (hp : Integrable (fun z : ℝ => Real.rpow |z| p) ν) :
    truncationBudget ν n t ≤
      Real.rpow (1 + t) p * ((n : ℝ) * ∫ z : ℝ, Real.rpow |z| p ∂ν)

theorem truncationBudget_cutoff_tail_one (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x : ℝ) (hx : 0 < x) :
    x * ((n : ℝ) * ∫ z : ℝ, if 1 / x < |z| then |z| else 0 ∂ν) ≤
      truncationBudget ν n x

theorem truncationBudget_cutoff_tail_two (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x : ℝ) (hx : 0 < x) :
    x ^ 2 * ((n : ℝ) * ∫ z : ℝ, if 1 / x < |z| then z ^ 2 else 0 ∂ν) ≤
      truncationBudget ν n x

theorem truncationBudget_cutoff_small_three (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (x : ℝ) (hx : 0 < x) :
    x ^ 3 * ((n : ℝ) * ∫ z : ℝ, if |z| ≤ 1 / x then |z| ^ 3 else 0 ∂ν) ≤
      truncationBudget ν n x
```

## Source connection and deferred assertions

The final three statements use precisely the cutoff `1/x` but the original
budget at `x`, with scale `1+x`. They combine the integrated marked bound at
scale `x` with pointwise monotonicity from `x` to `1+x`. Consequently a source
assumption `R_n(x)≤1`, together with `x>0`, gives the supplemental tail moment
bounds after dividing by the explicit positive factors `x`, `x²`, or `x³`.

The decomposition is the exact integrated retained-third/tail-second identity
used for the subsequent retained-variance and Lyapunov argument. The real
`p`-moment comparison gives the source's `β_(n,p)(1+t)^p` with
`β_(n,p)=n∫|z|^p dν`, including `p=2` and `p=3` when its stated moment is finite.
Local comparison is the actual `1/8` and `8` source assertion, without a
probability-law or positive-budget assumption.

Continuity of the measure-level budget, strict increase, its normalized limit
at infinity, and the sample-size lower bound remain separate future units.
No complete Lemma 3.1 is claimed by this proposal. All checks will be targeted
on the designated server and will leave existing frozen sources untouched.

## Implementation and designated-server receipt

All eighteen frozen declarations are implemented in
`drafts/c12/TruncationIntegrals.lean`, with the remote counterpart
`workspaces/lead-c12/Shao/Probability/TruncationIntegrals.lean`.

The integrability proofs use nonnegative Borel kernels and these actual square
moment dominators:

```text
F(a z)                         ≤ a² z²
|z| 1_{|z|>1/a}               ≤ a z²        (a>0)
z² 1_{|z|>1/a}                ≤ z²
|z|³ 1_{|z|≤1/a}              ≤ a⁻¹ z²      (a>0)
```

These dominators are integrable directly from `h2`; a global third moment is
never introduced. All uses of `integral_mono` provide explicit integrability
proofs for both functions. The additional real-power moment premise is used
only for its own comparison theorem.

After the pinned activation script and changing to `lead-c12`, the actual
targeted compiler command was:

```text
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/Probability/TruncationIntegrals.olean Shao/Probability/TruncationIntegrals.lean
```

Exit code: 0. The only diagnostic is an unused `ha` warning in
`integrable_truncation_tail_two`: that single integrability assertion is valid
even without a positive cutoff scale, but its frozen signature is preserved.
No hypotheses, quantifiers, event boundaries, or coefficients were changed.

The designated-server source SHA256 is:

```text
d7432b7c579c6e6e0d9980af322437941f59f8f670bebd2dd4770f6cfcf1e234
```

A separate server `lake env lean --stdin` import ran `#print axioms` on the
definition and all seventeen theorems. It exited 0; each declaration depends
exactly on `[propext, Classical.choice, Quot.sound]`. The pinned versions remain
Lean `leanprover/lean4:v4.36.0-rc1` and mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`.

Status: this complete frozen integral-comparison component is mechanically
checked; independent blind semantic/proof review is pending with the coordinator.
Continuity, strict increase, the normalized limit, and the sample-size lower
bound remain deferred as stated above.
