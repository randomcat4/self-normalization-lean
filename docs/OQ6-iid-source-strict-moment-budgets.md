# IID source-z strict truncated-moment budgets

`Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets`
derives the strict original IID truncated-moment margins from an explicit small-z
window. The exact repaired source is
`4905904cb5e8f37f1731c92da9e504e614e8dc7734a5de3f124ab2bceff55c36`
(10,716 bytes, 245 LF). Its four added `Real.rpow_eq_pow` normalization lines
leave the frozen declaration, ordinary values, assumptions and conclusions
unchanged; the initial 241-LF source and its failed native receipt are preserved.

For an arbitrary probability space, a measurable L2 scalar g with an explicitly
integrable p-th absolute moment, 2 < p <= 3, and cBudget > 0, write
`beta = integral |g|^p` and
`c = (min(1/2, cBudget)/2)^(1/p)`. This one positive c is chosen before all n and z
and depends only on p and cBudget. No centering, unit variance or positive-beta
assumption is added.

For every n >= 1 and z >= 1 the theorem uses the actual product probability
`P = pi (fun _ => mu)` and coordinates `xi_i = g(omega_i)/sqrt(n)`.
Its costs are integrals of the literal source test
`truncationF(z*xi_i)`, equivalently `(z*xi_i)^2 * min |z*xi_i| 1`.
It proves scalar and product integrability, equality of every marginal cost with
the scalar integral, `L = n*delta_i`, nonnegativity, and the unconditional bound
`L <= beta*z^p / n^((p-2)/2)`.

If beta is zero, all these costs are zero. If beta is positive and
`z <= c * beta^(-1/p) * n^((p-2)/(2*p))`, then
`L <= c^p`, every `delta_i < 1/2`, and `L < cBudget*z^2`.
The beta-zero case is handled explicitly before any inverse-power cancellation.
The scalar producer is applied at y = z - 1 so its `(1+y)` test is the actual
source z test; no compact `(1+z)` replacement is made.

The second native attempt and the audit of its same first original object both
returned Lean 0. The original object SHA256 is
`3cd5bce4f6aa2cd5f2da1da968e8b863dffa1417665055159060b0f0839a2fbe`.
Actual module-index discovery found eight owned theorems, 391 complete TYPE
lines and no non-theorem VALUE bodies. All recursive axioms belong to the
standard whitelist `propext`, `Classical.choice`, `Quot.sound`.
Six tactic warnings and the standing stderr are preserved separately from the
actual kernel codes. The original never-author reviewer's final independent
qualification covers this exact source, frozen interface and original object;
its complete report and machine join accompany this document.

One preparation attempt temporarily overwrote eight owned copies of old input
metadata (three changed bytes and all eight changed timestamps). The guard
stopped before configuration or Lean execution. All eight original complete
fingerprints were restored from the original upload plan before the successful
attempt; new repair inputs use a separate repair01 directory. No production
proof, old source, old configuration, old receipt or object was changed by that
incident. The observations and exact restoration are part of the reviewed
provenance. An earlier unexecuted controller-literal replacement error is also
retained. Continuous non-mutation of those eight metadata copies is not claimed.

This unit neither imports nor retries the original weighted consumer or the
normalized strict-margin preservation theorem. It supplies a separate original
IID ingredient. It does not identify cBudget with an external constant, transfer
the window to a coded normalized model, prove a weighted or CDF limit, or close
an original OQ56/root claim. Qualified old scalar-producer evidence is reused;
no old producer or unrelated leaf axiom check is replayed.
