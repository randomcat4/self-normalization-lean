# OQ3 first-unit independent statement review

STATUS: CORRECT — independent statement/source review only. The proposed U1
interface can be frozen without a mathematical signature correction. This is
not a proof review, Lean check, or acceptance of any complete OQ3 root.

The blind translation section below was written from the proposed Lean
declaration blocks alone, before reading their explanatory prose, root
contract, dependency map, or original-source anchors. No target implementation
or target proof has been read. This reviewer owns only this review file.

Initial declaration source: `drafts/oq3/first-unit-scope.md`, SHA256
`68a0774f95291674f025c355c7a84ef20c9b11e27e1cca88ffb9861d9f035257`.
The extracted blocks contain fourteen proposed definitions and eleven
theorem statements. They are proposed statements, not mechanically checked
theorems.

## Independent blind mathematical translation

Write `Y(x)=8x-x^2`, `b(x)=x^2-4x`,
`c_ell(x)=x exp(-ell Y(x))`, and
`f_ell(x)=(1,b(x),c_ell(x),x^2)` as a column vector with four real coordinates.
The target is `v(q)=(1,0,0,q)`. Four base atom locations are fixed as
`a=(-1,1,4+sqrt(10),2)`. The square matrix `M_ell` has column `i` equal
to `f_ell(a_i)`.

For any natural `J`, added locations `x_j` and real added weights `r_j`, let
`d=sum_j r_j f_ell(x_j)` and define the compensated base weights
`p'=p-M_ell^{-1}d`. The stage index is the disjoint sum
`Fin 4 + Fin J`; its locations concatenate the four base locations with
the added locations, and its weights concatenate `p'` with `r`.
The stage moment vector is the weighted sum of the four feature coordinates
over this finite disjoint index set. At this definition level weights are
arbitrary real numbers: no probability measure or nonnegativity is asserted.

The eleven proposed conclusions read as follows.

1. If `det(M_ell) != 0` and `M_ell p=v(q)`, then the complete stage moment
   vector is exactly `v(q)`, for all finite `J`, added locations, and real
   added weights. This is conditional finite linear compensation; it does
   not construct such a base vector or prove matrix invertibility.
2. If every absolute coordinate of `M_ell^{-1}d` is strictly below the
   corresponding `p_i`, then every compensated base weight is strictly
   positive. The stated strict comparison itself implies `p_i>0`.
3. Under that same strict comparison and strictly positive added weights,
   every complete stage weight is strictly positive. This uses actual
   index-wise weights; it does not separately assert distinct atom locations.
4. For each fixed `ell`, each fixed strictly positive four-vector `p`, and
   each fixed real `B>=0`, there exists `eps>0`, chosen before `J,x,r`, such
   that every finite added family with nonnegative weights, every feature
   coordinate bounded in absolute value by `B`, and total added weight
   strictly less than `eps`, leaves all compensated base weights positive.
   Thus the radius is uniform in the finite family size and locations once
   the displayed feature bound is fixed. It has no explicit dependence on
   `q`, and no invertibility assumption: it only bounds the finite, total
   matrix-inverse expression appearing in the definition.
5. Under the determinant and initial four-constraint hypotheses from item 1,
   the sum of all stage weights is one. This is an algebraic total-mass
   identity; nonnegative weights are not hypotheses of this theorem alone.
6. Under the same hypotheses, the weighted sum of atom locations is `q/4`.
   Together with the preserved square coordinate `q`, this is the finite
   identity `E x = E x^2/4` when the weights genuinely form a probability law.
7. For each natural `k`, the specified added atom
   `a_k=4+sqrt(10-2^{-(k+1)})` has `Y(a_k)=6+2^{-(k+1)}`.
8. Every such added atom is strictly greater than four.
9. Every such added atom is strictly less than `4+sqrt(10)`.
10. The map from natural `k` to this added atom is injective.
11. The four base normal values are exactly `(-9,7,6,12)` in base-index order.

The arbitrary added locations in items 1-6 are not restricted to the
particular dyadic sequence from items 7-10. Connecting those two parts is
a later instantiation, rather than an unstated premise of compensation.
The first added atom uses source mesh index `j=1`, not `j=0`.

Zero perturbation is included in items 1, 2, and 4: `r=0` gives `d=0` and
`p'=p`. Item 3 intentionally requires strict positivity of each added weight;
for nonempty `J` it cannot claim strictly positive weights when `r=0`.
For `J=0`, the added-weight and feature-bound hypotheses are vacuous and
the compensated stage reduces to the four base atoms. No asymptotic,
infinite-support, nonarithmetic, or counterexample conclusion occurs in
these proposed statements.

## Source and boundary comparison

After recording the blind translation above, I read the complete three
assigned candidate documents and the actual read-only source anchors listed
below. I then read `api-and-probes.md` as an object whose claims and scope
could be examined. Its reported API runs, exact arithmetic probes, proposed
radius proof object, and starter candidate are not proof evidence for this
verdict. I did not read the optional external-theorem map: U1 uses no such
external theorem. No historical verification report was used as a substitute
for reading the actual R1 anchors.

### Actual bytes reviewed

| Document | SHA256 |
|---|---|
| `drafts/oq3/root-contract.md` | `a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a` |
| `drafts/oq3/dependencies.md` | `b85ec1b3652c23b81f33136170f41fda1da416e25d8e1f645275bcc884cf48fc` |
| `drafts/oq3/first-unit-scope.md` | `68a0774f95291674f025c355c7a84ef20c9b11e27e1cca88ffb9861d9f035257` |
| `drafts/oq3/api-and-probes.md` | `eb50a52567aaf00105aac89a8086a42974d63f3d800be3242745a70123d55db9` |
| Original `current/oq3/proofs/r1/report.md` | `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` |
| Original `current/oq3/verdict.md` | `fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5` |
| Original `current/oq3/proofs/r2/repair01.md` | `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd` |

The first four paths have local root `C:/game/shao lean/`; the last three
have local root `C:/game/shao/`. Hashes were computed from actual local bytes,
not copied from the author's receipt. No source arithmetic was rerun.

### Exact source mapping

| Proposed interface | Read-only original anchor | Independent source check |
|---|---|---|
| `normalValue`, boundary/centering features | R1 lines 18-24 | Same `Y=8x-x^2`, `f1=x^2-4x`, `f2=x exp(-ell Y)`; source fixes `ell=log(31/30)` later. |
| Four base atoms, row/column convention, target vector | R1 lines 66-108, especially 89-92 and 105-108 | Fourth point is exactly 2; matrix columns are the feature vectors; all four constraints use one fixed `q`. |
| `compensated_stageMoment` | R1 lines 105-108 and 122-130 | The subtraction has the exact source sign; the added moment is subtracted through the inverse of that same column matrix. |
| Base/stage positivity and uniform radius | R1 lines 83-87 and 122-135 | Starting masses must be positive; sufficiently small total added mass preserves base positivity. Uniformity uses a common feature bound and is not allowed to deteriorate with `J`. |
| `stage_mass_one` and `stage_boundary_moment` | R1 lines 105-108 and 147-151 | Mass is the first preserved coordinate. The mean `q/4` follows jointly from `E f1=0` and `E X^2=q`, under the tilted law. |
| Added atom, strict location bounds, injectivity and normal value | R1 lines 113-120, with base point at lines 26 and 66-68 | Lean index `k` denotes source `j=k+1`; the branch is `4+sqrt(10-h_j)`, below its limiting base point. |
| U2 obligations, excluded from U1 | R1 lines 26-109 | The actual positive starter, its `1<q<103/100`, and invertibility must still be proved for the source specialization. U1 does not supply them. |
| Tilted law versus original law | R1 lines 122-145 and 147-153 | Finite compensation constructs `pi_J`; original `P_J` is obtained only by the separate normalized inverse tilt. |

### Probability meaning and conditional status

The law distinction is correct and necessary. R1 lines 122-130 name the
compensated law `pi_J`; lines 137-145 separately define
`P_J(dx)=exp(-ell Y(x)) pi_J(dx)/Z_J` and explain centering by `E_pi f2=0`.
The proposed `stageMoment` is a finite sum of real index weights, with no
`Measure`, `PMF`, or claim of original-law expectation. Its four coordinates
therefore implement the tilted constraints, not four equations under `P_J`.
In particular, `stage_boundary_moment` gives the tilted mean `q/4`, not the
original mean; `E_P X=0` is a different later conclusion. The scope's lines
7-9 and root-contract line 55 state this distinction explicitly.

The exact-preservation theorem explicitly assumes `det(M_ell)!=0` and the
initial constraint equation. It does not assert their existence for arbitrary
`ell`. The positivity radius explicitly assumes strict positivity of the
starting four-vector. Combining the preservation theorem with the radius
and positive added weights yields legitimate finite probability weights;
`stage_mass_one` alone is only a signed-weight identity. This is a proper
conditional U1 helper, rather than a new premise silently imposed on root A.

The missing source instantiation is correctly assigned to U2 in
`dependencies.md` lines 37-39: prove the source fixed `ell`, a genuine
positive starter, a `q` in the open interval, and the nonzero determinant.
The common feature bound and fixed positive infinite-stage construction are
still assigned to U2/U3. The dependency diagram's extra text correctly warns
that the starter part of U2 is independently constructed; no circular
existence argument is hidden in the displayed consumption arrows.

### Parameters and feasibility of the finite statements

The matrix orientation and the compensation definition match: rows are
features and columns are base locations, so a finite stage has vector moment
`M_ell(p-M_ell^{-1}d)+d`. The stated invertibility hypothesis is exactly what
is needed to simplify this expression to `M_ell p`, and `hp` supplies the
target. No transposed inverse or mismatched feature vector appears.

For the radius theorem, `ell`, `p`, and `B` precede `eps`, while `J,x,r`
follow it. This is the required quantifier order. A fixed real four-by-four
matrix has finite coefficient bounds, and the nonnegative added weights and
the common feature bound control each added-moment coordinate by
`B sum r`. A coordinatewise matrix bound can therefore depend on `ell,p,B`
and not on `J`. This confirms statement feasibility without consuming the
author's probe or a stage-dependent continuity assertion as evidence.
Invertibility is not needed for this pure small-perturbation estimate on the
fixed total inverse expression; it remains necessary for exact preservation.

The generic freedom in `ell`, arbitrary added locations, and real signed
weights in the algebraic statements is a valid generalization of the source
finite algebra. It does not weaken the eventual source obligation to fix
`ell=log(31/30)`, one `p`, and one `q` before all stages and sample sizes.
Likewise, the radius is not claimed uniform over changing `ell`, changing
base weights, or an unbounded feature family. The actual dyadic locations
must later receive a single common feature bound, as the scope states.

The exact finite types, real scalar operations, matrix inverse, disjoint-sum
index, and finite sums are appropriate for a Lean implementation. The scope
already requires the enclosing `noncomputable section`, which is necessary
for the real inverse/exp/sqrt definitions. No measurability or probability
typeclass is required for U1's algebra itself. This is an implementability
assessment, not a claim that the proposed declarations have compiled.

### Strict boundaries, zero cases, and probability mass

- The comparisons in `hsmall` and the total-mass radius are strict. Their
  conclusions are also strict positivity. Replacing the input bounds by
  closed bounds would allow zero base weights and would change the theorem;
  the proposal does not make that replacement.
- The radius permits nonnegative added weights, including zeros. Its
  conclusion concerns only the compensated four base weights. Full
  `stageWeight_pos` separately assumes each added weight is strictly
  positive. This correctly separates zero perturbation from positive added
  atoms. `J=0` is legal and imposes no artificial nonempty condition.
- For `B=0`, the radius conclusion remains sound. The first feature is one,
  so the common feature-bound premise is impossible for a nonempty added
  family; the empty-family case simply leaves `p` unchanged. A later radius
  proof must also handle a zero coefficient bound without multiplying a
  strict inequality by zero, but no new hypothesis is needed in the
  statement.
- The `k+1` shift avoids a zero dyadic level in the source atom sequence.
  Each mesh is strictly positive and at most `1/2`, placing the square-root
  radicand strictly between zero and ten. Thus the strict upper location
  bound, strict lower bound at four, and injectivity are compatible with
  the source formulas, including `k=0`.
- Distinct index weights do not require distinct locations for finite
  weighted-sum identities. If an eventual measure uses repeated locations,
  their positive masses must be combined by pushforward. U1 neither assumes
  a false injectivity of arbitrary `stageAtom x` nor asserts covariance
  nondegeneracy from finite weight positivity.
- `q` is unrestricted in the conditional algebraic helpers; source
  `1<q<103/100` is an open condition to be constructed by U2. This is not a
  substitution of a degenerate `q=0` into a probability root.
- The root contract keeps the original tail boundary weak in its sum
  inequality but retains `Q_n>0`/`q>0` (line 26). It explicitly says this
  domain is not a closed subset of all of `R^2`. U1 introduces no tail event
  or closure that would add the zero-square case.

### No promotion of local coverage or repair strength

R1 lines 11-14 and 132-135 still require the later order of selecting a
finite-stage witness and only then restricting future masses. The U1
statements quantify over finite `J`; none constructs a single infinite law,
proves nonlattice behavior, proves a local limit theorem, or transfers a
tail witness. The root contract explicitly quantifies one final `P,x0`
outside all sample sizes, and the dependency map leaves U3-U11 open.
Consequently acceptance of U1 cannot be reported as acceptance of the fixed
full counterexample.

The separate repair is consistently described as sufficient, not weakest:
the actual original `verdict.md` lines 5-7 and 29-40 say so, while original
`repair01.md` lines 214-226 explicitly retain the far-field probability
estimate and disclaim a characterization of the validity/failure boundary.
The root contract's final section makes no endpoint-beta, optimality,
priority, or full-formalization claim. U1 itself has no repair conclusion.
This review has not revalidated the external Song result, the numerical
starter certificate, the original counterexample proof, or any full root.

## Final verdict and remaining gates

CORRECT for the eleven proposed U1 theorem statements, fourteen definitions,
and their stated conditional source scope at the hash above. No blocking
signature or boundary correction is required before a coordinator freeze.

Implementation must still prove the frozen statements on the pinned server,
audit all new declarations and generated helpers for standard axioms, and
receive a fresh proof review. U2 must remove the starter/invertibility
assumptions by proving the source specialization; U3 and later units must
construct and control the one final law. All four OQ3 roots remain OPEN.

No Lean command, arithmetic recomputation, cache access/download, source
modification, or target implementation edit was performed during this
statement review. Only this independent review file was written.
