# RetainedVariance independent review

Verdict: **CORRECT** for the three frozen public statements at the source
hash below. No critical encoding or proof defect was found. The sequential
blind-translation and proof-audit checkpoints below are preserved.

Reviewed source candidate SHA256:
`5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6`.

Reviewer: the `deletion_inequality` agent, separate from the author of
`RetainedVariance.lean`. This reviewer did author the previously accepted
`RetainedMoments` dependency; it is treated as an accepted fixed interface,
not re-certified by this review. The reviewer has not authored or modified
the current variance implementation. Only this review file may be edited.

## Stage 1: blind translation before reading the Lean proof or author receipt

This stage used `RetainedVariance-scope.md` and extracted public theorem
statements only. Neither the Lean proof bodies nor
`RetainedVariance-review-receipt.md` had been read. The scope itself contains
a proposed mathematical decomposition, so this is blindness to the Lean
proof and author verification receipt, not a claim that the proof plan was
hidden.

The source hash was read directly from the local candidate and matches the
assigned hash above. The implementation exposes three public theorems and
no new public definition. Its namespace is `Shao` and `autoImplicit` is off.

My translation of the three actual statements:

1. For a true probability law `ν` with an integrable square, `x>0`, and
   positive mass of the existing weak cutoff `B={|z|≤1/x}`, let `ν_x` be the
   existing actual conditional measure and `μ_x=∫z dν_x`. The centered id,
   centered square and centered absolute cube are integrable under `ν_x`;
   `∫(z-μ_x)dν_x=0`; the actual centered-square integral is
   `∫z²dν_x-μ_x²`; and its centered absolute third moment is at most eight
   times its raw absolute third moment. This theorem does not assert
   positive variance or assume original mean zero, normalization, a global
   third moment, or Jensen as an input. Degenerate conditioned laws are
   permitted here.
2. For a probability law with integrable square, zero original mean and
   `n∫z²dν=1`, assume `x≥2`, `x⁶≤n`, natural `j≤x²/2`, and the literal
   budget `H_x=n∫F(xz)dν≤1`. With `M=↑(n-j)` using natural subtraction,
   `y=√(x²-j)`, and `V_x=∫(z-μ_x)²dν_x`, obtain actual conditional support
   `|z-μ_x|≤2/x` almost everywhere, `V_x>0`,
   `1/2≤M V_x≤2`, and `M∫|z-μ_x|³dν_x≤16/y³`. Neither conditional mass
   positivity nor variance positivity is a hypothesis of this theorem.
3. Under exactly the same quantitative inputs as item 2, bound the actual
   centered third moment divided by `√M (√V_x)³` by `64/y³`. This is the
   usual variance-normalized Lyapunov quantity at row length `M`, not a
   quotient with raw second moment, `M^(3/2)` alone, or a changed conditional
   law.

Independent arithmetic checks from those statements:

* `x≥2` and `x⁶≤n` force `n≥64`. Also
  `j/n≤1/(2x⁴)≤1/32`, so `j<n`, `M>0`, `M/n≥31/32`, and
  `0<y≤x`. Thus the natural subtraction and all intended divisions can be
  justified rather than postulated.
* The stronger accepted raw bound `n E_x z²≥1-1/x²≥3/4` implies
  `M E_x z²≥93/128`. The mean bound `n|μ_x|≤2/x` and `M≤n` give
  `Mμ_x²≤4/(n x²)≤1/64`. Their difference is at least `91/128>1/2`.
  Subtracting a mean square from only the relaxed raw lower bound `1/2`
  would not suffice; the stronger bound is essential.
* The centered/raw absolute-cube comparison, if proved with actual
  integrability, turns the accepted `M E_x|z|³≤2/y³` into `16/y³`.
* With `C=E_x|z-μ_x|³`, the exact normalization is
  `C/(√M(√V_x)³)=(M C)/(√(M V_x))³`. The positive lower bound on `M V_x`
  controls the denominator. Even the coarser lower bound
  `(√(M V_x))³≥1/4` suffices for `64/y³`.

No mathematical contradiction is apparent at this statement-only stage.
This is not yet an acceptance verdict: source correspondence, dependency
types, integral justification, the actual separation proof, and server
evidence remain to be checked.

## Stage 2: source and accepted dependency correspondence

Before reading the variance proof I checked the original supplement and
both accepted dependency scopes. Their actual local source hashes match
the accepted versions:

```text
RetainedMoments.lean
512cf7a51125f18f94f42b4ef855e21290a28f7a3185865a3d375bde8100d6cb
RetainedSample.lean
a507e549e2973dd04ce25f22e2c6973e0e6c491433a1d7fd2d88fbb082e86ca4
```

The source correspondence is faithful at this stage:

* `supplement.tex:172–197` uses the true conditional law at weak cutoff
  `|z|≤1/x`, `m=n-j`, `y=√(x²-j)`, mass at least `1/2`, and the displayed
  **raw** n-normalized moment bounds. Lines 199–203 give the raw retained-row
  bounds. These do not themselves assert a variance lower bound.
* The already accepted `RetainedMoments` API supplies actual conditional
  probability, id/square integrability, support, mean and raw square bounds
  under the literal `H_x≤1`. `RetainedSample` supplies actual conditional
  cube integrability, raw third moment, the stronger retained fraction and
  positive sample length/threshold bounds. Its raw lower bound must not be
  relabeled as variance.
* `supplement.tex:1240–1259` explicitly distinguishes
  `ν=k E B²` from `τ_B²=Var(B)`, then centers `Y=B-E B`. Its generic bound is
  obtained after a sufficiently-large-threshold reduction depending on `D`.
  The new constants `1/2`, `16`, and `64` are correctly presented as derived
  helpers for this more constrained retained law, rather than claims that
  the original generic lemma states those constants for every bounded law.
* `supplement.tex:1075–1080` uses centered absolute cube divided by
  `τ_B³√m`; lines 1203–1225 require positive variance and finite centered
  cube for completion. The candidate's `√M(√V_x)³` is that denominator.
* None of the three public candidate statements replaces `H_x` by
  `R_n(x)`, changes the cutoff to `1/(1+x)`, assumes a globally integrable
  original cube, or inserts positive variance as a premise. No iid claim
  at random retained sample length is made.

The implementation proof and its author receipt have still not been read
at this checkpoint. The remaining review must check that these actual
integrals and positive denominators are established in the proof, not just
named in the statements.

## Stage 3: proof-body audit, completed before reading the author receipt

I then read the complete candidate proof, lines 1–271. The proof matches
the statements and the accepted dependencies; no extra input is hidden in
a helper theorem or local variable.

1. Lines 18–42 prove the cube Jensen comparison for an arbitrary true
   probability law from actual id and absolute-cube integrability. The
   absolute-id integrability is obtained at lines 25–26. The nonnegative
   polynomial `(u-b)²(u+2b)` supplies the pointwise inequality; both sides
   are actually integrable at lines 34–38. The norm-of-integral inequality
   and multiplication by `3b²≥0` yield the result without dividing by `b`.
   Thus `b=0` is covered and Jensen is not an assumed premise.
2. Lines 57–70 install the genuine conditional probability and import the
   accepted raw integrability facts before proving centered id/square
   integrability. Lines 71–87 expand and integrate the actual centered
   square with all linearity premises supplied, obtaining
   `V_x=E_x z²-μ_x²`. Lines 88–106 establish the integrable cube dominator
   first and apply integral monotonicity afterward. There is no use of
   the default integral value for a nonintegrable function, no circular
   centered-cube assumption, and no replacement of raw square by variance.
3. Lines 133–142 derive the source size facts, `M>0`, and positive actual
   cutoff mass. The budget passed to every dependency is the literal
   `hcut : n∫F(xz)≤1`. Lines 146–163 derive the strong raw bound
   `M E_x z²≥93/128`, rather than relying on the relaxed raw `1/2` bound.
4. Lines 164–176 use an alternative valid mean-square estimate:
   `n|μ_x|≤2/x≤1`, `n≥64` imply `|μ_x|≤1/64`, hence
   `nμ_x²=(n|μ_x|)|μ_x|≤1/64`, and finally `Mμ_x²≤1/64`.
   Combined with the actual variance identity, lines 177–179 yield
   `M V_x≥1/2` and then `V_x>0`. The proof uses no variance positivity
   hypothesis. The raw upper bound is used only for the upper variance
   bound at lines 180–185.
5. Lines 186–197 derive the centered support `2/x` from the accepted
   support at `1/x` and the proved mean bound. Lines 198–202 multiply the
   actual centered/raw cube comparison by `M≥0` and use the accepted raw
   retained cube bound, giving the claimed `16/y³`.
6. Lines 225–255 derive all of `M>0`, `V_x>0`, `y>0`, `s>0`, and the
   positive original denominator. Lines 246–259 prove the exact identity
   `s³=M(√M(√V_x)³)` and hence the exact ratio rewrite. The lower bound
   `s³≥1/4` at lines 238–245 justifies the final `64/y³` bound. No zero
   denominator convention, raw-square surrogate, or silently standardized
   law is used.

Boundary audit: the generic first theorem allows degenerate conditional
laws; the quantitative theorems derive nondegeneracy. `x=2`, `j=0`, equality
in `j≤x²/2`, atoms at the weak cutoff, and centered mean zero are all
covered by non-strict inequalities with explicit positive denominators.
The source-derived size conditions exclude `n=0` and an empty retained row.
The stronger helper constants are not misreported as the original generic
bounded-endpoint lemma. No claim proves Berry–Esseen, completion, change of
measure, or the bounded-random root theorem itself.

No critical proof or encoding defect was found in this independent audit.
The author receipt and server artifact binding are the remaining checks;
the receipt will not substitute for the source and proof audit above.

## Stage 4: receipt and independent server artifact check

Only after completing the preceding statement, source and proof review did
I read `RetainedVariance-review-receipt.md`. Its frozen hash and described
proof match the source already reviewed. It reports a successful targeted
server compilation without diagnostics, plus twelve audited declarations
(three public, one private helper and generated declarations) at the
standard axiom whitelist. This is author evidence, kept distinct from my
independent review and server check.

My independent server action reused the existing compiled module; it did
not rebuild old dependencies or repeat the full author compilation/audit.
After activation in `workspaces/lead-c12`, one server call:

* computed the actual SHA256 of the candidate and both accepted dependency
  sources; all three match the hashes recorded above;
* imported `Shao.Probability.RetainedVariance` through
  `taskset -c 0-3 lake env lean --stdin`;
* printed the fully explicit `#check @...` types of all three public
  theorems, confirming the literal source hypotheses, true conditional
  integrals, natural retained length, positive-variance conclusion and
  actual square-root denominator;
* printed transitive axioms for each public theorem. Each result had
  exactly `[propext, Classical.choice, Quot.sound]`. The private polynomial
  helper is covered transitively by the first public theorem.

This independent server check exited 0 with empty stderr. A separate local
text-only prohibited-token scan of the candidate found no `sorry`, `admit`,
new `axiom`, `unsafe`, or `native_decide`. No Lean process ran locally, and
no Lean source, old definition, root import, audit tool, cache or lock was
edited by this reviewer.

## Final verdict and exact scope

**CORRECT** — source-to-statement encoding, actual conditional moments,
integrability, cube Jensen derivation, quantitative variance separation,
retained-row third moment and real Lyapunov normalization all check out for:

```text
RetainedVariance.lean
5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6
```

The accepted conclusion is precisely these three helpers. It is not an
acceptance of the unproved generic bounded-endpoint/completion,
Berry–Esseen, tilted-law comparison, or any full C1 root theorem.
