# Unit236 independent complete source review

**Verdict: CORRECT_SOURCE_KERNEL_PENDING.** The exact 239-line source is mathematically correct as a proof of its frozen deterministic statement. No critical source-to-statement or proof gap was found. This review does not qualify a Lean object: `qualified=false`, `kernelPending=true`, `kernelChecked=false`, and `axiomAudited=false`.

Reviewer role: `/root/oq56_exceptional_tail236_source_review`, fresh NEVER-AUTHOR independent context. The reviewer did not write or repair this source, freeze its declaration, participate in its Stage1 route, or review its accepted predecessors' proofs. The current task is independent verification under math-theorem; no math-ultra workflow was used. The actual runtime acknowledgement preceded mathematical review. Requested model/effort are explicitly `gpt-6.1-sol`/`xhigh`; actual runtime model/effort and input, cached-input, output and reasoning-subset token counts are not exposed and remain null.

## Exact object and authority

The source is `drafts/oq56/unit236/author-01/OriginalExceptionalTailAbsorption.lean`, SHA256 `ebddcd2141aa704400cec5d3c3b6157ba6d83cdb8df17a8b5b28ab8320cecf6d`, 11078 bytes, 239 LF, UTF-8 without BOM and without CR. The review activation is SHA256 `3717ba85b7334bf71c018175bcdd34f906fc075100c4f8cb3fca3f40e7cac6d8`, 10708 bytes. All 26 activation-bound immediate records (11 handoff/freeze/author records and 15 mathematical inputs) matched their expected byte lengths and SHA256 values. Additional nested frozen fragments and author-manifest references were verified separately in INPUT-BINDINGS.json. These are byte/structure observations, not Lean checks.

The sole frozen public declaration is
`Shao.OQ6.OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed`.
Frozen preamble, complete head, and closing were compared directly to the source and match exactly. The full freeze inventory was read, including every ordinary RHS, universe/instance context of the motivating interfaces, result quantifier, permitted local scalar, and explicit scope restriction.

Current governing AGENTS core, Coordinator5 appendix and subsequent OQ3 resumption appendix, SERVER restrictions, selected TEAM ownership, and selected current REGISTRY fields were read. Sole project Root is `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`; OQ56 lead remains `01a17665-2e41-7ed1-9911-57f16fe889fa`. Current phase is `ROOT_OQ56_OQ3_40`; OQ3 has been explicitly resumed, so older pause text is historical. Historical TEAM and SERVER resource passages do not supersede those current rules. This reviewer has heavy allowance zero and writes only `unit236/source-review-01/**`. No Root or other sidebar chat was messaged. Parent collaboration messages are the authorized runtime/report channel.

The pinned versions are `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The curated snapshot's toolchain/manifest and existing pinned primary source provenance are inputs; no local Lean executable or server connection was used. A missing workspace-root `lean-toolchain` path was a local lookup issue, resolved by locating the read-only `library/lean-toolchain`; it was not classified as a missing server toolchain.

## Statement, ordinary data, and quantifiers

The only theorem arguments are real `t0,cg` and proofs `0<t0`, `0<cg`. There are no ambient parameters, universe parameters, probability-space instances, hypotheses about rates, model witnesses, callbacks, or assumptions equal to the desired conclusion. The result fixes

\[
c=\min(1,\sqrt{t_0}/2)
\]

before the eventual natural index and all real thresholds. It asserts `c>0` and one eventual set of natural `n` on which **all** of the following hold: `n>=4`, `1<=c*n^(1/6)`, and the literal inequality for every `1<=z<=c*n^(1/6)`. Thus the window is closed and nonempty; its uniform cutoff may depend on `t0,cg` but not on `z`. There is no finite-n assertion or z-dependent eventual quantifier.

Writing `q=t0*n^(1/3)`, the exact assertion is

\[
6e^{-q}+2e^{-c_gn}+8e^{-\sqrt n/2}
\le e^{-(t_0/2)n^{1/3}}Q(z).
\]

Every fractional exponent is explicitly real: `(1/3:ℝ)`, `(1/6:ℝ)`, `(2/3:ℝ)`. Every square in the new proof is explicitly the natural square. Natural-to-real casts cannot turn a fractional exponent into natural division.

The result-type `cWindow` let is unchanged. There are exactly the five permitted proof-local ordinary lets, with no extra ordinary helper:

| Lines | Name and type | Complete RHS | Scope |
|---|---|---|---|
| 28 | `cWindow : ℝ` | `min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))` | Mirrors the result let; depends only on t0 |
| 29 | `b : ℝ` | `3 * t0 / (8 : ℝ)` | Before eventual n; depends only on t0 |
| 85 | `x : ℝ` | `(n : ℝ)` | Inside the chosen n branch |
| 86 | `s : ℝ` | `Real.rpow x (1 / 3 : ℝ)` | Same n branch |
| 87 | `u : ℝ` | `Real.rpow x (1 / 6 : ℝ)` | Same n branch |

All other named locals are proofs of propositions: order/equality facts, Tendsto or Eventually facts. In particular `hratio := ...` has the proposition supplied by a public theorem, and each unnamed `have h := ...` is also proof-valued. Inline functions in Tendsto propositions are fully displayed terms, not additional ordinary bindings. The `.mono (fun _ hn => hn.le)` function is an internal proof transformation, not a caller callback or an added data premise. There are no new definitions, helper theorems, structures, instances, `letI`/`haveI`, choice witnesses, or changed assumptions.

## Actual definitions and accepted interfaces

The exact accepted definitions read directly from the bound files are:

```lean
noncomputable def Shao.standardNormalDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 x
noncomputable def Shao.standardNormalTail (x : ℝ) : ℝ :=
  ((ProbabilityTheory.gaussianReal 0 1) (Set.Ioi x)).toReal
def Shao.OQ5.P51.boundedPolylogMomentOrder (t0 : ℝ) (n : ℕ) : ℝ :=
  t0 * Real.rpow (n : ℝ) (1 / 3 : ℝ)
noncomputable def Real.rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
noncomputable instance : Pow ℝ ℝ := ⟨Real.rpow⟩
```

The namespace-qualified presentation above is explanatory; the bound primary files give these declarations in their namespaces. Real.sqrt is the primary definition `NNReal.sqrt (Real.toNNReal x)`. Its positive-input properties are invoked only with the proved nonnegative/positive inputs. The unused P51 height definitions were also inspected in their actual contexts: `C * Real.rpow (Real.log (n:ℝ)) a`, and `Real.rpow (A * Real.log (n:ℝ) / tau) (1/alpha:ℝ)`.

All seven Gaussian public theorem heads were read completely: representation, basic, derivatives, Mills bounds, ratio, local comparison, and deletion comparison. All four P51 public heads were likewise read, with all imports/namespace/noncomputable-section/options context. Their exact source heads are included in COVERAGE.json. No accepted proof body was re-reviewed. The new proof uses only these two Gaussian interfaces:

```lean
theorem Shao.standardNormalTail_basic :
  Antitone Shao.standardNormalTail ∧
  Shao.standardNormalTail 0 = (1 / 2 : ℝ) ∧
  (∀ x : ℝ, 0 < Shao.standardNormalTail x ∧ Shao.standardNormalTail x < 1) ∧
  ∀ x : ℝ, Shao.standardNormalTail (-x) = 1 - Shao.standardNormalTail x

theorem Shao.standardNormalTail_ratio_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
  Shao.standardNormalTail y ≤
    (4 / 3 : ℝ) * ((1 + x) / (1 + y)) *
      Real.exp ((x ^ 2 - y ^ 2) / 2) * Shao.standardNormalTail x
```

The fixed accepted tail is therefore not an arbitrary function supplied by a target-bound premise, and the proof does not use a private density formula or assume a separate Mills lower bound.

## Complete proof review

**Lines 28–44: geometry and residual rate.** Since t0>0, sqrt(t0)>0; both arguments of the min are positive, so c>0. The min projections give c<=1 and c<=sqrt(t0)/2. Both factors in `(sqrt(t0)/2-c)*(sqrt(t0)/2+c)` are nonnegative. Expanding that product and using `(sqrt(t0))^2=t0` gives `c^2<=t0/4`. The local b is exactly `3*t0/8>0`; there is no smallness hypothesis on t0.

**Lines 45–78: genuine scalar growth and residual limit.** Natural cast tends to positive infinity. Composing the exact global positive-exponent rpow theorem yields divergence of the third, sixth and two-thirds powers of n. The global exponential-decay theorem at powers 0 and 1, coefficient b>0, composed with the third-power sequence, proves respectively `exp(-b*s)->0` and `s*exp(-b*s)->0`. Their sum and multiplication by 128/3 give

\[
R_n=(128/3)(1+s)e^{-bs}\longrightarrow0.
\]

The neighborhood `(-infinity,1)` of zero supplies eventual R_n<1, weakened to R_n<=1. This is derived rather than assumed; it contains no z.

**Lines 79–97: a single eventual set.** The proof intersects exactly five conditions before introducing z: `n>=4`, `u>=1/c`, `n^(2/3)>=t0/cg`, `u>=2*t0`, and R_n<=1. Inside this branch x=n>=1, hence x>0 and s,u>0. The cast uses the already proved natural n>=4. The approved aliases are introduced only in their frozen scopes.

**Lines 98–113: positive-base power algebra.** Real.rpow_natCast converts u squared to real exponent 2; the reverse rpow_mul identity at x>=0 gives `u^2=x^((1/6)*2)=s`. Exponent monotonicity for base x>=1 gives u<=s. The reverse rpow_add identity is applied with x>0, so `s*x^(2/3)=x^(1/3+2/3)=x`, and `s*u=x^(1/3+1/6)=sqrt(x)` by the primary sqrt/rpow identity. No multiplicative power identity is used at a prohibited negative base or without its positivity condition.

**Lines 114–127: nonemptiness and fast rates.** Dividing/multiplying the first growth condition uses c>0 and yields 1<=c*u. The second, using cg>0 and s>0, gives `t0*s<=cg*x`. The third, multiplied by s>0 and simplified with s*u=sqrt(x), gives `t0*s<=sqrt(x)/2`. These estimates hold for this n uniformly before z is introduced. They work for every fixed pair of positive parameters, including arbitrarily small c or cg.

**Lines 128–151: the entire closed window.** The proof returns n>=4 and the nonempty-window inequality, then introduces an arbitrary z satisfying the literal weak endpoints. Since z>=1, z>=0. Both factors `(c*u-z)` and `(c*u+z)` are nonnegative, so squaring the upper bound is justified: `z^2<=(c*u)^2=c^2*s`. Combining with c^2<=t0/4 and s>=0 gives `z^2/2<=(t0/8)*s`. Also `z<=c*u<=u<=s`, hence `1+z<=1+s`. Both denominators are strictly positive. Equality at either endpoint is fully retained; no strict window is substituted.

**Lines 152–180: correct reverse-ratio direction and exact 3/8.** Calling the public ratio theorem with x=z,y=0 requires z>=0 and 0>=0, both supplied. Public basic gives Q(0)=1/2, leaving

\[
1/2\le(4/3)(1+z)e^{z^2/2}Q(z).
\]

The proof multiplies this inequality by the strictly positive `exp(-z^2/2)`. Its explicit exp-add calculation proves `exp(z^2/2)*exp(-z^2/2)=1`. Rearrangement gives `(1/2)exp(-z^2/2)<=(4/3)(1+z)Q(z)`. Scaling by 3/4 and dividing by 1+z>0 yields

\[
(3/8)e^{-z^2/2}/(1+z)\le Q(z).
\]

There is no inversion of an inequality in the wrong direction. The factor 3/8 is exactly `(1/2)/(4/3)`.

**Lines 181–197: uniform Gaussian lower bound.** The squared-window inequality implies `exp(-(t0/8)*s)<=exp(-z^2/2)` with the displayed negative signs. Multiplication by 3/8 preserves order. Rather than silently comparing reciprocals, the proof multiplies through the positive denominators. It uses Q(z)>0 from public basic to enlarge `Q(z)*(1+z)` to `Q(z)*(1+s)`. Thus

\[
(3/8)e^{-(t_0/8)s}/(1+s)\le Q(z).
\]

**Lines 198–208: all literal numerator coefficients.** The established fast rates imply `exp(-cg*x)<=exp(-t0*s)` and `exp(-sqrt(x)/2)<=exp(-t0*s)`. Multiplying by 2 and 8 and adding the unchanged 6-term gives exactly `(6+2+8)exp(-t0*s)=16exp(-t0*s)`. None of the three summands or their coefficients is dropped.

**Lines 209–226: exact exponent and factor identity.** The exp-add calculation uses `b+t0/2+t0/8=t0`, since b=3t0/8. The displayed algebraic identity is

\[
R_n\left[e^{-(t_0/2)s}(3/8)e^{-(t_0/8)s}/(1+s)\right]
=16e^{-t_0s}.
\]

Its constant is `(128/3)*(3/8)=16`; cancellation of `(1+s)/(1+s)` uses the proved strict positivity. The identity therefore exposes both the 128/3 residual and the full 3t0/8 exponent loss, without an unproved asymptotic comparison.

**Lines 227–239: absorption and closure.** The bracketed factor is nonnegative. Multiplying R_n<=1 by it and rewriting the exact factor identity gives the absorption of 16exp(-t0*s). Transitivity with the numerator bound and the actual Gaussian lower bound, multiplied by positive exp(-(t0/2)*s), proves the exact frozen conclusion. The final namespace closing and all blank/context lines are covered; there is no omitted branch or deferred goal.

The source has no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`, and no placeholder. This source observation does not claim a transitive axiom result: the latter must be obtained from the actual first successful server object.

## Pinned API provenance and context

The pinned Pow.Asymptotics file is SHA256 `f736afe5ee0e392168895c13ce258c142fdc5d3b45ecb5d3dd12af9299a8ee42`, 19292 bytes. Its existing manifest explicitly records the pinned mathlib commit and that fingerprint. The relevant source contexts are `public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal`, `public section`, `open Real NNReal ENNReal Filter Set`, `open scoped Topology`, and `section Limits; open Real Filter`. Both used names are global:

```lean
theorem tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) :
  Tendsto (fun x : ℝ => x ^ y) atTop atTop
theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (s b : ℝ) (hb : 0 < b) :
  Tendsto (fun x : ℝ => x ^ s * Real.exp (-b * x)) atTop (𝓝 0)
```

The pinned Pow.Real source is SHA256 `f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd`, 50402 bytes, with `pinnedGitBlobExact=true` in the existing manifest. The definition and actual standard Pow instance were read. Its context includes the Complex public import, public noncomputable section, namespace Real, and real implicit variables. Exact relevant heads and their assumptions were read directly: rpow_natCast(x,n); rpow_pos_of_pos(hx>0,y); rpow_zero(x); rpow_one(x); rpow_add(hx>0,y,z); rpow_mul(hx>=0,y,z); rpow_le_rpow_of_exponent_le(hx>=1,hyz); and sqrt_eq_rpow(x). The proof's applications supply precisely these hypotheses. COVERAGE.json records their source line ranges and exact source heads.

The complete supplied nat-cast excerpt is SHA256 `ddc6a12d12faefee3dba7f13aaf338119f8dfaf8b21c3b5cc2dab5370a0f603b`, 1737 bytes. Its server-source binding records the pinned full source SHA256 `0ba4137bb8d0837d43b1140379163e3cdf89e88675c26807c51f5e801ad31df3`, 12631 bytes, and exact contexts/range. The global theorem has ambient `{R : Type*}` and `[Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]`, with conclusion `Tendsto ((↑):ℕ→R) atTop atTop`. At R=ℝ these are the ordinary existing instances; none is supplied by a new local instance. The public imports/section/open context and complete lines41–57 were read. This is supplied primary provenance, not a new remote observation by this reviewer.

The existing primary Real.Sqrt excerpt is SHA256 `bd1ce982c64140416e40c48711378711ac7275027e130962692804167ce3a78e`, 13562 bytes, through line384. Its actual sqrt definition, Real namespace context, sqrt_nonneg, sq_sqrt(h>=0), and sqrt_pos equivalence were read. It is an existing pinned-source excerpt, not a full new remote retrieval. No critical API provenance gap remains for this source review; exact elaboration and import availability remain server gates.

## Primary-source fidelity and exact reused evidence

Complete p54 (86 LF) and p51 (355 LF) were read. p51 S11 and S15–S19 motivate paying actual concentration failures on a small sixth-root window; p54 Section2/F5–F6 explicitly requires dividing by the actual Gaussian tail. The scalar theorem supplies a sufficient exponential absorption inequality for that sentence. It does not apply an event inequality, reconstruct an original model, or prove the whole probability chain.

p54 Section1 corrects p51 S6's false arbitrary-polynomial variation assertion for conditional p moments to convergence plus a uniform bound. Unit236 has no p-moment-rate premise or use of that false sentence. The actual `T=(W+D)/s`, with its s=0 branch, and p51's named external Shao–Zhou dependencies stay unchanged. Compact CDF/atom arguments and tail source applications are not conflated.

Complete public source heads and contexts of qualified233 and qualified235 were read, including all ordinary lets/functions, measurable-space and probability instances, existential cg scopes, window/rho premises and every payment. Their copied heads and contexts in the frozen inventory were compared directly to their exact source and matched. The qualified evidence was used only for its exact source/interface/scope/original-object/kernel/audit fields:

| Unit | Exact source SHA256 | First original object SHA256 | Existing native/audit | Existing owner/type/value scope |
|---|---|---|---|---|
| 233 | `8281cbb3a10297297d6e92fce7c258ad2d0c0ccd7406aae63aefd3194beccbab` | `b9d985696e9820554421e78424123ad8c7fdc11607b74794c6bb669b3c015d78` | 0/0 | 2 actual owners,470 TYPE LF,0 VALUE LF |
| 235 | `b16dcd02c4a14518bdbbd64b33ce94bcefe7c7770496e8f1a8a7c92872e3fb55` | `a5a8bdb264e88b97b4202a01a945ea06700a7c32c6b6d22520dd141c5ea4a07c` | 0/0 | 2 actual owners,264 TYPE LF,0 VALUE LF |

Both existing receipts record only `Classical.choice`, `Quot.sound`, `propext` transitively. Their old proofs and successful checks were neither re-reviewed nor replayed. These predecessors are motivation, not imports or assumptions of236.

Specifically233 pays `3exp(-q)+exp(-cg233*n)+4exp(-z*sqrt(n)/2)` for its actual H complement, while235 pays `3exp(-q)+exp(-cg235*n)+4exp(-sqrt(n)/2)` for the retained-clip1/physical comparison exception under its explicit premises. For z>=1 the former last term is bounded by the latter last term. Adding and choosing a proved-positive minimum of the **two independent** cg witnesses motivates literal6/2/8. That minimum, event union, shared-model binding, intersection with the actual remainder window and strict source budgets must still be implemented by a future consumer. This review never identifies the two witnesses by name alone.

No original-model same-witness construction, source analytic/coding/SZ application, relative-error consumer, CDF, atom, projection-zero/studentizer-zero probability closure, full S11/general S15/DC, root completion, or novelty claim is made. Correctness of this deterministic helper is distinct from completion or novelty of the research target.

## Actions and next gate

All executed actions were local reads, direct byte hashes, deterministic source/head comparisons, and writes within the review directory. There was no Lean/local-toolchain execution, server/network/upload action, Git/API action, child context, source/freeze/author/other-owner write, or old accepted proof/check replay. Local JSON reading encountered case-sensitive STATUS/status keys; re-reading with a case-preserving parser resolved that administrative issue without changing any input.

The next mathematical gate belongs to the lead: exact-source designated-server native elaboration/kernel check, followed on the same first successful original object by actual module-index owner discovery, all owned full TYPE and required VALUE output, and recursive/transitive AX audit. Until those receipts and the independent final machine-evidence join exist,236 remains kernel pending and unqualified. This same never-author context may join complete machine evidence later without duplicating the complete proof review unless bytes change or a concrete uncovered gap arises.

The final zero release is the last authorized write and binds the completed manifest. It asserts zero writer/heavy/inflight/pendingExternal/children/uncertain operations for this reviewer; it does not claim that another lane or the lead is idle.
