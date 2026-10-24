# Unit 88 independent final review

STATUS: CORRECT

This is a qualified complete independent review of `Shao.C2.IntervalSineCosineSeries`, separate from its author. All six public proofs, the complete frozen imports/context/heads/definition value, all 17 actual owned complete types, and the one complete actual non-theorem value were reviewed. The original successful server kernel and all-owned transitive-axiom gates are reused at their exact bytes; no gate was rerun.

## Exact version and scope

- source: `7a6c56921d098600ca2b5e952ce0313714c96f8ef30ce99bdcf54ff32d8285b2`
- freeze: `ee13dc4c4e1e9d6eccbac0a9d7f40d866da02b0e3c6e829b5a972928781c5585`
- receipt: `23e1744acead92c721242fd9d0ee2a11a186126f3b720c6ed89a6f4569bd939d`
- author release: `882e5470f4bdbe1c4fb6d2942b0ea70bc143ea62b285f4f199ca16a74e1b8a41`
- scope erratum: `f9881a557c155b1a5ae7260e1be12046cb55555e67aa373a11368f59d8c479c5`
- Original successful object: `7d3572ef937881411713e90bea6f89ff6fca05c962f521d1b37a6a19039853dc`

The source is UTF-8 without BOM and LF only. The original rollout freeze call/result at lines 9813/9817 completed at 14:15:16.018Z, before the first implementation call at line 9832, 14:16:47.949Z. The actual original freeze payload reconstructs the present exact 1570 bytes. All three retained source attempts project to that same freeze, including the complete definition value, every theorem head, imports, namespace, openings and context.

For a,T>0, and arbitrary real y,z, put

`C(a,T,u,n) = exp(-(pi^2*T/(8*a^2))*n^2) * cos(pi*n*u/(2*a))`.

The final identity is the actual positive sine series `mixedSineSeries 0 0 a z T y = (1/(4*a)) * (sumInt C(a,T,z-y) - sumInt C(a,T,z+y+2*a))`. Both full integer sums are genuinely summable. It is an analytic conversion identity, with no killed-kernel, image-series, or Brownian probability identification supplied as a hidden assumption.

The read-only original supplement SHA256 is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`; the entire 4192–4315 context was read. Its sine-expansion invocation is 4284–4291. Lines 4292–4297 concern the reciprocal free density and profile estimate. The present cosine conversion is an auxiliary proof step supporting that invocation, not a literal identity displayed at 4292–4297. This attribution correction is in the additive scope erratum. The original receipt, release, source, freeze, object and gates retain their exact bytes.

## Complete frozen declaration surface

```lean
import Shao.C2.IntervalSineHighTimeProfiles

noncomputable section
namespace Shao.C2.IntervalSineCosineSeries
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalSineTerms Shao.C2.IntervalSineSeries Shao.C2.IntervalSpectralGaussian

def integerCosineTerm (a T u : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-(Real.pi ^ 2 * T / (8 * a ^ 2)) * (n : ℝ) ^ 2) *
    Real.cos (Real.pi * (n : ℝ) * u / (2 * a))

theorem integerCosineTerm_neg (a T u : ℝ) (n : ℤ) :
    integerCosineTerm a T u (-n) = integerCosineTerm a T u n := by

theorem integerCosineTerm_pos_summable (a T u : ℝ) (ha : 0 < a) (hT : 0 < T) :
    Summable (fun n : ℕ => integerCosineTerm a T u ((n : ℤ) + 1)) := by

theorem integerCosineTerm_hasSum (a T u : ℝ) (ha : 0 < a) (hT : 0 < T) :
    HasSum (integerCosineTerm a T u)
      (1 + 2 * (∑' n : ℕ, integerCosineTerm a T u ((n : ℤ) + 1))) := by

theorem integerCosineTerm_summable (a T u : ℝ) (ha : 0 < a) (hT : 0 < T) :
    Summable (integerCosineTerm a T u) := by

theorem sineTerm_cosine_difference (a z T y : ℝ) (n : ℕ) (ha : 0 < a) :
    sineTerm a z T y n = (1 / (2 * a)) *
      (integerCosineTerm a T (z - y) ((n : ℤ) + 1) -
        integerCosineTerm a T (z + y + 2 * a) ((n : ℤ) + 1)) := by

theorem sineSeries_eq_integer_cosine (a z T y : ℝ) (ha : 0 < a) (hT : 0 < T) :
    mixedSineSeries 0 0 a z T y = (1 / (4 * a)) *
      ((∑' n : ℤ, integerCosineTerm a T (z - y) n) -
        (∑' n : ℤ, integerCosineTerm a T (z + y + 2 * a) n)) := by

end Shao.C2.IntervalSineCosineSeries
```

## Proof review, declaration by declaration

### `integerCosineTerm_neg` — CORRECT (source line 13)

The integer cast of -n is the real negative; its square is unchanged. The phase is the negative of the original phase and cos is even. No positivity assumption is needed.

### `integerCosineTerm_pos_summable` — CORRECT (source line 21)

Use the qualified weightedGaussian summability theorem with c=pi^2/8>0, x=T/a^2>0, r=0. The complete real norm is at most the positive exponential because |cos|<=1; cast normalization and nonzero a make its exponent exactly the Gaussian exponent.

### `integerCosineTerm_hasSum` — CORRECT (source line 36)

The positive modes have sum S. zero_add inserts precisely the n=0 mode into the nonnegative integer sequence. Whole-function evenness identifies the strictly negative sequence -(n+1) with the positive one. The disjoint exhaustive natural/negative-natural integer decomposition gives f(0)+S+S. f(0)=1 and the explicit scalar equality yield 1+2S.

### `integerCosineTerm_summable` — CORRECT (source line 60)

This is the genuine existence of a real unconditional integer sum, obtained from the immediately preceding HasSum witness, not an equality of fallback tsum values.

### `sineTerm_cosine_difference` — CORRECT (source line 64)

Write k=n+1 and frequency=k*pi/(2a). The exponential is exp(-frequency^2*T/2). The first phase is -(frequency*(y+a)-frequency*(z+a)); the second is their sum. cos_sub minus cos_add is 2*sin(A)*sin(B). Multiplying by exp/(2a) recovers the literal 1/a-normalized sineTerm. a>0 pays every denominator; T,y,z are otherwise unrestricted.

### `sineSeries_eq_integer_cosine` — CORRECT (source line 83)

The two positive-mode functions are genuinely summable. HasSum.sub then mul_left supplies their scaled difference sum. Unfolding mixedSineTerm at (0,0), with iteratedDeriv_zero twice, gives the term identity on the complete natural-index function. Both full integer sums equal 1+2 times their positive sums; their zero modes cancel. Exact scalar algebra yields the coefficient 1/(4a).

No convergence hypothesis is assumed in place of proof: Gaussian decay pays the positive series before any sum arithmetic, the integer decomposition pays the entire integer series, and the difference series is built using `HasSum.sub` and `mul_left`. The final `tsum_eq` steps therefore cannot exploit the default value of an unsummable sum. In particular the two integer zero modes contribute 1−1=0, and the positive/negative duplication contributes exactly the factor two responsible for 1/(4a). The reflected cosine phase retains the full `z+y+2a` shift; losing that shift would lose the wall/parity information.

The pointwise evenness theorem quantifies over arbitrary a,T,u and n. Its square/even-cosine proof does not require positivity. The sine-term equality requires only a>0; its exponent algebra works for any real T. The infinite identities require a>0,T>0. All y,z remain arbitrary real endpoints, so this analytic auxiliary has not silently restricted its quantifiers to the interior or used a boundary extension convention.

## Actual owner coverage

The audit iterates all `env.constants.toList`, resolves `env.getModuleIdxFor? name`, and selects the exact defining module, including private/generated constants and any alternate namespace. No namespace-prefix filter is used. Independently matching the exported name/kind map gives 17 owners: 16 theorem constants and one definition. Six are the public source theorems. All 17 names are covered below.

- `Shao.C2.IntervalSineCosineSeries.integerCosineTerm_neg` (theorem): CORRECT. The integer cast of -n is the real negative; its square is unchanged. The phase is the negative of the original phase and cos is even. No positivity assumption is needed. Complete type block `f9699ff1d2b4e77673d17693b85cbf1407b8b89768bcc8235ff448d75cc8691f`.
- `Shao.C2.IntervalSineCosineSeries.sineTerm_cosine_difference._simp_1_1` (theorem): CORRECT. Complete universe-polymorphic Zero/OfNat(2)/NeZero type: the proposition 2=0 is equal to False. Complete type block `18fd298c3aabef3c87326cc76e8a4c1a728c8113aae00d7d15860eec52bd1502`.
- `Shao.C2.IntervalSineCosineSeries.sineTerm_cosine_difference._simp_1_3` (theorem): CORRECT. Complete universe-polymorphic Zero/OfNat(4)/NeZero type: the proposition 4=0 is equal to False. Complete type block `d48ef17ef4b88fd1f2fd2204e0484ba43ff15d7d775d54109cd1ded069e29175`.
- `Shao.C2.IntervalSineCosineSeries.sineTerm_cosine_difference._simp_1_4` (theorem): CORRECT. Complete Mul/Zero/NoZeroDivisors type with explicit nonzero a and b: a*b=0 is equal to False. Complete type block `f3828c43ca02ec149309a8b93e3dfeac3111a5ef7177138e4a29d18e3b71e553`.
- `Shao.C2.IntervalSineCosineSeries.sineSeries_eq_integer_cosine` (theorem): CORRECT. The two positive-mode functions are genuinely summable. HasSum.sub then mul_left supplies their scaled difference sum. Unfolding mixedSineTerm at (0,0), with iteratedDeriv_zero twice, gives the term identity on the complete natural-index function. Both full integer sums equal 1+2 times their positive sums; their zero modes cancel. Exact scalar algebra yields the coefficient 1/(4a). Complete type block `5a6006d7ffc0212cadfa8ea67cc9bc97182fb8bdcca77af9d288be179071b7eb`.
- `Shao.C2.IntervalSineCosineSeries.sineTerm_cosine_difference._simp_1_6` (theorem): CORRECT. Complete GroupWithZero type with integer n and nonzero a: a^n=0 is equal to False; the full integer-power/zero instance context checked. Complete type block `6b7e9739d3123d8103d9429b24b877057c7a00657efa03e1d1f455e3a5a984c9`.
- `Shao.C2.IntervalSineCosineSeries.integerCosineTerm_hasSum` (theorem): CORRECT. The positive modes have sum S. zero_add inserts precisely the n=0 mode into the nonnegative integer sequence. Whole-function evenness identifies the strictly negative sequence -(n+1) with the positive one. The disjoint exhaustive natural/negative-natural integer decomposition gives f(0)+S+S. f(0)=1 and the explicit scalar equality yield 1+2S. Complete type block `34b350e2bf21c96763a502c50a636c050f1adbb02cc6cd278ce42b4ac9bdd314`.
- `Shao.C2.IntervalSineCosineSeries.integerCosineTerm` (definition): CORRECT. Complete Real^3 -> Int -> Real type and complete 2221-byte elaborated value checked: exact real Gaussian exponential multiplied by the stated real cosine, with integer cast, ordinary natural square, and exact 8a^2 and 2a denominators. Complete type block `71f784403adf7e9cf597ff7bf2327d31c726556a21b4d5dfded278d50efcfe6e`.
- `Shao.C2.IntervalSineCosineSeries.sineTerm_cosine_difference` (theorem): CORRECT. Write k=n+1 and frequency=k*pi/(2a). The exponential is exp(-frequency^2*T/2). The first phase is -(frequency*(y+a)-frequency*(z+a)); the second is their sum. cos_sub minus cos_add is 2*sin(A)*sin(B). Multiplying by exp/(2a) recovers the literal 1/a-normalized sineTerm. a>0 pays every denominator; T,y,z are otherwise unrestricted. Complete type block `5cabd3ed4084af4a4ae97388d27daf80dbe4adb9611273a64bb7f43c070891ac`.
- `Shao.C2.IntervalSineCosineSeries.sineTerm_cosine_difference._simp_1_7` (theorem): CORRECT. Complete AddMonoidWithOne/CharZero type with natural n: the cast n+1=0 proposition is equal to False; inherited cast/add/zero instances checked. Complete type block `54a394edeb113b0cd605c911cc98e096dcbe1e51c62e9e5a693dd8eee688d5b9`.
- `Shao.C2.IntervalSineCosineSeries.sineTerm_cosine_difference._simp_1_2` (theorem): CORRECT. Complete universe-polymorphic Zero/OfNat(3)/NeZero type: the proposition 3=0 is equal to False. Complete type block `b45f3886c63bd58b081c399d78fbeed88218997d2258a81378e40bd4b23009a6`.
- `Shao.C2.IntervalSineCosineSeries.sineTerm_cosine_difference._simp_1_5` (theorem): CORRECT. Complete MonoidWithZero/IsReduced type with natural n and nonzero a: a^n=0 is equal to False; all inherited Zero/Pow instances checked. Complete type block `fd933799f34d4479ea6b574a8adae4a1bca0c84f8f05d1a371d8dd0d93ec6706`.
- `Shao.C2.IntervalSineCosineSeries.integerCosineTerm._proof_2` (theorem): CORRECT. Complete generated Nat.AtLeastTwo (1+1) proof type: the literal two used in the cosine denominator. Complete type block `06b0c84fd723adcb784104e76daff778b3c8f13d0f552848074b326aa5700839`.
- `Shao.C2.IntervalSineCosineSeries.integerCosineTerm_pos_summable` (theorem): CORRECT. Use the qualified weightedGaussian summability theorem with c=pi^2/8>0, x=T/a^2>0, r=0. The complete real norm is at most the positive exponential because |cos|<=1; cast normalization and nonzero a make its exponent exactly the Gaussian exponent. Complete type block `eb987e668a854bdf5ee2055bc0d5eed6a05aa01fb4a955f9f765f80aa8a0987b`.
- `Shao.C2.IntervalSineCosineSeries.integerCosineTerm_summable` (theorem): CORRECT. This is the genuine existence of a real unconditional integer sum, obtained from the immediately preceding HasSum witness, not an equality of fallback tsum values. Complete type block `1a4c492ee4b9edb0cbeaf0f9a02802bc5387f223231d40fd2302c96f515ad022`.
- `Shao.C2.IntervalSineCosineSeries.integerCosineTerm.eq_1` (theorem): CORRECT. Complete generated defining equation, all four binders and Real instances checked against the full defining value. This equation introduces no additional hypothesis or interpretation. Complete type block `b83ed80f8ef1f0f291e9485ab1203f2f71fe3ede4fcac5225a3df762284bbdb1`.
- `Shao.C2.IntervalSineCosineSeries.integerCosineTerm._proof_1` (theorem): CORRECT. Complete generated Nat.AtLeastTwo (7+1) proof type: the literal eight used in the denominator. Complete type block `c0c0ee4628ec8548f48b01afbab2fbef198138128dcc77eb6b59f7223dfeeb53`.

The actual complete type file has 17431 UTF-8 bytes, SHA256 `a201b9a6ac2830b8d994dc4c625613aca1097350ab5c08cb9aad37de5242063f`. It was directly read in contiguous first-140-line and remaining-line chunks. The actual complete definition-value file has 2221 UTF-8 bytes, SHA256 `9123edddedaf6c319a4487f42892a876316acc5ee6f51099d92a4ba67489b205`, read directly in full. The full value is precisely the real exponential times real cosine shown in the frozen definition; all inherited instances, casts, powers and denominators were checked. No dictionary, structural summary or omitted binder/let/instance/value was used. Tactic-generated theorem proof-term expansion is unnecessary: their full actual types and recursive axioms are covered, and the complete production proofs generating them were read.

## Imported interfaces and established evidence reuse

Qualified independent complete evidence for units 77–86 is reused through the scalar, sine-term/series, reciprocal, and normalized-sine final-review reports, without repeating their old complete proofs. Current remote source bytes and installed object bytes for all ten modules 77–86 equal their qualified bindings. The current immediate import `IntervalSineHighTimeProfiles` has source `01107daeec09658fe0fff3de19f16cac388937385bf58b8a8c06d14c80cd15f5` and object `8da80010a32e35a336f2ca0e6c934c1cf0de3bbb77994b25300baa0e97ffdc50`.

The exact consumed actual complete types/values and source interfaces were read for `weightedGaussian`, `weightedGaussian_summable`, `frequency`, `sineTerm`, `mixedSineTerm`, and `mixedSineSeries`, including the imports/openings of their source modules. The Gaussian interface orders its arguments `(c,x,r)` and its value is `(n+1)^r*exp(-c*(n+1)^2*x)`; the call here uses c=pi²/8, x=T/a² and r=0. The sine term is literally `(1/a)*exp(-frequency²*T/2)*sin(frequency*(y+a))*sin(frequency*(z+a))`. `mixedSineTerm` is time iteration outside spatial iteration of that actual sine term; at j=l=0 `iteratedDeriv_zero` removes both operations. `mixedSineSeries` is its unconditional natural-index `tsum`.

Pinned standard full relevant declaration/proof and ambient context reads cover `HasSum.zero_add`, `HasSum.of_nat_of_neg_add_one`, `Summable.of_norm_bounded`, `HasSum.sub`, `HasSum.mul_left`, `Summable.hasSum`, `HasSum.summable`, `HasSum.tsum_eq`, `iteratedDeriv_zero`, and the real cosine addition/subtraction/evenness/bound identities. The natural/integer decomposition explicitly uses the complementary ranges of Nat.cast and Int.negSucc: zero is included in the former and excluded from the latter, so no mode is omitted or counted twice. Real supplies completeness, separation, the normed additive group and topological-ring conditions. Both arguments to subtraction carry their own sum witness. Seven relevant standard source files were compared byte-for-byte to the pinned mathlib Git content; all agree.

## Exact-source server gates and retained failures

The pinned environment is Lean `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, shared-v34 package view. Read-only observation saw branch `author/c12-interval-reciprocal-v71`, HEAD `c21c0b4b223f4bcb5aa9ceb0ba164ec580b332b7`. Original commands activate the project, then change to the C12 worktree, then take `c12-heavy.lock` for the actual check, with CPU14–17, native -M8192 and -j4.

- Attempt001: actual kernel exit 1; full preserved source and complete log read. The attempted HasSum congruence selected a finite-set binder, and the final untyped RHS function binder inferred Int instead of Nat.
- Attempt002: actual kernel exit 1; full preserved source and complete log read. The corrected binder/function equality was sound, but unrestricted ring conversion rewrote the summand while the scalar name S stayed opaque.
- Attempt003: actual kernel exit 0; complete final source and complete retained log read. It uses an explicit scalar equality with S left opaque. Original call/result are rollout lines 9885/9888, completed 14:21:06.231Z.
- Whole-owner audit: actual exit 0; original call/result are 9902/9905, completed 14:21:33.036Z. All source/object/audit/type/value/freeze/log/receipt hashes match the original receipt.

The complete owned-audit log is exactly the reviewed 17 full-type blocks, one full-value block, and a 213-byte residual containing the known package-dirty warning and the owner-count summary. There is no unreviewed remainder. The kernel success log has only the known package warning and tactic-linter warnings; no Lean error. Failure evidence remains on the server. No raw server logs or binary objects were copied into this review directory.

The audit uses recursive `Lean.collectAxioms` for every actual owner. The pinned complete `CollectAxioms.lean` implementation was read: it traverses checked constant types/values, recursively uses imported transitive entries, and exposes private bodies while collecting. All 17 results are contained in the whitelist `propext`, `Classical.choice`, `Quot.sound`; no new axiom or forbidden production token (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`) occurs. The complete audit source/report were read. No new Lean, audit, build, cache or Git mutation was performed by this reviewer.

## Decision and release boundary

There is no critical gap or uncovered scope within the frozen unit 88 targets. Correctness and complete proof review are accepted for this exact source/object/receipt. This is a standard analytic auxiliary, with no research novelty claim. It does not certify unit 87, the Poisson/image identity, killed/Brownian identification, the original interval derivative/PDE/Taylor completion, or any original root closure. C1/C2/OQ3/OQ4/OQ56 remain OPEN; OQ3 remains user-paused. p54 repairs and external attribution remain unchanged.

The prescribed reviewer configuration is gpt-6.1-sol/xhigh. Runtime model/effort telemetry and separate input/cached-input/output/reasoning-subset token telemetry were unavailable and are recorded as null, with no inferred subscription allocation. The actual runtime ACK was sent at review start. Reviewer writes are confined to this review directory; no child was created. The release record states zero heavy/in-flight work and releases this bounded review responsibility.
