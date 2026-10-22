# Brownian B2 node S — fresh independent proof and source-semantics review

STATUS: CORRECT

Reviewer: `/root/brownian_s_proof_review`, fresh never-author context. Scope: the complete final proofs, definitions, private helpers and generated-declaration audit of `BrownianSpectralEnvelope.lean` and `BrownianFirstTerm.lean`, together with the precise M/G/B1 interfaces they consume. This reviewer did not author or repair any reviewed implementation, change a statement, run Lean, or read the parallel M/G review reports. The full M/G proofs remain the responsibility of their separately assigned fresh reviewers. This is S acceptance, not the independent root integration gate or a claim that S3, OQ4, C12, or all original roots are closed.

## Frozen source binding and exact statements

The locally recomputed SHA256 of `brownian-b2-frozen-v1.md` is `b1a1c447eb2354f627807f6dafe56e1c3d71184d107aa94152dc5d2b82bf20fb`. Its approved separation of the finite spectral proof into a second module is respected. The reviewed route and interface hashes are respectively `596ba300939b539e470e8d3a48b294d090e0a8a1e26c143abf0ba7b6c7c4ff16` and `d929bd9e124348b8a1705e25079653be33c51472bcd7fe7f40f6f6e1bff9b90b`.

I read the original `C:/game/shao/current/oq4/frozen01.md` (recomputed SHA256 `ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a`) and the S3 consumer freeze (recomputed SHA256 `19f162418e88f7b3ddea57e1c735404f94fd3e50fbd471bfd937eaf93424a71c`), especially its Sections 3–4. The latter requires the actual Brownian weak-event probability, the exact deterministic first term, a positive-side ratio limit equal to one, and derived eventual positivity. It does not permit substituting a free tail function or adding positivity/limit hypotheses.

At `BrownianSpectralEnvelope.lean:12`, the public definition is literally

`firstTerm x = (4 / Real.pi) * Real.exp (-(Real.pi ^ 2 / 8) / x ^ 2)`.

Thus its positive-radius value is exactly `(4/pi) exp(-pi²/(8x²))`, with the required standard Brownian scale. Its total real-function value at zero is irrelevant to the positive-side conclusion. The exact final public statements are:

- `BrownianSpectralEnvelope.lean:69`: for each fixed `0 < x < 1` and each positive additive `η`, the actual finite Rademacher survival probability is eventually within `firstTerm x * (C exp(-pi²/x²)) + η` of `firstTerm x`.
- `BrownianFirstTerm.lean:112`: for every `0 < x < 1`, `|probability B P hB x / firstTerm x - 1| ≤ C exp(-pi²/x²)`.
- `BrownianFirstTerm.lean:143`: the exact positive-side epsilon-delta ratio limit equal to one, with all radii `0 < x < δ` quantified.
- `BrownianFirstTerm.lean:154`: there is a positive punctured interval on which both the actual probability and its ratio to the first term are strictly positive.

Here `C` is the accepted `Shao.OQ4.RademacherSpectralTail.absoluteC`, not a new selected constant. The audit's elaborated signatures confirm that the final three theorems quantify arbitrary `Ω`, `[MeasurableSpace Ω]`, `B : NNReal → Ω → ℝ`, `P : Measure Ω`, `[IsProbabilityMeasure P]`, and `hB : IsBrownianReal B P`. They have no other stochastic, survival, convergence, modulus, density, or no-atom premise. This is the frozen original first-term contract, with the additionally approved quantitative envelope and positivity conclusions.

## Actual-object and imported-interface check

The consumed B1 probability is the accepted measurable version of the actual supremum: `BrownianSup.lean:121–125` defines `U` from the actual countable trace and `probability` as `P.real {ω | U B P hB ω ≤ x}`. Its accepted `U_ae_eq_pathSup`, `U_le_ae_iff_fullStrip`, and `probability_eq_fullStrip` identify it with the continuous-time weak event `∀ t ∈ [0,1], |B t ω| ≤ x`. S imports this definition unchanged; it never redefines the probability through a scalar expression. The B1 source hash is `f7f86bd8db582d9a4e53241f9cfc8384f86ee33765a40c5541a15b6f0c22a718` and its object hash is `8a3072bc84c46e050f77f2dac29b3d2ebff1102bd4623ed38178101f05bea68c`, matching the author receipt and accepted B1 binding.

I inspected the actual remote M/G definitions and consumed theorem heads, also matching the local frozen copies:

- M's `radMeasure` is the genuine finite product of `RademacherCosine.law`; `radSurvival n x` is its real probability of `closedStrip (x sqrt(n))`. `coarseStrip` tests every `j ≤ d`, including both endpoint indices, on the same product path. `rademacher_coarse_comparison` gives `R_(dm)(x) ≤ q_(d,m)(x) ≤ R_(dm)(x+ε) + 6/(d ε⁴)` under precisely `d,m > 0`, `x ≥ 0`, `ε > 0`.
- G's `gridTime d j` is `j/d`, its `brownianGridProbability` is the real measure of the literal finite weak-grid event, and its fixed-grid theorem gives `q_(d,m)(x) → Q_d(x)` for fixed positive `d,x` using the same `B,P,hB`. Its dyadic theorem gives `Q_(2^r)(x) → probability B P hB x` for every real `x`.

M source/object: `abb08df1b17a154ab6a8a8c59fda06eadec6a44009c89d02c8f2aeedbd4acaac` / `a7e40944ff983751d3c2bdead76e6672dbdc27b74ef1f42883d50ac0d38afe73`.

G source/object: `98741686b236686ea72d9d6b9c44dced7b6f1036528942bb7bf69154972bd5e9` / `fa4e0ffe41fe390ff80aa1b9b97c19eae3391f448e992015eb46309ecae31d58`.

These consumed statements are proved imported outputs, not assumptions in S. My review checks their exact binding and use; it does not duplicate their independent full-proof reviews.

I also read the accepted scalar/tail definitions and the precise paired-spectrum identity. `Pair.amplitude` unfolds to `Scalar.a`, and `Pair.rho` to `Scalar.rho`; S proves both adapters. `Scalar.H=m+1`, `lambda=pi²/8`, `C_a=pi/3`, and `C_rho=pi⁴/48`. SCA1 and SCA2 require only `m ≥ 1`. The accepted `closedStrip_probability_normalized` is an identity for the actual product probability on the weak cell `m ≤ h < m+1`, for all natural times. `Pair.epsilon=(-1)^(n+m)` and `Pair.remainder` is the actual finite normalized tail including its zero-mode term. `remainder_uniform` applies under `m ≥ 1` and `(m+1)² ≤ n`; it controls that same remainder by `C exp(-pi² n/(m+1)²)`. No abstract remainder was substituted.

The three accepted spectral source hashes independently match the local curated snapshot and the server: Scalar `12670bd33a813849156b245cad28f5efb783a55919f8a0743fcf3fb9fbff329f`; Pairing `7cc1e142db3c9e6f2c788ca83f213bb2ea1c4d58d2207b30a43ed5fd471d50ea`; Tail `a29cb9e520aa20e644095f9ac776ccd92f747184ac1d8a121992757a5bf16db0`.

## Complete finite spectral reasoning

I read every proof in both S sources, including all private helpers. At Spectral lines 25–67, put `m_n=floor(x sqrt(n))` and `H_n=m_n+1`. The natural-floor inequalities, with `x>0`, give `x sqrt(n) ≤ H_n ≤ x sqrt(n)+1`. After the explicit eventual restriction `n ≥ 1`, division by positive `sqrt(n)` squeezes `H_n/sqrt(n)` to `x`. The lower inequality also gives `H_n → +∞`. Squaring and inversion, with nonzero positive `x`, give `n/H_n² → 1/x²`; multiplication by `H_n^(-2) → 0` then gives `n/H_n⁴ → 0`. The algebra uses `sqrt(n)²=n` only where `n>0`. These assertions do not require monotonicity of the floor sequence beyond the supplied lower bound.

At lines 82–134, `H_n ≥ 2` eventually gives the spectrum's required `m_n ≥ 1`. SCA1 squeezes the amplitude to `4/pi` with error `C_a/H_n²`. Multiplying SCA2 by the nonnegative real cast of `n` bounds the error in `n log(rho(m_n)) + (pi²/8)n/H_n²` by `C_rho n/H_n⁴`, which tends to zero. Hence `n log(rho(m_n)) → -(pi²/8)/x²`. Accepted `rho_pos` justifies `exp(n log rho)=rho^n`, so `D_n=amplitude(m_n) rho(m_n)^n → firstTerm x`.

The squared tangent correction tends to zero because its angle `pi/(4H_n)` tends to zero and tangent is continuous at zero. This does not assert tangent is globally continuous. The accepted parity coefficient has absolute value exactly one, for every parity of `n+m_n`; no subsequence or parity class is discarded.

At lines 143–151, `x<1` is used at its necessary location: `1/x²>1`, so the convergence of `n/H_n²` implies eventually `H_n² ≤ n`. Together with `m_n≥1`, this is exactly the accepted tail theorem's domain. Early zero time, small cells and any center-mode issue are left in the finite prefix rather than silently removed from an all-time identity.

At lines 153–178, the exact weak-cell bounds `floor(x sqrt(n)) ≤ x sqrt(n) < floor(x sqrt(n))+1` instantiate the actual probability identity. Positivity of the normalizer and the triangle inequality give

`|R_n(x)-D_n| ≤ D_n (tan(pi/(4H_n))² + C exp(-pi² n/H_n²))`.

The right side plus `|D_n-firstTerm x|` converges to `firstTerm x * C exp(-pi²/x²)`. For arbitrary positive additive `η`, this proves the exact eventual finite envelope. Crucially, the proof neither claims nor needs convergence of `R_n(x)` itself. Floor cells, weak attainable walls, parity and the accepted normalized remainder all remain the original actual objects.

## Ordered transfer and final limit

Let `g=firstTerm`, `E(x)=C exp(-pi²/x²)`, and `H(x)=g(x)(1+E(x))`. All helpers at FirstTerm lines 11–110 have complete proofs.

At lines 33–47, fix positive integer `d` and positive `x<1`. The proved map `m ↦ d*m` tends to infinity. Restricting to eventual `m≥1` satisfies M's hypotheses; its lower comparison and the finite lower envelope imply `g(x)-g(x)E(x) ≤ Q_d(x)+η` after G's fixed-grid limit. `le_of_forall_pos_le_add` then removes the arbitrary positive `η`. The explicit `include hB` retains the body-used Brownian premise in this private helper.

At lines 50–66, still fix `d`, now also `ε>0` with `x+ε<1`. Apply the finite upper envelope at `x+ε`, M's upper comparison, and G's limit at `x`. Passing `m→∞` and independently removing `η` yields `Q_d(x) ≤ H(x+ε)+6/(d ε⁴)`. Neither step assumes a survival probability limit or a uniform CLT error.

At lines 68–91 set `d=2^r`. Every such `d` is positive, including `r=0`. G's dyadic probability limit passes the lower bound to the actual probability. For the upper bound keep `ε` fixed while `r→∞`; the explicitly proved reciprocal-power limit makes `6/(2^r ε⁴)→0`. Thus `b(x)≤H(x+ε)` for the same actual B1 probability.

At lines 93–110 choose `ε_k=(1-x)/(k+2)`. Each shift is strictly positive, below `1-x`, and tends to zero. Continuity is required only of the explicit scalar function `H` at the fixed positive `x`, where its division by `x²` is legitimate. Passing this last limit gives `b(x)≤H(x)`. No continuity or absence of atoms of the Brownian supremum distribution is used.

The order is therefore: `m→∞` at fixed `d,x,ε`; then dyadic `d→∞` at fixed `x,ε`; then `ε→0` at fixed `x`; only then `x↓0`. No exchange of these limits or division of an uncontrolled CLT error by an exponentially small probability occurs.

At lines 112–128 the two actual bounds imply `|b(x)-g(x)|≤g(x)E(x)`. The separately proved strict positivity of `g(x)` justifies division and gives the exact public ratio envelope. At lines 130–141, positive-side inversion, squaring, multiplication by `pi²>0`, negation and the exponential limit at negative infinity prove `E(x)→0`. At lines 143–152 the right-neighborhood basis supplies a positive `δ`, and `min δ 1` ensures the envelope's `x<1` domain. This proves exactly the frozen epsilon-delta formula for all positive `x` in that interval. At lines 154–163, applying it with tolerance `1/2` gives a positive ratio; positivity of `g` then gives positive actual probability. The requested positivities are conclusions throughout.

## Independently inspected mechanical evidence

No Lean command was rerun in this review. I used the existing `tools/server.py` transport for read-only Python inspection, with every remote command restricted to CPU10–13. All raw logs remained on the server. I independently hashed every file listed in the actual remote `repro_outputs/node-s/author-receipt.json`; all 14 file hashes and byte sizes matched, including the five source modules, the audit source, all three final logs and all five compiled objects. The two local S source copies have the same hashes as their remote counterparts:

| Module | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| BrownianSpectralEnvelope | `97e1a9f13d2b86874b94df93540d3355dcc38dac8dff81ad3a823ded68396fc7` | `223889f3055e37ccf9c6c3f32fdb6486cbca2271553e6b6063a52c17b1fbc241` |
| BrownianFirstTerm | `f4faa8c89016aea74dd16c8ea0dc359213390413d3ab0faff234dd98d0a87c6a` | `a4645242cb1bc0709084e46a308562533053b7a0aa9ba0750478316d7f805ec1` |

The actual project pin is `leanprover/lean4:v4.36.0-rc1`; its manifest fixes mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The existing receipt records native exits zero for `spectral-04-emit`, `firstTerm-04-emit`, and `audit-01`, using `-j4 -M8192 -DautoImplicit=false`, CPU10–13. Both final build logs contain no error or sorry indication. The known mathlib local-changes warning is preserved in the logs; it is not represented here as a mathematical failure or erased. The final strict root integration gate remains separate.

I read the audit implementation and independently parsed the actual multiline records in `audit-01.log` (SHA256 `75daa139723b7224e569fefab45004f190917f9a343fef98fd4fb46d2838d413`, 160192 bytes). There are exactly 1022 unique `DEPENDENCY` records, 36 unique `OWNED` records, and no duplicate names. The latter are exactly the dependency records whose actual environment owner module is one of the two S modules. Counts are 12 Spectral-owned and 24 FirstTerm-owned constants; the recorded split is 33 theorem constants and three definitions. All four public targets and the public definition are present. The audit uses actual owner modules, so it also includes private declarations, generated proof/simp declarations, and lazily generated equation theorems whose displayed namespace is an imported OQ4 namespace. It does not rely on a public-name prefix.

For every one of those 1022 imported Shao constants, the audit calls `Lean.collectAxioms` transitively. The independently parsed union is exactly `{propext, Classical.choice, Quot.sound}`, with no record outside that whitelist. The four public `#print axioms` results agree, and the elaborated `#check` output has exactly the intended assumptions and conclusions. The pass record is `owned=36 theorems=33 public=4 definitions=1 dependencies=1022`. Independent token scans of both actual S sources find no `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` token. No source, object, Git, cache, process, affinity, or limit was mutated by this reviewer; the protected external PID143204/CPU0–9/80GiB workload was untouched.

## Verdict boundary

There is no critical mathematical, quantifier, actual-object, source-to-statement or axiom gap in the frozen S implementation reviewed above. It supplies the actual Brownian first term and derived eventual positivity required by original `oq4/frozen01.md` and the S3 Brownian consumption contract. Acceptance of the assembled Brownian B2 chain still requires the separately assigned M/G proof acceptances and the independent root gate for these exact sources/objects. This report does not certify an exact Brownian survival series, canonical Brownian existence, S3 assembly, the general OQ4 theorem, or full C12 closure. No novelty claim is made.
