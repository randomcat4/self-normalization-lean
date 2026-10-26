# Unit194 repair01 — same independent reviewer's complete affected SOURCE review

STATUS: CORRECT

AFFECTED_SOURCE_REVIEW_COMPLETE: true

QUALIFIED: false

ACTUAL_OWNED: UNKNOWN

The complete changed generic-ratio proof is mathematically correct. Each of the four edits directly addresses its supplied native01 diagnostic without changing a theorem statement, definition, assumption, anonymous computational value, or mathematical scope. I found no critical gap or additional source repair requirement. The original complete SOURCE review and its seven payloads remain byte-preserved and are reused exactly for the unaffected scope. No final machine acceptance is asserted.

Reviewer is the same fresh independent role `/root/oq56_polylog194_final_review`, separate from the author. This reactivation writes only `drafts/oq56/unit194/final-review-01/repair-01/`. Requested model/effort remain `gpt-6.1-sol` / `xhigh`; actual runtime introspection is `UNKNOWN_TOOL_NOT_EXPOSED`, and separate input/cached-input/output/reasoning-subset counters are unknown/null. All reviewer Lean, server, network, Git/API, upload, cache, heavy, and child operations remain zero.

## Exact version, authorized delta and reused coverage

The new source is `author-01/stage2/repair-01/BoundedPolylogWindow.lean`, SHA256 `1d2ad2ca13be7c987c8e0520c5687dba60669af0db6e0dd01edcbc3105043b7e`, 9803 bytes, 218 LF, strict UTF-8, CR0/BOM0. Its source-byte prefix is decimal105,109,112 (`imp`), not a BOM. The old source remains SHA256 `416a3f8e7f41341a36fc5fea6923308cd09d96a195192f1d4ef7e247d72f520a`. The exact 1633-byte patch is SHA256 `b5576393f2c7c54825d4c980aa86e70e9f2f3d1aa8e6d1b753253da0ef561619`.

I read all61 lines of the complete changed declaration/head/proof, new lines35–95; the complete patch; all four full native01 diagnostics; the author's diagnostic dispositions; the complete body-byte and written-type/capture maps; and the complete newly frozen raw bridge with its chronological scope and instance. No partial review is substituted for these affected proof contexts.

The parent delta freeze, SHA256 `6c43e83a47ca5fb71e7f3577a63d4c8edce8a2e462d63cc0b4e31a52d89a77b3`, predates this repair and narrowly authorizes the notation bridge and ordinary Prop pointwise symmetry transport in declaration3. The base freeze remains SHA256 `fc1612a0ca066c74edea4ec41716583fe635fbc5c103cf03540dabe3a9435278`; no statement or data re-freeze is needed. Parent complete repair intake SHA256 `d7dec59f767cef542ff231b33bb6e1fda1c80f49c4dc8ae10dde96e56d796468` has88 checks. Author release SHA256 `3e210d7b88084f50c6b6548c1e9dd0e5deb44a50b75fb43686ac4e7404e4a620` reports all writer/execution/inflight counts zero.

I independently reconstructed the new source from the old source by exactly the four unique replacements in the patch; the result is byte-exact. Independent declaration-block extraction verifies that all seven heads and three global definition blocks are exact, only declaration3's proof block changes, and all three other complete proof blocks are exact. The context/import/namespace bytes and every other byte are unchanged by this reconstruction. The new source has no forbidden proof token.

All29 baseline `have` names, order and complete written types are byte-exact. The original full29-context analysis, full source-to-original-p44/p51/p54 semantic review, full14937-byte local-data/scope contract, and complete baseline32-primary/146-scope/six-instance review are reused. I did not repeat their mathematical proofs or any accepted Lean/axiom checks. Original source-review manifest SHA256 `3ed2ad66d300676e0cdaa02b320c41a1043ca9bbd4836efe62e9798e732a5c48` and all seven original payload hashes remain exact. Its original release and the actual failed native01 evidence remain historical, immutable evidence.

`INDEPENDENT-AFFECTED-BINDING.json` records these independent comparisons and all exact primary slices. It is static evidence, not a TYPE print, proof execution or acceptance result.

## Known native01 failure and all four dispositions

The supplied exact source-bound diagnostic record SHA256 `1b33d472f34dc527834ce95fea3291366b8a5846c26c6ce41eb76436d6abe874` reports actual native01 KNOWN_ENDED, RC1, four source errors, zero source warnings, no object, all11700 protected full fingerprints preserved, and no owned Lean process remaining. The stderr's repository-local-changes notice is distinct from source warnings. This failure is preserved and is not a proof pass or an uncertain in-flight operation. The subsequent native02 is a fresh check of changed bytes, not a replay of that failed source.

1. **Old line70 → new lines70–73, `hlogpow`.** The old reverse rewrite's pattern used real-power notation `x^a`, while the goal used explicit `Real.rpow`. New line70 first applies only the frozen `Real.rpow_eq_pow` rule to these explicit real-power occurrences. The complete equality proposition remains `((Real.rpow (log n) a)^2) = Real.rpow (log n) (2*a)`. After notation normalization, the reverse `rpow_mul_natCast hlog.le a (2:ℕ)` rewrite has the intended syntactic shape. It converts the outer natural square to a real exponent `a*(2:ℝ)`; `congr 1; ring` identifies that exponent with `2*a`. The natural square remains a natural square. The paid sign `hlog.le` and every numeric exponent/data input are unchanged.

2. **Old line77 → new lines78–79, first equality in `hthird`.** Adding only `Real.rpow_eq_pow` to the existing `simpa only [Real.rpow_one]` set normalizes both the target and the supplied symmetric `rpow_sub hn0 (1/3) 1` theorem to the same notation. The strict positivity hypothesis `hn0` is unchanged and sufficient. The resulting equality still says `n^(1/3)/n = n^(1/3-1)`; no finite zero denominator is cancelled and no new domain restriction is assumed.

3. **Old line83 → new line84, final equality in `hthird`.** Adding only the same bridge to `simpa only [one_div]` makes explicit `Real.rpow` and the raw `rpow_neg hn0.le (2/3)` result coincide syntactically. The base nonnegativity is the unchanged consequence of `hn0`. Both sides still express `n^(-2/3)=1/n^(2/3)`. The intermediate exponent normalization remains unchanged and correct.

4. **Old line92 → new lines93–95, final limit transport.** The old eventual-equality object did not support `.symm` field notation in the actual elaboration. The new source applies `hscaled.congr'`, then binds a pointwise equality using `filter_upwards [heq] with n hn`, and returns `hn.symm`. This constructs exactly the reverse eventual equality required to transport the scaled convergence to the target convergence. The argument is fully explicit at the Prop level and mathematically valid. The author disposition's prose spelling `hscaled.congr` is shorthand; the actual patch/source contains `hscaled.congr'` and that actual code was reviewed.

These edits repair the concrete expressions that failed. I do not infer native02 success merely from that correspondence.

## Complete changed generic-ratio proof and new Prop callback

The whole declaration35–95 retains the original statement and complete binder order `C,a,t0,hC,ha,ht0`. Lines41–57 still establish the real log-power little-o relation at exponent2/3, restrict it to naturals, take the quotient limit, and scale by the frozen real coefficient `C^2*t0`. The already reviewed primary assumptions and argument orders remain sufficient. No new result is substituted for the logarithmic domination theorem.

Lines58–67 still prove the eventual sign domain `1<n`, its real cast, positivity of the natural cast and positivity of its logarithm. The now normalized equalities in68–84 prove precisely the same two algebraic identities as before. Lines85–92 expand the two frozen definitions and reassociate real products/divisions to identify the requested ratio with

`(C^2*t0) * (Real.rpow (Real.log (n:ℝ)) (2*a) / Real.rpow (n:ℝ) (2/3))`.

Every sign-sensitive identity occurs on the proved eventual domain, and the new bridge itself is unconditional. Lines93–95 finish the limit by the following full ordinary Prop frame:

- The target after `hscaled.congr'` is eventual equality of the scaled function with the original ratio, in that order.
- `n:ℕ` is an arbitrary bound eventual input, not a chosen witness. The hypothesis `hn` has full type
  `(boundedPolylogHeight C a n)^2 * boundedPolylogMomentOrder t0 n / (n:ℝ) = (C^2*t0) * (Real.rpow (Real.log (n:ℝ)) (2*a) / Real.rpow (n:ℝ) (2/3))`.
- `hn.symm` proves exactly the reversed equality. The full eventual target is `∀ᶠ n:ℕ in atTop`, followed by that reversed equality. Data captures are only `C:ℝ,a:ℝ,t0:ℝ`; proof captures are the existing `hscaled` and `heq` with their unchanged complete convergence/eventual-equality types.

The callback does not add a data initializer, choice, selector, local instance or structure value. Its output is an equality proof in Prop. The29 baseline `have` contexts remain genuine Prop contexts and are unchanged; this added pointwise Prop callback introduces no new `have` and cannot support a data choice.

## Complete added primary declaration and scope

The one newly consumed raw declaration is exactly:

```text
@[simp]
theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl
```

It is lines39–40 of pinned `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`, whose full-file hash is `f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd` (50402 bytes). I compared the raw declaration, all eight supplied chronological prefix rows and the line37 global instance with exact slices from the unchanged pinned packet. All10 rows and the full-file byte hash match. The prefix is module/imports, exposed public section, noncomputable section, `open Real Finset Set`, `namespace Real`, and the preceding `{x y z:ℝ}` variables. The theorem explicitly binds its own `x y:ℝ`; no `z`, new universe, extra positivity hypothesis or typeclass assumption is silently captured.

The preceding anonymous global instance is exactly `noncomputable instance : Pow ℝ ℝ := ⟨rpow⟩`. Consequently the theorem is a definitional notation equality with proof `rfl`, valid for every real base and exponent. The compiled instance name is not invented. The real exponent of each bridge use is already a frozen expression; the outer natural-square exponent is not converted into a different operation.

The first new use has base `Real.log(n:ℝ)` and exponents `a` and `2*a`, capturing `n,a`. The second use has base `(n:ℝ)` and exponents1/3 and1/3−1, capturing only `n`. The third has base `(n:ℝ)` and exponents−2/3 and2/3, again capturing only `n`. All arguments existed in the frozen equalities. This is not a new computational value or a changed capture/scope. Effective primary evidence is exactly base32 plus this one declaration, total33; the old32 metadata is not rewritten. The prefix rows and instance are contextual evidence already compatible with the baseline chronology, not newly introduced module instances.

## Qualification and continuation boundary

This repair changes no original-source meaning or boundary-case treatment. It leaves the p51 deterministic fixed-polylog/cutoff prerequisite as the only mathematical result. The exact generic assumptions and cutoff positivity assumptions remain unchanged. The same treatment of all naturals,0/1, C=0, a=0 and positive t0 is reused from the complete baseline review. S16 probability concentration, S17 actual geometry and OQ56 root closure remain later obligations; p54 repairs, published SZ6.1 attribution and the non-prerequisite status of124 are preserved. C2/C12/OQ56 remain OPEN and OQ3 remains PAUSED_BY_USER.

Current phase is `ROOT_OQ56_22`, ledger SHA256 `8201fb56f1f87839f558792b0bf5a58b4730d824bda033ea661fb6a96f85ae12`: Root1/C120/OQ561, maximum two project heavy commands, OQ56 CPU52–55/original lock/cap unchanged. This reviewer has heavy0. The preserved initial review's phase21 snapshot remains accurate for its date. Native01 occurred in phase21 before phase22's23:04:37 UTC activation; upcoming native02 belongs to phase22. This phase transition is administrative and changes no proof assumption.

The combined complete SOURCE verdict for the new hash is CORRECT by the original exact reused coverage plus this complete affected review. Final `qualified` stays false and `actualOwned` stays UNKNOWN until the parent supplies native02's actual success and the same original new object's complete module-index all-owner TYPE/FULLVALUE-or-body/level/component/recursive-axiom packet. All actual names, generated auxiliaries and transitive dependencies must be checked there against `propext`, `Classical.choice`, `Quot.sound`. None is fabricated from source text. No new source repair or mathematical gap is identified.
