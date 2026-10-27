# Unit221 minimal proof representation repair plan

Status: PLAN ONLY. No implementation or Lean source is written by this repair-plan role. Parent review/freeze and an explicit same-author implementation activation are required before applying these hunks.

The exact405LF source was independently CORRECT_SOURCE_ONLY_MACHINE_PENDING. Its first complete native check naturally ended RC1 with2 errors,2 warnings and no object; allOwnedEnded/preservationEqual were true and no timeout occurred. The failed receipt remains immutable: ac07a179cd5886237f592268f47cc290d118e2ba8179f7a1f6696c5ca0cfa114. This plan does not reinterpret that failure as a mathematical counterexample or a check pass.

The observed errors are rewrite-matching failures, not missing mathematical interfaces. At old line231 the producer law has the expanded reduced finite pi measure on its left, while the target uses local P0. At old line302 the first g/r rewrites succeed, but expanded producer hrho does not match the named rho0 let in the remaining observable packet. The plan changes only the representation of already available local Prop hypotheses.

Four insertions, seven source lines in total, normalize those hypotheses with change ... at existingProp. No new proof helper name, mathematical assumption, instance, lambda, predicate, witness or non-Prop value is introduced. There are only TWO observed errors; the full-sample and retained law insertions below address the same concrete alias/matcher pattern at later uses in this same source, rather than claiming additional observed failures.

## hrho — original line 210

Existing219 hrho is the expanded sqrt-integral equality. Retype it to exactly the frozen local rho0/rho aliases before either rewrite use; kernel definitional equality supplies the conversion.

Old exact text:

```lean
  have hreq : r₀ = r := funext (fun o => funext (hrpoint o))
```

Proposed exact text:

```lean
  have hreq : r₀ = r := funext (fun o => funext (hrpoint o))
  change rho₀ = rho at hrho
```

## finite.hPmap — original line 222

Existing219 finite identity has an expanded pi lhs while the goal contains P0. Retype the same equality with exact frozen P/P0,mJ/mJ0 aliases so rewrite matches the actual local lhs.

Old exact text:

```lean
        hPprob, hPmap, _⟩
```

Proposed exact text:

```lean
        hPprob, hPmap, _⟩
    change P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P at hPmap
```

## sample.hPmap — original line 244

The same expanded-pi/named-local alias pattern occurs at the full-sample identity reused in three later law proofs. Normalize it once in its own scope.

Old exact text:

```lean
        _, hPmap, _⟩
```

Proposed exact text:

```lean
        _, hPmap, _⟩
    change P₀ =
      @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P at hPmap
```

## retained.hPRetMap — original line 388

The retained-product E law uses the identical expanded-pi/named-PRet0 matcher pattern. Normalize that existing equality once, with explicit original/reduced spaces.

Old exact text:

```lean
          _, hPRetMap, _⟩
```

Proposed exact text:

```lean
          _, hPRetMap, _⟩
      change PRet₀ =
        @Measure.map ({j : Fin n // j ≠ i} → Ω)
          ({j : Fin n // j ≠ i} → Ω) mRet mRet₀ id PRet at hPRetMap
```

## Why the conversions preserve the proof

All four changes are definitional re-presentations of existing equalities. rho0 is literally Real.sqrt v0 and v0 is the same reduced residual-square integral in219; rho is the same original sqrt integral. Thus change rho0=rho at hrho checks the existing proof against an exactly definitionally equal type. The original base-result assembly already accepted hrho at this named equality before execution reached the failing rewrite. Retyping once also covers its later use in the fixed-zero E factor equation, without changing E or its captures.

For arbitrary J, the frozen definitions are mJ=pi of mOmega, mJ0=pi of m0, P=pi of original mu and P0=pi of literal mu.trim hm0. Therefore the expanded219 law and P0=@Measure.map ... mJ mJ0 id P are definitionally equal propositions. The old generic conjunction had already accepted hPmap at precisely this named-law target; rewrite failed only when its expanded left side was used as a syntactic pattern. change preserves its proof and makes that pattern the actual local P0. The Fin n and retained-subtype conversions are exactly the same definition unfolding, with no altered index, Fintype, measure or map.

After normalization, the existing rw[hPmap,Measure.map_map ...] / rw[hPRetMap,Measure.map_map ...] bodies remain unchanged. The same measurable identity maps and the same observable measurability hypotheses still justify composition. No real scalar law is promoted to a vector law. All original/reduced map spaces remain explicit and unchanged. The changes use the core definitional-conversion tactic only; no speculative API query or additional producer proof is needed. These are formal justifications, not an executed elaboration/kernel pass.

## Exact proposed target and data boundary

Applying only exact-hunks.json replacements IN MEMORY gives 21808 bytes / 412 LF, SHA256 `8691f69ca9ab84649f92b20385c415a2129250cc8f64375d6296e2d59a381627`. It has no BOM or CR. No target .lean file has been materialized.

The frozen declaration head remains161LF with SHA256 `3c86fd2ed057e8c32add0f38941dae3bcc350b5abfb92481e4b59ca4c3009025`. Exact preamble/head/closing,45 ordinary header data values and all their types/captures, one header measurable-space instance, assumptions and all existential witnesses remain byte-for-byte unchanged. All existing body let/letI texts are unchanged. Both letI warnings at original lines202/208 are retained; no linter option or warning-suppression change is proposed.

DATA-INVENTORY.json records explicit empty lists for all new/changed non-Prop data, helpers, instances, lambdas/binders, predicates, Prop-valued DATA families, assumptions, observation selectors and existential witnesses. It separately lists the four existing Prop types being re-presented and their existing capture environments. The only source insertions are their typed change statements.

The same original h/mu/g/r/v/rho, total Bochner rows and row-integrability iff, all-p MemLp iff and AE canonicality remain. The common countably generated m0, literal trim mu0, arbitrary finite J including empty types, original-n coefficients, signed deleted triple, physical s=0/clipped V=0 guards and full-sample cap/deletedTest remain exactly as frozen. E still comes only from qualified220 at real z=0 with the same n/C0/rho; actual-z measurability remains separate.

## Evidence and next boundary

All producer218/219/220 qualifications/public types and original source context are reused from the same exact frozen bindings; no old producer, leaf AX or full old-proof review is repeated. The old source, independent review, failed native receipt and diagnostics are immutable. Same independent affected review should cover the four Prop conversions and their joins: generic B law; original rho equality/rewrite and zero-E factor; Tclip/Tactual/full signed-triple laws; retained E law. The repaired complete source still needs its authorized new-source server check and, if successful, same-original-object/all-owned evidence.

The independent source verdict also preserves nonblocking prior author metadata errata: first header/proof anchor confusion and two omitted bullet-have inventory names. Future repaired source maps should derive proof-scoped positions and include bullet have declarations, preserving lexical fun/funext separation and case-sensitive hD/hd. Those are metadata corrections only, not extra source hunks or new mathematics; sealed old maps remain unchanged.

No CDF/root/fee-limit, atom/reflection or zero-event-payment closure is asserted. p51 candidate status, p54 repairs, external Shao–Zhou attribution and the OQ3 user pause remain. No Lean/server/network/Git/API/upload/publication/child/Goal/schedule action has occurred. Same requested gpt-6.1-sol/xhigh; actual model/effort and separated usage telemetry remain unexposed/null.
