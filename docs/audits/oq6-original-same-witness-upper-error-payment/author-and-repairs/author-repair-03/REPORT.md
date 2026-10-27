# Unit238 same-author bounded repair03

The complete source004 is supplied for the sole observed native003 failure in the existing proposition `hCm`. Qualification is **false**. The same original independent reviewer must inspect this affected change, and the lead must obtain a new exact-source designated-server native check and same-first-object all-actual TYPE/VALUE/transitive-axiom evidence before final qualification.

## Exact source and single replacement

Input source003: `2d9f90190751d15cd9f53c81681b5f3182843ee65490ac9cc499d935168d72da`, 43455 bytes, 748 LF. Output source004: `c1d52289bd4bb7d971feb933d13fcd3e347020117767572e5c7210913e46e2dd`, 43577 bytes, 750 LF. Both are UTF-8 without BOM and have LF line endings.

At old source line547, replace only:

~~~lean
    rw [borel_pi]
~~~

with:

~~~lean
    have hB : (inferInstance : MeasurableSpace (Fin n → ℝ)) =
        borel (Fin n → ℝ) := BorelSpace.measurable_eq
    rw [← hB]
~~~

This is one contiguous replacement within `have hCm : Measurable[mAug, borel (Fin n → ℝ)] (C 0)`. The subsequent `apply measurable_pi_iff.2`, coordinate binder and exact `hηpacket 0` coordinate measurability proof are byte-identical. The full diff is in EXACT-DIFF.patch. COMPATIBILITY.json binds unchanged prefix/suffix segments of 34002/9435 bytes. Those two segments and the replacement reconstruct source004 exactly.

## Primary API and mathematical effect

The activation-bound pinned-borel-Pi-API-context.json records primary pinned mathlib source Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean, SHA256 5eede22bbb9d69e270ae3123180ab7cfecaf77f6c40aceedd39799b46a3fdb6f, 34545 bytes, at mathlib commit 807d3836b165983210ee2ecf3cd28f239436949c. Its supplied complete relevant context at631–654 gives pi_le_borel_pi and the existing Pi.borelSpace instance. This requires countable index and second-countable coordinate topologies, already available for Fin n and real. Thus the installed instance gives BorelSpace (Fin n → ℝ).

BorelSpace.measurable_eq states that the installed measurable structure equals the Borel structure. The new hB spells out this equality's full type. Rewriting backwards converts only the codomain measurable structure of hCm to its existing Pi structure. The unchanged measurable_pi_iff.2 reduces the same tuple C0 to the same coordinate measurability facts from the full retained original234 packet. The domain mAug and the tuple are unchanged.

At the lead's explicit additional authorization, the accepted curated library/Shao/OQ6/CoordinateBorelFactorization.lean was read for this API bridge only. Its binding is d245e4f1495972f54a1a823ca075afa526a3f82759fd2030141c0badab780c5c, 7334 bytes. Actual observed lines55–56 show the explicit Prop equality via BorelSpace.measurable_eq; lines137–138 give its Fin n → ℝ specialization, and lines145–147 use the backwards rewrite. The precise excerpts are in compatibility. This does not review or replay the accepted proof or its checks. The supplied bounded primary server contexts were read locally; no server call was made and no entire external mathlib file is claimed read.

The new hB has type (inferInstance : MeasurableSpace (Fin n → ℝ)) = borel (Fin n → ℝ) and RHS BorelSpace.measurable_eq. It is Prop-valued. No local instance, ordinary data, witness, new assumption, helper declaration, callback or import is introduced.

## Frozen interface, full context and ordinary data

The frozen preamble, complete original-assumption theorem head and closing are exact bytes. The 2554-byte freeze and 135871-byte inventory remain unchanged. All 131 scoped result RHS entries and 138 approved optional ordinary entries remain unchanged. Nine explicit ordinary lets are byte-identical to source003; all full types/RHS/scopes are recorded in compatibility:

- cg : ℝ, the original qualified233 good-set choice.
- m₀ : MeasurableSpace Ω, Classical.choose hModelExists.
- ξ0 : Fin n → (Fin n → Ω) → ℝ and C : ℕ → (Fin n → Ω × ℝ) → (Fin n → ℝ), exact frozen mirrors.
- G1,G2 : (Fin n → ℝ) → ℝ, the frozen two choices from hFactor0.
- t : (Fin n → Ω) → (Fin n → Ω × ℝ), idΩ : Ω → Ω and idSample : (Fin n → Ω) → (Fin n → Ω), unchanged literal maps.

The 39 dependent introductions, 48 optional result mirrors and six existing local instances are unchanged. The model is still selected once, only from the original234 conjunction, with its full original universal packet retained. The fixed original-law cg choice precedes model/envelope/window choices. The same actual epsilon and Y, literal eta, code map, k0 factors, original/reduced/augmented spaces, measures and laws remain.

The deterministic section retains only its scalar-measurability role; Hsource, Ssafe, Jsafe and exact ν→P₀→P transport remain unchanged. Qualified232 is applied to the same literal family; E/E2/Z, quantifiers, limits, event contracts and numeric payment remain unchanged. All three prior source003 proposition bridges remain byte-identical. Source assumptions, p54 repairs, attribution, same witness and same eta have not changed.

## Failed native evidence and pending gates

Native003 ended naturally with actual RC1 in 59.73149485886097 seconds and produced no object. Its supplied complete bounded diagnostics show one error at547:8, error(lean.unknownIdentifier): Unknown identifier borel_pi, and six existing local-instance style warnings. Those warnings remain outside this bounded repair.

The original narrow counter searched the literal ': error:' and reported zero errors. That exact observation remains preserved. The new coded diagnostic does not match that literal search, and the separate bound corrected-counts file records one error. Neither the old narrow zero count nor the source edit is a proof pass. Native003's RC1/no-object/natural completion and all earlier source/review/failure bytes remain preserved.

Prior full SOURCE and affected01/02 reviews are reused only for exact unchanged scopes. They do not qualify the changed hCm in source004. The same original never-author reviewer must review affected03. A new exact-source native004 and same-first-object all-actual TYPE/VALUE/transitive-axiom evidence remain pending. No statement is made that the rest of source004 passes the kernel. No source-CDF/OQ56/root completion is claimed; unqualified237 was not read or used and 235/236 were not assembled.

## Bindings and operations

All 14 activation inputs were verified before substantive repair; the actual runtime ACK was written first. The additional local API source is bound. Prior exact input maps, mathematical sources, qualified evidence and curated import closure are reused with deterministic SHA256/byte rechecks. Unique-path counts are derived afresh in INPUT-BINDINGS.json. No raw server receipt or stdout was downloaded.

No Lean, server, network, upload, Git/API, child, shared, frozen, other-owner or prior-version write was performed. Requested model/effort remain gpt-6.1-sol/xhigh. Actual backend/model/effort and input/cached-input/output/reasoning-subset counters are unexposed and recorded null. The manifest binds every payload including the final zero release. That release is the final artifact write; further writes require a new activation.
