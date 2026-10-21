# Independent review: balanced block and canonical edges

STATUS: CORRECT / LEAN_FULLY_CHECKED for the exact two modules and frozen contracts below. These are source prerequisites; this receipt does not close p52, p53, OQ6 or RS2. Each freeze was independently source-translated before implementation and each completed proof was reviewed by a never-author reviewer.

| Unit | Module | Source SHA256 | Public declarations |
|---|---|---|---|
|33|Shao/OQ5/P45/BalancedBlock.lean|5aa37b415a44f18294bb8b9eec57685d0277a27747249bbe1d72279786c8e125|3 definitions+6 theorems|
|34|Shao/OQ5/P50/CanonicalEdges.lean|f81b3297213af8b8a6714e9c413d277e6aa5f023781f9619f7265925d1c79c6c|0 definitions+5 theorems|

Together:11 new public theorems and14 new public declarations. All14 public transitive axiom queries are confined to {propext,Classical.choice,Quot.sound}. All frozen body/type comparisons pass. No source assumption or public declaration was added or changed. All complete implementations and private helpers were freshly elaborated from exact source bytes by the independent audits.

## Unit33 finite positive block

Independent reviewer oq56_verify33 found no source/proof/boundary gap. It verifies the exact global-negation bridges to immutable p35 finite formulas before use; actual once-counted U, erased rows and original centered jackknife; target balance/squares/tuning; target-only A; all background terms; real subtraction and n≥3; and the t=0/empty/odd-cardinality deterministic boundary. It makes no probability, strict-positive R, full-kernel PSD or operator-rank claim.

Actual target exit0,3.172s,empty stdout/stderr. Exact-source-prefix clean audit exit0,3.429s, no diagnostics:18 loaded-definition body equalities by rfl,6 full frozen types and5 loaded dependency types,29 transitive axiom entries (9 newpublic+20 dependencies), all whitelist-only. The audit source begins with all10,316 target bytes. An earlier appendix version had only unused-proof-binder warnings; the clean appendix changes only its linter setting and retains the exact same implementation prefix. No predecessor proof module was redundantly rebuilt.

The four-file project closure is the target plus these immutable accepted sources:

- Shao/OQ6/FiniteRows.lean: bb4dc865f5ab96ce57814f0721fbd31a2885d6fce7a9facd150941c4c2f91930.
- Shao/OQ5/P35/TargetCancellation.lean: b5b5f4b1bc5a3f0815253063a61fec83c0a9d677122b2db10535f4e2f933549c.
- Shao/OQ5/P35/RowIdentity.lean:73bb0809bc6d323b31775327e468677d6320b38f8fe87363936860164f17f975.

All four hashes remain anchored; full nested-comment/string-aware prohibited-code scan is clean. Raw evidence work/oq56/fresh-review33/: final-clean.json SHAf3859c03b30cb40b6cc3022cae7d4740af411c5fd9dac7f260d5e343b1b968ac; ExactPrefixClean.lean SHA9816995d50883599cb821f61013273a0fc6b7ded0481e4c51a3f1b37f6bfe6c8; exact-prefix-clean.json SHA82d32ba455d681eeecabee823138aacce17266f41954e17cd67cd39a8fc27a02; source-manifest.json SHAd32f7433ee647070fcf8c02eea0cd8b76d4546e0258df048bab3e5d118de42f8. Full lane report drafts/oq56/unit33/proof-review.md SHA234470a83e00bea3f7107201e6c84adcd254fcbe0e0d3e99ab17a33b42889a69.

## Unit34 general canonical kernel

Independent reviewer oq56_verify34 verifies all five exact polymorphic types, actual marginal/pair/triple law derivations from hX/hIndep/IdentDistrib, product-law L2 pullback, real square marginal, genuine L1/Fubini zero edge mean without global Measurable r, product L1 from two L2 edges, and the shared-first-vertex zero integral. It explicitly checks the a.e. integrable right sections, actual canonical condition on the same ν, integrable triple Fubini, and integral_map rather than an embedding-only projection identity. No symmetry, fourth moment, every-row assumption, independence of adjacent edges, Fintype, free variance parameter or desired-moment envelope is used.

Actual target exit0,4.102s,empty stdout/stderr. Exact-source-prefix audit exit0,4.216s: all five full types independently restated and matched;24 whitelist-only transitive axiom entries (5public+3private lawhelpers+16 official dependencies). Its first8,062 bytes are the entire actual target source, importing no target olean. The review appendix retains33 harmless unused-binder warnings in its independently restated examples; the actual target and source prefix have no diagnostics. No accepted target was rerun to remove appendix warnings.

The project closure is the singleton target: all five direct imports are pinned official Mathlib modules. The complete target declaration inventory is5 public+3 private theorems, no definitions. Comment/string-aware prohibited-code scan is clean, UTF8/LF/noBOM, and source hashes unchanged after both checks. Actual metadata verifies the compiler, manifest, package source Git HEAD and unchanged pinned Mathlib sources.

Raw evidence work/oq56/fresh-review34/: final.json SHAd3bd6a4d3c73a41bae66ea7ce88de927e32f3ee9170bd13c0372044dfd519220; target.json SHAd41df2bda0c3601ad07ffed77e56029258846b5e273b57d094ab5a6814815748; ExactSourceAudit.lean SHAa0ba079826c8369d7dbf17b5fe5d9924bb28134ba0b223c3cd8df133ba2acd16; prefix.json SHAd28afb062771190612dd251e7bf5af18ab0e55b91e0ef879f3ce29798ee55f80; frozen-type-comparison.json SHA34f4e90a8ec7d863aa7c260fb79198b2c0c796f488ba0ff673d479ad532fbec2. Full lane report drafts/oq56/unit34/proof-review.md SHA86dde00dcef0f4521954eca6145312bd79261923e4b5ff3d6094f0ba003aa90a.

## Pins, provenance and integration

Lean4.36.0-rc1 commitc9afcddf514a6772bd4d649f7cfc04eff0b9f15e; Lake5.0.0-src+c9afcdd; manifest and actual Mathlib checkout807d3836b165983210ee2ecf3cd28f239436949c. Every Lean invocation ran only on the designated server after activation then cd to lead-oq56, with affinity0,1,2,3. No shared cache/source/pin/import/manifest changes were made by this lane.

Unit33 candidate/author oq56_balanced_candidate, source and final never-author reviewer oq56_verify33. Unit34 problem/freeze/author lanelead, read-only API input oq56_canonical_api, source and final never-author reviewer oq56_verify34. Source historical approval labels are not proof premises; no novelty claim is made.

After independent acceptance, the continuation branch was normally fast-forwarded to known integrated main661318d074b04eb8ff8fa4e6b20c92f4f01982ef. Both new hashes and all three immutable Unit33 dependency hashes are unchanged. No accepted proof check was repeated; packaging independently verifies these bytes, exact new declarations and files. Root owns the two module imports,11-name public theorem manifest update,14 public declaration audits, whole-library integrated gate and merge.

Only these finite/general-kernel prerequisites are certified. Full p52/p53/OQ6/RS2 remain OPEN. Original p35 and previous finite-foundation PR33 are separate integrated results with source hashes preserved.
