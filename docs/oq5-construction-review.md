# Actual p35 construction and moments: independent verification

Status: units06–11 CORRECT and LEAN_FULLY_CHECKED at the immutable hashes below. The Construction aggregate also compiles. All full OQ5/OQ6 root conclusions remain OPEN.

Pinned server: Lean 4.36.0-rc1 (c9afcddf514a6772bd4d649f7cfc04eff0b9f15e), Mathlib 807d3836b165983210ee2ecf3cd28f239436949c. Every check sourced activate.sh before changing to the assigned lead-oq56 worktree. No local Lean or lane cache writes. Root provisioned the InfinitePi package closure. This branch was fast-forwarded to integrated main 7a6ba6438136630ac0ca46b1fbda0d6eaa773827 before final aggregate checking; shared imports/manifests were preserved.

| Module under Shao/OQ5/P35 | Accepted SHA256 | Public declaration audit |
| --- | --- | --- |
| InfiniteSample.lean | cdaa18c8361c59586e04323b523d85b116a830827f84f463bd25d76ebb40987c | 7: 2 defs, 1 instance, 4 theorems |
| PopulationKernel.lean | 6709d96689f6a0ee544d1fe32de12c0b8baf69ae1d09cab1189fc6d1f358bba4 | 11: 3 defs, 8 theorems |
| NoiseMoments.lean | a9d0e65b0c090528a7985edab8695238f565047989bd5a5fe0f87b434338e76f | 5 theorems |
| RealMoments.lean | b254f73230074702afec88c535666f56d1624126f844c035ee670aa2c52dcd62 | 11 theorems |
| KernelMoments.lean | 34c9efb21d34065396aab955464552c42b6ba371ec0a134a8d5fdaad1a4046a6 | 15: 4 defs, 11 theorems |
| ProjectionMoments.lean | 68545c519a8ffe968976d3ac4976ce9b4fa7e152120d48a59908717c0c623426 | 6 theorems |
| Construction.lean (imports only) | 9d327d4f7564b13cc6456dc27dc821c04373f63c87550e3e2fd933ba9ea57bbd | No new declarations |

Every component's author and an independent fresh reviewer ran actual targeted `lake env lean Shao/OQ5/P35/<module>.lean` checks on the designated server. All final checks exited 0 without diagnostics. The aggregate also compiled. The reviewer audited each source's public definitions, named instances and theorems using its exact byte prefix followed by #check/#print axioms. All 55 public declarations (45 public theorems) have only propext, Classical.choice and Quot.sound transitively; private proof helpers are included through dependencies. Source scans found no proof placeholders, new axioms or bypass constructs.

The fresh reviewer authored or repaired none of the accepted proofs. They independently matched actual Lean definitions and quantifiers to the frozen interfaces and p35 sections 1–3 at SHA256 F5308D1BCDBE2C54E075626617572BF264E3148DD4393324A22AC9664E4E2DA5. All six verdicts were CORRECT. In particular they checked the single infinite probability space and full mutual independence; the distinct-index pair condition; the raw unscaled global Borel kernel and matrix bridge; genuine interval/noise integrability and first/second moments; noninjective decoder pushforwards; actual h² and fixed-x section integrability; exact Hoeffding centering/canonical residual; two-coordinate second-moment factorization without EZ⁴; actual absolute cubic g integrability and variance≥1/3 from the proven category/noise joint law. Offset/feature independence is never assumed.

Complete independent reports are retained in the shared archive at drafts/oq56/unit06 through unit11, each named proof-review.md. Raw target/audit/manifests remain server-side under work/oq56/fresh-review06 through fresh-review11, with construction-aggregate-check.log for the aggregate. Author logs/receipts are also retained there and in the shared unit directories. Ordinary elaboration/API repairs did not alter any frozen statement or root premise.

Provenance: OQ56 lead owns the frozen statements; isolated gpt-6.1-sol xhigh source translator reviewed them before implementation without author files. Authors are the coefficient/sample author, law/noise/kernel author, and lane lead for population kernel, real-moment transport and projection moments. Final verifier is a fresh gpt-6.1-sol xhigh context separate from all authors. The analytic construction and inherited sparse mechanism retain p35 attribution; no novelty claim is made.

The root coordinator owns global imports, theorem manifest and integrated coverage/audit. Importing Shao.OQ5.P35.Construction exposes these modules and the prior fixed-law foundations. This receipt does not replace root's integrated gate. No L2 rank/eigenspace, domination failure, true Studentizer positivity, conditional probability bound, rare-event lower bound or tail-ratio theorem is claimed complete.

Packaging note: InfiniteSample had one final CR removed. The independent reviewer verified the exact whitespace-only old/new comparison, rebuilt its lane-local target and repeated all seven public declaration axiom checks at the current hash in this table. All passed; its unit06 report retains the mapping and evidence.
