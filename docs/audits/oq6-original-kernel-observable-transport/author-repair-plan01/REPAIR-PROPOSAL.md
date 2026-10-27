# Unit 219 same-author repair proposal 01

Status: planning only. No `.lean` file is written by this packet. The parent must freeze the exact revised head, values and proof fragments before implementation. The source to which every proposed patch applies is `OriginalKernelObservableTransport.lean`, SHA256 `2552c6826f608e3bb3b6427530feab30405dac4d8929983066e9783b8a644c35`, 13050 bytes, 299 LF. The exact original preamble and source closing are retained.

The complete proposed head is SHA256 `ba5389f303f918cbb46b15295e09d6c5203fd56e193abf2761a7c67b61777b0f`, 3189 bytes and 63 LF. All 12 exact hunks match their original ranges and occur once at complete-line boundaries. A deterministic application in memory only would produce SHA256 `616d2145fc8be92ac3d9aea92c28ab801e32b447ad62c4123838b45c95f1832f`, 13850 bytes and 319 LF, with proof lines 82–315. That prospective source was not written to disk and has not been checked by Lean. Its hash is a reproducibility target for a future authorized implementation, not a proof artifact.

The proposal has three mathematical/elaboration components and one local style correction. The first component explicitly anchors the four original-law values in both the theorem head and the proof-local recreations. The second anchors the spaces in the pair-map and tuple-measurability API applications. The third supplies a typed first subtraction function in the almost-everywhere residual-canonicality calculation. The proof-local reduced measurable-space binding uses ordinary `let`, as requested by the observed Prop-goal linter warning.

`EXACT-PATCHES.json` is the authoritative proposed text delta. Each row gives the complete old and new text, old line range, required exact occurrence count, reason and API binding. `REVISED-FROZEN-HEAD.txt` supplies the complete proposed public head without a proof. `REVISED-DECLARATION-DATA.json` records the unchanged preamble and closing, the complete revised public head, all 18 typed transparent header values, their captures, and the proposed local instance/Prop changes. A parent repair freeze should bind those exact payloads, rather than interpreting the prose as implementation authority.

The native01 diagnostic map is:

| Old source location | Observed failure | Proposed treatment |
|---|---|---|
| 35 and 82 | Original residual-square product selected the reduced coordinate instance | Explicit original `Measure.prod` arguments in `v`, in head and proof |
| 39 and 86 | Original projection pushforward selected the reduced source instance | Explicit original domain and canonical real Borel target in `projectionLaw`, in head and proof |
| 40 and 87 | Original pair law selected the reduced coordinate instance despite its result annotation | Explicit original `Measure.prod` arguments in `pairLaw`, in head and proof |
| 45 and 92 | Original finite product law selected the reduced coordinate family | Explicit original coordinate family and supplied `Fintype J` in `P`, in head and proof |
| 104 warning | `letI` in a proposition-valued goal | Ordinary proof-local `let` with the same type/value `MeasurableSpace Ω := m₀`; header `letI` retained |
| 170 | `map_prod_map` inferred the reduced source coordinate instance | Explicit original/reduced spaces, original factors, identity functions, and derived original SFinite proof |
| 231 | Rewriting could not match pointwise lambda against application of a function subtraction | Typed `hsub` and direct `calc` use of `integral_sub`; remaining normalization unchanged |
| 263 | `measurable_pi_iff` inferred the reduced tuple space as its source | Explicit original tuple source space and reduced target coordinate family |
| 176, 181, 245, 276 | Expected terms involved invalid original-law captures | Retain these four proof steps; reassess from the next exact-source diagnostics if they persist |

The last row is deliberately not a native-success claim. The invalid captures explain the mismatch between `pairLaw` and original `μ.prod μ`, between `projectionLaw` and original `μ.map g`, and between `P` and the original finite product. Once those definitions are correctly anchored, the unchanged identity compositions and API conclusions have the intended definitional equalities. No rewrite against a generated recovery term is proposed.

The residual calculation remains within the same Fubini-good set. After introducing `o` and `ho : Integrable (h o) μ₀`, the existing `hconst : Integrable (fun _ : Ω => g₀ o) μ₀` and `hgIntegrable : Integrable g₀ μ₀` suffice. The new local proof has type `Integrable (fun y : Ω => h o y - g₀ o) μ₀` and value `ho.sub hconst`. A typed equality then separates the final subtraction by `g₀`. The inner subtraction, probability integral of the constant, and `hgMean = 0` give `g₀ o - g₀ o - 0 = 0`. This changes only the functional expression presented to rewriting.

There are no changes to the assumption binder list, conclusion list, original/reduced functions, measure definitions, universes, public declaration count, imports, options or namespace. There are no new global definitions or helper lemmas. The unchanged `rowIntegrable : Ω → Prop` and `gLp : ℝ≥0∞ → Prop` are captured function data, not additional assumptions. The reduced probability and mapped-coordinate SigmaFinite family remain derived local class proofs.

Only the exact changed head/value and proof delta invalidate the corresponding old source evidence. The parent independent complete review of all 299 LF is preserved as historical coverage of the failed exact source. It does not qualify the proposed source. The affected changes require independent review and an actual exact-source kernel check, followed on success by all-owned actual type/value and transitive-axiom coverage under the standard whitelist `propext`, `Classical.choice`, `Quot.sound`. No failed first-native object or axiom evidence exists to reuse.

The packet's source reading and input hashes are in `INPUT-BINDINGS.json` and `SOURCE-INTERFACE-MAP.md`; semantic limits are in `SEMANTIC-COMPARISON.md`. No source implementation, server command, network request, upload, publication, child task, Goal or schedule is issued by this author in the repair-planning turn. The parent alone performs the narrowly requested API-type inspection. The next authorized step after delivery is a parent exact repair freeze, followed by a separately activated same-author implementation.
