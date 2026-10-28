# Unit244 source002: same independent affected SOURCE review

STATUS: **CORRECT_SOURCE002_AFFECTED_REVIEW_ONLY**.

The two repaired constant-limit calls are source-level correct against the complete pinned global API. The accepted complete SOURCE001 review is reused exactly for all unaffected bytes and mathematical contexts. There is no remaining uncovered affected-source gap. This is not a kernel, actual-owner TYPE/VALUE or transitive-axiom qualification: `qualified=false`, `kernelChecked=false`, `axiomAudited=false`, `kernelPending=true` remain in force.

The reviewed source002 is `C:/game/shao lean/drafts/oq56/unit244/author-repair-01/OriginalSameWitnessEventualTailApplication.lean`, SHA256 `d4682d3bf6658f442c77e55af10e32f28755241f68752c181a9d31c34509a2df`, 214999 bytes /3156 LF. Its full source001 predecessor is `695291df7f178eac964ef420d9bf65a47da3959d99ae6aebf09f70229958a1ec`, the exact source covered by the sealed complete review manifest `713189bab3627d1bba14506f8f6d1b93110f796afec600e6532c5a43fbea8f69` and final release `5158760b0da7a4e4e47540573b9895de7cd694e55cfc9fdcbbef80ef0f182c59`. The same independent never-author role performs this affected-only join. All new writes belong exclusively to `unit244/affected-source-review-01/`; no sealed predecessor artifact is modified.

## Activation and preserved failed attempt

Activation `a9816fd1cb83663d1d923c6fd9f1ea98ab0b3ecc8aa015611bfaef43da68e4cd`, 6006 bytes, binds 21 exact inputs. All 21, the activation itself, all eight repair-author payloads and all eight old SOURCE-review payloads were verified before the actual runtime ACK: 38 binding comparisons including repeated references. The current repair author's release and old reviewer's release were both verified with writer/heavy/inflight/pendingExternal/children/uncertain all zero before that ACK. Subsequently all 22 author activation inputs and the author activation were independently verified as an additional 23 binding comparisons; these later checks are not represented as pre-ACK observations.

The repair-author manifest is `08c730dc80fa1d62ee02aaad1dce22c9c30b5ce051ad66aa16b4eaef73039632`, 9798 bytes. Its release is `9f0d15d98d7dfe07dd03c5e9609da7104cea4b9b1386bdd281c854f815731fca`, 2279 bytes, final-write and all six zero.

The bound native001 diagnostic projection records actual RC1 after 22.392378056421876 seconds, exactly two unknown-constant errors at source lines 3103 and 3110, three warnings and no object. Both errors name `Filter.tendsto_const_nhds`. It records all owned processes ended, preservation/before-after equality, no timeout and no cleanup/ownership uncertainty. This reviewer only read that exact local projection; no server operation or replay occurred. The failed native receipt remains bound as SHA256 `6281a839d0a05cdaa54d76c58e72e022ed51b8526b1e6d93428018134f529a8d`. A failed attempt is retained as a failure, not converted into a proof pass.

The earlier complete SOURCE review covered the mathematical continuity argument, but its constant-limit reference used the wrong namespace. The actual native failure identifies that precise reference defect. This affected review checks the newly supplied exact API and both repaired calls; it makes no broader free-variable or causal-fix claim.

## Exact changed bytes and complete affected reading

I read the entire 1314-byte unified patch and the complete repaired `hLowerLim` and `hUpperLim` declarations and proofs, source002 lines 3099–3112, 989 bytes, SHA256 `f329b62f9e9a0da2ac7ed1becaa0117c993fa72a382dee87474263c8a5384fea`. This includes both full limit types, their complete multiplication/exponential calculations, the explicit constant-limit type annotations, and the closing subtraction/addition calls. This was one bounded untruncated literal reading. The whole unchanged proof and accepted243 proof were not reread.

Independently comparing all old/new source bytes establishes precisely two equal-length replacements:

- At line 3103, token interval `[211381,211406)`: `Filter.tendsto_const_nhds` becomes `_root_.tendsto_const_nhds` in `hLowerLim`.
- At line 3110, token interval `[211873,211898)`: the same replacement in `hUpperLim`.

Each token is 25 ASCII bytes; exactly 12 byte positions differ overall. Forward substitution reproduces all source002 bytes and the expected SHA256; inverse substitution reconstructs every source001 byte and its accepted SHA256. The only changed lines are 3103 and 3110. Source length, all line breaks, all offsets and strict UTF-8 without BOM/CR remain unchanged. The complete frozen02 preamble, head, initial introduction and closing are unchanged.

`COVERAGE.json` partitions the complete current source into the two repaired token spans and three exact unchanged spans, with old/new hashes and the prior complete source-review reference. The larger completely read 3099–3112 region covers both repaired tokens and their whole mathematical call contexts. Unchanged spans are covered by byte equality to the accepted complete SOURCE001 reading, not by sampling or an automatic whole-proof reread.

## Complete pinned global API and instantiation

I read the full bound 9886-byte packet `ce78c141e41dedd5dce5b0302f8549d6ab45aae526e8e5ba44e31f76dcc09d3d` without truncation. It includes the complete source prefix for enclosing-scope verification, the complete declaration and proof, its actual full name and pinned source binding. The source is Mathlib/Topology/Neighborhoods.lean, SHA256 `3bb04d7208d43fa6a30531b7c551bb39bb965c3ae61e38e3ca5dad8c65c55428`, 17707 bytes; the declaration is at line 192.

The complete enclosing context is `module`, `public section`, `open Set Filter`, `open scoped Topology`, universes `u v`, and variables `{X : Type u} [TopologicalSpace X] {ι : Sort v} {α : Type*} {x : X} {s t : Set X}`. The complete prefix contains no enclosing namespace command. Explicitly named declarations such as `Filter.Eventually.self_of_nhds` in that prefix do not open the Filter namespace. Thus the displayed declaration is global:

```lean
theorem tendsto_const_nhds {f : Filter α} :
    Tendsto (fun _ : α => x) f (𝓝 x) :=
  tendsto_nhds.mpr fun _ _ ha => univ_mem' fun _ => ha
```

The proof is the direct neighborhood-preimage argument for a constant function: an open neighborhood contains `x`, so every input maps into it and its preimage is the whole domain, a member of every filter. The declaration has no order, positivity, nontrivial-filter, probability, finite-index or extra mathematical premise. Unused surrounding variables `ι`, `s` and `t` do not become parameters of the theorem. Its only relevant structure premise is the existing topology of the codomain.

Both source calls have the unchanged complete type annotation:

```lean
Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
  Filter.atTop (nhds (1 : ℝ))
```

They instantiate `X := ℝ`, its existing topological-space instance, `α := ℕ`, `x := (1 : ℝ)`, and `f := Filter.atTop`. `_root_.tendsto_const_nhds` explicitly selects the actual global declaration from inside the project namespace. It introduces no assumption, helper, alias, import or instance. Constant convergence holds along an arbitrary filter, so no extra atTop condition is hidden in this use.

For `hLowerLim`, subtracting the unchanged limit of `C2 * unperturbedSourceCostη` from that constant limit yields `1 - C2 * sourceCost0`. For `hUpperLim`, addition yields `1 + C4 * sourceCost0`. The original full product limits then follow from the same previously reviewed multiplication and exponential continuity calculations. Both full goal types remain byte-identical. The repair does not change factors, signs, errors, cost semantics or witness/cutoff selection.

## Unaffected complete mathematical evidence

Independent recursive JSON comparison establishes that the new ACTUAL-PROP-CONTEXTS object changes only `/source/path` and `/source/sha256`. Every complete Prop, every one of the 33 DAG nodes, all typed bindings/RHS/scopes, all expanded canonical hashes and source annotation offsets/hashes remain deeply equal. All 27 annotation intervals were also checked directly against both source byte arrays; the equal-length repairs occur outside those annotations.

The new COMPATIBILITY object changes only the source reference and the reference to that updated context file (its path, SHA256 and byte length). All mathematical fields are deeply equal, including all 91 actual ordinary rows, the 140 approved optional/138 public rows, all 3 actual/6 approved instance entries and the frozen interface checks. The old authority entry in this retained compatibility map remains historical full-implementation provenance; the bounded repair authority is separately bound by the current activation/manifest/release.

Consequently the complete SOURCE001 review continues to cover the same original 16 binders, complete 36190-byte result Prop, qualified243 full premise, sole `cg/m₀`, original measures/normalized family, 60 retained old branch conjuncts plus the new clause, finite-coordinate/strict-total admissibility, unperturbed-cost closeness, full-product limits, exactly one tolerance on each bound, one common output cutoff and both literal exceptional probabilities. No mathematical declaration, premise, data or instance changed. All old source bytes, releases, failed receipts and accepted producer evidence remain retained.

## Verdict and next dependency

The exact two-reference repair is **CORRECT at SOURCE level**. All affected syntax, complete call types and pinned API scopes have been reviewed, with no critical gap. There were zero reviewer Lean/server/network/upload/Git/API actions, zero children and zero source edits. The local deterministic comparisons are integrity/scope checks, not a Lean or axiom result.

Next, the lead controls installation of source002 and its actual server native check. Only after success should the same FIRST original object receive the complete actual-owner TYPE/VALUE and recursive transitive-axiom audit. Return this same independent reviewer for one final join with the completed SOURCE001 and affected-source evidence; no unchanged whole-proof or accepted243-proof rereview is needed.

No external-input existence, probability limit, CDF/physical identification, uniform rate, OQ56/Root closure or free-variable cause is claimed. Requested configuration remains `gpt-6.1-sol/xhigh`; actual backend/model/effort and input, cached-input, output and reasoning-subset usage are unavailable and null. Sealing precedes the last FINALWRITE release, with all six counters zero and no subsequent reviewer writes in this directory.
