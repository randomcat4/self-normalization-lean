# Unit 189 repair002 author notes

Status: LOCAL REPAIR CANDIDATE; INCOMPLETE pending parent server kernel, actual declaration/type and all-owned transitive axiom receipts, plus independent review of changed proof scope. No new mathematical qualification is claimed.

The predecessor is the immutable `source-kernel001.lean.txt`, SHA256 `826f8a4d10c44727380e58a40e2af878f123763debaf4bc762ccab439f726814`, 38310 bytes / 826 lines. Parent reported and the archived response confirms natural kernel exit 1, unchanged server source and no object. Repair002 starts from those exact archived bytes. No old check is replayed by this author.

## Ownership and actual activity

Canonical role `/root/initial_double_kernel_repair002_author`, requested gpt-6.1-sol / xhigh / fresh context. Actual backend, model, effort, input, cached input, output and reasoning-subset counts are not observable and remain separately null. Runtime ACK is `repair002-runtime-ack.json`.

Only `InitialDoubleCompletionKernel.lean` and new repair002 notes/checkpoints in this directory were written. No edits to 190/191, freezes, archived source snapshots/receipts, the independent review directory, library, common source, coordination or original paper sources. No subagents, Lean/lake execution, actual environment/type/axiom audit, upload, publication, process or resource change occurred. Remote operations were bounded read-only source searches/excerpts through the existing transport.

## Repairs and reasons

1. `doubleCompletion_eq`, former line 30: replace the nonexistent `Set.univ_diff` simplification name by reverse `Set.compl_eq_univ_sdiff`. Its native head is `theorem compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s`; the inverse rule changes only the set expression `univ \ A` to `Aᶜ`. Also replace deprecated `Set.mem_diff` by native `Set.mem_sdiff` in the existing elementary set identity. The inclusion-exclusion argument and its events are unchanged.
2. `doubleCompletion_exterior`, former line 122: normalize both sides using `sub_eq_add_neg` rather than the absent reverse-name `add_neg_eq_sub`. The negative endpoint branch still has the same reflection formula and the same equality wall coverage.
3. `variation_add_le`, former line 255: use current `abs_add_le`, the real triangle inequality, in the same scalar bound. No inequality or partition changes.
4. `variation_le_of_pointwise_limit`, former line 280: use generated current `tendsto_finsetSum (Finset.range n)` with its explicit finite set. The per-index `edist` limits and the existing common finite-partition bound remain the same.
5. `initial_geometric_series_budget`, former line 354: use `add_le_add le_rfl hfinite`. The kernel001 diagnostic showed `add_le_add_left hfinite _` elaborating with the finite sum in the first addend; the explicit two-inequality form directly gives `2*r + finiteSum ≤ 2*r + tsum`.
6. `actual_initial_double_completion_kernel`: all repairs are inside its proof. The `hIvar` monotone and antitone branches now explicitly `change` to the two real exponential inequalities before using `Real.exp_le_exp.mpr`; remove the two `dsimp [I]` calls that the actual kernel reported had no remaining work. `hAbound`/`hJbound` use `sub_eq_add_neg` for the signed coefficients. Replace every remaining obsolete `abs_add` and `add_neg_eq_sub` use, including the later prefix-bound and negative-tail branches not reached by the failed proof. The `hTvar` and `hSvar` estimates explicitly expose just their outer function shape. Every `hsub` and every variation-add application in the four-image estimate, finite-prefix induction, prefix bound and final `f=F-L-R` variation argument receives explicit function/set arguments. Nested additions use `add_le_add` with `le_rfl` on the unchanged summands. This addresses the reported former line 485 `isDefEq` timeout by preventing higher-order inference through `eVariationOn` from metavariables; it does not raise the unchanged 4000000 heartbeat limit. The original infinite tail, wall telescoping remainder, exterior corrections and final conjunction are retained.

`repair002-proof-delta.diff` is the exact old-to-new proof delta. The affected declarations are exactly the six declarations listed above (five private theorems and the public theorem). The other nine private theorem proofs and the sole def/value are byte-identical to kernel001. No new global helper or assumption was introduced. Existing local lets remain the same values; explicit proof-local function expressions only guide elaboration.

## Pinned native source evidence

Successful bounded read-only excerpts and full-file hashes are in `repair002-native-readonly-002.json`. The three native files came from the designated existing `cache-overlays/shared-v34/packages/mathlib` view, under the pinned mathlib commit supplied by the parent. This author did not run a Lean command or independently inspect an elaborated environment.

- `Mathlib/Order/BooleanAlgebra/Set.lean:337`: complete `compl_eq_univ_sdiff` head and proof `top_sdiff.symm`; native file SHA256 `9da12d237105504533571f9ebbe30ba15821d532854523e73b36c3345961461d`.
- `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:123`: `@[to_additive] lemma mabs_mul_le (a b : α) : |a*b|ₘ ≤ |a|ₘ*|b|ₘ`, with its CommGroup/MulLeftMono section; the generated additive name is `abs_add_le`, as also used in current pinned Mathlib consumers. Native file SHA256 `574421adeb1391adcc9008c7e4a7981b2b444416f5d63ecf3ec48a4454851463`.
- `Mathlib/Topology/Algebra/Monoid.lean:941`: `@[to_additive] theorem tendsto_finsetProd ... (s : Finset ι) : (∀ i ∈ s, Tendsto (f i) x (nhds (a i))) → Tendsto (fun b => ∏ c ∈ s, f c b) x (nhds (∏ c ∈ s, a c))`; generated additive name `tendsto_finsetSum`, with the analogous sum head and explicit finite-set parameter. Native file SHA256 `b92c681b0f32e9a46b0959f845ee21f67a64af2ede2f1d8b34098371250410e6`.

The generated names/contracts are source-rule deductions, not newly observed elaborated types. The parent still must obtain actual types and kernel qualification. `repair002-native-readonly.json` preserves an unsuccessful read-only excerpt attempt (remote Python quoting SyntaxError, exit 1); it did not mutate any source. An earlier remote search discovered `rg` absent and used bounded `grep` as fallback. Neither failure is a proof-check result.

## Exact invariants and review boundary

`repair002-source-text-invariants.json` records byte comparison against kernel001, all 16 declaration heads, all 7 pre-existing frozen input files, the exact sole `doubleCompletion` def body and the complete prefix context. All heads are byte-exact to kernel001; each frozen head/value also matches after whitespace normalization; no declaration was added or removed. The sole value and unchanged proofs are byte-exact. The source is UTF-8 without BOM, contains no CR bytes, and ends with LF. Forbidden-token count in the Lean candidate is zero. These are source-text invariants, not a formal or transitive-axiom audit.

The existing independent complete static review is bound to old SHA256 `826f8a4d...` and remains archived. Its correctness judgment must not be presented as a complete review of this changed source. Reuse its evidence for exact unchanged proof/value blocks and unchanged original-scope analysis; a qualified independent reviewer must cover the six changed declarations, their actual native/type contracts and material interactions. A fresh review of accepted old library proofs is not requested.

Next exact dependency: parent uploads this exact candidate, runs only the affected unit189 source-bound server kernel/type/all-owned-axiom gates in its allocated phase/lock, preserves results, and obtains qualified changed-proof review coverage. Any further edit invalidates only evidence affected by that edit. C2/C12 remains OPEN.

Candidate SHA256: `2f38639174a6a70086c4a6d1dbac35986ce1beed3ac849c9764ac1114b3b460a`; 39034 bytes / 836 lines.
