# Unit220 exact repair-plan02 proposal

STATUS: EXACT_BATCH_PROPOSAL_ONLY_PARENT_FREEZE_REQUIRED. No source/.lean file was edited or written, and no Lean/server/network/publication/child action ran.

The selected batch replaces exactly five existing proof blocks from immutable317LFsource204a4b7d4bfe98819cd553b90ec98f6185b2b941ff019a22328fad59a1969718:

| Block | Old lines | Proposed change |
| --- | --- | --- |
| hgsquares |104–108| Add Pi.mul_def to the pow_two simp set. |
| hrowsquares |135–140| Add Pi.mul_def to the pow_two simp set. |
| hJ |141–143| Derive typed hJfun by funext from the qualified pointwise row-square identity, rewrite J, then use hrowsquares.div_const. |
| hcenteredrowsquares |172–179| Add Pi.mul_def and Pi.sub_def to the pow_two simp set. |
| hV2 |192–193| Add Pi.mul_def to the pow_two simp set. |

These fixes address all five observed type errors as one representation batch. The pinned primary Pi source was read completely; multiplication is defined pointwise by Pi.instMul and expanded by Pi.mul_def. The subtraction expansion is the existing @[to_additive] generated Pi.sub_def from div_def. The Arithmetic excerpt confirms Measurable.mul returns Measurable(f*g). API-CONTEXT.json binds the exact source and context. No further API retrieval is needed for this proposal.

The hJfun proof is the sole additional local Prop. There are no additional local data lets, witnesses, structures, mathematical assumptions or public heads. The total stays one source public theorem,23header values and7proof data witnesses/lets; named derived Props become50. DATA-CAPTURE-LEDGER.md and PATCHES.json give the exact type/value/captures before implementation.

Applying the five blocks only in memory gives a deterministic preview of15,983B/324LF and SHA256052fb7eb6bb1d17218bf47c6c4f5b6715561da68b022bdacf6835fee5d667103. No complete-source artifact is written here. Reversing all five proposed replacements recovers the exact immutable base. Frozen preamble/full head/closing remain exact, and all four existing deprecation source uses stay unchanged.

Native02is a known ended failure,not an uncertain operation or219result. Its actual source/module/path/SHA bind220 despite the inherited numeric cfg label219; original config/receipt bytes stay intact. There is no object or220qualification. The next action is the parent's exact block/data freeze,then same-author implementation in a separately authorized directory and same-reviewer affected review. No automatic source/check authority is inferred from this plan.
