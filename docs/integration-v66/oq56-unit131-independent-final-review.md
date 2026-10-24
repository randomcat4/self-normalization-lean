# Unit131 final independent review

STATUS: CORRECT — QUALIFIED EXACT SOURCE/OBJECT

The finite deterministic p39(4) cleared-projection-energy row-square identity is accepted for exact source SHA256 `723212291e59277244b7db38699375ca65b4950a8ed971331d01dedbda60cf53` and original compiled object SHA256 `64811ccaacfd2f4e968334a38f6ee2a401b9152a0770882a08db447e2611f80b`. This is one source-public theorem, two source-private theorem helpers, and two compiler-generated theorem helpers. There are no new definitions or non-theorem values. No root probability theorem is closed.

Reviewer `/root/oq56_final131_kernel_fresh` is permanently `NEVER_AUTHOR131`, fresh context explicitly dispatched as `gpt-6.1-sol` / `xhigh`. Neither the original proof nor its two repairs was authored by this reviewer. Input/cached-input/output/reasoning-subset usage counters are unavailable and remain unknown. All work stayed in the assigned review directory or explicitly authorized bounded server audit/evidence outputs; no candidate/shared/curated source, Git or cache was changed by this reviewer.

## Exact statement and complete source review

The frozen contracts SHA256 is `eabfff97d7575f664c8e8a8554fb8c87b8e66d648c2487420c85361622407964`; frozen prose SHA256 is `7bf371e2f88fc0c707a860a1988d7efb23fcb71761310f48ba9ef81e78374753`. The final 4124-byte / 108-line source was read completely, including every visible declaration's full type and proof. Its public header literally matches the complete frozen header; all three raw types and the sole import remain identical through the directed repairs. The final source is strict UTF-8/LF with no BOM and no forbidden proof token.

Original p39 SHA256 `251249839300f1c15b0c05cdb407167c7ab9f9a8b294e25747a3e1ef57d338a4`, lines 59–107, and p38 SHA256 `4ba79f1a288608220b5d0a8db76d3499c8c8ebd353687ec71dbc426b9ee6171b`, lines 1–140, were read for the source interpretation and separate denominator events. Actual accepted rowMean/uncenteredSq values were inspected in FiniteRows SHA256 `bb4dc865f5ab96ce57814f0721fbd31a2885d6fce7a9facd150941c4c2f91930`; actual once-counted unorderedPairSum and generic double-counting type/proof were inspected in RowIdentity SHA256 `73bb0809bc6d323b31775327e468677d6320b38f8fe87363936860164f17f975`. Previously accepted old kernel checks were not repeated.

For arbitrary g, arbitrary symmetric r with unrestricted diagonal, and n≥3, put S=Σg, Q=Σg², ψᵢ=Σ_{j≠i}rᵢⱼ, F=Σ_{i<j}rᵢⱼ, a=n−2 and b=n−1. The actual rowMean of Hᵢⱼ=gᵢ+gⱼ+rᵢⱼ is (agᵢ+S+ψᵢ)/b: erasing the diagonal subtracts 2gᵢ from ngᵢ+S. This private helper never cancels b, so its all-n type is valid, including the harmless total-division n=1 case and vacuous n=0 case.

The second private helper expands and sums all six terms of (agᵢ+S+ψᵢ)². The public proof then uses symmetry only through Σψ=2F. The full numerator is

N = a²Q + (3n−4)S² + 2aΣgᵢψᵢ + 4SF + Σψᵢ².

Unfolding actual uncenteredSq gives s_*²=N/(b a²). The final identity is obtained from b(s_*²−Q/n)=N/a²−bQ/n and Q−(n−1)Q/n=Q/n. The nonzero facts for n, b and a follow solely from n≥3. Final source lines 101–102 perform square-of-quotient normalization before inverse multiplication and finite-sum factor extraction; the exact server kernel run confirms this directed repair works. Both mixed terms and every coefficient are retained.

With V²=Q/n, W=S/√n and D1=F/[√n(n−1)], nW²=S² and n(n−1)WD1=SF, so this is exactly p39(4) with the D2 projection division cleared. It covers Q=0 without asserting the quotient D2 formula there. No sample centering, canonical degeneracy, diagonal-zero, iid, moment, tail, Q>0 or physical R>0 premise is used. The physical R=0 event remains distinct from V=0.

## Producer receipt and disclosed style-warning exception

The exact author03 direct Lean target exited **0** in 3.161731608 seconds and generated the object above, 472584 bytes, mtime_ns `1792795300887745230`. Producer receipt SHA256 is `d0420152b180f9163b794b0e5bd7d359930028083af2533158bd20ace7f2f324`; config SHA256 `e09f597733578691b9b5ca67d5ed91437d92ab7d5e3a274b825d56722977f5eb`; RUN-ENDED SHA256 `faff39557244ac4611867a7b2532f88ba49d84e447c14a8811693790bd3110cc`.

The producer's strict empty-output wrapper success remains **false**. Its complete 396-byte stdout contains exactly two style warnings at line 104: unusedTactic and unnecessarySeqFocus both advise replacing `<;>` by `;`. Stderr is empty and there are no Lean errors. These lints concern equivalent tactic sequencing style after field simplification; they do not indicate an open proof obligation, changed statement or additional axiom. I independently accept the direct kernel/object evidence with this explicit style-warning exception. This is not a FIRSTEMPTY or strict clean-output receipt. No warning cleanup, source rewrite or producer recompile was performed after kernel success.

Stopped-warning seal SHA256 `aa345dcf060a15f3fb11d29c45105e41566e3ffc509f12bdae90de88c60f344e` and released-writer handoff SHA256 `32c6ba5e03030b631dedb2f012aebef0eac27442a0050d5680102ff4673cf519` preserve this distinction. Earlier failed bytes and receipts remain archived and are not represented as qualified.

## Actual compiled-module type and axiom coverage

Exactly one authorized audit imported only `Shao.OQ6.ResidualRowExpansion` and did not use `-o` or re-elaborate the proof source. It enumerated the complete actual imported module index, anchored at the frozen public theorem, and checked every owned constant with Lean.collectAxioms. Actual count is five, derived from the inventory rather than copied from the three source declarations. All five are thmInfo with proof expressions present; there are zero non-theorem values.

All five complete pp.all type strings were literally read, totaling 16618 UTF-8 bytes, without ellipses or factoring. The exact raw marker stream was losslessly roundtripped by the established parser. Mapping:

- Private `residual_rowMean_formula`: current source lines 20–36; exact all-n erased-row formula type.
- Private `finite_sum_affine_sq`: lines 38–54; exact arbitrary-a/S six-term finite-square expansion type.
- Public `uncenteredSq_sub_projectionSq_expansion`: lines 56–104; exact frozen arbitrary-g/symmetric-r/n≥3 type and fixed lets. No additional premise appears in its compiled type.
- Generated private `finite_sum_affine_sq._simp_1_1`: lines 53–54; reversed Finset.mul_sum, Σ a*fᵢ = a*Σ fᵢ, over the displayed arbitrary NonUnitalNonAssocSemiring and universes u_1/u_4.
- Generated public-parent `uncenteredSq_sub_projectionSq_expansion._simp_1_1`: line 102; reversed Finset.sum_mul, Σ fᵢ*a = (Σ fᵢ)*a, over the same generic algebraic class/universes.

The three source theorem axiom lists are each {propext, Classical.choice, Quot.sound}; each generated rewrite helper uses {propext, Quot.sound}. There are five complete lists / thirteen axiom occurrences. Every transitive dependency is on the standard whitelist. No sorryAx, new axiom or unsafe escape is present in the accepted scope.

Audit receipt SHA256 `b680477917e0801e0345960e5f9fe7af7050f0fa59ed8d1deb8964de52b670e7`, direct rc0/success true, no diagnostics or stderr, 3.126611490 seconds; RUN-ENDED SHA256 `bf93284060538464c92828c8d786b4d0d9c71fcda4b900c3f75bac1e6a56d650`. Curated summary SHA256 `91b29a6bbb9ed1fc469e6b6fcf02a86d0d104f06b02c7a83e704f87e846dd3b3`; complete type expressions SHA256 `f0ecdd33094fd69a7dc8f166c52aad136bb63226445a1296265e8ef16c7444ee`; complete per-entry coverage SHA256 `815e601f4fe9f2c9b9a5cba7ab57f7693e4c3d7b8ebe287a037b3d8be03211f2`. Raw audit output remains on the server, SHA256 `455880218038f23503a5f97c3cb755d93d9b8a39baaacd87763ff78c6d84b072`, 19326 bytes.

## Preservation, execution and remaining scope

The audit used the existing mature bounded runner on CPU22–25, native -M8192 -j4 and the existing lane lock/resource guards, pinned Lean 4.36.0-rc1 and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. External CPU0–9/80GiB was untouched.

Final validation rehashed all 954 actual protected records (953 listed inputs plus the audit config), retained the entire author936 map and all92 canonical key-to-physical descriptors (old90 plus this source/object), and preserved all74 Git refs and exact HEAD/branch/tree. No timeout, cleanup or ownership issue occurred. Both owned groups ended and final observed lane-live Lean list is empty. Final evidence validation SHA256 `b2e2fce51e656f84bd5d10209fd2b58c9e982a8de68ff541689b0ac638825614` binds the exact source/object, receipts, counts, coverage, resource state and warning exception. No further reviewer Lean invocation is authorized or needed for this unchanged unit.

Accepted scope is only this deterministic finite identity. The G-envelope, deleted-row costs, V=0 or physical R=0 probability, scalar SZ engine, p53, RS2 and all OQ6/original root groups remain OPEN. The lead can reuse this exact qualified source/object review and receipt at acceptance, checking hashes and integration interactions without repeating unchanged old proofs.
