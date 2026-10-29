# Unit275 minimal repair04 handoff

The complete candidate changes exactly two proof-term lines in `actual_common_physical_compact_raw_bounds`, at SOURCE1141 and SOURCE1155, helper7 PROOF53 and PROOF67. Both replace `add_le_add_left (abs_sub_le _ _ _) _` by `add_le_add (le_refl _) (abs_sub_le _ _ _)`. No other source line or proof line changes. The mathematical inequality, constants, assumptions, actual functions and frozen statements are unchanged. This is an affected elaboration alignment repair, pending SAME independent review and a fresh parent-run native05; qualified=false and kernelChecked=false.

## Authority, reading and exact inputs

The explicit SAME-author activation is `author-repair04-ACTIVATION.json`, SHA256 `5a93ff945d2b2a378d9681820785be893c29d424dd4d40b5bbd3408ca318c70a`, 40617 bytes. All168 exact input bindings were actually verified by SHA256 and byte count before the first write, with zero mismatches. The sole new write scope is `C:/game/shao lean/drafts/oq56/unit275/author-repair-04`. The other active owner and all old sources, seals, freezes, reviews, library and shared files were left untouched.

The complete13644-byte native04 inspection was read, including both full557-character error contexts with no clipping. The complete20260-byte prior independent SOURCE3 report, complete5288-byte verdict, complete2577-byte parent intake, and complete90-line old/new affected helper7 proof were read. Prior same-author complete source/HEAD reading is retained and all frozen byte bindings were checked again. An initial local read command failed before reading because it constructed a combined path; it was corrected and the complete individual files were then read. That administrative read failure performed no mutation or Lean action.

## Native04 evidence preserved

The exact old source checked by native04 is SHA256 `4f3ecd10323122eaf3d35d3f782d893fdfa6294e26f6605aa4e02ffa07707a95`, 83832 bytes,1618 LF. Native04 naturally ended RC1 in9.668974505737424 seconds, without an object. All34953 protected artifacts were preserved; all owned work ended and ownLive=[]. No timeout intervention, cleanup or ownership issue was recorded. Its only two emitted errors are the SOURCE1141/1155 type mismatches;58 warning headings were retained. The inspection records no heartbeat message and no maximum-error-cap text. This errored run is not a whole-source default-budget or kernel pass.

Inspection binding: `lead-execution-01/native04-terminal-inspection.json`, SHA256 `f218e56efc283029737f871ed502a737580d43cba3fddb7d5f4e125fd1e44fef`,13644 bytes. Raw17417-byte stdout remains server-only and unread here, SHA256 `25755eb31c998b70bdbff673e7b44b02d4dfa0ff8ea2ed113e7fa75dfb0c45c8`. No native request was replayed, no new Lean/AX call was made, and no warning cleanup is included.

## Exact type alignment and mathematical role

For the closed CDF calculation let A=|P(T<=x)-P(Tstar<=y)|, a=P(Tstar<=y), b=Phi(y), and c=Phi(x). The actual calc target is

`A + |a-c| <= A + (|a-b| + |b-c|)`.

The previous proof term was elaborated as `|a-c|+A <= (|a-b|+|b-c|)+A`, which puts the common summand on the opposite syntactic side from this target. The new term uses `le_refl A` as the LEFT input to `add_le_add`, and `abs_sub_le a b c` as the RIGHT input. Its conclusion is exactly the displayed target, without any commutativity or associativity transport. The underscores in the one-line Lean term are typed by that concrete calc target; they do not add a hypothesis or leave a proof obligation as an escape.

For the open CDF calculation the same reasoning uses A=|P(T<x)-P(Tstar<y)| and a=P(Tstar<y), with b=Phi(y), c=Phi(x) unchanged. The repaired source steps remain in the same closed/open calculations. Their initial triangle steps, actual physical probability comparison, Z payment, uncentered CDF bound, normal-CDF movement and final ring equality all stay byte-identical. The strict/closed tail complement arguments below them also stay byte-identical.

There is no coefficient repair or mathematical weakening. Helper7 still returns the same raw error C*(Lcompact+65552*(1+y)*s/q)+2*exp(-cg*N)+(1/8+33104*s)/q+12/N, y=tau(x), for all n>=3 and x in[0,1]. Its caller still performs the same common-K absorption.

## Complete candidate and exact preservation

New complete source: `UniformPMomentOriginalPhysicalCompactCDF.lean`, SHA256 `215e03f4731a56bce41aa7682de1269c907ceab1d57afd0587acda2a465c45b4`,83842 bytes,1618 LF. The ten-byte increase is exactly five ASCII bytes at each repaired proof term. The complete new helper7 PROOF is SHA256 `f9a6bad1e9a7271fca153a0a40fc058c81587d8cc8b45013ac17b1b4d7bc5c15`,5200 bytes,90 LF. Main PROOF remains byte-identical at SHA256 `eb4641c5e92daa45daaeae7ded73b923a6264e4ab178923201057105e987e1a1`,7079 bytes,146 LF.

All eight helper PROOF files and main PROOF are supplied completely. The other seven helper proofs and main proof are copied byte-for-byte from repair03; only helper7 changes. Every proof begins exactly `:= by` then LF and ends with exactly one LF. Aggregate proof stream remains1240 LF; aggregate frozen HEAD stream remains350 LF.

The parent pack `freeze-repair03-01/frozen-helpers.json`, SHA256 `1ec9be4be87db6c1b92122dd63d03b5c84efb25662106d1bfa7e21fb08cedf53`,7215 bytes, remains the sole declaration freeze. All eight private HEADs, their order/universes/binders, PRE18, public HEAD47, CLOSE2 and all eight additional separator LFs remain byte-exact. Canonical assembly remains all28 segments with no extra declaration/import/section. `DECLARATION-ASSEMBLY.json` recomputes every source byte offset and preserves all line ranges. Helper7 HEAD is SOURCE1046-1088 and its complete PROOF is SOURCE1089-1178, exactly as before. Later byte offsets increase by ten; line positions do not change.

No resource override occurs in any proof. The source's only option is the unchanged frozen `autoImplicit false`; all heartbeat/depth/memory/time/job limits remain unchanged. The prior removed maxHeartbeats/maxRecDepth directives are not restored.

## Full patch and continuous maps

`patch.diff` is one unified hunk covering SOURCE1046-1178: the complete frozen43-line helper7 HEAD and complete90-line proof context. It has exactly two removed lines, two inserted lines and131 equal context lines. Thus the full affected declaration context and every source change are present, not clipped excerpts. The hunk's old/new ranges are both1046,133.

`patch-map.json` provides five continuous opcodes consuming all old/new1618 source lines; five further opcodes consume all old/new1240 proof-stream lines. The changed proof-stream lines are862 and876. It also records all nine full proof-file byte/hash/range mappings, exact identity of the other eight proof files, and full helper7 context/source positions. Opcode endpoints are zero-based half-open; displayed source/proof lines are one-based inclusive. Equal regions must be actually equal; changed regions are exactly the two one-line replacements. Reconstructing the patch's old/new hunk and surrounding unchanged source reconstructs both complete source versions exactly.

## Accepted review union and affected review obligation

The prior SAME independent complete SOURCE3 verdict is CORRECT for old source4f3ecd10...,83832 bytes, with full SOURCE1-1618, proof-stream1-1240 and HEAD-stream1-350 coverage and no holes. The parent intake binding is SHA256 `e0a4b790db0eb78029a93b46c702981f54f57c774e724ad32855ff93e6070b08`,2577 bytes. That exact evidence remains applicable to every unchanged byte/context. It is SOURCE acceptance, not a native/object/AX result. The two repaired proof terms are new and require SAME affected independent review of their actual calc targets and full helper7 context before fresh native05. No blanket new kernel qualification or automatic accepted-new-source claim is made.

The frozen interfaces and all original-data semantics are unchanged: K=131112*C+33117+2/cg is fixed before every model; cg comes from qualified265 at the same p,B; true g,r,v,s and actual FiniteRows.uStatistic/jackknifeSq and exact physical zero branch remain; all n>=3 and all four strict/closed CDF/tail errors on[0,1] remain. The full residual-scale split, actual cost producer, finite CDF engine, common G/H/Z payments, original observable law transport and arbitrary measurable-space scope are unchanged. No residual budget, independence, mixed-moment, envelope, StandardBorel or desired-conclusion input is added. The external hSZC contract stays explicit and distinct, with no existence claim. Neither unqualified273 nor274 is a dependency. The original five-page source scope is retained; OQ56 roots remain OPEN.

After affected SOURCE acceptance, the parent alone may run a new complete exact-source native05 under original defaults. If successful, its same first original object needs the mandatory actual-owned TYPE/non-theorem FULLVALUE/transitive-axiom packet with propext, Classical.choice, Quot.sound only. This author turn supplies no such receipt, no object and no default-budget success claim.

## Deterministic checks and release

`STATIC-CHECKS.json` records the exact-two-line diff, unchanged other proof bytes and frozen fragments,28-segment canonical assembly, all proof/HEAD/source counts, full map continuity and equality, full patch reconstruction, proof boundaries, allowed nine global theorem names/order, absence of forbidden escapes/resource overrides,168 input byte/hash bindings, and UTF-8 without BOM/LF/single-final-LF format. These are file/structure checks and do not run Lean or establish independent mathematical qualification.

All writing is within the new scope. Lean/AX/toolchain/server/SSH/transfer/network/GitAPI/child/Goal/schedule/sidebar/proxy counts are zero. Prescribed settings remain gpt-6.1-sol/xhigh. Actual backend/model/effort and input/cached-input/output/reasoning-subset usage are unexposed and recorded as null, with no exact subscription-percentage allocation claim.

All18 authorized outputs are sealed. Unique LAST is the final filesystem mutation and releases all author, repair, implementation, write, review, execution, child, publication and retained authority. Heavy/inflight/pendingExternal/writer/child/publication are all zero; activeWait=false and endOrdinaryTurn=true. No persistent continuation claim is made. qualified=false and kernelChecked=false.
