# Unit240 native002 whole-function transport repair

Status: COMPLETE_AFFECTED_REPAIR_PENDING_SAME_REVIEWER_DELTA_AND_NEW_SOURCE_SERVER_GATE. Qualified=false; no new Lean/kernel/object/actual-TYPE/VALUE/axiom result is claimed.

The same-author activation is 21a75114abfff0803da08c368d202cc4c57fe53c19319ddb9756ad9bec78b964 /6397B. All seventeen listed inputs were verified before the first runtime ACK and implementation. This author writes only unit240/author-repair-02. All prior source/freeze/review/failure/history and other-owner files remain read-only. The requested role/model/effort is /root/oq56_same_witness_coding240_stage1_author, gpt-6.1-sol/xhigh under sole OQ56 lead 01a17665-2e41-7ed1-9911-57f16fe889fa. Actual backend/model/effort and the four usage counters are unexposed and remain null.

## Exact native002 diagnosis

The attempted source is eb17f3e3942d6c84e786d3f457525c28c4207fc494e98a21f54539563140aa52 /41403B/674LF. Native002 naturally ended actual RC1 in122.88678081706166s with one error at649, three warnings, no object, all owned processes ended and preservation equal. Its exact receipt is 950ff13d33e9e960fc8030ffc48421d7596ac92760e446c4593c0f36be8171d6 /22119326B. The complete small diagnostics projection and source-preparation binding were read; the large raw receipt was not fetched or copied.

The actual measurable term still contains the UNAPPLIED whole function subtraction `(fun a => (Ftriple a).2.1) - fun a => (Ftriple a).1`. The target is the pointwise lambda `fun t => (Ftriple t).2.1 - (Ftriple t).1`. The existing hBReal transport is preserved. The prior final `simpa only [FAdelete, Pi.sub_apply]` did not rewrite this whole unapplied function head; Pi.sub_apply rewrites values after an argument is supplied. That source-level compatibility expectation is superseded by the native002 result, which remains preserved.

## Minimal replacement

Only old line649 is replaced by the following new649-656 block. The previous hBReal declaration and reverse equality rewrite at646-648 are byte-exact:

```lean
      have hPiSub :
          ((fun t : ({j : Fin n // j ≠ i} → ℝ) => (Ftriple t).2.1) -
            (fun t : ({j : Fin n // j ≠ i} → ℝ) => (Ftriple t).1)) =
          (fun t : ({j : Fin n // j ≠ i} → ℝ) =>
            (Ftriple t).2.1 - (Ftriple t).1) := by
        funext t
        simp only [Pi.sub_apply]
      simpa only [FAdelete, hPiSub] using hFT.snd.fst.sub hFT.fst
```

Every lambda domain is explicitly the same deleted real tuple type. hPiSub is an Eq proposition about the complete functions, not a new ordinary function alias. Function extensionality introduces an arbitrary point of that already-stated domain; at this applied value Pi.sub_apply gives the identical real subtraction on both sides. The final simp then uses hPiSub itself as a whole-function rewrite and unfolds the already-frozen FAdelete RHS. The original hFT projection/subtraction proof term is retained literally. This addresses the displayed un-applied-head mismatch instead of repeating Pi.sub_apply alone in the final step.

The hPiDiv comparison source in unit241/author-repair-01/UnperturbedDeletedWeightedCostBridge.lean was read at343-357, especially its fully typed equality, funext/Pi.div_apply proof and final explicit equality rewrite at348-355. Its exact source binding is a3f6a76b636d66b1049289293c12884bcc8474379b059f835507f3f49f73e5f8 /19004B. It is strategy/API context only; unit240 does not invoke a241 theorem or claim a241 kernel result.

## Exact byte provenance and preserved scope

The repaired complete source is 2fef6cf8b8e7dfa5346871728488ed3388ff90e2ec6b301b439069c22ae6e339 /41723B/681LF. The fixed prefix before old649/new649 is40256B, SHA256 b263520c1872f6cacc8d91955109af8c1f088b1fcff815bf8a1416f02ef46422. It includes the unchanged complete frozen declaration, all ordinary values/instances, and existing hBReal transport. The fixed suffix is1075B, SHA256 51520d70458322342c316d05438b17e81f484cec9fcf044b7019592d732ca934. It begins with the unchanged FBdelete proof, at old650/new657, and preserves every remaining identity, algebraic step, returned old packet and closing.

The removed failed line is72B; the replacement is392B. DELTA-PROVENANCE.json records both full exact strings and their hashes, plus exact old/new reconstruction from the common prefix and suffix. No previous source or failed receipt was overwritten, and no intermediate native attempt was dispatched in this repair.

All frozen preamble/head/closing,136 result ordinary and146 approved optional records,98 source-level ordinary values/result mirrors,3 explicit instances, choices, ordinary types/RHS/scopes, imports and assumptions remain unchanged. FAdelete still denotes the same second-minus-first factor from the same Ftriple; FBdelete and its proof are unchanged. The only newly named fact is fully typed hPiSub:Prop. No new ordinary helper, alias, witness, instance, callback or assumption is introduced or needed. hBReal remains the existing local Prop from the prior repair.

The same original independent reviewer should assess this affected delta and bearing context, reusing the exact unchanged original complete SOURCE coverage and affected Borel-transport coverage. No redundant complete proof review, accepted producer/kernel check or old leaf-AX replay was run by this author. Both native001 and native002 failures and all prior source bytes remain retained evidence.

Local checks establish exact frozen source segments, prefix/suffix reconstruction, unchanged ordinary/instance/import source lines, the retained hBReal and FBdelete bytes, UTF-8 without BOM/LF, all input bindings and no prohibited proof tokens. They do not establish Lean elaboration or a kernel/axiom pass. After affected independent review, the lead must perform the new-source server native check and, only on success, same-first-original-object all-owned TYPE/required VALUE/transitive AX audit with the final independent evidence join.

Original same-witness analytic/strict/payment/coding conclusions and source assumptions remain unchanged. External Shao-Zhou input, CDF/atoms/continuous-epsilon/physical=coded/full OQ56/Root conclusions remain OPEN. This author ran no Lean/local compile/server/network/upload/Git/API/children. Final zero RELEASE is the last write and records writer/heavy/inflight/pendingExternal/children/uncertain all zero.
