# Unit220 repair02: same independent reviewer's affected SOURCE and interaction report

STATUS: CORRECT

JUSTIFICATION: All five frozen changes preserve the exact mathematical functions and proof contracts. The four square proofs explicitly expand the existing pointwise function multiplication, with pointwise subtraction additionally expanded for centered rows. The J proof lifts the already qualified pointwise original row-square identity to a typed equality of the same functions by funext, then rewrites the measurability goal. No additional premise, selected observation, replacement function, coefficient or law is introduced. Exact replacement and inverse checks combine293unchanged prior lines with31freshly reviewed lines, yielding complete324-line SOURCE coverage.

`sourceAcceptedForNative=true`; `kernelChecked=false`; `qualified=false`. This is an affected SOURCE/statement/type-capture/interaction verdict, not evidence that a new native check or axiom audit has run. The reviewer is the same permanent never-author220reviewer. This context performed zero Lean, server, network, upload, Git/API/publication, child, Goal or schedule operations and wrote only in final-review-01/affected-repair02.

## Exact bindings and reused full review

New source: `author-01/repair-02/OriginalClippedStatisticMeasurable.lean`, SHA256 `052fb7eb6bb1d17218bf47c6c4f5b6715561da68b022bdacf6835fee5d667103`,15983UTF-8bytes,324LF/0CR/noBOM/finalLF. Its base is the accepted-for-native317LFsource, SHA256 `204a4b7d4bfe98819cd553b90ec98f6185b2b941ff019a22328fad59a1969718`,15680bytes. The original315LFsource and both prior review packets remain unchanged.

The parent freeze SHA256 is `01c146e52de87695c0662a114157a3266d1455454c1ce68f6966d57c0cae61db`,8117bytes. The exact author manifest is `089dcf623b121d4900e95d053e217ba86e513cbe3aa0c80aaca4e9bde42f620e`,4785bytes; all10payloads and14direct inputs were independently hashed. Parent author-intake SHA256 `c98f36567e3c0a30717343c6b03d3ed05a80f883aad781f277e5538914a8e3a1`,1421bytes, is exact. The two prior review manifests remain `c2190889cd38bff8d1f58fcc45e7f58418d1aa92d134d80a0d51b06f14ab1e2a`/2612bytes and `a45c87d10a9977d30b298fbdaf0666a18b3f08f934ce11f0458b2ac038629294`/2492bytes; all14bound prior payloads retain their hashes. The previously recorded hD/hd metadata correction remains preserved and this review continues using case-sensitive claim names.

Each old/new frozen patch text occurs exactly once, matches its supplied range and text hash, and applying exactly those five replacements gives the exact324LFsource. Reversing them gives the exact317LFsource. Six intervening source segments are unchanged. Old patches cover24lines and new patches31lines;317-24=293unchanged lines and293+31=324. The entire public declaration head,preamble,separator,closing,23typed header values and7proof-data witnesses/lets are unchanged. There is still1public theorem and no new global definition/alias/instance or forbidden proof-escape token. There are50named derived Prop proofs, including the previous hpair and the added hJfun.

The original complete315-line source-to-statement/proof review, full p40/p41/p51/p54reading, exact original model/coefficients/attribution and pinned API/accepted-project TYPE review are reused. The accepted317LFaffected review supplies the explicit hrcoord/hpair coverage and corrected case-sensitive hD/hd reasons. No complete accepted old producer proof was re-reviewed, and no Lean/AXcheck was replayed.

## Failed native02 evidence and provenance

I read the complete3391UTF-8byte native02stdout, SHA256 `f47af6c0b3c25b9426b8fd4ef75408ae4f8296af830e585c8ce0aef76ce92971`, in the bound5914byte affected-diagnostics projection. It records RC1,five errors,four deprecated-if warnings,noobject,all owned processes ended,source/protection preservation and no timeout/post-error/ownership issue. The errors are exactly the four function-product-versus-pointwise-square mismatches and the bare J-function-versus-pointwise-identity mismatch targeted here. No failed result is converted to a pass, and no object or220qualification is inferred.

The immutable old native02configuration's numeric unit219label was clerical: the actual module/path/source hash identify unit220and the317LFsource. Its source/module/path/hash and remote config/receipt byte bindings are retained, without rewriting that ended configuration or replaying its check. A future configuration for this new324LFsource must identify unit220. The four warning sites at old121/122/169/170 are unchanged at new121/122/176/177; this review does not claim a new observed warning count. No complete remote receipt/config/log was downloaded by this context.

## Pinned function-algebra API validation

I read the complete supplied primary `Mathlib/Algebra/Notation/Pi/Defs.lean`164-line source and the `Mathlib/MeasureTheory/Group/Arithmetic.lean`103–131excerpt. Context JSON SHA256 is `446e500811c495cc01111da45eaf2431c43e09e555d6a13d6969129481db5600`,7165bytes, pinned to mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The whole Pi source's4657bytes and SHA256 `12c8b14e6382cd08e76febdeb4ac5ce6396338cd8d42f07361352bedf4b1df92` match; the arithmetic excerpt body hash matches its supplied primary hash and its full-file hash agrees with the already reviewed arithmetic context. The prior arithmetic section variables/closures remain the applicable context.

`Pi.mul_def` has the primary declaration `[∀i,Mul(M i)] → (f*g = fun i => f i*g i)` and proof rfl. Its target is the very same pointwise Mul instance defined in that source. The primary div_def under `[∀i,Div(G i)]` is annotated to_additive and generates `Pi.sub_def`, expressing `f-g = fun i => f i-g i` under pointwise Sub. These are public notation lemmas requiring no new measurability,moment,nonzero or sample-space structure hypothesis. In this proof their domain is Fin n→Ω and codomain is ℝ with its existing canonical arithmetic structures.

The pinned `Measurable.mul` has conclusion `Measurable(f*g)` under MeasurableMul₂ of the codomain, explaining the failed bare-function products. The canonical real instance is unchanged. `pow_two` rewrites the scalar square; Pi.mul_def turns the measurable product into the exact pointwise scalar product. In the centered-row case Pi.sub_def additionally turns each function difference into the exact rowMean-minus-uStatistic scalar expression. These steps do not alter any summand,centering term or instance. Actual selected instance values/generated owners remain subject to the later all-owner server audit.

The existing fully reviewed qualified TYPE of `residualEnergyJ_eq_rowSqSum` is unconditional in n,r,ξ and has exactly the original rowSum-square function divided by ((n:ℝ)-2)^2. It adds no symmetry,measurability,canonicality or nonzero-denominator hypothesis. Its accepted proof/AXevidence is reused, not repeated.

## Five complete affected proof blocks

| Patch and new lines | Independent SOURCE/type/interaction check |
| --- | --- |
| P02-01,hgsquares104–108 | Each (hgcoord i).mul(hgcoord i) proves measurable multiplication of the same two score functions. pow_two and Pi.mul_def yield exactly ξ↦g(ξ i)^2; the existing finite-sum proof and its indices are unchanged. hV112then divides this same empirical squared sum by original n and applies total sqrt. |
| P02-02,hrowsquares135–140 | The same reasoning applies to (hrrow i).mul(hrrow i), with actual erased-diagonal rowSum entries. No row term or index is changed; the same row-square sum feeds hJ. |
| P02-03,hJ141–150 with hJfun142–148 | The fully typed equality names the same J and literal original row-square function. funext introduces an arbitrary ξ:Fin n→Ω; the old pointwise theorem gives its equality with exactly n,r,ξ. rw[hJfun] changes the bare J in Measurable J to that displayed function. hrowsquares.div_const((n-2)^2) then proves the goal. No cancellation or nonzero assumption is used. |
| P02-04,hcenteredrowsquares179–186 | The measurable function (hrowmean i)-hustat is multiplied by itself. Pi.mul_def and Pi.sub_def expose exactly (rowMean(sampledKernel ξ)i-uStatistic(sampledKernel ξ))^2 after pow_two. Both occurrences are the same original centered difference; finite summation preserves every original term. hs2187–193uses the unchanged jackknife coefficient and division by4. |
| P02-05,hV2199–200 | hV.mul hV gives measurable V*V; Pi.mul_def identifies exactly ξ↦Vξ*Vξ and pow_two identifies Vξ². The later hd201–205retains its actual s2/V²-1branch under the same V=0guard. |

The four changed simp sets introduce no function binder,value or selected datum. The existing data functions are the same g-coordinate,row-sum,centered-row difference and V. Their function domain/codomain,Pimeasurable structure,real arithmetic and captures are unchanged; the source merely exposes their pointwise definitions.

## Complete new hJfun, function-expression and binder/capture review

The exact new proposition is:

```lean
J = (fun ξ : Fin n → Ω =>
  (∑ i : Fin n, (Shao.OQ6.ResidualDeletion.rowSum
    (fun j k : Fin n => r (ξ j) (ξ k)) i) ^ 2) /
      ((n : ℝ) - 2) ^ 2)
```

The new hJfun is a derived equality proof in Prop, local to hJ. Its direct type captures are Ω,n,J,r; its proof value is `funext(fun ξ:Fin n→Ω => residualEnergyJ_eq_rowSqSum n r ξ)`, whose direct proof-value captures are Ω,n,r. Transitive original captures mΩ,μ,h,g occur through the already frozen r/J definitions. No equality or measurability premise is added. J is the frozen let residualEnergyJ n r,not a caller-provided substitute or chosen value.

The RHS is data: a function of exact type `(Fin n→Ω)→ℝ`, directly capturing Ω,n,r. It is not a new function let or witness. ξ:Fin n→Ω is its sample lambda binder; i:Fin n is the finite-sum binder; j,k:Fin n are the row matrix lambda binders. The tactic funext binder ξ at new147has the same full tuple type, fixed by the equality's explicitly typed function. Its target is the existing pointwise identity at that ξ. No retained tuple,deleted coordinate,law or filler enters this equality.

Its measurable domain later remains the same Pi of mΩ and real Borel target. Its denominator is the original ((n:ℝ)-2)^2; no sample size/cardinality or positivity premise is substituted. The seven earlier data entries F,Lrow,pdel,Dret,Jret,Bret,E retain their exact types,formulas,captures,pointwise constraints and retained-subtype semantics,with only the expected+7source-line shift after the new hJ block. The previous explicit hpair function and Prop remain covered unchanged. Existing implicit real/Pi/product structures and classical decisions are unchanged; there is no letI/instance declaration.

## Coverage composition and metadata distinctions

COVERAGE.json records all324source lines and all50derived Props by case-sensitive names. The five new blocks receive fresh full-block review; all other293lines map exactly to the317LFcoverage,including its already fresh hpair treatment and the transitive original315LFcoverage. Of the prior49claims,five are affected and44reuse their exact old source segments/reasons; the new hJfun makes six freshly reviewed claims and50total. Each data type/value/capture is checked independently of its shifted source location.

Independent lexical derivation finds65actual source lines with the standalone `fun` keyword. The author map lists68records because three additional lines contain identifiers with the substring `fun`: new142(hJfun) and196/198(measurableSet_eq_fun). All65actual lambda lines are present; those three records are retained and classified as non-lambda metadata rather than counted as new function data. The actual funext binder at147is separately covered. This small inventory overcount requires no source repair,old-byte rewrite or Lean replay. METADATA-NOTES.json records the exact provenance and corrected derived count.

The parameter record's new230deletion-index location and additional hJfun/funext binder are the expected source-map changes. The semantic-boundary wording now states that219is not a formal dependency rather than retaining stale 'unqualified planned only' wording; it makes no219qualification assumption in this proof. These metadata changes neither change the frozen theorem nor license a different source model. The previous hD/hd case-sensitive correction is reused exactly; all old sealed bytes remain preserved.

The four corrected proof outputs still feed the same full W/V/D/J/A/B1,s2/s/d/e,Tclip/Tactual observable packet and the same deletedTest expression. Physical s=0and clipped V=0guards remain distinct; continuous cap/deletedTest remain full-sample functions; only the signed Ddel/Jdel/B1deltriple factors through genuine retained coordinates with original n,n-1,n-2. There is no new canonicality,CDF,probability,law or root theorem claim.

## Source verdict and required next evidence

No affected mathematical,statement,API-assumption,capture or interaction blocker was found. The new324LFsource is SOURCE_CORRECT_NATIVE_PENDING. A successful exact-source server native receipt and same-first-original-object audit of every actual owner TYPE and non-theorem VALUE,with complete recursive AX restricted to propext/Classical.choice/Quot.sound,remain required. Return those exact receipts and source/object preservation evidence to this same independent never-author reviewer before final qualification.

p51remains UNCERTIFIED_REPAIR_CANDIDATE,p54repairs and Shao–Zhou2016attribution remain binding. Unit219's separate publication does not supply an assumption or import here. S27/CDF,atom/reflection,zero-denominator probability payments,S11/generalS15/DC/fullOQ56 remain OPEN; original C1immutablev85 and assigned C2/C12v112completion and separate OQ3userpause are unaffected. At this packet's final seal the review writer/heavy/inflight/pending/uncertain/children are zero.
