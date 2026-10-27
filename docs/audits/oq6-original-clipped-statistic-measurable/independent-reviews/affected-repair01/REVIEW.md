# Unit220 repair01: same independent reviewer's affected source review

STATUS: CORRECT

JUSTIFICATION: The frozen repair gives the same canonical coordinate-pair function an explicit domain and product codomain before composing it with the already qualified literal residual's measurability. The new local hpair is a derived Prop proof, not an additional assumption or a chosen observation/function witness. The existing hrcoord contract is unchanged, so its three downstream uses and the previously reviewed statistic/deletion argument retain exactly their original semantics. The other312 old source lines are byte-identical; their complete prior independent coverage is reused and combined with the five newly reviewed lines to cover the complete317-line source.

`sourceAcceptedForNative=true`, `kernelChecked=false`, `qualified=false`. This verdict authorizes the next source-bound native attempt only. No220object exists in the supplied evidence and native02 has not been dispatched at this review checkpoint. This context remains permanently not an author220 and has performed zero Lean, server, network, upload, publication, child, Goal or schedule operations.

## Exact change and preserved evidence

The new source is `author-01/repair-01/OriginalClippedStatisticMeasurable.lean`, SHA256 `204a4b7d4bfe98819cd553b90ec98f6185b2b941ff019a22328fad59a1969718`,15680UTF-8bytes,317LF/0CR/noBOM/finalLF. The base source remains SHA256 `05835d00b91a71a93d12dd5b6ff8ba80e49aa0f71c716b948153764b23993303`,15590bytes/315LF.

The exact affected freeze is SHA256 `f4e9cac4e4c6f091a706f252522bb402183141dd076dacd9e372af5092c96ea3`,3262bytes, and its activation SHA256 is `048d345c57c92e2c2aeefd245bb42e9a453f0a6dbb81b8b3d6bfb3a071085cb0`,903bytes. Parent repair intake SHA256 `300d130d6397af43c3875e0578fa838bf25f041bd3fa6071ebd51f3e192c382a`,6402bytes, and author repair manifest SHA256 `e2fa71805da63263db37760f2afea38d0d9a03c15a39766804cf4cf143d25cc5`,4144bytes, are exact. All10author payloads and8repair inputs were independently hashed. The same reviewer's prior manifest `c2190889cd38bff8d1f58fcc45e7f58418d1aa92d134d80a0d51b06f14ab1e2a`/2612bytes and all7prior sealed review payloads remain exact.

The complete first-native diagnostic is228UTF-8bytes, SHA256 `ea888111a0ba5bb1c03abb54753315c042052c53dadb685af2bf5c4b8262a3b9`. It reports the single old96:4composition elaboration mismatch, unresolved coordinate-pair/domain metavariables,RC1/oneerror/0warnings/noobject, naturally ended with preserved source/protected effects. This is retained failed evidence; it is not a proof pass, an uncertain in-flight operation, or a successful check to replay. No full remote receipt/log was downloaded by this context.

The exact old94–96replacement occurs once. The source equals applying the parent's frozen replacement, and reversing the replacement recovers the exact old315-line source. Prefix old/new1–93 and suffix old97–315/new99–317 are identical. The full original declaration head,23typed header values,preamble,closing,1public theorem,0newglobaldefinitions and7proof-data witnesses/lets are unchanged. No forbidden proof escape token appears.

## Affected mathematical and type review

The complete new94–98hunk is:

```lean
  have hrcoord (i j : Fin n) :
      Measurable (fun ξ : Fin n → Ω => r (ξ i) (ξ j)) := by
    have hpair : Measurable (fun ξ : Fin n → Ω => (ξ i, ξ j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hr.comp hpair
```

1. hrcoord's exact type remains `∀ i j:Fin n, Measurable(fun ξ:Fin n→Ω => r(ξ i)(ξ j))`. Its i,j are the existing universal finite indices. No binder or quantifier is narrowed, and no inequality between indices is assumed.
2. The explicit function expression has type `(Fin n→Ω)→Ω×Ω` and value `fun ξ:Fin n→Ω => (ξ i,ξ j)`. Its direct data captures are Ω,n and those bound i,j. Its domain measurable structure is `@MeasurableSpace.pi (Fin n) (fun _:Fin n => Ω) (fun _:Fin n => mΩ)`; its target is `mΩ.prod mΩ`. The implicit structures capture the same mΩ. It is the original coordinate pair, not a new data let, a chosen function or a replacement observation.
3. hpair has the exact proposition `Measurable(fun ξ:Fin n→Ω => (ξ i,ξ j))`. Its proof is precisely `(measurable_pi_apply i).prodMk (measurable_pi_apply j)`. Each Pi evaluation is measurable by the previously reviewed pinned Pi API; pinned prodMk accepts those two functions with the shared explicit domain and yields this product-valued function. No topology,Nonempty,separation,countable-generation or standard-Borel hypothesis on Ω is needed. i=j and equal observation values are allowed.
4. The old hr is still `Measurable(fun t:Ω×Ω => r t.1 t.2)`, selected from the same qualified actual h/μ model. With hpair typed, composition's intermediate type is Ω×Ω and domain is Fin n→Ω. Its function reduces definitionally to `fun ξ => r(ξ i)(ξ j)`. hpair's proof captures Ω,mΩ,n,i,j and canonical Pi/product structures; it captures no r,h,μ,extra sample or chosen inhabitant. The enclosing composition additionally uses hr/r, exactly as before.
5. The new named item hpair is a proof in Prop. The explicit pair function and the inverse-image predicates implicit in Measurable are data and were reviewed separately; they are not conflated with hpair's proof. No new theorem premise,local instance,data witness/global head or mathematical assumption appears. The named derived-Prop count is49 rather than48; the7explicit proof-data witnesses/lets remain F,Lrow,pdel,Dret,Jret,Bret,E.

The literal original h/μ/g/r/rho,normalizations,real guard functions and all header captures remain unchanged. The new hpair is scoped inside hrcoord; it is not exposed as assumed evidence to later proof steps.

## Interaction and complete317-line coverage composition

The exact hrcoord output type is unchanged, so the uses at new121,134,153 remain valid under the same arguments:

- hupper uses it for the sample-independent i<j branch of the actual residual sum; no diagonal or ordering assumption is added to hrcoord itself.
- hrrow uses it on each actual row summand over univ.erase i.
- hsample adds it to the same two g-coordinate functions in sampledKernel.

Those three consumers feed D,J,B1 and the literal centered row/physical/clipped measurability proof. All their source expressions are unchanged. The erased pair/row-square factorization obtains use the unchanged hr directly, so no deletion witness/capture or original n,n-1,n-2 coefficient is altered. The continuous cap and deletedTest retain legitimate full-sample dependence; only the signed deleted D/J/B1triple has the retained-coordinate factorization. The physical s=0 and clipped V=0 guards remain distinct. The repair supplies no zero-event probability,CDF,canonicality or law conclusion.

`COVERAGE.json` maps every new source line to its prior independent line coverage, except new94–98,which have fresh affected coverage. Unchanged old1–93 maps identically; old97–315 maps to new99–317. Its claim table reuses the prior47unaffected claim reviews with their exact unchanged source segments, replaces hrcoord by the five-line reviewed proof, and adds hpair. The header,7data capture graph,implicit predicates/instances,exact existing provider TYPEs and pinned context fields were mechanically compared with their old source-map values; all are identical. The63new proof lambda lines match the updated map: one new explicit coordinate-pair expression was added to the previously covered62lines. This composes full317SOURCEcoverage without repeating any complete accepted old proof review or old producer/AXcheck.

The original complete p40/p41/p51/p54reading and source-fidelity/API review remain those in the sealed initial REVIEW.md,COVERAGE.json and BINDING-VALIDATION.json. Their scope is unchanged. p51 remains an uncertified repair candidate,p54's rate/atom-safe payment repairs remain binding,and the external probability input remains attributed to Shao–Zhou2016. Unit219 is not imported and its qualification is not assumed. S27/CDF,atom/reflection,zero-denominator probability payments,S11/generalS15/DC/fullOQ56 remain OPEN.

One prior coverage-metadata defect was detected while composing by exact names: PowerShell's case-insensitive dictionary had copied the `hd` explanatory reason into the prior JSON's distinct `hD` record. The sealed original Markdown table correctly states both proofs, and their exact source/range records were already distinct. No old byte is changed. This repair's coverage uses case-sensitive names and the correct original Markdown reasons for both claims; METADATA-CORRECTION.json records this metadata-only correction. The first attempted composition stopped before writing a coverage file when its case-insensitive lookup compared `hd` against `hD`; the corrected ordinal lookup completes the exact-source check. This does not change proof coverage,source bytes or mathematical acceptance and triggers no old proof/check replay.

## Verdict and next gate

There is no affected mathematical,statement,type-capture or source-fidelity blocker. The repair's explicit type guidance is appropriate to the observed elaboration error. A successful new native result is still required; it cannot be inferred from this static assessment. After that, the exact first original object must receive all actual-owner TYPE/non-theorem VALUE and transitive AX evidence with whitelist propext/Classical.choice/Quot.sound. Return that evidence to this same never-author reviewer for final qualification. This affected packet releases its writers/heavy/inflight/pending/uncertain/children at zero after sealing; all previous source,evidence and failed receipts remain preserved.
