# Actual marked odd/even pair IBP — independent final review

STATUS: **CORRECT**. No critical gap or required fix.

Reviewer: /root/common_marked_pair_review, fresh independent gpt-6.1-sol / xhigh; math-theorem, no math-ultra. Author/reviewer separation preserved. This review covers only the frozen module below and reuses its successful exact-source server gates.

## Exact accepted version

- Commit: b32cfa951e60c00e9d289b21cb32896038bf96c0; parent a0f8ba9118e91f701b39db3b4e0abcddabb31992.
- Module: Shao/Probability/SourceOddEvenMarkedIBP.lean; 28,423 bytes, 513 lines.
- Source SHA256: 37cbf000078f4b60e383a0b736df9c718810a55b983f7c2d7288fba3bb15a414.
- Object SHA256: 814d8a4a7fec3af1e42a586daf9fa31de6a4757f9307cd17bcf53148bc51e452.
- Local draft, server source and the frozen commit blob are equal. The commit changes only this module. Source is UTF-8 without BOM, LF only, zero CR.
- Both complete public headers are byte-identical to the root-frozen candidate, excluding the proof marker and surrounding whitespace. Their header hashes are recorded in the JSON report. A later branch HEAD does not expand this acceptance.

All source/proof lines 1–513 were read. All 32 actual owned types were read: 2 public, 19 private handwritten and 11 generated theorems, with zero definition values. Display folding was confined to 606 standard instance subtrees; all mathematical parameters, measures, quantifiers, guards and infinity remained explicit. The original full export was untouched and has no U+22EF/U+2026 truncation marker. The JSON contains an individual unabridged type hash, axiom list, source range and verdict for every owned constant.

## Original source and statement fidelity

The read-only supplement SHA256 is b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd. Complete ranges LF2340–2376 and LF2554–2595 were read, including the actual D/E inversion formulas and LF2570–2583 whole-line twice-IBP passage.

Both public theorems preserve the actual probability law, third absolute moment, positive variance, positive support radius h and almost-everywhere support bound. They quantify over every natural m, including 0, every real q, every positive y and the closed guard |w| ≤ y/16. They state actual real o' and standard nested real e'' and actual nested u derivatives of D and W=uE. There is no supplied inverse, regularity, decay, pair-L1, centering or symmetry premise.

The true amplitudes are chi(r)/(sqrt(r)+w/y)^2 and chi(r)/(sqrt(r)-w/y)^2. The actual sine shifts are w and -w. The outside phase is exp(+i*v*q), while the r-integrated mark retains exp(-i*v*r). The identity is valid beyond the source's later regional-estimate parameter restrictions; no bound or probability conclusion is inferred from that broader equality scope.

## Complete proof check

1. **Joint measurability, lines 12–57 and 381–389.** The actual raw/full characteristics and actual sine mark are parameter integrals of jointly measurable integrands. Difference quotients with s(n)=1/(n+1)>0 converge pointwise to the actual derivative on every differentiable v slice. Applying this twice gives genuine joint measurability of the actual second u derivative. The reflected raw characteristic uses the correct (v,-u) substitution. Actual full-law probability instances are obtained from the existing law producer.

2. **True marked pair L1, lines 59–107.** At fixed u, the actual mark-v norm theorem pays the v integral. With a nonnegative envelope B independent of v,
   integral_v ||G(u,v)|| ≤ C*M*y*|u|*B(u).
   The accepted envelope's k=1 moment pays the remaining u integral, and joint measurability permits integrable_prod_iff. This proves actual absolute integrability on volume of R×R, including u=0. The proof does not integrate the v-independent envelope over the whole v line.

3. **Fixed-v u/r Fubini, lines 109–181.** The actual r mark is dominated by |a(r)|. For each fixed v, the two-variable pre/post-IBP integrands are dominated by ||F(u)||*|a(r)| and the corresponding actual second-derivative product. Genuine product L1 pays both u/r exchange directions. Neither this helper nor its use claims absolute integrability in (r,u,v).

4. **Cutoff, amplitude and phase payment, lines 183–270.** The sine/cosine identity keeps the exact half factor and both shifts. The accepted amplitude family at k=2 supplies the global actual quotient, smoothness, compact support and actual derivative bounds through order 2; it also handles denominator zeros away from cutoff support. Positive y gives |w/y|≤1/16. On actual cutoff tsupport, r>1/16 gives sqrt(r)>1/4, so both actual phases y*sqrt(r)±w>3y/16>0. The helper concludes the nonzero phase needed by whole-line IBP. Where chi(r)=0 both quotient expressions vanish by totalized division; otherwise the genuine phase and denominator are nonzero. Exact algebra factors out -y^-2.

5. **From fixed-v identity to the pair identity, lines 272–379.** Each actual nonzero r phase receives the accepted full-real-line twice-IBP identity. The two shifts yield (-1/2)*y^-2 times their sum. The actual pre-IBP pair-L1 comes from the existing odd/even inverse; both actual post-IBP pair-L1 statements are paid independently by the genuine mark-v bounds and the uniform-v second-derivative envelope. Only these genuine pair-L1 facts are used for the final u/v exchange, v integration and addition. No slice-L1 claim is substituted for pair-L1.

6. **Actual odd/even public consumers, lines 391–511.** The odd proof consumes the actual D'' envelope (the third norm bound). The even proof consumes the actual W'' envelope (the sixth norm bound), with W=uE and exact product rearrangement. Both generic helper premise sets are paid by actual producers with the same probability/moment/support hypotheses. Multiplying the inherited coefficients 2i/(2pi)^2 and -2/(2pi)^2 by (-1/2)y^-2 gives exactly -i/((2pi)^2*y^2) and +1/((2pi)^2*y^2). No factor 2, sign, u factor, shift or phase is discarded.

The eleven generated types were separately inspected: complement/singleton membership, two copies of a+(-b)=a-b, explicit nonzero numerals 2/3/4, nonzero product, natural and integer powers of nonzero elements, and Nat.cast(n)+1 under characteristic zero. All actual binders and instance hypotheses match the standard relations. The JSON records all 32 individual decisions.

## Exact server evidence reused

Pinned Lean is leanprover/lean4:v4.36.0-rc1; mathlib is 807d3836b165983210ee2ecf3cd28f239436949c. The author used CPU10–13, root-heavy.lock and -M8192 -j4 -DautoImplicit=false. No reviewer Lean/build/audit rerun, cache scan or cache mutation was performed.

- Author receipt SHA256: a55b6a3d63b54f57353429260be44a48d117e9228c1e262b0f267c6adb676f07.
- Original execution exits JSON SHA256: 0372b64a8837c2ca7dc948c53f4f171683b7cf8546209418b0e603ac139aa034; object, owned-axiom and actual-type export exits are all 0.
- Both targeted/object logs SHA256: fba92798401e89109ac7d84c8cea11527992a1f6b153b3c1d2aada0eebf025a2. Each contains only the known mathlib local-changes warning.
- Complete actual-owned type log: 199,450 bytes, SHA256 0907320cac6a8c0e02fe2688e5958e23ae695e4e94840fa1edd7b4cb7908011b.
- Owned audit JSON SHA256: 5283b78ecd3ea70bc71e8939bd5f39831b2bbceb956870615e9b71ca850af65a; audit log SHA256 e313550da02184f6e35d0150eb44b1ca749a13680509126a38009ddede00418a.

Both audit/export scripts were fully read. Exact module ownership selects every public/private/generated constant, and collectAxioms is transitive for every selected declaration. The 32 exported names equal the audit set; all name/kind/axiom rows in JSON and log agree. The union is contained in propext, Classical.choice and Quot.sound. No sorry/admit/new axiom/unsafe/native_decide occurs in the source.

The complete consumed declarations and exact source/object hashes of SourceOddEvenWholeLineIBP, SourceFutureNoiseOddEven, SourceKernelAmplitudeFamily and SourceMarkFourierNorms were checked against their existing independent CORRECT reviews. Their old proofs were not commissioned for another review. The accepted actual cutoff interface and its source hash were also checked.

## Acceptance boundary and runtime

Accepted: the two exact frozen actual marked pair IBP identities, both genuine post-IBP pair-L1 outputs, and the complete owned/private/generated proof/type/axiom coverage above.

This closes neither quantitative marked regional estimates nor probability/C1/C2 roots. It does not certify an (r,u,v) triple absolute-L1 assertion or a novelty claim. Remaining quantitative regional assembly, probability consumers and the remaining inversion/desmoothing chain stay open.

Only this review Markdown and its JSON were written. No source was changed, no subagent was created and no server/Lean command remains in flight. Assigned review COMPLETE; reviewer released. Exact usage counters are unavailable and no subscription-percentage allocation is inferred.
