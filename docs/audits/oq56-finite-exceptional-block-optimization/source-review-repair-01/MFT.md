# Unit277 repair01 independent fidelity and failure-to-repair mapping

The accepted SOURCE hash is `0073a6b41714f383603bd0b332da818a6862527d688cc9afd788c703844ecc42`, 15694B/371LF. `sourceAccepted=true`, `kernelChecked=false`, `qualified=false`. Every diagnostic SHA256 and new-line slice below was independently verified against the complete saved native01 diagnostic text and revised source. "Covered" means affected mathematical SOURCE review, not a successful new compiler result.

| Actual old diagnostic | New source lines | Independent mathematical/API finding |
|---|---|---|
| #1, old76, H02 ordered-add type mismatch | 76–78 | Definitionally expose ap; N>=0 times a<=max(a,0) supplies Na<=Nap; linear arithmetic adds the same arbitrary Ky on both sides. No reversed-add API shape remains. |
| #2, old133, H03 local N cast | 136–137 | `change` exposes real n cast; exact_mod_cast still uses only n>=2. |
| #3, old136, H03 local M cast | 141–142 | `change` exposes real B.card cast; positivity comes from the original B.Nonempty. |
| #4, old137, H03 local K cast | 144–145 | `change` exposes real A.card cast; Nat.zero_le allows K=0. |
| #5, old193, H03 residual T/N/X equality | 202 | Only the local N/X definitions are additionally unfolded after Q>0 has already been proved; actual Q guard, original numerator and sqrt factors remain identical. |
| #6, old207, H03 0^2 normalization | 215 | pow_two and zero_mul reduce 0^2 to0 without a conditional exponent lemma; (N-1)C remains nonnegative from existing facts. |
| #7, old247, H04 local N cast | 256–257 | Exposes real n cast, retaining the same n>=4 hypothesis and all original denominator conditions. |
| #8, old270, H04 mixed n/N numerator denominators | 286–288 | Definitionally normalizes c's complete original denominator to (N-1)(N-2), preserving F, N*c and D; field algebra clears only proven nonzero denominators. |

The old native source was `d183e84abbb1d37364b3272f465150e1018a5a60349a5b7eb2afd56783265939`. Its RC1/8errors/6warnings/noobject outcome is preserved. The repair map has eight diagnostic entries but seven actual diff hunks because adjacent M/K cast fixes share a hunk. Independent old/new proof comparison gives exactly H02 30 LF, H03 110 LF, H04 62 LF changed/full-review scope =202 LF; H01 48 LF and H05 30 LF are identical/reused =78 LF.

| Primary/supplier anchor | Preserved object and changed-proof interaction |
|---|---|
| p41:65–70; P35.mean/center | Actual complementary finite B/A, arithmetic block means, actual Qb and full centered Q. H03's casts do not alter these definitions. |
| p41:73–80, (3) | H02's exact weighted completion and H03's derived-Q optimization retain positive part and factors n-1,n,k/m. K=0 and negative a/y remain included; H02 needs no N=M+K premise. |
| p41:80; exact unchanged H01 | Q=Qb+QA+MK/N*y^2. Empty A is handled without dividing by K; H03 consumes the same exact interface. |
| p41:82 | Abstract deterministic relaxation and the same actual b,F substitution; no g/r independence or realization of every optimizing vector. |
| p51:18–29; P51 W/D/residualU | psi/(n-2), F unordered-pair sum and D=F/[sqrt(n)(n-1)] unchanged. H04 numerator normalization preserves every factor. |
| FiniteRows original jackknife; P51 centeredSq_eq_center_sum | Original centered-row denominator gives s^2=Q/(n-1), R_h=2s; H04 still covers zero Q/s even for nonzero numerator. |
| Exact unchanged H05 | Consumes identical frozen H03/H04 conclusions with the same actual b,F,c,s,T; actual scope remains n>=4/card B>=3/Qb>0. Actual n=3 is excluded explicitly. |
| p41(4)–(5), sections4–7; p51 later probability interfaces | No new conclusion. Background comparison, conditional interaction, weighted rare-block integration and full original-mu PE-R remain outside this source acceptance. |

The complete previous primary/proposal/interface reading and unchanged supplier qualification are reused by exact binding. This phase rereviews all changed proof semantics and interactions, not all old accepted proofs. No additional assumption, definition, helper, zero guard, option, external CDF contract or desired tail payment enters the frozen source.
