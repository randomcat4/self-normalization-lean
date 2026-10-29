# Unit276 frozen private finite bridge: complete author derivation

Status: AUTHOR_PROOF_COMPLETE_STATIC_ONLY. The frozen finite identity has a complete author proof body. Neither this body nor the finite-only scratch assembly has been compiled or independently accepted. Both are NOT_CHECKED_NOT_MAIN276. No mathematical root, full OQ56 or main276 completion is claimed.

The author is `/root/oq56_unit276_author`, prescribed `gpt-6.1-sol` with `xhigh`. Actual backend, actual model, actual effort, input tokens, cached input tokens, output tokens and reasoning-subset tokens are unexposed and recorded as null. There is no quota or subscription estimate.

## Exact declaration and scope

The private declaration is exactly `finite_physical_centered_projection_bridge`, frozen in the 773-byte/14-LF HEAD with SHA256 `ef857d3c6621f1b2b5416e0a043764f9e09a0320a6cea5222e3dc02c738d9606`. The only mathematical hypotheses are `4 ≤ n` and pointwise symmetry of `h`. The type `Ω` and the real function `g` are arbitrary. The residual is the actual pointwise definition `r a b = h a b - g a - g b`.

The conclusion equates the actual finite-row statistic `sqrt(n) * U / sqrt(R2)`, guarded by `0 < R2`, with `(projectionW + residualStatisticD) / s`, guarded by `s = 0`, where `s = sqrt(centeredSq)`. The U-statistic, jackknife square and centeredSq are exactly the imported public definitions. No alternate jackknife coefficient, uncentered row square, law, expectation or asymptotic statistic is substituted.

The original 297-byte/10-LF PRE is unchanged. The parent approved one separate lexical supplement, `open Shao.OQ5.P51`, in AMENDMENT.json (1434 bytes, SHA256 `ab5dd05ca477097145dd298d637c06f8614fdcd9227fdded7213878e254c715b`). OPEN.txt is 18 bytes/1 LF with SHA256 `51b4a1e0b3a318df1db7471e31787a78cff6f46c6e072d73d69bcd318a9fcb4f`. The original imported273 source's own `open` is not assumed to export lexical context. The scratch order is exactly PRE + OPEN + HEAD + PROOF + two closing lines. This supplement changes name resolution to the intended public P51 definitions and adds no premise or resource option.

## Complete mathematical derivation

Fix an arbitrary sample ζ. Write `N = (n : ℝ)`, `G = ∑ i, g (ζ i)` and `F = originalUpper n r ζ`. These are explanatory abbreviations; no additional Lean definitions or assumptions are introduced.

1. The given pointwise symmetry of h implies pointwise symmetry of r: subtracting `g a + g b` from `h a b` commutes under swapping a and b. Independently, `sampledKernel n g r ζ` equals the actual sample kernel `(i,j) ↦ h (ζ i) (ζ j)` by the definition of r and the ring identity `g a + g b + (h a b - g a - g b) = h a b`. This equality holds at every pair, including diagonal indices and repeated observations.
2. Since n ≥ 4, N > 0, N ≠ 0, N - 1 ≠ 0 and sqrt(N) ≠ 0. Also `sqrt(N)^2 = N`.
3. Apply the public qualified `Shao.OQ5.P51.sampled_uStatistic_formula n g r ζ hrsymm hn`. After replacing sampledKernel by the actual kernel, it gives `U ζ = 2G/N + 2F/(N*(N-1))`. Expanding only projectionW and residualStatisticD, clearing the justified nonzero denominators, and using `sqrt(N)^2 = N` yields `projectionW n g ζ + residualStatisticD n r ζ = sqrt(N) * U ζ / 2`.
4. The public `Shao.OQ6.FiniteRows.jackknifeSq_nonneg` gives `R2 ζ ≥ 0`; its n ≥ 3 requirement follows from n ≥ 4. By the public definition of centeredSq and the same pointwise sampled-kernel equality, `centeredSq n g r ζ = R2 ζ / 4`. Consequently `s ζ ≥ 0` and `(s ζ)^2 = R2 ζ / 4`.
5. Both `sqrt(R2 ζ)` and `2 * s ζ` are nonnegative. Their squares agree because `sqrt(R2 ζ)^2 = R2 ζ = 4 * (s ζ)^2`. The ordered square equality therefore gives `sqrt(R2 ζ) = 2 * s ζ` without a sign ambiguity.
6. If `s ζ = 0`, its squared identity gives `R2 ζ = 0`. The physical guard `0 < R2 ζ` is false and the centered guard `s ζ = 0` is true, so both sides are exactly zero. No cancellation by s occurs in this branch.
7. Otherwise, nonnegativity gives `s ζ > 0`; its squared identity then gives `R2 ζ > 0`. Both nonzero branches are selected. Substituting the numerator and square-root identities reduces the conclusion to `sqrt(N) * U ζ / (2*s ζ) = (sqrt(N)*U ζ/2) / s ζ`, which follows by field algebra with `s ζ ≠ 0`.

This proves the entire frozen pointwise finite conclusion at author level. There is no probability or AE premise hidden in any step.

## Public dependencies and provenance

The proof calls the public `sampled_uStatistic_formula` and `jackknifeSq_nonneg`, unfolds public `sampledKernel`, `projectionW`, `residualStatisticD` and `centeredSq`, and uses standard square-root/order/finite-algebra tactics. Their relevant exact source types and definitions were completely read in the 742-LF P51 geometry and 103-LF FiniteRows inputs. The physical finite-row quantities retain the exact source unordered off-diagonal pair convention and centered jackknife coefficient.

The complete qualified273 source and frozen HEAD were read. Its hnum/hscale calculation was used only as an algebraic recipe. No private273 lemma is called. Its hypotheses about measures, normalization, moments and conditional models are not imported into this declaration. Its source/qualification receipts were not rerun or rewritten. The supplied public import chain is retained as frozen contextual assembly, not as a claim that the273 theorem is an additional finite-bridge hypothesis.

There is no read or use of a275 private helper, no dependence on unqualified275 and no call to a275 theorem. Main276 remains unfrozen pending its separately qualified275 actual TYPE and is not implemented here. This finite identity establishes neither a tail payment nor an AE-to-pointwise projection upgrade. It is a supporting finite identity, with no novelty certification.

## Quantifiers and boundaries

- The sample is arbitrary, not an almost-everywhere sample. No measurable-space structure, probability measure, integral, mean-zero condition, projection normalization, integrability, variance lower bound or canonicality is required.
- The function g is arbitrary. It need not be the Hoeffding projection. Reconstruction of the physical kernel is purely definitional.
- The endpoint n = 4 is covered by the same n-positive and N-1-nonzero arguments. No stronger integer lower bound is inserted.
- Repeated sample values, ties, diagonal values and either sign of h and g are allowed. The public finite-row definitions exclude diagonal indices where prescribed; the sampled-kernel equality itself is valid even on the diagonal.
- Degenerate `R2 = 0` and `s = 0` cases are explicitly covered. Negative R2 is excluded by the public nonnegativity theorem, not by an added premise. No numerator cancellation or convention at zero is assumed.
- Empty Ω needs no special inhabitance premise: the statement is universally quantified over samples and introduces no chosen observation.

## Static verification and remaining gates

PROOF.txt is the complete 75-LF body starting with `:= by`. The scratch source has one explicit private declaration and is exactly the frozen-context assembly recorded in DECLARATION-ASSEMBLY.json. The complete body is partitioned without gaps or overlaps into the finite derivation steps; generated owner names/counts are unknown until the later actual complete-module audit and are not guessed.

STATIC-CHECKS.json records strict UTF-8, no BOM, LF-only text, one final LF, exact frozen PRE/OPEN/HEAD byte assembly, complete body assembly, one allowed `set_option autoImplicit false`, no other resource options and absence of forbidden proof escapes. These are static text checks only. They do not establish elaboration, kernel success, actual TYPE ownership, transitive axioms or independent mathematical review.

No local Lean/toolchain probe, compilation, smoke check, AX check, server/SSH call, transfer, network call, Git/API publication, child creation, Goal, schedule, sidebar, proxy or resource-setting change occurred. Explicit task restrictions supersede the skill's default preference for immediate mechanical checking. No standalone helper compilation or prefix acceptance is requested or planned. The parent may later insert the exact bridge into the complete276 source only after the main declaration freeze and required independent complete SOURCE review. The resulting complete source still requires the authorized server native/all-actual-owner/recursive-axiom gates and qualified independent final review.

All ten original bindings were verified before the first author write. The two additional parent amendment inputs were also read and verified before assembly. All original frozen, qualified, shared and other-owner files remain untouched. The first write was READ_ACK.json inside this role's sole new directory. Final unique LASTFINALWRITE.json releases all assigned author/write/review/execution/child/publication authority, records six zero runtime counts and no active wait, and ends this ordinary turn.
