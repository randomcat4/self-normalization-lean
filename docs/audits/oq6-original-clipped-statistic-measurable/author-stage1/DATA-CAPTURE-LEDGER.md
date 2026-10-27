# Typed data and capture ledger

STAGE1_ONLY. This is a declaration/data inventory; it contains no proof body. The exact head is mirrored byte-for-byte in candidate-declarations-data.json. Every value below is fixed by the head or is an explicitly constrained existential output. There are no new global definitions, aliases, private declarations, header local instances or extra assumed data families.

## Caller data

| Name | Exact type | Origin and captures |
| --- | --- | --- |
| Ω | `Type u` | caller arbitrary observation type; captures none |
| mΩ | `MeasurableSpace Ω` | caller current measurable structure; may be the reduced m0, with no separation/countable-generation premise; captures Ω |
| μ | `@Measure Ω mΩ` | caller SAME original law in the current measurable structure; captures Ω, mΩ |
| h | `Ω → Ω → ℝ` | caller SAME original normalized kernel; captures Ω |
| n | `ℕ` | caller original sample size; never replaced by a deleted cardinality; captures none |
| z | `ℝ` | caller compact threshold, constrained by 0≤z≤1; captures none |
| C0 | `ℝ` | caller nonnegative original studentizer budget coefficient; captures none |

All other caller binders are Props, recorded in the JSON: IsProbabilityMeasure μ; hh; hh2; symmetry; joint mean zero; literal projection second integral one; n≥4; 0≤z≤1; C0≥0. Ω has no CountablyGenerated, standard Borel, separation or Nonempty instance.

## Fixed typed header values

| Name | Exact type | Exact value | Direct captures |
| --- | --- | --- | --- |
| g | `Ω → ℝ` | `fun o => ∫ y, h o y ∂μ` | Ω, mΩ, μ, h |
| r | `Ω → Ω → ℝ` | `fun o y => h o y - g o - g y` | Ω, h, g |
| v | `ℝ` | `∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)` | Ω, mΩ, μ, r |
| rho | `ℝ` | `Real.sqrt v` | v |
| N | `ℝ` | `Real.sqrt (n : ℝ)` | n |
| W | `(Fin n → Ω) → ℝ` | `projectionW n g` | n, Ω, g |
| V | `(Fin n → Ω) → ℝ` | `projectionV n g` | n, Ω, g |
| D | `(Fin n → Ω) → ℝ` | `residualStatisticD n r` | n, Ω, r |
| J | `(Fin n → Ω) → ℝ` | `residualEnergyJ n r` | n, Ω, r |
| Ddel | `(Fin n → Ω) → Fin n → ℝ` | `residualStatisticDDeleted n r` | n, Ω, r |
| Jdel | `(Fin n → Ω) → Fin n → ℝ` | `residualEnergyJDeleted n r` | n, Ω, r |
| A | `(Fin n → Ω) → ℝ` | `fun ξ => \|D ξ\|` | n, Ω, D |
| Adel | `(Fin n → Ω) → Fin n → ℝ` | `fun ξ i => \|Ddel ξ i\|` | n, Ω, Ddel |
| B1 | `(Fin n → Ω) → ℝ` | `studentizerClipBudget n r C0 rho 1` | n, Ω, r, C0, rho |
| B1del | `(Fin n → Ω) → Fin n → ℝ` | `studentizerClipBudgetDeleted n r C0 rho 1` | n, Ω, r, C0, rho |
| s2 | `(Fin n → Ω) → ℝ` | `centeredSq n g r` | n, Ω, g, r |
| s | `(Fin n → Ω) → ℝ` | `fun ξ => Real.sqrt (s2 ξ)` | n, Ω, s2 |
| d | `(Fin n → Ω) → ℝ` | `centeredDelta n g r` | n, Ω, g, r |
| e | `(Fin n → Ω) → ℝ` | `clippedCenteredDelta n g r C0 rho 1` | n, Ω, g, r, C0, rho |
| Tclip | `(Fin n → Ω) → ℝ` | `clippedCenteredStatistic n g r C0 rho 1` | n, Ω, g, r, C0, rho |
| Tactual | `(Fin n → Ω) → ℝ` | `fun ξ => if s ξ = 0 then 0 else (W ξ + D ξ) / s ξ` | n, Ω, s, W, D |
| cap | `(Fin n → Ω) → Fin n → ℝ` | `fun ξ i => min (\|g (ξ i)\| / N) (1 / (1 + z))` | n, Ω, g, N, z |
| deletedTest | `(Fin n → Ω) → Fin n → ℝ` | `fun ξ i => cap ξ i * (\|A ξ - Adel ξ i\| + z * \|B1 ξ - B1del ξ i\|)` | n, Ω, cap, A, Adel, z, B1, B1del |

There are 23 typed header values. D/Ddel/J/Jdel/B1/B1del use the same residual and original n. e is the studentizer clip; cap is the separate continuous compact coordinate weight. Tactual has the physical s=0 guard; Tclip retains the library's V=0 guard. No sample measure is replaced or invented: this statement is measurable-function/data preparation only. At each later law use the sample measure is the same Measure.pi of the selected current μ.

## Derived data appearing in the conclusion

- `zeroVSet : Set (Fin n → Ω) := {ξ : Fin n → Ω | V ξ = 0}`; captures n, Ω, V.
- `zeroStudentizerSet : Set (Fin n → Ω) := {ξ : Fin n → Ω | s ξ = 0}`; captures n, Ω, s.
- `capAtDeletedIndex : (Fin n → Ω) → ℝ := fun ξ : Fin n → Ω => cap ξ i`; captures n, Ω, cap, i.
- `DdelAtDeletedIndex : (Fin n → Ω) → ℝ := fun ξ : Fin n → Ω => Ddel ξ i`; captures n, Ω, Ddel, i.
- `JdelAtDeletedIndex : (Fin n → Ω) → ℝ := fun ξ : Fin n → Ω => Jdel ξ i`; captures n, Ω, Jdel, i.
- `AdelAtDeletedIndex : (Fin n → Ω) → ℝ := fun ξ : Fin n → Ω => Adel ξ i`; captures n, Ω, Adel, i.
- `B1delAtDeletedIndex : (Fin n → Ω) → ℝ := fun ξ : Fin n → Ω => B1del ξ i`; captures n, Ω, B1del, i.
- `deletedTestAtDeletedIndex : (Fin n → Ω) → ℝ := fun ξ : Fin n → Ω => deletedTest ξ i`; captures n, Ω, deletedTest, i.
- `deletedRestriction : {j : Fin n // j ≠ i} → Ω := fun j : {j : Fin n // j ≠ i} => ξ j.val`; captures n, Ω, i, ξ.
- `literalDeletedTriple : ℝ × ℝ × ℝ := (Ddel ξ i, Jdel ξ i, B1del ξ i)`; captures Ddel, Jdel, B1del, ξ, i.

The six functions indexed by i are actual full-sample observables. In particular cap and deletedTest capture ξ_i and are never claimed to be deleted functions. Only the E identity claims retained-coordinate factorization for Ddel/Jdel/B1del.

## Existential and bound data

For every i:Fin n, E has exact type `({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ`. It is an existential result, not an extra hypothesis or a global selected family. Its value is not implemented in stage1. The head constrains every value on a retained sample by the exact triple identity. Its permitted captures are Ω,mΩ,n,r,C0,rho,i (and their transitive h/μ/g definitions); forbidden captures are ξ_i, a filler/default observation, a replacement kernel or law.

The proposed witness recipe uses the two existing existential factors: F_i:(deleted sample)→ℝ for the erased unordered-pair sum and Λ_i:(deleted sample)→ℝ for the erased row-square sum. Then E_i(q)=(F_i(q)/(N*(n-1)), Λ_i(q)/(n-2)^2, C0*((1+rho)/N+(Λ_i(q)/(n-2)^2)/((1+rho)*N))). This records a route/data recipe only, with no Lean proof term or source body. The exact implementation and every proof-local data value remain subject to parent freeze and final VALUE review.

Universal observation/sample/index binders are Ω-valued o,y; pair t:Ω×Ω; ξ:Fin n→Ω; i:Fin n; and retained j:{j:Fin n//j≠i}. Their values are caller/universal inputs, not chosen witnesses. There is no universal arbitrary statistic T, arbitrary D1/D2, p-moment family, existential measure or existential original kernel in the candidate.

## Implicit structures

- `sampleMeasurableSpace : MeasurableSpace (Fin n → Ω) := @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)`; captures n, Ω, mΩ.
- `deletedSampleMeasurableSpace : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) := @MeasurableSpace.pi {j : Fin n // j ≠ i} (fun _ => Ω) (fun _ => mΩ)`; captures n, Ω, mΩ, i.
- `pairMeasurableSpace : MeasurableSpace (Ω × Ω) := mΩ.prod mΩ`; captures Ω, mΩ.
- `realMeasurableSpace : MeasurableSpace ℝ := borel ℝ`; captures none.
- `tripleRealMeasurableSpace : MeasurableSpace (ℝ × ℝ × ℝ) := (borel ℝ).prod ((borel ℝ).prod (borel ℝ))`; captures none.
- `finiteIndices : Fintype (Fin n) := canonical existing Fin n instance`; captures n.
- `finiteDeletedIndices : Fintype {j : Fin n // j ≠ i} := canonical existing finite subtype instance`; captures n, i.

Real field/topology/sqrt/order instances and finite-index decision data are existing imported canonical instances. The imported centeredDelta uses its existing Classical.propDecidable guard. No new local instance, axiom or mathematical assumption is introduced. Parent-provided actual TYPE context remains the authority for elaborated dependencies; source heads alone are not claimed as a new machine certificate.
