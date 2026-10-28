from pathlib import Path
import re

B = Path('C:/game/shao lean')
O = B / 'drafts/oq56/unit255/author-01'
F = B / 'drafts/oq56/unit255/freeze-01'
old = (B / 'library/Shao/OQ6/OriginalClippedCanonicalCostPacket.lean').read_text(encoding='utf-8')
body = old.split(':= by\n', 1)[1].split('\nend\n', 1)[0] + '\n'
body = body.replace('OriginalClippedCanonicalCoding.actual_original_clipped_canonical_normalized_coding',
                    'OriginalLevelDependentCanonicalCoding.actual_original_level_dependent_canonical_normalized_coding')
body = body.replace('intro n hn C0 hC0 ε hε hεsmall',
                    'intro n hn y hy hywindow ε hε hεsmall')
body = body.replace('hfor n hn C0 hC0 ε hε hεsmall',
                    'hfor n hn y hy hywindow ε hε hεsmall')
body = body.replace('B1del', 'Bdelete').replace('B1', 'B')
body = body.replace('    J A Adel B deletionMass deletionTotal\n',
'''    J A Adel B deletionMass deletionTotal
    ξ0 S0 S0delete Sν Sνdelete fullTest0 deleteTest0 fullTestν deleteTestν
    Ioriginal Ireduced Icoded costOriginal costReduced costCoded
''')
a = body.index('  have hcost :=\n')
b = body.index('  let τ :', a)
body = body[:a] + '''  have hcost :=
    @Shao.OQ6.OriginalLevelDependentCorrectionEnvelope.actual_original_level_dependent_correction_envelope
      Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy hywindow
  dsimp only at hcost
  rcases hcost with
    ⟨_, _, _, _, hAIP, hAdelIP, hBIP, hBdeleteIP, heIP,
      hFullBounds, hDeletedBounds, _⟩
  change Integrable A P at hAIP
  change ∀ i : Fin n, Integrable (fun ζ : Fin n → Ω => Adel ζ i) P at hAdelIP
  change Integrable B P at hBIP
  change ∀ i : Fin n, Integrable (fun ζ : Fin n → Ω => Bdelete ζ i) P at hBdeleteIP
  change Integrable D2 P at heIP
  change ∀ ζ : Fin n → Ω, 0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |D2 ζ| ≤ B ζ at hFullBounds
  change ∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ Adel ζ i ∧ 0 ≤ Bdelete ζ i at hDeletedBounds
''' + body[b:]
body = body.replace('C0 * (((1 + rho) * 1) / N + J ζ / ((1 + rho) * 1 * N))',
                    '512 * (((1 + rho) * y) / N + J ζ / ((1 + rho) * y * N))')
body = body.replace('((1 + rho) * 1 * N)', '((1 + rho) * y * N)')
body = body.split('  refine ⟨hP₀prob, hP₀map, hO, hOindep, hgcoord, hgenergy,', 1)[0]
suffix = '''  have hAugDeleted (i : Fin n) :
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Adel (q x) i) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Bdelete (q x) i) ∧
      Integrable (fun x : Fin n → Ω × ℝ => Adel (q x) i) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => Bdelete (q x) i) ν ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |B (q x) - Bdelete (q x) i|) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ∧
      Integrable (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => |B (q x) - Bdelete (q x) i|) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ν := by
    rcases hDiff i with ⟨hADm, hBDm, hMassm, hADi, hBDi, hMassi⟩
    exact ⟨(hAdelm i).comp hqpres.measurable,
      (hBdeletem i).comp hqpres.measurable,
      hqpres.integrable_comp_of_integrable (hAdelI i),
      hqpres.integrable_comp_of_integrable (hBdeleteI i),
      hADm.comp hqpres.measurable, hBDm.comp hqpres.measurable,
      hMassm.comp hqpres.measurable,
      hqpres.integrable_comp_of_integrable hADi,
      hqpres.integrable_comp_of_integrable hBDi,
      hqpres.integrable_comp_of_integrable hMassi⟩
  have hweighted :=
    @Shao.OQ6.OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost
      Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy hywindow 512 (by norm_num)
  dsimp only at hweighted
  rcases hweighted with ⟨hIoriginalPos, hFullOriginalI, hDeleteOriginalI,
    hCostOriginalNonneg, hCostOriginalBound⟩
  change 0 < Ioriginal at hIoriginalPos
  change Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P at hFullOriginalI
  change ∀ i : Fin n,
    Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P at hDeleteOriginalI
  change 0 ≤ costOriginal at hCostOriginalNonneg
  change costOriginal ≤
    64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
      (1 + y) ^ 3 / Real.sqrt (n : ℝ) at hCostOriginalBound
  have hξ0m (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) :=
    (hgcoord i).1.comp (hO i).1
  have hphase0m (j : Fin n) : Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2) :=
    ((hξ0m j).const_mul y).sub
      ((((hξ0m j).const_mul y).pow_const (2 : ℕ)).div_const 2)
  have hS0m : Measurable[mN₀, borel ℝ] S0 :=
    Finset.measurable_sum Finset.univ (fun j _ => hphase0m j)
  have hS0deletem (i : Fin n) :
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => S0delete ζ i) :=
    Finset.measurable_sum (Finset.univ.erase i) (fun j _ => hphase0m j)
  have hcap0m (i : Fin n) : Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => min |y * ξ0 i ζ| 1) := by
    simpa only [Real.norm_eq_abs] using
      ((hξ0m i).const_mul y).norm.min measurable_const
  have hFullWeightedm : Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => fullTest0 ζ * Real.exp (S0 ζ)) :=
    ((hAm.const_mul y).add (hBm.const_mul (y ^ 2))).mul hS0m.exp
  have hDeleteWeightedm (i : Fin n) : Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => deleteTest0 ζ i * Real.exp (S0delete ζ i)) :=
    ((hcap0m i).mul ((hDiff i).1.add ((hDiff i).2.1.const_mul y))).mul
      (hS0deletem i).exp
  have hSνpoint (x : Fin n → Ω × ℝ) : Sν x = S0 (q x) := by
    rfl
  have hSνdeletepoint (i : Fin n) (x : Fin n → Ω × ℝ) :
      Sνdelete x i = S0delete (q x) i := by
    rfl
  have hFullReducedI : Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P₀ := by
    apply (hId.integrable_comp hFullWeightedm.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hFullOriginalI
  have hDeleteReducedI (i : Fin n) :
      Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P₀ := by
    apply (hId.integrable_comp (hDeleteWeightedm i).aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hDeleteOriginalI i
  have hFullCodedI : Integrable (fun x => fullTestν x * Real.exp (Sν x)) ν := by
    simpa only [Function.comp_def, fullTestν, hSνpoint] using
      hqpres.integrable_comp_of_integrable hFullReducedI
  have hDeleteCodedI (i : Fin n) :
      Integrable (fun x => deleteTestν x i * Real.exp (Sνdelete x i)) ν := by
    simpa only [Function.comp_def, deleteTestν, hSνdeletepoint] using
      hqpres.integrable_comp_of_integrable (hDeleteReducedI i)
  have hIreducedEq : Ireduced = Ioriginal := by
    change (∫ ζ, Real.exp (S0 ζ) ∂P₀) = ∫ ζ, Real.exp (S0 ζ) ∂P
    rw [hP₀map]
    exact integral_map hidN.aemeasurable hS0m.exp.aestronglyMeasurable
  have hIcodedEq : Icoded = Ioriginal := by
    change (∫ x, Real.exp (S0 (q x)) ∂ν) = Ioriginal
    calc
      _ = ∫ ζ, Real.exp (S0 ζ) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable hS0m.exp.aestronglyMeasurable).symm
      _ = Ireduced := by rw [hqpres.map_eq]
      _ = Ioriginal := hIreducedEq
  have hIreducedPos : 0 < Ireduced := by
    rw [hIreducedEq]
    exact hIoriginalPos
  have hIcodedPos : 0 < Icoded := by
    rw [hIcodedEq]
    exact hIoriginalPos
  have hFullReducedEq :
      (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) =
        ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P := by
    rw [hP₀map]
    exact integral_map hidN.aemeasurable hFullWeightedm.aestronglyMeasurable
  have hFullCodedEq :
      (∫ x, fullTestν x * Real.exp (Sν x) ∂ν) =
        ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P := by
    change (∫ x, fullTest0 (q x) * Real.exp (S0 (q x)) ∂ν) = _
    calc
      _ = ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable hFullWeightedm.aestronglyMeasurable).symm
      _ = ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀ := by rw [hqpres.map_eq]
      _ = _ := hFullReducedEq
  have hDeleteReducedEq (i : Fin n) :
      (∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) =
        ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P := by
    rw [hP₀map]
    exact integral_map hidN.aemeasurable (hDeleteWeightedm i).aestronglyMeasurable
  have hDeleteCodedEq (i : Fin n) :
      (∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) =
        ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P := by
    change (∫ x, deleteTest0 (q x) i * Real.exp (S0delete (q x) i) ∂ν) = _
    calc
      _ = ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable
          (hDeleteWeightedm i).aestronglyMeasurable).symm
      _ = ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀ := by rw [hqpres.map_eq]
      _ = _ := hDeleteReducedEq i
  have hCostReducedEq : costReduced = costOriginal := by
    simp only [costReduced, costOriginal, hIreducedEq, hFullReducedEq, hDeleteReducedEq]
  have hCostCodedEq : costCoded = costOriginal := by
    simp only [costCoded, costOriginal, hIcodedEq, hFullCodedEq, hDeleteCodedEq]
  have hCostReducedNonneg : 0 ≤ costReduced := by
    rw [hCostReducedEq]
    exact hCostOriginalNonneg
  have hCostCodedNonneg : 0 ≤ costCoded := by
    rw [hCostCodedEq]
    exact hCostOriginalNonneg
  have hCostReducedBound : costReduced ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
        (1 + y) ^ 3 / Real.sqrt (n : ℝ) := by
    rw [hCostReducedEq]
    exact hCostOriginalBound
  have hCostCodedBound : costCoded ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
        (1 + y) ^ 3 / Real.sqrt (n : ℝ) := by
    rw [hCostCodedEq]
    exact hCostOriginalBound
  exact ⟨hP₀prob, hP₀map, hO, hOindep, hgcoord, hgenergy,
    hQid, hW0eq, hV0eq, hT0eq, hD1m, hD2m, hhalf,
    hTclipm, hTclipOriginal, hTcliplaw, hνprob, hqpres,
    hs, hηeval, hηindep, hηL2, hηInts, hηmean, hηenergy,
    hηnull, hVηnull, hpositiveDenominator, hCmeas, hCcomap,
    hfactor, hretained, hscalar, hdeletedFactor, hTηmeas,
    hZ0m, hZ0Original, hZmeas, hZcodedlaw, hZ0law,
    hZcodedreal, hsigned, hcomparison,
    hFullBounds, hDeletedBounds, hJm, hAm, hBm,
    (fun i : Fin n => ⟨(hDeletedMeasurable i).1, (hDeletedMeasurable i).2.1,
      hAdelm i, hBdeletem i⟩), hAI, hBI, heI,
    (fun i : Fin n => ⟨hAdelI i, hBdeleteI i, (hDiff i).1,
      (hDiff i).2.1, (hDiff i).2.2.1, (hDiff i).2.2.2.1,
      (hDiff i).2.2.2.2.1, (hDiff i).2.2.2.2.2⟩),
    hTotalm, hTotalI,
    hAm.comp hqpres.measurable, hBm.comp hqpres.measurable,
    hD2m.comp hqpres.measurable,
    hqpres.integrable_comp_of_integrable hAI,
    hqpres.integrable_comp_of_integrable hBI,
    hqpres.integrable_comp_of_integrable heI, hAugDeleted,
    hTotalm.comp hqpres.measurable,
    hqpres.integrable_comp_of_integrable hTotalI,
    hSνpoint, hSνdeletepoint, hIoriginalPos, hIreducedEq, hIcodedEq,
    hIreducedPos, hIcodedPos, hFullOriginalI, hDeleteOriginalI,
    hFullReducedI, hDeleteReducedI, hFullCodedI, hDeleteCodedI,
    hFullReducedEq, hFullCodedEq, hDeleteReducedEq, hDeleteCodedEq,
    hCostReducedEq, hCostCodedEq, hCostOriginalNonneg, hCostReducedNonneg,
    hCostCodedNonneg, hCostOriginalBound, hCostReducedBound, hCostCodedBound⟩
'''
body += suffix
assert 'C0' not in body and 'B1' not in body
(O/'PROOF-BODY.txt').write_bytes(body.encode('utf-8'))
whole = (F/'FROZEN-PREAMBLE.txt').read_bytes() + (F/'FROZEN-HEAD.txt').read_bytes() + b':= by\n' + body.encode('utf-8') + (F/'FROZEN-CLOSING.txt').read_bytes()
(O/'OriginalLevelDependentCanonicalCostPacket.lean').write_bytes(whole)
print('Assembled complete source from frozen preamble/head/body/closing; no Lean execution.')
