from pathlib import Path
import hashlib, json

ROOT = Path('C:/game/shao lean')
OUT = ROOT / 'drafts/oq56/unit256/author-01'
FREEZE = ROOT / 'drafts/oq56/unit256/freeze-01'

def read(path):
    return Path(path).read_text(encoding='utf-8')

old = read(ROOT / 'library/Shao/OQ6/OriginalLiteralWeightedConsumer.lean')
proof = old.split(' := by\n', 1)[1].split('\nend\n\nend Shao.OQ6.OriginalLiteralWeightedConsumer', 1)[0].rstrip() + '\n'
proof = proof.replace('Shao.OQ6.OriginalLiteralRemainderEnvelope.actual_original_literal_remainder_envelope',
    'Shao.OQ6.OriginalLevelDependentCanonicalCostPacket.actual_original_level_dependent_canonical_cost_packet')
proof = proof.replace('refine ⟨hμ₀prob, ?_⟩', 'refine ⟨hμ₀prob, hfor, ?_⟩')
proof = proof.replace('intro n hn C0 hC0 z hz', 'intro n hn z hz hwindow')
proof = proof.replace('  have hn1 : 1 ≤ n := by omega', '  have hz0 : 0 ≤ z := (by norm_num : (0 : ℝ) ≤ 1).trans hz\n  have hn1 : 1 ≤ n := by omega')
proof = proof.replace('hfor n hn C0 hC0 z hz K hK (ε 0)', 'hfor n hn z hz hwindow (ε 0)')
proof = proof.replace('  rcases hSuffix0 with ⟨hξPacket, hξSecond, hξenergy, hSuffixRest0⟩', '''  rcases hSuffix0 with
    ⟨hSνpoint0, hSνdeletepoint0, hIoriginalPos0, hIreducedEq0, hIcodedEq0,
      hIreducedPos0, hIcodedPos0, hFullOriginalI0, hDeleteOriginalI0,
      hFullReducedI0, hDeleteReducedI0, hFullCodedI0, hDeleteCodedI0,
      hFullReducedEq0, hFullCodedEq0, hDeleteReducedEq0, hDeleteCodedEq0,
      hCostReducedEq0, hCostCodedEq0, hCostOriginalNonneg0, hCostReducedNonneg0,
      hCostCodedNonneg0, hCostOriginalBound0, hCostReducedBound0, hCostCodedBound0⟩''')
start = proof.index('  have hξ (i : Fin n)')
end = proof.index('  have hξ0mean (i : Fin n)', start)
proof = proof[:start] + '''  have hξ0m (i : Fin n) : Measurable[mN₀, borel ℝ] (ξ0 i) :=
    ((hgcoord i).1).comp (hO i).1
  have hξ (i : Fin n) : Measurable[mAug, borel ℝ] (ξ i) :=
    (hξ0m i).comp hq.measurable
  have hξ2 (i : Fin n) : MemLp (ξ i) 2 ν := by
    have hi : MemLp (ξ0 i) 2 P₀ := (hgcoord i).2.1
    exact hi.comp_measurePreserving hq
''' + proof[end:]
start = proof.index('  have hD1 : Measurable')
proof = proof[:start] + '''  have hξsecondTransport (i : Fin n) :
      (∫ x, (ξ i x) ^ 2 ∂ν) = (∫ ζ, (ξ0 i ζ) ^ 2 ∂P₀) := by
    have hf : AEStronglyMeasurable (fun ζ => (ξ0 i ζ) ^ 2)
        (@Measure.map (Fin n → Ω × ℝ) (Fin n → Ω) mAug mN₀ q ν) := by
      rw [hq.map_eq]
      exact ((hξ0m i).pow_const 2).aestronglyMeasurable
    have hmap := integral_map hq.aemeasurable hf
    rw [hq.map_eq] at hmap
    simpa only [ξ, ξlocal, ξ0, q] using hmap.symm
  have hξenergy : (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 := by
    calc
      _ = ∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P₀ :=
        Finset.sum_congr rfl (fun i _ => hξsecondTransport i)
      _ = 1 := hgenergy
''' + proof[start:]
proof = proof.replace('hAint hBint hAdeleteint hBdeleteint z hz K hK', 'hAint hBint hAdeleteint hBdeleteint z hz0 K hK')
start = proof.index('  -- Each normalization and factorization')
end = proof.index('  have hQeq', start)
current = '''  have hTripleBorel :
      (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ)) = borel (ℝ × ℝ × ℝ) :=
    BorelSpace.measurable_eq
  have hRetainedCodeBorel (i : Fin n) :
      (inferInstance : MeasurableSpace ({j : Fin n // j ≠ i} → ℝ)) =
        borel ({j : Fin n // j ≠ i} → ℝ) := BorelSpace.measurable_eq
  let Uret : ∀ i : Fin n, ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ :=
    fun i y => ∑ j : {j : Fin n // j ≠ i}, (ξlocal j.val (y j)) ^ 2
  have hUretMeas (i : Fin n) :
      Measurable[
        @MeasurableSpace.pi {j : Fin n // j ≠ i}
          (fun _ : {j : Fin n // j ≠ i} => Ω × ℝ)
          (fun _ : {j : Fin n // j ≠ i} => mAugLocal), borel ℝ] (Uret i) := by
    exact Finset.measurable_sum Finset.univ
      (fun (j : {j : Fin n // j ≠ i})
        (_hj : j ∈ (Finset.univ : Finset {j : Fin n // j ≠ i})) =>
          ((hξlocalMeas j.val).comp (measurable_pi_apply j)).pow_const (2 : ℕ))
  have hSubtypeSum (i : Fin n) (f : Fin n → ℝ) :
      (∑ j : {j : Fin n // j ≠ i}, f j.val) = ∑ j ∈ Finset.univ.erase i, f j := by
    letI : Fintype {j : Fin n // j = i} := Subtype.fintype (fun j : Fin n => j = i)
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j : Fin n => j = i) f
    have hSingleSubtypeSum : (∑ j : {j : Fin n // j = i}, f j.val) = f i := by
      letI : Unique {j : Fin n // j = i} :=
        { default := ⟨i, rfl⟩
          uniq := fun j => Subtype.ext j.property }
      simp only [Fintype.sum_unique]
      rw [(default : {j : Fin n // j = i}).property]
    rw [hSingleSubtypeSum] at hsplit
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    linarith
  have hUretPoint (i : Fin n) (x : Fin n → Ω × ℝ) :
      Uret i (fun j : {j : Fin n // j ≠ i} => x j.val) =
        ∑ j ∈ Finset.univ.erase i, (ξ j x) ^ 2 := by
    simpa only [Uret, ξ] using hSubtypeSum i (fun j : Fin n => (ξ j x) ^ 2)
  have hVretPoint (i : Fin n) (x : Fin n → Ω × ℝ) :
      Real.sqrt (Uret i (fun j : {j : Fin n // j ≠ i} => x j.val)) = Vdelete i x := by
    rw [hUretPoint i x]
  -- The packet at k supplies every k-dependent normalization and factorization.
  have hCurrent (k : ℕ) :
      ((1 / 2 : ℝ) < s k ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η k i x = ηlocal k i (x i)) ∧
        iIndepFun (η k) ν ∧
        (∀ i : Fin n, Measurable[mAug, borel ℝ] (η k i) ∧ MemLp (η k i) 2 ν ∧
          (∫ x, η k i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1 ∧
        ν {x : Fin n → Ω × ℝ | Vη k x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη k x ∧ 0 < b x ∧ 0 < Vη k x * b x)) ∧
      (∀ x : Fin n → Ω × ℝ,
        Wη k x + Dη k x - z * Vη k x * b x = W x + D1 (q x) - z * V x * b x) ∧
      (∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
        Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
        ∀ x : Fin n → Ω × ℝ, (M k x, Anew k x, B x) = Ffull (C k x)) ∧
      (∀ i : Fin n, ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
        ∀ x : Fin n → Ω × ℝ,
          (Mdelete k i x, AdeleteNew k i x, Bdelete i x) =
            Fdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
      (∃ G1 G2 : (Fin n → ℝ) → ℝ,
        Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
        Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
        ∀ x : Fin n → Ω × ℝ, Dη k x = G1 (C k x) ∧ D2 (q x) = G2 (C k x)) := by
    have hPacket := hfor n hn z hz hwindow (ε k) (hε k) (hεsmall k)
    rcases hPacket with
      ⟨hP₀probK, hP₀mapK, hOK, hOindepK, hgcoordK, hgenergyK,
        hQidK, hW0eqK, hV0eqK, hT0eqK, hD1mK, hD2mK, hhalfK,
        hTclipmK, hTclipOriginalK, hTcliplawK, hνprobK, hqK,
        hsK, hηevalK, hηindepK, hηL2K, hηIntsK, hηmeanK, hηenergyK,
        hηnullK, hVηnullK, hpositiveK, hCmeasK, hCcomapK,
        hfactorK, hretainedK, hscalarK, hdeletedFactorK, hTηmeasK,
        hZ0mK, hZ0OriginalK, hZmeasK, hZcodedlawK, hZ0lawK,
        hZcodedrealK, hsignedK, hcomparisonK, hFullBoundsK, hDeletedBoundsK,
        hJmK, hAmK, hB1mK, hDeletedMeasurableK, hAIK, hB1IK, heIK,
        hDeletedCostsK, hTotalmK, hTotalIK, hAugAmK, hAugBmK,
        hAugD2mK, hAugAIK, hAugBIK, hAugD2IK, hAugDeletedK,
        hAugTotalmK, hAugTotalIK, hWeightedSuffixK⟩
    refine ⟨⟨hsK, hηevalK, hηindepK,
      (fun i => ⟨(hηL2K i).1, (hηL2K i).2, hηmeanK i⟩),
      hηenergyK, hVηnullK, hpositiveK⟩, hsignedK z, ?_, ?_, ?_⟩
    · have hMm : Measurable[mAug, borel ℝ] (M k) := measurable_const.mul hHm
      rcases hfactorK (M k) hMm with ⟨FM, hFMMeas, hFMPoint⟩
      rcases hfactorK (Anew k) (hAnewSpec k).1 with ⟨FA, hFAMeas, hFAPoint⟩
      rcases hfactorK B hB with ⟨FB, hFBMeas, hFBPoint⟩
      let Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ := fun t => (FM t, FA t, FB t)
      have hFfullMeas : Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull := by
        rw [← hTripleBorel]
        exact hFMMeas.prodMk (hFAMeas.prodMk hFBMeas)
      refine ⟨Ffull, hFfullMeas, ?_⟩
      intro x
      change (M k x, Anew k x, B x) = (FM (C k x), FA (C k x), FB (C k x))
      rw [hFMPoint x, hFAPoint x, hFBPoint x]
    · intro i
      rcases hdeletedFactorK i with ⟨Fdel, hFdelMeas, hFdelPoint⟩
      rcases hretainedK i (Uret i) (hUretMeas i) with
        ⟨FU, hFUMeas, hFULocalPoint, hFUFullRestrictionMeas, hFUPoint⟩
      let Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ :=
        fun t : ({j : Fin n // j ≠ i} → ℝ) =>
          (K * ε k * ((1 + Real.sqrt (FU t)) *
            (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + (Fdel t).2.2))),
           |(Fdel t).1| + K * ε k * ((1 + Real.sqrt (FU t)) *
            (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + (Fdel t).2.2))),
           (Fdel t).2.2)
      have hFdeleteMeas :
          Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete := by
        rw [← hRetainedCodeBorel i, ← hTripleBorel] at hFdelMeas ⊢
        rw [← hRetainedCodeBorel i] at hFUMeas
        apply Measurable.prodMk
        · exact measurable_const.mul
            ((measurable_const.add hFUMeas.sqrt).mul
              (measurable_const.add (measurable_const.mul
                (measurable_const.add hFdelMeas.snd.snd).sqrt)))
        · apply Measurable.prodMk
          · simpa only [Real.norm_eq_abs] using hFdelMeas.fst.norm.add
              (measurable_const.mul
                ((measurable_const.add hFUMeas.sqrt).mul
                  (measurable_const.add (measurable_const.mul
                    (measurable_const.add hFdelMeas.snd.snd).sqrt))))
          · exact hFdelMeas.snd.snd
      refine ⟨Fdelete, hFdeleteMeas, ?_⟩
      intro x
      change (Mdelete k i x, AdeleteNew k i x, Bdelete i x) =
        (K * ε k * ((1 + Real.sqrt (FU (fun j : {j : Fin n // j ≠ i} => η k j.val x))) *
          (Real.sqrt (n : ℝ) + z * Real.sqrt
            (1 + (Fdel (fun j : {j : Fin n // j ≠ i} => η k j.val x)).2.2))),
         |(Fdel (fun j : {j : Fin n // j ≠ i} => η k j.val x)).1| +
          K * ε k * ((1 + Real.sqrt (FU (fun j : {j : Fin n // j ≠ i} => η k j.val x))) *
            (Real.sqrt (n : ℝ) + z * Real.sqrt
              (1 + (Fdel (fun j : {j : Fin n // j ≠ i} => η k j.val x)).2.2))),
         (Fdel (fun j : {j : Fin n // j ≠ i} => η k j.val x)).2.2)
      rw [← hFdelPoint x, ← hFUPoint x, hVretPoint i x]
    · rcases hscalarK with ⟨G2, hG2, hG2eq, hG1for⟩
      rcases hG1for z with ⟨G1, hG1, hG1eq⟩
      exact ⟨G1, G2, hG1, hG2, fun x => ⟨hG1eq x, hG2eq x⟩⟩
  have hMnonneg (k : ℕ) (x : Fin n → Ω × ℝ) : 0 ≤ M k x :=
    mul_nonneg (mul_nonneg hK (hε k).le) (hHnonneg x)
  have hMdnonneg (k : ℕ) (i : Fin n) (x : Fin n → Ω × ℝ) : 0 ≤ Mdelete k i x :=
    mul_nonneg (mul_nonneg hK (hε k).le) (hHdnonneg i x)
  have hDeltaEq (k : ℕ) (i : Fin n) (x : Fin n → Ω × ℝ) :
      Δ k i x = M k x - Mdelete k i x := by
    dsimp only [Δ, Anew, AdeleteNew]
    ring
  have hDeltaBound (k : ℕ) (i : Fin n) (x : Fin n → Ω × ℝ) :
      |Δ k i x| ≤ M k x + Mdelete k i x := by
    rw [hDeltaEq k i x]
    simpa only [abs_of_nonneg (hMnonneg k x), abs_of_nonneg (hMdnonneg k i x)] using
      abs_sub (M k x) (Mdelete k i x)
  have hDeltaI (k : ℕ) (i : Fin n) :
      Integrable[mAug] (fun x => |Δ k i x|) ν ∧
      (∫ x, |Δ k i x| ∂ν) ≤ ε k * (K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) := by
    have hMI : Integrable[mAug] (M k) ν := hHint.const_mul (K * ε k)
    have hMdI : Integrable[mAug] (Mdelete k i) ν := (hHdeleteSpec i).2.const_mul (K * ε k)
    have hDI : Integrable[mAug] (fun x => |Δ k i x|) ν := by
      simpa only [hDeltaEq k i] using (hMI.sub hMdI).abs
    refine ⟨hDI, ?_⟩
    calc
      _ ≤ ∫ x, M k x + Mdelete k i x ∂ν :=
        integral_mono hDI (hMI.add hMdI) (hDeltaBound k i)
      _ = ε k * (K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) := by
        rw [integral_add hMI hMdI]
        change (∫ x, (K * ε k) * H x ∂ν) +
          (∫ x, (K * ε k) * Hdelete i x ∂ν) = _
        rw [integral_const_mul, integral_const_mul]
        ring
'''
proof = proof[:start] + current + proof[end:]
proof = proof.replace('(ε k) (hε k) (hεsmall k) (herr k) z hz', '(ε k) (hε k) (hεsmall k) (herr k) z hz0')
needle = '  refine ⟨hP₀prob, hP₀map, hνprob, hq, (fun k => ⟨hε k, hεsmall k⟩), hεlim,'
pos = proof.index(needle)
proof = proof[:pos] + '''  have hSourceNonneg : 0 ≤ sourceCost0 := hCostOriginalNonneg0
  have hSourceBound : sourceCost0 ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
        (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) := hCostOriginalBound0
  have hSourceEventually (δ : ℝ) (hδ : 0 < δ) : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      sourceCostη k ≤
        64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *
          (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ) + δ := by
    have htail : ∀ᶠ k : ℕ in Filter.atTop, sourceCostη k < sourceCost0 + δ :=
      hSourceLim.eventually (gt_mem_nhds (lt_add_of_pos_right sourceCost0 hδ))
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 htail
    exact ⟨k₀, fun k hk => (hk₀ k hk).le.trans (add_le_add_right hSourceBound δ)⟩
''' + proof[pos:]
proof = proof.replace('    (fun k i x => (hCurrent k).2.2.2.2.2.1 i x),\n    (fun k i => (hCurrent k).2.2.2.2.2.2 i),',
    '    (fun k i x => ⟨hDeltaEq k i x, hDeltaBound k i x⟩), hDeltaI,')
proof = proof.replace('(fun k => (hCurrent k).2.2.2.2.1),', '(fun k => (hCurrent k).2.2.2.2),')
proof = proof.replace('hCompactLim, hSourceLim, hCompactCostLim⟩',
    'hCompactLim, hSourceLim, hCompactCostLim, hSourceNonneg, hSourceBound, hSourceEventually⟩')
assert 'C0' not in proof
assert 'hNew' not in proof
assert 'hSuffixRest' not in proof
assert proof.endswith('  ring\n')
OUT.mkdir(parents=True, exist_ok=True)
(OUT / 'PROOF-BODY.txt').write_bytes(proof.encode('utf-8'))
preamble = (FREEZE / 'FROZEN-PREAMBLE.txt').read_bytes()
head = (FREEZE / 'FROZEN-HEAD.txt').read_bytes()
closing = (FREEZE / 'FROZEN-CLOSING.txt').read_bytes()
source = preamble + head + b':= by\n' + proof.encode('utf-8') + closing
(OUT / 'OriginalLevelDependentLiteralWeightedConsumer.lean').write_bytes(source)
print(json.dumps({'sourceBytes': len(source), 'sourceLF': source.count(b'\n'),
    'sha256': hashlib.sha256(source).hexdigest(), 'proofBytes': len(proof.encode()), 'proofLF': proof.count('\n')}, ensure_ascii=False))
