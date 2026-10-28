# Unit251 complete source-local declarations

Source-only inventory. This is not machine owner/TYPE/VALUE evidence.

## 1. g (frozen-conclusion-let, lines 29-29)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
```

## 2. r (frozen-conclusion-let, lines 30-30)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
```

## 3. v (frozen-conclusion-let, lines 31-31)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
```

## 4. rho (frozen-conclusion-let, lines 32-32)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let rho : ℝ := Real.sqrt v
```

## 5. P (frozen-conclusion-let, lines 33-33)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
```

## 6. N (frozen-conclusion-let, lines 34-34)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let N : ℝ := Real.sqrt (n : ℝ)
```

## 7. W (frozen-conclusion-let, lines 35-35)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let W : (Fin n → Ω) → ℝ := projectionW n g
```

## 8. V (frozen-conclusion-let, lines 36-36)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let V : (Fin n → Ω) → ℝ := projectionV n g
```

## 9. D (frozen-conclusion-let, lines 37-37)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let D : (Fin n → Ω) → ℝ := residualStatisticD n r
```

## 10. J (frozen-conclusion-let, lines 38-38)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
```

## 11. Ddelete (frozen-conclusion-let, lines 39-39)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
```

## 12. Jdelete (frozen-conclusion-let, lines 40-40)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
```

## 13. A (frozen-conclusion-let, lines 41-41)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
```

## 14. Adelete (frozen-conclusion-let, lines 42-42)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let Adelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i => |Ddelete ζ i|
```

## 15. B (frozen-conclusion-let, lines 43-43)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
```

## 16. Bdelete (frozen-conclusion-let, lines 44-45)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let Bdelete : (Fin n → Ω) → Fin n → ℝ :=
      studentizerClipBudgetDeleted n r 512 rho z
```

## 17. d (frozen-conclusion-let, lines 46-46)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let d : (Fin n → Ω) → ℝ := centeredDelta n g r
```

## 18. e (frozen-conclusion-let, lines 47-47)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
```

## 19. Tclip (frozen-conclusion-let, lines 48-48)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho z
```

## 20. s (frozen-conclusion-let, lines 49-49)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let s : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq n g r ζ)
```

## 21. Tphysical (frozen-conclusion-let, lines 50-51)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let Tphysical : (Fin n → Ω) → ℝ := fun ζ =>
      if s ζ = 0 then 0 else (W ζ + D ζ) / s ζ
```

## 22. ξ0 (frozen-conclusion-let, lines 52-52)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
```

## 23. cap (frozen-conclusion-let, lines 53-53)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ζ i => min |z * ξ0 i ζ| 1
```

## 24. S (frozen-conclusion-let, lines 54-55)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let S : (Fin n → Ω) → ℝ := fun ζ =>
      ∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
```

## 25. Sdelete (frozen-conclusion-let, lines 56-57)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let Sdelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
```

## 26. fullTest (frozen-conclusion-let, lines 58-58)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let fullTest : (Fin n → Ω) → ℝ := fun ζ => z * A ζ + z ^ 2 * B ζ
```

## 27. deletedTest (frozen-conclusion-let, lines 59-60)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
      cap ζ i * (|A ζ - Adelete ζ i| + z * |B ζ - Bdelete ζ i|)
```

## 28. I (frozen-conclusion-let, lines 61-61)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let I : ℝ := ∫ ζ, Real.exp (S ζ) ∂P
```

## 29. sourceCost (frozen-conclusion-let, lines 62-64)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
    let sourceCost : ℝ :=
      ((∫ ζ, fullTest ζ * Real.exp (S ζ) ∂P) +
        ∑ i : Fin n, ∫ ζ, deletedTest ζ i * Real.exp (Sdelete ζ i) ∂P) / I
```

## 30. hC0 (proof-local-have, lines 107-107)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hC0 : (0 : ℝ) ≤ 512 := by norm_num
```

## 31. hz0 (proof-local-have, lines 108-108)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hz0 : (0 : ℝ) ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 1) hz
```

## 32. hrho (proof-local-have, lines 109-109)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hrho : 0 ≤ rho := Real.sqrt_nonneg v
```

## 33. hg (proof-local-have, lines 110-111)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hg : Measurable g :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
```

## 34. hsym (proof-local-have, lines 112-116)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hsym : ∀ o y : Ω, r o y = r y o := by
    intro o y
    change h o y - g o - g y = h y o - g y - g o
    rw [hhsymm o y]
    ring
```

## 35. habs (proof-local-have, lines 117-119)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have habs (f : (Fin n → Ω) → ℝ) (hf : Measurable f) :
      Measurable (fun ζ : Fin n → Ω => |f ζ|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
```

## 36. hξ0 (proof-local-have, lines 120-121)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hξ0 (i : Fin n) : Measurable (ξ0 i) :=
    (hg.comp (measurable_pi_apply i)).div_const N
```

## 37. hshared (proof-local-have, lines 122-149)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hshared :
      Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
      Measurable A ∧ Measurable (centeredSq n g r) ∧ Measurable s ∧
      Measurable d ∧ Measurable Tphysical ∧
      MeasurableSet {ζ : Fin n → Ω | V ζ = 0} ∧
      MeasurableSet {ζ : Fin n → Ω | s ζ = 0} ∧
      (∀ i : Fin n,
        Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
        ∃ E0 : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
          Measurable E0 ∧ ∀ ζ : Fin n → Ω,
            (Ddelete ζ i, Jdelete ζ i,
              studentizerClipBudgetDeleted n r 512 rho 1 ζ i) =
                E0 (fun j : {j : Fin n // j ≠ i} => ζ j.val)) := by
    rcases Shao.OQ6.OriginalClippedStatisticMeasurable.actual_normalized_compact_clipped_observables
        μ h hh hh2 hhsymm hcenter hprojectionsecond n hn 0
        (le_refl 0) (by norm_num) 512 hC0 with
      ⟨hW0, hV0, hD0, hJ0, hA0, _hB10, hs20, hs0, hd0, _he10,
        _hTclip10, hTphysical0, hVzero0, hszero0, _hpositive10,
        _hzero10, hdeletes0⟩
    refine ⟨hW0, hV0, hD0, hJ0, hA0, hs20, hs0, hd0, hTphysical0,
      hVzero0, hszero0, ?_⟩
    intro i
    rcases hdeletes0 i with
      ⟨_hcap0, hDdelete0, hJdelete0, hAdelete0, _hBdelete10,
        _hdeletedTest0, E0, hE0, hE0factor⟩
    exact ⟨hDdelete0, hJdelete0, hAdelete0, E0, hE0, hE0factor⟩
```

## 38. hB (proof-local-have, lines 153-157)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hB : Measurable B := by
    change Measurable (fun ζ : Fin n → Ω =>
      512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
        J ζ / ((1 + rho) * z * Real.sqrt (n : ℝ))))
    exact measurable_const.mul (measurable_const.add (hJ.div_const _))
```

## 39. hclipvalue (proof-local-have, lines 158-161)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hclipvalue : Measurable (fun ζ : Fin n → Ω =>
      studentizerClip (B ζ) (d ζ)) := by
    unfold studentizerClip
    exact ((hB.min measurable_const).neg).max (hd.min hB)
```

## 40. he (proof-local-have, lines 162-165)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have he : Measurable e := by
    change Measurable (fun ζ : Fin n → Ω =>
      if V ζ = 0 then 0 else studentizerClip (B ζ) (d ζ))
    exact Measurable.ite hVzero measurable_const hclipvalue
```

## 41. hTclip (proof-local-have, lines 166-171)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hTclip : Measurable Tclip := by
    change Measurable (fun ζ : Fin n → Ω =>
      if V ζ = 0 then 0 else
        (W ζ + D ζ) / (V ζ * Real.sqrt (1 + e ζ)))
    exact Measurable.ite hVzero measurable_const
      ((hW.add hD).div (hV.mul (measurable_const.add he).sqrt))
```

## 42. hfullTest (proof-local-have, lines 172-173)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hfullTest : Measurable fullTest :=
    (measurable_const.mul hA).add (measurable_const.mul hB)
```

## 43. hglobal (proof-local-have, lines 174-177)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hglobal (ζ : Fin n → Ω) :
      (1 / 2 : ℝ) ≤ 1 + e ζ ∧ |e ζ| ≤ B ζ ∧ |e ζ| ≤ |d ζ| ∧
      (0 < V ζ → 0 < V ζ * Real.sqrt (1 + e ζ)) :=
    clippedCenteredDelta_bounds n g r 512 rho z ζ hC0 hrho hz0
```

## 44. hzero (proof-local-have, lines 178-180)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hzero (ζ : Fin n → Ω) (hζ : V ζ = 0) :
      d ζ = 0 ∧ e ζ = 0 ∧ Tclip ζ = 0 :=
    clippedCentered_zero n g r 512 rho z ζ hζ
```

## 45. hphysicalzero (proof-local-have, lines 181-184)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hphysicalzero (ζ : Fin n → Ω) (hζ : s ζ = 0) :
      Tphysical ζ = 0 := by
    change (if s ζ = 0 then 0 else (W ζ + D ζ) / s ζ) = 0
    rw [if_pos hζ]
```

## 46. hdeletion (proof-local-have, lines 185-247)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hdeletion :
      ∀ i : Fin n,
        Measurable (fun ζ : Fin n → Ω => cap ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) ∧
        Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) ∧
        ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
          Measurable E ∧ ∀ ζ : Fin n → Ω,
            (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
              E (fun j : {j : Fin n // j ≠ i} => ζ j.val) := by
    intro i
    rcases hdeletes i with ⟨hDdelete, hJdelete, hAdelete, E0, hE0, hE0factor⟩
    let pdel : (Fin n → Ω) → ({j : Fin n // j ≠ i} → Ω) :=
      fun (ζ : Fin n → Ω) (j : {j : Fin n // j ≠ i}) => ζ j.val
    let Dret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (E0 q).1
    let Jret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (E0 q).2.1
    let Bret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω =>
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jret q / ((1 + rho) * z * Real.sqrt (n : ℝ)))
    let E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (Dret q, Jret q, Bret q)
    have hDret : Measurable Dret := hE0.fst
    have hJret : Measurable Jret := hE0.snd.fst
    have hBret : Measurable Bret :=
      measurable_const.mul (measurable_const.add (hJret.div_const _))
    have hE : Measurable E := hDret.prodMk (hJret.prodMk hBret)
    have hDfactor (ζ : Fin n → Ω) : Ddelete ζ i = Dret (pdel ζ) :=
      congrArg (fun t : ℝ × ℝ × ℝ => t.1) (hE0factor ζ)
    have hJfactor (ζ : Fin n → Ω) : Jdelete ζ i = Jret (pdel ζ) :=
      congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) (hE0factor ζ)
    have hBfactor (ζ : Fin n → Ω) : Bdelete ζ i = Bret (pdel ζ) := by
      change 512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jdelete ζ i / ((1 + rho) * z * Real.sqrt (n : ℝ))) =
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jret (pdel ζ) / ((1 + rho) * z * Real.sqrt (n : ℝ)))
      rw [hJfactor ζ]
    have hzξ0 : Measurable (fun ζ : Fin n → Ω => z * ξ0 i ζ) :=
      measurable_const.mul (hξ0 i)
    have hcap : Measurable (fun ζ : Fin n → Ω => cap ζ i) :=
      (habs (fun ζ : Fin n → Ω => z * ξ0 i ζ) hzξ0).min measurable_const
    have hBdelete : Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) := by
      change Measurable (fun ζ : Fin n → Ω =>
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jdelete ζ i / ((1 + rho) * z * Real.sqrt (n : ℝ))))
      exact measurable_const.mul (measurable_const.add (hJdelete.div_const _))
    have hdeletedTest : Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) :=
      hcap.mul
        ((habs (fun ζ : Fin n → Ω => A ζ - Adelete ζ i)
          (hA.sub hAdelete)).add
          (measurable_const.mul
            (habs (fun ζ : Fin n → Ω => B ζ - Bdelete ζ i)
              (hB.sub hBdelete))))
    refine ⟨hcap, hDdelete, hJdelete, hAdelete, hBdelete, hdeletedTest,
      E, hE, ?_⟩
    intro ζ
    change (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
      (Dret (pdel ζ), Jret (pdel ζ), Bret (pdel ζ))
    rw [hDfactor ζ, hJfactor ζ, hBfactor ζ]
```

## 47. pdel (proof-local-let, lines 199-200)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    let pdel : (Fin n → Ω) → ({j : Fin n // j ≠ i} → Ω) :=
      fun (ζ : Fin n → Ω) (j : {j : Fin n // j ≠ i}) => ζ j.val
```

## 48. Dret (proof-local-let, lines 201-202)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    let Dret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (E0 q).1
```

## 49. Jret (proof-local-let, lines 203-204)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    let Jret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (E0 q).2.1
```

## 50. Bret (proof-local-let, lines 205-208)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    let Bret : ({j : Fin n // j ≠ i} → Ω) → ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω =>
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jret q / ((1 + rho) * z * Real.sqrt (n : ℝ)))
```

## 51. E (proof-local-let, lines 209-210)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    let E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ :=
      fun q : {j : Fin n // j ≠ i} → Ω => (Dret q, Jret q, Bret q)
```

## 52. hDret (proof-local-have, lines 211-211)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hDret : Measurable Dret := hE0.fst
```

## 53. hJret (proof-local-have, lines 212-212)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hJret : Measurable Jret := hE0.snd.fst
```

## 54. hBret (proof-local-have, lines 213-214)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hBret : Measurable Bret :=
      measurable_const.mul (measurable_const.add (hJret.div_const _))
```

## 55. hE (proof-local-have, lines 215-215)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hE : Measurable E := hDret.prodMk (hJret.prodMk hBret)
```

## 56. hDfactor (proof-local-have, lines 216-217)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hDfactor (ζ : Fin n → Ω) : Ddelete ζ i = Dret (pdel ζ) :=
      congrArg (fun t : ℝ × ℝ × ℝ => t.1) (hE0factor ζ)
```

## 57. hJfactor (proof-local-have, lines 218-219)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hJfactor (ζ : Fin n → Ω) : Jdelete ζ i = Jret (pdel ζ) :=
      congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) (hE0factor ζ)
```

## 58. hBfactor (proof-local-have, lines 220-225)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hBfactor (ζ : Fin n → Ω) : Bdelete ζ i = Bret (pdel ζ) := by
      change 512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jdelete ζ i / ((1 + rho) * z * Real.sqrt (n : ℝ))) =
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jret (pdel ζ) / ((1 + rho) * z * Real.sqrt (n : ℝ)))
      rw [hJfactor ζ]
```

## 59. hzξ0 (proof-local-have, lines 226-227)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hzξ0 : Measurable (fun ζ : Fin n → Ω => z * ξ0 i ζ) :=
      measurable_const.mul (hξ0 i)
```

## 60. hcap (proof-local-have, lines 228-229)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hcap : Measurable (fun ζ : Fin n → Ω => cap ζ i) :=
      (habs (fun ζ : Fin n → Ω => z * ξ0 i ζ) hzξ0).min measurable_const
```

## 61. hBdelete (proof-local-have, lines 230-234)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hBdelete : Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) := by
      change Measurable (fun ζ : Fin n → Ω =>
        512 * (((1 + rho) * z) / Real.sqrt (n : ℝ) +
          Jdelete ζ i / ((1 + rho) * z * Real.sqrt (n : ℝ))))
      exact measurable_const.mul (measurable_const.add (hJdelete.div_const _))
```

## 62. hdeletedTest (proof-local-have, lines 235-241)

Lexical container: hdeletion; scope ends at line 247.

Full explicit header, parameter binders and RHS:

```lean
    have hdeletedTest : Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) :=
      hcap.mul
        ((habs (fun ζ : Fin n → Ω => A ζ - Adelete ζ i)
          (hA.sub hAdelete)).add
          (measurable_const.mul
            (habs (fun ζ : Fin n → Ω => B ζ - Bdelete ζ i)
              (hB.sub hBdelete))))
```

## 63. hgeometry (proof-local-have, lines 248-263)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hgeometry :
      (1 + rho) * z ≤ N →
        (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n g z →
          -(1 / 2 : ℝ) ≤ d ζ →
          e ζ = d ζ ∧ 0 < V ζ * Real.sqrt (1 + e ζ) ∧
          0 < s ζ ∧ V ζ * Real.sqrt (1 + e ζ) = s ζ ∧
          Tclip ζ = Tphysical ζ) ∧
        {ζ : Fin n → Ω | Tclip ζ ≠ Tphysical ζ} ⊆
          (projectionGood n g z)ᶜ ∪ lowerStudentizerBad n g r z := by
    intro hgeom
    refine ⟨?_, ?_⟩
    · intro ζ hGood hLower
      exact literal_clippedCentered_comparison_on_projectionGood n g r rho z ζ
        hn hz hsym hrho hgeom hGood hLower
    · exact literal_clippedCentered_comparison_exception_subset n g r rho z
        hn hz hsym hrho hgeom
```

## 64. hcost (proof-local-have, lines 264-274)

Lexical container: main theorem; scope ends at line 277.

Full explicit header, parameter binders and RHS:

```lean
  have hcost :
      0 < I ∧
      Integrable (fun ζ => fullTest ζ * Real.exp (S ζ)) P ∧
      (∀ i : Fin n,
        Integrable (fun ζ => deletedTest ζ i * Real.exp (Sdelete ζ i)) P) ∧
      0 ≤ sourceCost ∧
      sourceCost ≤
        64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
          (1 + z) ^ 3 / Real.sqrt (n : ℝ) :=
    Shao.OQ6.OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost
      μ h hh hh2 hhsymm hcenter hprojectionsecond n hn z hz hwindow 512 hC0
```

