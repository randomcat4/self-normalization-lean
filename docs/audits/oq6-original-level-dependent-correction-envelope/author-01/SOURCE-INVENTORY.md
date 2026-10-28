# unit252 完整源码局部库存

本库存逐项保留实际源码块；行列从1开始，字节偏移从0开始，结束位置为不含端点。全部49项是24个冻结let、24个证明have及1个局部letI，绝非机器所属声明数量。

## 1. g

源码行 29–29；UTF-8字节区间 [1009,1058)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Ω → ℝ
```

完整声明及右端：
```lean
let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
```

## 2. r

源码行 30–30；UTF-8字节区间 [1063,1120)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Ω → Ω → ℝ
```

完整声明及右端：
```lean
let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
```

## 3. v

源码行 31–31；UTF-8字节区间 [1125,1187)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
ℝ
```

完整声明及右端：
```lean
let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
```

## 4. rho

源码行 32–32；UTF-8字节区间 [1192,1220)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
ℝ
```

完整声明及右端：
```lean
let rho : ℝ := Real.sqrt v
```

## 5. P

源码行 33–33；UTF-8字节区间 [1225,1291)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Measure (Fin n → Ω)
```

完整声明及右端：
```lean
let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
```

## 6. N

源码行 34–34；UTF-8字节区间 [1296,1330)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
ℝ
```

完整声明及右端：
```lean
let N : ℝ := Real.sqrt (n : ℝ)
```

## 7. ξ0

源码行 35–35；UTF-8字节区间 [1335,1405)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Fin n → (Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
```

## 8. D

源码行 36–36；UTF-8字节区间 [1410,1466)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let D : (Fin n → Ω) → ℝ := residualStatisticD n r
```

## 9. J

源码行 37–37；UTF-8字节区间 [1471,1524)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
```

## 10. Ddelete

源码行 38–38；UTF-8字节区间 [1529,1608)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整声明及右端：
```lean
let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
```

## 11. Jdelete

源码行 39–39；UTF-8字节区间 [1613,1689)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整声明及右端：
```lean
let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
```

## 12. A

源码行 40–40；UTF-8字节区间 [1694,1744)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
```

## 13. Adelete

源码行 41–41；UTF-8字节区间 [1749,1825)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Fin n → (Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let Adelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ => |Ddelete ζ i|
```

## 14. B

源码行 42–42；UTF-8字节区间 [1830,1899)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
```

## 15. Bdelete

源码行 43–44；UTF-8字节区间 [1904,2019)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Fin n → (Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let Bdelete : Fin n → (Fin n → Ω) → ℝ :=
      fun i ζ => studentizerClipBudgetDeleted n r 512 rho z ζ i
```

## 16. e

源码行 45–45；UTF-8字节区间 [2024,2094)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
```

## 17. V

源码行 46–46；UTF-8字节区间 [2099,2184)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let V : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (∑ j : Fin n, (ξ0 j ζ) ^ 2)
```

## 18. Vdelete

源码行 47–48；UTF-8字节区间 [2189,2314)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Fin n → (Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let Vdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ0 j ζ) ^ 2)
```

## 19. H

源码行 49–49；UTF-8字节区间 [2319,2406)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let H : (Fin n → Ω) → ℝ := fun ζ => (1 + V ζ) * (N + z * Real.sqrt (1 + B ζ))
```

## 20. Hdelete

源码行 50–51；UTF-8字节区间 [2411,2538)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Fin n → (Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let Hdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
      (1 + Vdelete i ζ) * (N + z * Real.sqrt (1 + Bdelete i ζ))
```

## 21. M

源码行 52–52；UTF-8字节区间 [2543,2615)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
ℝ → (Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let M : ℝ → (Fin n → Ω) → ℝ := fun ε ζ => 4 * ε * N * H ζ
```

## 22. Mdelete

源码行 53–54；UTF-8字节区间 [2620,2724)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
ℝ → Fin n → (Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let Mdelete : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
      4 * ε * N * Hdelete i ζ
```

## 23. κ

源码行 55–56；UTF-8字节区间 [2729,2829)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
Fin n → ℝ
```

完整声明及右端：
```lean
let κ : Fin n → ℝ := fun i =>
      4 * N * ((∫ ζ, H ζ ∂P) + (∫ ζ, Hdelete i ζ ∂P))
```

## 24. Δ

源码行 57–58；UTF-8字节区间 [2834,2983)；范围：dependent result let chain through final result; the same definitional let is introduced in the body at lines95-96

完整类型：
```lean
ℝ → Fin n → (Fin n → Ω) → ℝ
```

完整声明及右端：
```lean
let Δ : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
      (A ζ + M ε ζ) - (Adelete i ζ + Mdelete ε i ζ) - (A ζ - Adelete i ζ)
```

## 25. 匿名 letI

源码行 97–98；UTF-8字节区间 [5206,5316)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
IsProbabilityMeasure P
```

完整声明及右端：
```lean
letI : IsProbabilityMeasure P :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ)))
```

## 26. hn1

源码行 99–99；UTF-8字节区间 [5319,5370)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
1 ≤ n
```

完整声明及右端：
```lean
have hn1 : 1 ≤ n := Nat.le_trans (by norm_num) hn
```

## 27. hn3

源码行 100–100；UTF-8字节区间 [5373,5424)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
3 ≤ n
```

完整声明及右端：
```lean
have hn3 : 3 ≤ n := Nat.le_trans (by norm_num) hn
```

## 28. hn4R

源码行 101–101；UTF-8字节区间 [5427,5486)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
(4 : ℝ) ≤ (n : ℝ)
```

完整声明及右端：
```lean
have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
```

## 29. hnR

源码行 102–102；UTF-8字节区间 [5489,5548)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
(0 : ℝ) < (n : ℝ)
```

完整声明及右端：
```lean
have hnR : (0 : ℝ) < (n : ℝ) := by linarith only [hn4R]
```

## 30. hN2

源码行 103–103；UTF-8字节区间 [5551,5602)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
N ^ 2 = (n : ℝ)
```

完整声明及右端：
```lean
have hN2 : N ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
```

## 31. hnNe

源码行 104–104；UTF-8字节区间 [5605,5648)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
(n : ℝ) ≠ 0
```

完整声明及右端：
```lean
have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hnR
```

## 32. hC0

源码行 105–105；UTF-8字节区间 [5651,5694)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
(0 : ℝ) ≤ 512
```

完整声明及右端：
```lean
have hC0 : (0 : ℝ) ≤ 512 := by norm_num
```

## 33. hz0

源码行 106–106；UTF-8字节区间 [5697,5770)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
(0 : ℝ) ≤ z
```

完整声明及右端：
```lean
have hz0 : (0 : ℝ) ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 1) hz
```

## 34. hrho

源码行 107–107；UTF-8字节区间 [5773,5816)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
0 ≤ rho
```

完整声明及右端：
```lean
have hrho : 0 ≤ rho := Real.sqrt_nonneg v
```

## 35. hBI

源码行 115–119；UTF-8字节区间 [6321,6579)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
Integrable B P
```

完整声明及右端：
```lean
have hBI : Integrable B P := by
    change Integrable (fun ζ : Fin n → Ω =>
      512 * (((1 + rho) * z) / N + J ζ / ((1 + rho) * z * N))) P
    exact ((integrable_const (((1 + rho) * z) / N)).add
      (hJI.div_const ((1 + rho) * z * N))).const_mul 512
```

## 36. hBdeleteI

源码行 120–124；UTF-8字节区间 [6582,6886)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ i : Fin n, Integrable (Bdelete i) P
```

完整声明及右端：
```lean
have hBdeleteI (i : Fin n) : Integrable (Bdelete i) P := by
    change Integrable (fun ζ : Fin n → Ω =>
      512 * (((1 + rho) * z) / N + Jdelete ζ i / ((1 + rho) * z * N))) P
    exact ((integrable_const (((1 + rho) * z) / N)).add
      ((hJdeleteI i).div_const ((1 + rho) * z * N))).const_mul 512
```

## 37. hFullBounds

源码行 125–129；UTF-8字节区间 [6889,7104)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ ζ : Fin n → Ω, 0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |e ζ| ≤ B ζ
```

完整声明及右端：
```lean
have hFullBounds (ζ : Fin n → Ω) :
      0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |e ζ| ≤ B ζ := by
    exact ⟨abs_nonneg _,
      studentizerClipBudget_nonneg n r 512 rho z ζ hC0 hrho hz0,
      (hglobal ζ).2.1⟩
```

## 38. hDeletedBounds

源码行 130–133；UTF-8字节区间 [7107,7301)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ Adelete i ζ ∧ 0 ≤ Bdelete i ζ
```

完整声明及右端：
```lean
have hDeletedBounds (i : Fin n) (ζ : Fin n → Ω) :
      0 ≤ Adelete i ζ ∧ 0 ≤ Bdelete i ζ := by
    exact (clippedDeletion_envelopes_nonneg n r 512 rho z ζ i
      hC0 hrho hz0).2.2
```

## 39. heI

源码行 134–137；UTF-8字节区间 [7304,7495)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
Integrable e P
```

完整声明及右端：
```lean
have heI : Integrable e P := by
    apply hBI.mono' hem.aestronglyMeasurable
    exact ae_of_all P (fun ζ : Fin n → Ω => by
      simpa only [Real.norm_eq_abs] using (hFullBounds ζ).2.2)
```

## 40. hBdeleteM

源码行 138–139；UTF-8字节区间 [7498,7579)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ i : Fin n, Measurable (Bdelete i)
```

完整声明及右端：
```lean
have hBdeleteM (i : Fin n) : Measurable (Bdelete i) :=
    (hdeletes i).2.2.2.2.1
```

## 41. hwindow0

源码行 140–143；UTF-8字节区间 [7582,7780)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
(0 : ℝ) ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))
```

完整声明及右端：
```lean
have hwindow0 : (0 : ℝ) ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ)) :=
    div_nonneg (Real.sqrt_nonneg (n : ℝ))
      (mul_nonneg (by norm_num) (Real.exp_pos (1 / 2 : ℝ)).le)
```

## 42. hcoord

源码行 147–149；UTF-8字节区间 [7985,8131)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ i : Fin n, MeasurePreserving (fun ζ : Fin n → Ω => ζ i) P μ
```

完整声明及右端：
```lean
have hcoord (i : Fin n) :
      MeasurePreserving (fun ζ : Fin n → Ω => ζ i) P μ :=
    measurePreserving_eval (μ := fun _ : Fin n => μ) i
```

## 43. hpull

源码行 150–155；UTF-8字节区间 [8134,8452)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ (i : Fin n) (f : Ω → ℝ), Measurable f → (∫ ζ, f (ζ i) ∂P) = ∫ o, f o ∂μ
```

完整声明及右端：
```lean
have hpull (i : Fin n) (f : Ω → ℝ) (hf : Measurable f) :
      (∫ ζ, f (ζ i) ∂P) = ∫ o, f o ∂μ := by
    calc
      _ = ∫ o, f o ∂P.map (fun ζ : Fin n → Ω => ζ i) :=
        (integral_map (hcoord i).measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [(hcoord i).map_eq]
```

## 44. hξm

源码行 156–157；UTF-8字节区间 [8455,8551)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ i : Fin n, Measurable (ξ0 i)
```

完整声明及右端：
```lean
have hξm (i : Fin n) : Measurable (ξ0 i) :=
    (hgm.comp (measurable_pi_apply i)).div_const N
```

## 45. hξ2

源码行 158–160；UTF-8字节区间 [8554,8728)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ i : Fin n, MemLp (ξ0 i) 2 P
```

完整声明及右端：
```lean
have hξ2 (i : Fin n) : MemLp (ξ0 i) 2 P := by
    simpa only [ξ0, div_eq_mul_inv, Function.comp_def] using
      ((hg2.comp_measurePreserving (hcoord i)).mul_const N⁻¹)
```

## 46. hξmean

源码行 161–163；UTF-8字节区间 [8731,8889)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ i : Fin n, (∫ ζ, ξ0 i ζ ∂P) = 0
```

完整声明及右端：
```lean
have hξmean (i : Fin n) : (∫ ζ, ξ0 i ζ ∂P) = 0 := by
    change (∫ ζ, g (ζ i) / N ∂P) = 0
    rw [integral_div, hpull i g hgm, hgmean, zero_div]
```

## 47. hξsecond

源码行 164–167；UTF-8字节区间 [8892,9138)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ i : Fin n, (∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 / (n : ℝ)
```

完整声明及右端：
```lean
have hξsecond (i : Fin n) : (∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 / (n : ℝ) := by
    change (∫ ζ, (g (ζ i) / N) ^ 2 ∂P) = 1 / (n : ℝ)
    simp_rw [div_pow]
    rw [integral_div, hpull i (fun o => g o ^ 2) (hgm.pow_const 2), hgsecond, hN2]
```

## 48. hξenergy

源码行 168–171；UTF-8字节区间 [9141,9341)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
(∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1
```

完整声明及右端：
```lean
have hξenergy : (∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 := by
    simp_rw [hξsecond]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnNe]
```

## 49. hVeq

源码行 172–176；UTF-8字节区间 [9344,9589)；范围：theorem body after this binding through final exact at line197; parameters written in the binder are local to this declaration and its RHS

完整类型：
```lean
∀ ζ : Fin n → Ω, V ζ = projectionV n g ζ
```

完整声明及右端：
```lean
have hVeq (ζ : Fin n → Ω) : V ζ = projectionV n g ζ := by
    change Real.sqrt (∑ i : Fin n, (g (ζ i) / N) ^ 2) =
      Real.sqrt ((∑ i : Fin n, (g (ζ i)) ^ 2) / (n : ℝ))
    congr 1
    simp only [div_pow, ← Finset.sum_div, hN2]
```
