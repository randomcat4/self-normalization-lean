import Shao.OQ3.TorusMetricDiophantine

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem real_ratio_diophantine_ae (m : ℕ) (hm : 6 ≤ m) :
    ∀ᵐ r ∂(volume : Measure (Fin m → ℝ)),
      ∃ Q : ℝ, 0 ≤ Q ∧ ∀ q : ℤ, Q < |(q : ℝ)| →
        ∃ j : Fin m, ∀ p : ℤ,
          Real.rpow |(q : ℝ)| (-(3 : ℝ) / 16) ≤
            |(q : ℝ) * r j - (p : ℝ)| := by
  classical
  let F : (Fin m → ℝ) → (Fin m → UnitAddCircle) := fun r j => (r j : UnitAddCircle)
  let cube : (Fin m → ℤ) → Set (Fin m → ℝ) := fun z =>
    Set.pi Set.univ (fun j => Set.Ioc (z j : ℝ) ((z j : ℝ) + 1))
  let P : (Fin m → UnitAddCircle) → Prop := fun x =>
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ j : Fin m,
      Real.rpow ((n : ℝ) + 1) (-(3 : ℝ) / 16) < ‖((n + 1 : ℕ) : ℤ) • x j‖
  have hMP (z : Fin m → ℤ) : MeasurePreserving F
      (volume.restrict (cube z)) volume := by
    change MeasurePreserving (fun r j => (r j : UnitAddCircle))
      ((Measure.pi (fun _ : Fin m => (volume : Measure ℝ))).restrict
        (Set.pi Set.univ (fun j => Set.Ioc (z j : ℝ) ((z j : ℝ) + 1))))
      (Measure.pi (fun _ : Fin m => (volume : Measure UnitAddCircle)))
    rw [Measure.restrict_pi_pi]
    exact measurePreserving_pi
      (fun j : Fin m => (volume : Measure ℝ).restrict (Set.Ioc (z j : ℝ) ((z j : ℝ) + 1)))
      (fun _ : Fin m => (volume : Measure UnitAddCircle))
      (fun j => AddCircle.measurePreserving_mk (T := 1) (z j : ℝ))
  have hcover : (⋃ z : Fin m → ℤ, cube z) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro r
    refine Set.mem_iUnion.mpr ⟨fun j => ⌈r j⌉ - 1, ?_⟩
    change ∀ j ∈ Set.univ, ((⌈r j⌉ - 1 : ℤ) : ℝ) < r j ∧
      r j ≤ ((⌈r j⌉ - 1 : ℤ) : ℝ) + 1
    intro j _
    have hl : (⌈r j⌉ : ℝ) - 1 < r j := Int.le_ceil_iff.mp le_rfl
    have hu := Int.le_ceil (r j)
    simp only [Int.cast_sub, Int.cast_one]
    constructor <;> linarith
  have hP : ∀ᵐ r ∂(volume : Measure (Fin m → ℝ)), P (F r) := by
    have hlocal : ∀ᵐ r ∂volume.restrict (⋃ z : Fin m → ℤ, cube z), P (F r) :=
      (ae_restrict_iUnion_iff cube (fun r => P (F r))).2
        (fun z => (hMP z).quasiMeasurePreserving.ae
          (torus_metric_diophantine_eventually m hm).2)
    simpa only [hcover, Measure.restrict_univ] using hlocal
  filter_upwards [hP] with r hr
  obtain ⟨N, hN⟩ := hr
  refine ⟨(N : ℝ) + 1, by positivity, ?_⟩
  intro q hq
  have hqR : (N : ℝ) + 1 < (q.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hq
  have hNk : N + 1 < q.natAbs := by exact_mod_cast hqR
  have hkn : q.natAbs - 1 + 1 = q.natAbs := Nat.sub_add_cancel (by omega)
  have hNn : N ≤ q.natAbs - 1 := by omega
  obtain ⟨j, hj⟩ := hN (q.natAbs - 1) hNn
  have hbase : ((q.natAbs - 1 : ℕ) : ℝ) + 1 = |(q : ℝ)| := by
    calc
      ((q.natAbs - 1 : ℕ) : ℝ) + 1 = ((q.natAbs - 1 + 1 : ℕ) : ℝ) := by norm_cast
      _ = (q.natAbs : ℝ) := by rw [hkn]
      _ = |(q : ℝ)| := by simp only [Nat.cast_natAbs, Int.cast_abs]
  have hsign : ‖(q.natAbs : ℤ) • (r j : UnitAddCircle)‖ =
      ‖q • (r j : UnitAddCircle)‖ := by
    rw [Int.natCast_natAbs]
    rcases le_total (0 : ℤ) q with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, neg_smul, norm_neg]
  change Real.rpow (((q.natAbs - 1 : ℕ) : ℝ) + 1) (-(3 : ℝ) / 16) <
    ‖((q.natAbs - 1 + 1 : ℕ) : ℤ) • (r j : UnitAddCircle)‖ at hj
  rw [hbase, hkn, hsign] at hj
  refine ⟨j, ?_⟩
  intro p
  apply hj.le.trans
  calc
    ‖q • (r j : UnitAddCircle)‖ = |(q : ℝ) * r j - round ((q : ℝ) * r j)| := by
      rw [← AddCircle.coe_zsmul, zsmul_eq_mul, UnitAddCircle.norm_eq]
    _ ≤ |(q : ℝ) * r j - (p : ℝ)| := round_le _ p

end
end Shao.OQ3
