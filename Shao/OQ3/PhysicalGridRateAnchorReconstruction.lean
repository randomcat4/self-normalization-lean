import Shao.OQ3.PhysicalGridWeightedReconstruction
import Shao.OQ3.PhysicalWindowCellRateAnchors

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology BigOperators
noncomputable section

theorem physical_grid_rate_anchor_weighted_reconstruction
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) (hn : 1 ≤ n)
    (level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) :
    let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let Theta : Set (ℝ × ℝ) := e.symm '' V
    let Klog : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let J : (ℝ × ℝ) → ℝ := fun w =>
      (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - Klog (e.symm w)
    let I : (ℝ × ℝ) → EReal :=
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
    (∀ w ∈ V, e.symm w ∈
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) →
    (∀ aL aR qL qR : ℝ,
      let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
      let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
      A.Nonempty → ∃ y ∈ closure A, y ∈ Q ∩ V ∧ I y = (J y : EReal) ∧
        ∀ w ∈ closure A, I y ≤ I w ∧ J y ≤ J w) →
    ∀ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
       Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    let rect : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      Set.Icc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
      Set.Icc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))
    let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    0 < C ∧ ∃ K : Finset (ℤ × ℤ),
      (∀ k : ℤ × ℤ, k ∈ K ↔ (cell k).Nonempty) ∧
      (K.card : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
      ∃ y : (ℤ × ℤ) → (ℝ × ℝ),
        (∀ k ∈ K, y k ∈ closure (cell k) ∧ y k ∈ rect k ∩ V ∧
          I (y k) = (J (y k) : EReal) ∧
          ∀ w ∈ closure (cell k), I (y k) ≤ I w ∧ J (y k) ≤ J w) ∧
        let tau : (ℤ × ℤ) → (ℝ × ℝ) := fun k => e.symm (y k)
        ∃ Ec : (ℤ × ℤ) → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
          (∀ k ∈ K, tau k ∈ Theta ∧
            tau k ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) ∧
            ∀ htau : tau k ∈ Theta, Ec k = E ⟨tau k, htau⟩) ∧
          let Q : (ℤ × ℤ) → Measure (Shao.Path n) := fun k =>
            Measure.pi (fun _ : Fin n =>
              mu.tilted (fun x => (tau k).1 * x + (tau k).2 * x ^ 2))
          let F : (ℤ × ℤ) → (ℝ × ℝ) → (ℝ × ℝ) := fun k w =>
            Real.sqrt (n : ℝ) • Ec k (w - y k)
          let T : (ℤ × ℤ) → Shao.Path n → (ℝ × ℝ) := fun k z => F k (M z)
          let laws : (ℤ × ℤ) → Measure (ℝ × ℝ) := fun k => (Q k).map (T k)
          let B : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k => F k '' cell k
          let g : (ℤ × ℤ) → (ℝ × ℝ) → ℝ := fun k v =>
            Real.exp (-Real.sqrt (n : ℝ) *
              ((tau k).1 * ((Ec k).symm v).1 + (tau k).2 * ((Ec k).symm v).2))
          (∀ k ∈ K, MeasurableSet (B k) ∧ Integrable (g k) (laws k)) ∧
          P.real (M ⁻¹' V) = ∑ k ∈ K, Real.exp (-(n : ℝ) * J (y k)) *
            ∫ v : ℝ × ℝ in B k, g k v ∂laws k := by
  classical
  dsimp only
  intro hdomain hanchors E
  let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
  let Theta : Set (ℝ × ℝ) := e.symm '' V
  let Klog : (ℝ × ℝ) → ℝ := fun p => Real.log
    (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
  let J : (ℝ × ℝ) → ℝ := fun w =>
    (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - Klog (e.symm w)
  let I : (ℝ × ℝ) → EReal :=
    Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
  let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
    (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
     Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
  let rect : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
    Set.Icc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
    Set.Icc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))
  let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  obtain ⟨hC, K, hK, hcard, _, hW⟩ :=
    iid_parabola_finite_grid_weighted_reconstruction mu n hn level a0 rho hrho
  have ha (k : ℤ × ℤ) : ∃ z : ℝ × ℝ, k ∈ K →
      z ∈ closure (cell k) ∧ z ∈ rect k ∩ V ∧ I z = (J z : EReal) ∧
      ∀ w ∈ closure (cell k), I z ≤ I w ∧ J z ≤ J w := by
    by_cases hk : k ∈ K
    · obtain ⟨z, hcl, hrect, hrate, hmin⟩ := hanchors
        ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ))
        ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ)) ((hK k).1 hk)
      exact ⟨z, fun _ => ⟨hcl, hrect, hrate, hmin⟩⟩
    · exact ⟨0, fun hk' => (hk hk').elim⟩
  choose y hy using ha
  let tau : (ℤ × ℤ) → (ℝ × ℝ) := fun k => e.symm (y k)
  have htau (k : ℤ × ℤ) (hk : k ∈ K) : tau k ∈ Theta :=
    ⟨y k, (hy k hk).2.1.2, rfl⟩
  have hdom (k : ℤ × ℤ) (hk : k ∈ K) : tau k ∈
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) :=
    hdomain (y k) (hy k hk).2.1.2
  let Ec : (ℤ × ℤ) → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) := fun k =>
    if h : tau k ∈ Theta then E ⟨tau k, h⟩ else ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)
  have hEc (k : ℤ × ℤ) (h : tau k ∈ Theta) : Ec k = E ⟨tau k, h⟩ := by
    simp only [Ec, dif_pos h]
  refine ⟨hC, K, hK, hcard, y, hy, Ec,
    (fun k hk => ⟨htau k hk, hdom k hk, fun h => hEc k h⟩), ?_⟩
  exact hW tau hdom y Ec

end
end Shao.OQ3
