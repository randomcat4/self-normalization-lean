import Shao.OQ3.FiniteConstraints

/-!
# The actual source starter for OQ3

Source: current/oq3/proofs/r1/report.md, lines 18-108.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U2 scope: cc30966e69ad95f0f1b44c673a5649ec851f4219966b7cbd6b893a36c96d5896.
The three-point second moment is distinct from the moment after adding the
fourth atom. This file constructs only the finite tilted-law starter.
-/

namespace Shao.OQ3

open scoped Matrix

noncomputable section

def sourceU : ℝ := 31 / 30
def sourceEll : ℝ := Real.log sourceU
def sourceA : ℝ := (sourceU ^ 7)⁻¹
def sourceB : ℝ := sourceU ^ 9
def sourceC : ℝ := (sourceU ^ 6)⁻¹
def sourceDenominator : ℝ :=
  sourceB * (13 + 4 * Real.sqrt 10) +
  sourceA * (5 + 4 * Real.sqrt 10) +
  8 * sourceC * (4 + Real.sqrt 10)
def sourceZ : ℝ := (3 * sourceB - 5 * sourceA) / sourceDenominator
def sourceTripleMass : Fin 3 → ℝ :=
  ![3 / 8 - (13 + 4 * Real.sqrt 10) / 8 * sourceZ,
    5 / 8 + (5 + 4 * Real.sqrt 10) / 8 * sourceZ, sourceZ]
def sourceTripleQ : ℝ := 1 + (25 + 8 * Real.sqrt 10) * sourceZ
def sourceConstraint3 : Matrix (Fin 3) (Fin 3) ℝ :=
  fun k i => constraintFeature sourceEll (baseAtom i.castSucc) k.castSucc
def sourceTripleCorrection : Fin 3 → ℝ :=
  sourceConstraint3⁻¹ *ᵥ
    (fun k => constraintFeature sourceEll (baseAtom 3) k.castSucc)
def sourceStarterWeight (delta : ℝ) : Fin 4 → ℝ :=
  ![sourceTripleMass 0 - delta * sourceTripleCorrection 0,
    sourceTripleMass 1 - delta * sourceTripleCorrection 1,
    sourceTripleMass 2 - delta * sourceTripleCorrection 2, delta]
def sourceStarterQ (delta : ℝ) : ℝ :=
  ∑ i, sourceStarterWeight delta i * (baseAtom i) ^ 2

theorem sourceEll_pos : 0 < sourceEll := by
  exact Real.log_pos (by norm_num [sourceU])

theorem source_base_centering_values :
    (fun i => centeringFeature sourceEll (baseAtom i)) =
      ![-sourceB, sourceA, (4 + Real.sqrt 10) * sourceC,
        2 * (sourceU ^ 12)⁻¹] := by
  have he (n : ℕ) : Real.exp ((n : ℝ) * sourceEll) = sourceU ^ n := by
    rw [Real.exp_nat_mul, sourceEll, Real.exp_log (by norm_num [sourceU])]
  have hn (n : ℕ) : Real.exp (-((n : ℝ) * sourceEll)) = (sourceU ^ n)⁻¹ := by
    rw [Real.exp_neg, he]
  have e9 : Real.exp (sourceEll * 9) = sourceB := by
    simpa [sourceB, mul_comm] using he 9
  have e7 : Real.exp (-(sourceEll * 7)) = sourceA := by
    simpa [sourceA, mul_comm] using hn 7
  have e6 : Real.exp (-(sourceEll * 6)) = sourceC := by
    simpa [sourceC, mul_comm] using hn 6
  have e12 : Real.exp (-(sourceEll * 12)) = (sourceU ^ 12)⁻¹ := by
    simpa [mul_comm] using hn 12
  have hy (i : Fin 4) : normalValue (baseAtom i) =
      (![-9, 7, 6, 12] : Fin 4 → ℝ) i := congrFun normalValue_baseAtom i
  ext i
  simp only [centeringFeature, hy i]
  fin_cases i <;> norm_num [baseAtom, e9, e7, e6, e12]

private theorem source_matrix4 : constraintMatrix sourceEll =
    !![1, 1, 1, 1;
      5, -3, 10 + 4 * Real.sqrt 10, -4;
      -sourceB, sourceA, (4 + Real.sqrt 10) * sourceC, 2 * (sourceU ^ 12)⁻¹;
      1, 1, 26 + 8 * Real.sqrt 10, 4] := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)
  have hc (j : Fin 4) := congrFun source_base_centering_values j
  ext i j
  fin_cases i
  · fin_cases j <;> simp [constraintMatrix, constraintFeature]
  · fin_cases j <;> norm_num [constraintMatrix, constraintFeature, boundaryFeature, baseAtom]
    nlinarith [hs]
  · simpa [constraintMatrix, constraintFeature] using hc j
  · fin_cases j <;> norm_num [constraintMatrix, constraintFeature, baseAtom]
    nlinarith [hs]

private theorem source_matrix3 : sourceConstraint3 =
    !![1, 1, 1;
      5, -3, 10 + 4 * Real.sqrt 10;
      -sourceB, sourceA, (4 + Real.sqrt 10) * sourceC] := by
  ext i j
  change constraintMatrix sourceEll i.castSucc j.castSucc = _
  rw [source_matrix4]
  fin_cases i <;> fin_cases j <;> norm_num

theorem sourceConstraint3_det : sourceConstraint3.det =
    -8 * (sourceC * (4 + Real.sqrt 10) + sourceB) -
    (sourceA + sourceB) * (5 + 4 * Real.sqrt 10) := by
  rw [source_matrix3, Matrix.det_fin_three]
  norm_num
  ring

private theorem sourceA_pos : 0 < sourceA := by norm_num [sourceA, sourceU]
private theorem sourceB_pos : 0 < sourceB := by norm_num [sourceB, sourceU]
private theorem sourceC_pos : 0 < sourceC := by norm_num [sourceC, sourceU]

theorem sourceConstraint3_det_neg : sourceConstraint3.det < 0 := by
  rw [sourceConstraint3_det]
  have hA := sourceA_pos
  have hB := sourceB_pos
  have hC := sourceC_pos
  have h1 : 0 < sourceC * (4 + Real.sqrt 10) + sourceB := by
    positivity
  have h2 : 0 < (sourceA + sourceB) * (5 + 4 * Real.sqrt 10) := by
    positivity
  linarith

theorem source_constraintMatrix_det :
    (constraintMatrix sourceEll).det =
      -(20765025879526713743120420649631 : ℝ) /
        242243227707969139777546875000 -
      (20921320404866133143120420649631 : ℝ) /
        775178328665501247288150000000 * Real.sqrt 10 := by
  rw [source_matrix4, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, sourceA, sourceB, sourceC, sourceU]
  ring

theorem source_constraintMatrix_det_neg : (constraintMatrix sourceEll).det < 0 := by
  rw [source_constraintMatrix_det]
  nlinarith [Real.sqrt_nonneg (10 : ℝ)]

theorem source_constraintMatrix_nonsingular : (constraintMatrix sourceEll).det ≠ 0 :=
  source_constraintMatrix_det_neg.ne

private theorem sourceDenominator_pos : 0 < sourceDenominator := by
  have hA := sourceA_pos
  have hB := sourceB_pos
  have hC := sourceC_pos
  unfold sourceDenominator
  positivity

private theorem sourceNumerator_pos : 0 < 3 * sourceB - 5 * sourceA := by
  norm_num [sourceA, sourceB, sourceU]

private theorem sourceZ_pos : 0 < sourceZ :=
  div_pos sourceNumerator_pos sourceDenominator_pos

private theorem sourceDenominator_mul_sourceZ :
    sourceDenominator * sourceZ = 3 * sourceB - 5 * sourceA := by
  unfold sourceZ
  exact mul_div_cancel₀ _ sourceDenominator_pos.ne'

theorem sourceTripleMass_pos : ∀ i, 0 < sourceTripleMass i := by
  have hr := Real.sqrt_nonneg (10 : ℝ)
  have hA := sourceA_pos
  have hC := sourceC_pos
  have hzpos := sourceZ_pos
  have hden : 0 < 13 + 4 * Real.sqrt 10 := by positivity
  have hdifference :
      0 < 3 * sourceDenominator -
        (3 * sourceB - 5 * sourceA) * (13 + 4 * Real.sqrt 10) := by
    have h : 0 < sourceA * (80 + 32 * Real.sqrt 10) +
        sourceC * (96 + 24 * Real.sqrt 10) := by positivity
    dsimp [sourceDenominator]
    nlinarith only [h]
  have hz : sourceZ < 3 / (13 + 4 * Real.sqrt 10) := by
    unfold sourceZ
    apply (div_lt_div_iff₀ sourceDenominator_pos hden).mpr
    linarith
  have hbound := (lt_div_iff₀ hden).mp hz
  intro i
  fin_cases i
  · norm_num [sourceTripleMass]
    nlinarith
  · norm_num [sourceTripleMass]
    positivity
  · exact sourceZ_pos

theorem sourceTriple_constraints :
    sourceConstraint3 *ᵥ sourceTripleMass = ![1, 0, 0] := by
  have hz := sourceDenominator_mul_sourceZ
  dsimp [sourceDenominator] at hz
  rw [source_matrix3]
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sourceTripleMass]
  · ring
  · ring
  · nlinarith only [hz]

private theorem source_triple_squares :
    (fun i : Fin 3 => (baseAtom i.castSucc) ^ 2) =
      ![1, 1, 26 + 8 * Real.sqrt 10] := by
  ext i
  fin_cases i <;> norm_num [baseAtom]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]

theorem sourceTriple_square_moment :
    (∑ i : Fin 3, sourceTripleMass i * (baseAtom i.castSucc) ^ 2) = sourceTripleQ := by
  simp_rw [congrFun source_triple_squares]
  norm_num [Fin.sum_univ_succ, sourceTripleMass, sourceTripleQ]
  ring

theorem sourceTripleQ_bounds : 1 < sourceTripleQ ∧ sourceTripleQ < 103 / 100 := by
  have hcert : 3 * sourceDenominator -
      100 * (25 + 8 * Real.sqrt 10) * (3 * sourceB - 5 * sourceA) =
      (299507669583416286189251 : ℝ) / 60170087060757000000000 +
      (51968216310132498132281 : ℝ) / 45127565295567750000000 * Real.sqrt 10 := by
    norm_num [sourceDenominator, sourceA, sourceB, sourceC, sourceU]
    ring
  have hmargin : 0 < 3 * sourceDenominator -
      100 * (25 + 8 * Real.sqrt 10) * (3 * sourceB - 5 * sourceA) := by
    rw [hcert]
    positivity
  have hupper : (25 + 8 * Real.sqrt 10) * sourceZ < 3 / 100 := by
    unfold sourceZ
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ sourceDenominator_pos).mpr
    nlinarith only [hmargin]
  constructor
  · unfold sourceTripleQ
    have hp : 0 < (25 + 8 * Real.sqrt 10) * sourceZ :=
      mul_pos (by positivity) sourceZ_pos
    linarith
  · unfold sourceTripleQ
    linarith

theorem sourceStarter_constraints (delta : ℝ) :
    (constraintMatrix sourceEll) *ᵥ sourceStarterWeight delta =
      constraintTarget (sourceStarterQ delta) := by
  let v : Fin 3 → ℝ := fun k => constraintFeature sourceEll (baseAtom 3) k.castSucc
  have hc : sourceConstraint3 *ᵥ sourceTripleCorrection = v := by
    unfold sourceTripleCorrection
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr sourceConstraint3_det_neg.ne),
      Matrix.one_mulVec]
  have ht : sourceConstraint3 *ᵥ (sourceTripleMass - delta • sourceTripleCorrection) +
      delta • v = ![1, 0, 0] := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hc, sourceTriple_constraints,
      sub_add_cancel]
  ext k
  fin_cases k
  · convert congrFun ht (0 : Fin 3) using 1 <;>
      norm_num [constraintMatrix, sourceConstraint3, constraintFeature, constraintTarget,
        sourceStarterWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v]
    ring
  · convert congrFun ht (1 : Fin 3) using 1 <;>
      norm_num [constraintMatrix, sourceConstraint3, constraintFeature, constraintTarget,
        sourceStarterWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v]
    ring
  · convert congrFun ht (2 : Fin 3) using 1 <;>
      norm_num [constraintMatrix, sourceConstraint3, constraintFeature, constraintTarget,
        sourceStarterWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v]
    ring
  · simp [constraintMatrix, constraintFeature, constraintTarget, sourceStarterQ,
      Matrix.mulVec, dotProduct, mul_comm]

private theorem sourceStarterQ_affine (delta : ℝ) :
    sourceStarterQ delta = sourceTripleQ + delta *
      (4 - ∑ i : Fin 3, sourceTripleCorrection i * (baseAtom i.castSucc) ^ 2) := by
  rw [← sourceTriple_square_moment]
  norm_num [sourceStarterQ, sourceStarterWeight, Fin.sum_univ_succ, baseAtom]
  ring

theorem exists_source_starter_delta :
    ∃ delta : ℝ, 0 < delta ∧ (∀ i, 0 < sourceStarterWeight delta i) ∧
      1 < sourceStarterQ delta ∧ sourceStarterQ delta < 103 / 100 := by
  let m : ℝ := min (sourceTripleMass 0)
    (min (sourceTripleMass 1) (sourceTripleMass 2))
  have hm : 0 < m := lt_min (sourceTripleMass_pos 0)
    (lt_min (sourceTripleMass_pos 1) (sourceTripleMass_pos 2))
  have hmi : ∀ i : Fin 3, m ≤ sourceTripleMass i := by
    intro i
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  let C : ℝ := |sourceTripleCorrection 0| + |sourceTripleCorrection 1| +
    |sourceTripleCorrection 2|
  have hC : 0 ≤ C := by positivity
  have hCi : ∀ i : Fin 3, |sourceTripleCorrection i| ≤ C := by
    intro i
    fin_cases i <;> dsimp [C] <;>
      linarith [abs_nonneg (sourceTripleCorrection 0),
        abs_nonneg (sourceTripleCorrection 1), abs_nonneg (sourceTripleCorrection 2)]
  let d : ℝ := 4 - ∑ i : Fin 3, sourceTripleCorrection i * (baseAtom i.castSucc) ^ 2
  let g : ℝ := min (sourceTripleQ - 1) (103 / 100 - sourceTripleQ)
  have hg : 0 < g := lt_min (by linarith [sourceTripleQ_bounds.1])
    (by linarith [sourceTripleQ_bounds.2])
  have hdenC : 0 < 1 + C := by positivity
  have hdend : 0 < 1 + |d| := by positivity
  let eps : ℝ := min (m / (1 + C)) (g / (1 + |d|))
  have heps : 0 < eps := lt_min (div_pos hm hdenC) (div_pos hg hdend)
  let delta : ℝ := eps / 2
  have hdelta : 0 < delta := half_pos heps
  have hdc : delta < m / (1 + C) :=
    (half_lt_self heps).trans_le (min_le_left _ _)
  have hdd : delta < g / (1 + |d|) :=
    (half_lt_self heps).trans_le (min_le_right _ _)
  have hcprod := (lt_div_iff₀ hdenC).mp hdc
  have hdprod := (lt_div_iff₀ hdend).mp hdd
  have hsmall : ∀ i : Fin 3, |delta * sourceTripleCorrection i| < sourceTripleMass i := by
    intro i
    rw [abs_mul, abs_of_pos hdelta]
    have hle := mul_le_mul_of_nonneg_left (hCi i) hdelta.le
    have hlt : delta * C < m := by nlinarith
    exact hle.trans_lt (hlt.trans_le (hmi i))
  have hw : ∀ i, 0 < sourceStarterWeight delta i := by
    intro i
    fin_cases i
    · exact sub_pos.mpr ((le_abs_self _).trans_lt (hsmall 0))
    · exact sub_pos.mpr ((le_abs_self _).trans_lt (hsmall 1))
    · exact sub_pos.mpr ((le_abs_self _).trans_lt (hsmall 2))
    · exact hdelta
  have hperturb : |delta * d| < g := by
    rw [abs_mul, abs_of_pos hdelta]
    nlinarith
  have haffine : sourceStarterQ delta = sourceTripleQ + delta * d :=
    sourceStarterQ_affine delta
  have hgl : g ≤ sourceTripleQ - 1 := min_le_left _ _
  have hgu : g ≤ 103 / 100 - sourceTripleQ := min_le_right _ _
  refine ⟨delta, hdelta, hw, ?_, ?_⟩
  · have hbound := neg_le_abs (delta * d)
    linarith
  · have hbound := le_abs_self (delta * d)
    linarith

theorem exists_source_starter :
    ∃ (p : Fin 4 → ℝ) (q : ℝ), (∀ i, 0 < p i) ∧
      1 < q ∧ q < 103 / 100 ∧
      (constraintMatrix sourceEll) *ᵥ p = constraintTarget q := by
  obtain ⟨delta, _, hp, hlo, hhi⟩ := exists_source_starter_delta
  exact ⟨sourceStarterWeight delta, sourceStarterQ delta, hp, hlo, hhi,
    sourceStarter_constraints delta⟩

end
end Shao.OQ3
