# ClippedDeletionEnvelope — exact qualified interface

Original p51 S13 deterministic/measurable deletion support: four nonnegative envelopes; retained-coordinate invariance and measurable factorization; exact original-n signed deletion, reverse-triangle and exact B cost. No S14 expectation fee or probability/root theorem is claimed.

Source SHA256: 2a74d49a472f6015212a18db330ce7e81f31bae2885019219d10cf10ef35b5a0; bytes: 13584.

Complete source heads:

```lean
def residualStatisticDDeleted (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) (i : Fin n) : ℝ :=
  Shao.OQ5.P35.unorderedPairSum
      (Shao.OQ6.ResidualDeletion.eraseIncident
        (fun j k : Fin n => r (x j) (x k)) i) /
    (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))

def residualEnergyJDeleted (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) (i : Fin n) : ℝ :=
  (∑ j : Fin n,
    (Shao.OQ6.ResidualDeletion.rowSum
      (Shao.OQ6.ResidualDeletion.eraseIncident
        (fun k l : Fin n => r (x k) (x l)) i) j) ^ 2) /
    ((n : ℝ) - 2) ^ 2

def studentizerClipBudgetDeleted (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (C0 rho y : ℝ)
    (x : Fin n → Ω) (i : Fin n) : ℝ :=
  C0 * (((1 + rho) * y) / Real.sqrt (n : ℝ) +
    residualEnergyJDeleted n r x i /
      ((1 + rho) * y * Real.sqrt (n : ℝ)))

theorem residualEnergyJ_eq_rowSqSum
    (n : ℕ) {Ω : Type u} (r : Ω → Ω → ℝ) (x : Fin n → Ω) :
    residualEnergyJ n r x =
      (∑ j : Fin n,
        (Shao.OQ6.ResidualDeletion.rowSum
          (fun k l : Fin n => r (x k) (x l)) j) ^ 2) /
        ((n : ℝ) - 2) ^ 2

theorem clippedDeletion_envelopes_nonneg
    (n : ℕ) {Ω : Type u} (r : Ω → Ω → ℝ)
    (C0 rho y : ℝ) (x : Fin n → Ω) (i : Fin n)
    (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho) (hy : 0 ≤ y) :
    0 ≤ |residualStatisticD n r x| ∧
    0 ≤ studentizerClipBudget n r C0 rho y x ∧
    0 ≤ |residualStatisticDDeleted n r x i| ∧
    0 ≤ studentizerClipBudgetDeleted n r C0 rho y x i

theorem clippedDeletion_coordinate_invariant
    (n : ℕ) {Ω : Type u} (r : Ω → Ω → ℝ)
    (C0 rho y : ℝ) (i : Fin n) (x z : Fin n → Ω)
    (hxz : ∀ j : Fin n, j ≠ i → x j = z j) :
    residualStatisticDDeleted n r x i = residualStatisticDDeleted n r z i ∧
    residualEnergyJDeleted n r x i = residualEnergyJDeleted n r z i ∧
    studentizerClipBudgetDeleted n r C0 rho y x i =
      studentizerClipBudgetDeleted n r C0 rho y z i

theorem clippedDeletion_measurable_factorization
    (n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2))
    (C0 rho y : ℝ) (i : Fin n) :
    Measurable (fun x : Fin n → Ω => |residualStatisticD n r x|) ∧
    Measurable (fun x : Fin n → Ω => studentizerClipBudget n r C0 rho y x) ∧
    ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ,
      Measurable E ∧
      ∀ x : Fin n → Ω,
        (|residualStatisticDDeleted n r x i|,
          studentizerClipBudgetDeleted n r C0 rho y x i) =
            E (fun j : {j : Fin n // j ≠ i} => x j.val)

theorem clippedDeletion_cost_identities
    (n : ℕ) {Ω : Type u} (r : Ω → Ω → ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a)
    (C0 rho y : ℝ) (x : Fin n → Ω) (i : Fin n)
    (hn : 4 ≤ n) (hC0 : 0 ≤ C0) (hrho : 0 ≤ rho) (hy : (1 : ℝ) ≤ y) :
    let M : Fin n → Fin n → ℝ := fun j k : Fin n => r (x j) (x k)
    let psi : Fin n → ℝ := fun j : Fin n =>
      Shao.OQ6.ResidualDeletion.rowSum M j
    let Lambda : ℝ := ∑ j : Fin n, (psi j) ^ 2
    let LambdaDeleted : ℝ := ∑ j : Fin n,
      (Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident M i) j) ^ 2
    residualStatisticD n r x - residualStatisticDDeleted n r x i =
      psi i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1)) ∧
    abs (abs (residualStatisticD n r x) - abs (residualStatisticDDeleted n r x i)) ≤
      |residualStatisticD n r x - residualStatisticDDeleted n r x i| ∧
    residualEnergyJ n r x - residualEnergyJDeleted n r x i =
      (Lambda - LambdaDeleted) / ((n : ℝ) - 2) ^ 2 ∧
    Lambda - LambdaDeleted = (psi i) ^ 2 +
      ∑ j ∈ Finset.univ.erase i,
        (2 * M i j * (psi j - M i j) + (M i j) ^ 2) ∧
    studentizerClipBudget n r C0 rho y x -
        studentizerClipBudgetDeleted n r C0 rho y x i =
      C0 * (residualEnergyJ n r x - residualEnergyJDeleted n r x i) /
        ((1 + rho) * y * Real.sqrt (n : ℝ)) ∧
    |studentizerClipBudget n r C0 rho y x -
        studentizerClipBudgetDeleted n r C0 rho y x i| =
      C0 * |Lambda - LambdaDeleted| /
        (((n : ℝ) - 2) ^ 2 * ((1 + rho) * y * Real.sqrt (n : ℝ)))
```

Validation: qualified complete independent source/proof review, complete actual all-module TYPE/required non-theorem FULLVALUE and transitive axiom audit on the first original object. Old source/check evidence is reused exactly. Prior-freeze/data-contract attachments preserve their original bytes; repair amendments are authoritative for corrected notation. Native212 has 0 source warnings; native213 has 11. Both actual native and same-original-object audits exit0; strict wrapper success is false with the standing134B mathlib stderr (213 also has source stdout warnings), and FIRSTEMPTY is null because it is not a runner field. No merge or root completion is claimed.
