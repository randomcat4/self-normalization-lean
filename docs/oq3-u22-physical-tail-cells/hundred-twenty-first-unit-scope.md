# OQ3 unit121 (U22an): actual zero-convention tail and near/far probability split
Frozen before implementation. Source report.md section1 zero-energy convention and physicalTail; sections3–4 local/exterior split. Direct consumer actual cell/retilting probability and the separately required far-field bound after AL local integral. Two public theorems,0globaldefinitions.
The statistic explicitly equals zero on actual energy=0. This must not create a spurious positive tail. n>=1 andlevel>0 are explicit. Actual samplemean uses actual raw first/second sums, not centered substitutes or arbitrary random maps. Second law is precisely iid mu finite product pushed forward by this map. Measurable U only; no probability asymptotic or approximation is a premise.
```lean
theorem sample_self_normalized_tail_iff
    (level : ℝ) (hlevel : 0 < level) (n : ℕ) (hn : 1 ≤ n) (z : Shao.Path n) :
    let M : ℝ × ℝ :=
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    level * Real.sqrt (n : ℝ) ≤
        (if Shao.energy z = 0 then 0 else (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z)) ↔
      0 < M.2 ∧ level * Real.sqrt M.2 ≤ M.1

theorem iid_self_normalized_tail_map_and_split
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (level : ℝ) (hlevel : 0 < level) (n : ℕ) (hn : 1 ≤ n)
    (U : Set (ℝ × ℝ)) (hU : MeasurableSet U) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
    let T : Set (Shao.Path n) := {z | level * Real.sqrt (n : ℝ) ≤
      (if Shao.energy z = 0 then 0 else (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z))}
    MeasurableSet Tail ∧ MeasurableSet T ∧
      P.real T = (Measure.map M P).real Tail ∧
      P.real T = (Measure.map M P).real (U ∩ Tail) +
        (Measure.map M P).real (Tail \ U)
```
All strict/inclusive boundary signs and measure domains frozen. No actual local probability-to-integral approximation or far exponential bound is asserted; original B/D stillOPEN. Exact server kernel/whole-owner axioms and fresh full semantic/proof/alltypes/localvalue review required.
