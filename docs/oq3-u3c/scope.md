# OQ3-U3c：与极限律共享参数的真实有限阶段概率律

冻结候选v1，PROPOSED；未实现，须独立声明审查。拟文件 `Shao/OQ3/FiniteStageMeasure.lean`，导入冻结U4与必要有限和/HasSum库。命名空间Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。

来源R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，113–145行。补齐目前U1有限有符号矩恒等式到实际有限概率测度pi_J/P_J的桥。沿用唯一整条r，前J个自然数指标j=0,...,J-1对应源j=1,...,J；不把截断r随J的总质量或正性当成新可选参数。所有阶段与极限共享同一p/q/eps。

有限阶段使用AtomicIndex上的零延拓，不重定义fixedAtom，也不把固定无限律P换成P_J参与既有共振极限。未激活的新增原子质量为零，因此不能套用要求每个无限索引严格正的U5a熵定理；本单元不宣称有限阶段正KL、鞍点或LLT已完成。

## 待冻结导出声明

```lean
def finiteMass (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ) : AtomicIndex → ℝ :=
  Sum.elim (finiteBase ell p r J) (fun j => if j < J then r j else 0)

theorem finiteMass_constraints (ell q : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q) :
  ∀ k, HasSum (fun i => finiteMass ell p r J i * constraintFeature ell (fixedAtom i) k)
    (constraintTarget q k)

theorem exists_uniform_finite_radius (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) :
  ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℕ → ℝ),
    (∀ j, 0 ≤ r j) → Summable r → (∑' j, r j) < eps →
    ∀ (J : ℕ) (i : Fin 4), 0 < finiteBase ell p r J i

theorem finiteMass_nonneg (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j) :
  ∀ i, 0 ≤ finiteMass ell p r J i

theorem atomicMeasure_finiteMass_ae_range (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ) :
  ∀ᵐ x ∂atomicMeasure (finiteMass ell p r J),
    x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)

theorem originalMeasure_finiteMass_ae_range (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ) :
  ∀ᵐ x ∂originalMeasure ell (finiteMass ell p r J),
    x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)

theorem finite_original_properties (ell q : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j) :
  IsProbabilityMeasure (originalMeasure ell (finiteMass ell p r J)) ∧
    (Integrable (fun x : ℝ => x) (originalMeasure ell (finiteMass ell p r J)) ∧
      (∫ x, x ∂originalMeasure ell (finiteMass ell p r J)) = 0) ∧
    (∀ᵐ x ∂originalMeasure ell (finiteMass ell p r J),
      1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
    (originalMeasure ell (finiteMass ell p r J)).tilted
      (fun x => ell * normalValue x) = atomicMeasure (finiteMass ell p r J)

theorem finite_original_atom_pos (ell q : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 < finiteBase ell p r J i) (hr : ∀ j, 0 < r j)
    (i : Fin 4 ⊕ Fin J) :
  0 < (originalMeasure ell (finiteMass ell p r J)).real
    {stageAtom (fun j : Fin J => addedAtom j.val) i}

theorem exists_source_finite_and_limit_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      (∀ i, 0 < limitingMass sourceEll p r i) ∧
      (∀ k, HasSum (fun i => limitingMass sourceEll p r i *
        constraintFeature sourceEll (fixedAtom i) k) (constraintTarget q k)) ∧
      ∀ J : ℕ, (∀ i, 0 < finiteBase sourceEll p r J i) ∧
        (∀ k, HasSum (fun i => finiteMass sourceEll p r J i *
          constraintFeature sourceEll (fixedAtom i) k) (constraintTarget q k)) ∧
        IsProbabilityMeasure (originalMeasure sourceEll (finiteMass sourceEll p r J)) ∧
        (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (finiteMass sourceEll p r J)) ∧
          (∫ x, x ∂originalMeasure sourceEll (finiteMass sourceEll p r J)) = 0) ∧
        (∀ᵐ x ∂originalMeasure sourceEll (finiteMass sourceEll p r J),
          x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
            stageAtom (fun j : Fin J => addedAtom j.val) i))
```

一定义、八目标。一般有限矩恒等式允许有符号r；实际概率结论明确消费非负质量。AE有限值域目标不需要概率性，因为零延拓使值域外的正部质量总为零。active support严格正性只对Fin4⊕FinJ陈述，不能输出所有AtomicIndex严格正。

J=0必须包括：此时无新增原子，Fin0分支空，finiteBase=p，阶段是原四点starter。任何有限J也不能声称其支持已经包含无限新增族，或把它称为严格联合非格点（有限阶段源本来具有法向格点）。

最终量词先固定p/q/eps，后选一整条r，再对全部J；可用两个正半径的min统一有限正性与极限正性，但不能对每个J重选p/q。均值零与有界/下界支撑属于P_J，四矩约束属于pi_J，两律不能互换。尾质量的定量TV控制、产品测度、先witness后选尾对角、正KL、全局鞍点唯一性与LLT均不在此单元，根ABCD仍OPEN。
