# OQ3-U5b：允许零延拓的实际离散熵与各有限阶段正率

冻结候选v1，PROPOSED；未实现，须独立声明审查。拟文件 `Shao/OQ3/FiniteStageRate.lean`，导入冻结U5a与U3c、所需严格Jensen库。命名空间Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。无新定义。

来源R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，137–159与251–258行，特别是 `Lambda0=ell*q+logZ=D(pi||P)>0` 及同一论证适用于每个有限阶段。U5a要求每个无限索引w严格正，不能直接覆盖U3c的零延拓有限质量；本单元显式补这个接口，保留既有源码不动。

允许w_i=0时，整个加权项按标准离散相对熵约定为零；不能单独对log(0/0)使用实对数除法公式。应先分w_i=0和w_i>0，再证明加权似然恒等式及真实HasSum。w_i>0时P的同一点质量也严格正；双方均集中于单射fixedAtom值域，因此该和仍是标准离散D(pi||P)。

## 待冻结导出声明

```lean
theorem weighted_original_log_atom_ratio (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) :
  w i * Real.log (w i / (originalMeasure ell w).real {fixedAtom i}) =
    w i * (ell * normalValue (fixedAtom i) + Real.log (inverseNormalizer ell w))

theorem originalAtomEntropy_hasSum_of_nonneg (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  HasSum (fun i => w i * Real.log (w i / (originalMeasure ell w).real {fixedAtom i}))
    (saddleRate ell q w)

theorem originalAtomEntropy_eq_of_nonneg (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  originalAtomEntropy ell w = saddleRate ell q w

theorem inverseNormalizer_gt_exp_of_two_positive_atoms (ell q : ℝ) (hell : ell ≠ 0)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) (i j : AtomicIndex) (hi : 0 < w i) (hj : 0 < w j)
    (hne : normalValue (fixedAtom i) ≠ normalValue (fixedAtom j)) :
  Real.exp (-ell * q) < inverseNormalizer ell w

theorem entropy_rate_pos_of_two_positive_atoms (ell q : ℝ) (hell : ell ≠ 0)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) (i j : AtomicIndex) (hi : 0 < w i) (hj : 0 < w j)
    (hne : normalValue (fixedAtom i) ≠ normalValue (fixedAtom j)) :
  0 < saddleRate ell q w ∧ 0 < originalAtomEntropy ell w

theorem finite_original_entropy_rate (ell q : ℝ) (hell : ell ≠ 0)
    (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 < finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j) :
  originalAtomEntropy ell (finiteMass ell p r J) = saddleRate ell q (finiteMass ell p r J) ∧
    0 < saddleRate ell q (finiteMass ell p r J) ∧
    0 < originalAtomEntropy ell (finiteMass ell p r J)

theorem exists_source_finite_and_limit_entropy_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (originalAtomEntropy sourceEll (limitingMass sourceEll p r) =
        saddleRate sourceEll q (limitingMass sourceEll p r) ∧
        0 < saddleRate sourceEll q (limitingMass sourceEll p r)) ∧
      ∀ J : ℕ, IsProbabilityMeasure (originalMeasure sourceEll (finiteMass sourceEll p r J)) ∧
        (originalAtomEntropy sourceEll (finiteMass sourceEll p r J) =
          saddleRate sourceEll q (finiteMass sourceEll p r J) ∧
          0 < saddleRate sourceEll q (finiteMass sourceEll p r J))
```

零定义、七目标。对一般非负w，严格性只要求两个具有正质量且normalValue不同的实际原子，不能把X不同自动当成Y不同。ell≠0不可删除，i/j在每个声明中先给定，不能依据J/n后换固定原律。一般熵恒等式本身无需ell≠0，两原子严格性仅用于正率。

有限阶段使用两个正基点-1和1，其法向值-9与7不同；即使J=0仍提供严格性。新增前缀r可只非负，零质量的未来索引不能通过全w>0假设偷过。最终存在量词统一采用U3c同一p/q/eps，使有限和极限律同时为真概率、熵恒等且正率；对固定r的所有J均成立，不重选q/P/参数。

本单元没有将严格正KL误作全局正尾鞍点唯一性；后者还需要R1第3节的数据处理和三段全局比较。不证明协方差正定、有限阶段LLT、曲边界常数、尖点、产品TV或先witness后选尾对角。根ABCD仍OPEN。
