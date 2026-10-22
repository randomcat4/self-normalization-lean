# OQ3-U8：真实有限阶段的最大法向格距

冻结候选v1，PROPOSED；未实现，须独立声明审查。拟文件 `Shao/OQ3/FiniteNormalSpan.lean`，只导入U3c `FiniteStageMeasure` 与U6c `ResonanceArithmetic`。命名空间Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。

来源R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，113–119、396–406行。源J>=1的最大格距为h_J=2^-J；本单元另把J=0的四旧点情形精确列为h_0=1。已有scaled_integer只给网格包含，不能替代最大性；必须从真实正质量原子排除更大的任意平移网格。

下面定义消费实际测度在x上的AE法向取值，不只是一个抽象有限集。允许任意平移offset，故最大性也不偷限到零点网格。正实span与真实单点正质量排除零测度/虚支撑情形。泛型引理不要求mu概率；实际族仍由U3c同时保持原有概率性与参数固定性，本单元不重复构造。

## 待冻结导出声明

```lean
def HasNormalLattice (mu : Measure ℝ) (h : ℝ) : Prop :=
  0 < h ∧ ∃ offset : ℝ, ∀ᵐ x ∂mu, ∃ k : ℤ,
    normalValue x = offset + h * (k : ℝ)

def IsMaximalNormalLattice (mu : Measure ℝ) (h : ℝ) : Prop :=
  HasNormalLattice mu h ∧ ∀ h' : ℝ, HasNormalLattice mu h' → h' ≤ h

theorem stageAtom_normalValue_lattice (J : ℕ) (i : Fin 4 ⊕ Fin J) :
  ∃ k : ℤ, normalValue (stageAtom (fun j : Fin J => addedAtom j.val) i) =
    dyadicMesh J * (k : ℝ)

theorem addedAtom_normal_difference (J : ℕ) :
  normalValue (addedAtom J) - normalValue (baseAtom 2) = dyadicMesh (J + 1)

theorem normal_lattice_of_stage_range (mu : Measure ℝ) (J : ℕ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)) :
  HasNormalLattice mu (dyadicMesh J)

theorem normal_lattice_span_le_of_positive_atoms (mu : Measure ℝ) (h : ℝ)
    (hspan : HasNormalLattice mu h) (x y : ℝ)
    (hx : 0 < mu.real {x}) (hy : 0 < mu.real {y})
    (hdiff : 0 < normalValue x - normalValue y) :
  h ≤ normalValue x - normalValue y

theorem stage_normal_span_maximal (mu : Measure ℝ) (J : ℕ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
  IsMaximalNormalLattice mu (dyadicMesh J)

theorem finite_atomic_normal_span_maximal (ell : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ)
    (hp : ∀ i, 0 < finiteBase ell p r J i) (hr : ∀ j, 0 < r j) :
  IsMaximalNormalLattice (atomicMeasure (finiteMass ell p r J)) (dyadicMesh J)

theorem finite_original_normal_span_maximal (ell q : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 < finiteBase ell p r J i) (hr : ∀ j, 0 < r j) :
  IsMaximalNormalLattice (originalMeasure ell (finiteMass ell p r J)) (dyadicMesh J)

theorem exists_source_finite_maximal_normal_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      ∀ J : ℕ,
        IsMaximalNormalLattice (atomicMeasure (finiteMass sourceEll p r J)) (dyadicMesh J) ∧
        IsMaximalNormalLattice (originalMeasure sourceEll (finiteMass sourceEll p r J))
          (dyadicMesh J)
```

## 来源和裁决界限

两定义、八目标。U6c scaled_integer给实际有限原子的全部法向值落在dyadicMesh J的零平移网格。J>=1时最新原子addedAtom(J-1)与旧点baseAtom2的法向差恰为h_J；J=0由baseAtom1与baseAtom2的法向值7、6之差1。任意AE平移网格在这些真实正质量点仍成立，二点差是h'的非零整数倍，从而h'不超过该正差。三旧点中的1、2都一直有正质量，不需要新增原子在J=0存在。

finite_atomic版本要求补偿后四旧权重正与整条r正，用既有真实singleton公式及finite AE range；有限未来零权不参与正性前提。finite_original版本由既有finite_original_atom_pos及AE range给相同最大span，未把倾斜律pi当成P。最后一目标只固定一次p/q/eps，再对任意整条r和全部J同时给两种真实测度的结论；不先选r再重选q或eps，不引入依赖n的律。

本单元不证明混合局部极限、相位返回、尾估计、曲层常数或最终反例。不声称有限阶段联合非格点；有限法向格点正是这里的结论。最大span接口是后续只在Y上Fourier反演的必要输入。所有根A/B/C/D保持OPEN。
