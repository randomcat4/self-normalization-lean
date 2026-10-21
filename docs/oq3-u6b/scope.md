# OQ3-U6b：正原子与真正联合非格点

冻结候选v1，PROPOSED；未实现，需独立声明审查。拟文件 `Shao/OQ3/JointNonlattice.lean`，导入冻结U6a、Mathlib Analysis.Convex.Integral与Complex指数周期库。命名空间Shao.OQ3，open MeasureTheory，noncomputable section。

来源R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，259–277行。这里补实际概率测度的特征函数等号桥，再消费U6a的全原子相位投影排除。目标适用于任意实线概率测度，只要每个fixedAtom都有严格正概率；不要求它仅集中于这些原子。因此不依赖尚待检查的U4，也不偷用P=π。

## 定义候选

```lean
def jointPhase (xi eta x : ℝ) : ℂ :=
  Complex.exp (((xi * x + eta * x ^ 2 : ℝ) : ℂ) * Complex.I)

def jointCharacteristic (mu : Measure ℝ) (xi eta : ℝ) : ℂ :=
  ∫ x, jointPhase xi eta x ∂mu
```

## 待冻结导出声明

```lean
theorem jointPhase_norm (xi eta x : ℝ) : ‖jointPhase xi eta x‖ = 1

theorem integrable_jointPhase (mu : Measure ℝ) [IsProbabilityMeasure mu] (xi eta : ℝ) :
  Integrable (jointPhase xi eta) mu

theorem jointCharacteristic_norm_le_one (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (xi eta : ℝ) :
  ‖jointCharacteristic mu xi eta‖ ≤ 1

theorem jointPhase_eq_of_modulus_one (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (xi eta : ℝ) (hmod : ‖jointCharacteristic mu xi eta‖ = 1)
    (x y : ℝ) (hx : 0 < mu.real {x}) (hy : 0 < mu.real {y}) :
  jointPhase xi eta x = jointPhase xi eta y

theorem jointPhase_eq_iff_lattice (xi eta x y : ℝ) :
  jointPhase xi eta x = jointPhase xi eta y ↔
    ∃ m : ℤ, xi * (x - y) + eta * (x ^ 2 - y ^ 2) = (2 * Real.pi) * (m : ℝ)

theorem jointCharacteristic_norm_lt_one_of_positive_atoms (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hpos : ∀ i, 0 < mu.real {fixedAtom i})
    (xi eta : ℝ) (hne : xi ≠ 0 ∨ eta ≠ 0) :
  ‖jointCharacteristic mu xi eta‖ < 1
```

两个定义、六目标。二维频率由xi/eta一起量化；最后非零门为二者至少一个非零，不是只控制X或只控制X²的一维非格点。这里没有把有限阶段律代入结论：有限阶段不能满足整个无限原子族的正质量前提。

## 验收风险

- 复积分为实际概率测度下的特征函数；先证单位相位的真实Integrable，范数≤1不能靠不可积总化为0的默认值冒充。
- 模一→常相位须证明实际AE结论或等价积分严格凸等号条件；再用指定单点实概率严格正，把AE关系提升到每个指定原子，不能从AE直接声称所有点。
- 实指数相位的周期是2π整数，xi/eta为实数；等价式须保留整数证人和正确符号/2π因子，不能只证明单向或模数漏2π。
- 消费U6a时，选实际旧原子beta=fixedAtom(Sum.inl 2)为同一相位基准，再对全索引给固定格距2π的关系。必须使用beta原子严格正，不能把极限点当作自动正原子。
- hpos在整个Fin4⊕ℕ上，不能弱化为只有限或只旧点。generic结论即使允许另外连续支撑仍应成立。
- 本单元不构造原律P或连接其source family，不证明强非格点失败、逃向无穷近共振、LLT、尖点、对角或完整根A/B/C/D。后续U4与本定理结合后，才可为实际P取得此联合非格点性质。
