# OQ3-U6c：嵌套法向格点与逃向无穷的共振频率

冻结候选v1，PROPOSED；未实现，需独立声明审查。拟文件 `Shao/OQ3/ResonanceArithmetic.lean`，导入冻结U6a。命名空间Shao.OQ3，open Filter，noncomputable section。本单元独立于U4/U6b缺失的共享分析缓存，不修改共用入口/pins/cache。

来源R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，113–119和279–291行。取Q_J=2^J，频率(xi_J,eta_J)=(16πQ_J,−2πQ_J)。本单元只给整数相位对齐与频率逃逸；没有复积分极限、特征函数模趋1或概率强非格点失败结论。

## 定义候选

```lean
def resonanceXi (J : ℕ) : ℝ := 16 * Real.pi * (2 : ℝ) ^ J

def resonanceEta (J : ℕ) : ℝ := -2 * Real.pi * (2 : ℝ) ^ J
```

## 待冻结导出声明

```lean
theorem stageAtom_normalValue_scaled_integer (J : ℕ) (i : Fin 4 ⊕ Fin J) :
  ∃ m : ℤ, (2 : ℝ) ^ J * normalValue
    (stageAtom (fun j : Fin J => addedAtom j.val) i) = (m : ℝ)

theorem fixedAtom_eventually_scaled_integer (i : AtomicIndex) :
  ∀ᶠ J in Filter.atTop, ∃ m : ℤ,
    (2 : ℝ) ^ J * normalValue (fixedAtom i) = (m : ℝ)

theorem resonance_phase_normalValue (J : ℕ) (x : ℝ) :
  resonanceXi J * x + resonanceEta J * x ^ 2 =
    (2 * Real.pi) * (2 : ℝ) ^ J * normalValue x

theorem resonance_frequency_escape :
  Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
    Filter.atTop Filter.atTop

theorem fixedAtom_eventually_resonant (i : AtomicIndex) :
  ∀ᶠ J in Filter.atTop, ∃ m : ℤ,
    resonanceXi J * fixedAtom i + resonanceEta J * (fixedAtom i) ^ 2 =
      (2 * Real.pi) * (m : ℝ)
```

两个定义、五目标。源J≥1的结论在此也允许J=0的空新增阶段；四旧原子的Y都为整数，故此扩展正确且不宣称J=0的最大span。每个固定新增原子在J≥j+1以后对齐，阈值可依赖该原子，不偷换成某有限J同时对齐整个无限族。

## 验收风险

- J阶段的Fin J新增指标为0,…,J−1，内含mesh(j+1)；必须由j+1≤J保证2^J整除/消去相应dyadic分母。
- 整数证人必须是精确ℤ嵌入，不能用近似整数或实数证人替代。
- 固定原子的eventually量词先给i，再取依赖i的最终阈值；不声称所有无限原子在同一J一齐对齐。
- 二次相位与normalValue的恒等须保持xi/eta的16π和−2π及Y=8x−x²，避免符号或倍数失配。
- 频率逃逸是实际|xi_J|+|eta_J|→∞，需π>0且2^J→∞；不能只证明某分量非零。
- 尚无概率测度或复相位积分极限。真正联合非格点、强非格点失败、LLT、对角和完整根A/B/C/D仍OPEN。
