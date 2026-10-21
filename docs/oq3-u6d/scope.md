# OQ3-U6d：逃逸共振与固定原律的弱非格点分类

冻结候选v1，PROPOSED；未实现，需独立声明审查。拟文件 `Shao/OQ3/ResonantLimit.lean`，导入冻结U4、U6b、U6c及所需Bochner支配收敛库。命名空间Shao.OQ3，open MeasureTheory Filter，open scoped Matrix，noncomputable section。无新定义。

来源R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，259–292行。源的weakly nonlattice是逐非零二维频率模严格小于1，同时存在逃逸频率模趋1；不是定量弱Cramér下界。本单元只完成此分类，不完成尾展开反例。

可以使用与源尾质量估计等价的支配收敛路线：每个固定原子在足够大J后相位恒为1，实际概率测度几乎处处集中于原子值域，相位范数恒为1可积。逐原子的阈值允许依赖原子，不能升级成某阶段同时对齐整个无限族。

## 待冻结导出声明

```lean
theorem jointPhase_resonance_of_scaled_integer (J : ℕ) (x : ℝ)
    (h : ∃ m : ℤ, (2 : ℝ) ^ J * normalValue x = (m : ℝ)) :
  jointPhase (resonanceXi J) (resonanceEta J) x = 1

theorem fixedAtom_jointPhase_eventually_one (i : AtomicIndex) :
  ∀ᶠ J in Filter.atTop, jointPhase (resonanceXi J) (resonanceEta J) (fixedAtom i) = 1

theorem jointPhase_resonance_ae_tendsto (mu : Measure ℝ)
    (hsupp : ∀ᵐ x ∂mu, x ∈ Set.range fixedAtom) :
  ∀ᵐ x ∂mu, Filter.Tendsto
    (fun J => jointPhase (resonanceXi J) (resonanceEta J) x) Filter.atTop (nhds 1)

theorem jointCharacteristic_resonance_tendsto_one (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hsupp : ∀ᵐ x ∂mu, x ∈ Set.range fixedAtom) :
  Filter.Tendsto (fun J => jointCharacteristic mu (resonanceXi J) (resonanceEta J))
    Filter.atTop (nhds 1)

theorem jointCharacteristic_resonance_norm_tendsto_one (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hsupp : ∀ᵐ x ∂mu, x ∈ Set.range fixedAtom) :
  Filter.Tendsto (fun J => ‖jointCharacteristic mu (resonanceXi J) (resonanceEta J)‖)
    Filter.atTop (nhds (1 : ℝ))

theorem exists_source_weakly_nonlattice_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (∫ x, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
      (∀ᵐ x ∂originalMeasure sourceEll (limitingMass sourceEll p r),
        1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        ‖jointCharacteristic (originalMeasure sourceEll (limitingMass sourceEll p r)) xi eta‖ < 1) ∧
      Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun J => ‖jointCharacteristic
        (originalMeasure sourceEll (limitingMass sourceEll p r)) (resonanceXi J) (resonanceEta J)‖)
        Filter.atTop (nhds (1 : ℝ))
```

零定义、六目标。generic复积分极限只要求概率性及a.e.原子值域，不要求全部原子质量严格正；最终source family的严格联合非格点另消费U4的全原子正质量。µ若有原子值域外的连续质量，则不能套用generic共振极限；这与U6b允许额外连续质量的严格非格点接口不同。

## 验收风险

- 复指数周期精确为2π整数，不能以相位实数趋0代替相位最终等于1的精确来源。
- 每个x的点态极限要从同一无限原子族取其索引，再取依赖该索引的阈值。概率积分极限须证明AE收敛和实际可积支配，不能以逐点最终性推出统一频率gap。
- 指数相位范数恒为1提供真正L1支配；必须使用固定同一mu，不能让概率测度随J变成有限阶段mu_J。
- 最终mu是U4的originalMeasure(P)，不是atomicMeasure(π)。它的a.e.原子值域可由倾斜的绝对连续性和atomicMeasure_ae_range推出，不能只凭有界支撑界推出可数原子支撑。
- 最终p/q/eps先于全部r/J/n固定；r是之后选定的一条整序列，P不随频率J或样本n改变。
- 逃逸频率的实范数和→∞必须显式保留；只有CF模趋1而频率不逃逸，不能说明强非格点失败。
- 本单元不证明任何多项式弱Cramér条件的失败，也不实现正KL/鞍点唯一性、有限阶段LLT、完整曲边界常数、尖点差异或witness后选尾对角。根A/B/C/D仍OPEN。
