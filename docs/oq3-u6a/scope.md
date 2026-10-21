# OQ3-U6a：累积原子排除非零二维格点投影

冻结候选 v1，PROPOSED；未实现，需独立声明审查。拟文件 `Shao/OQ3/AtomProjection.lean`，导入冻结 U3a 与基础极限库。命名空间 Shao.OQ3，open Filter，noncomputable section。此单元独立于U4的原律构造；只证明原子几何，不输出特征函数模严格小于1的测度结论。

R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，113–119行的新增原子极限，259–277行从累积原子排除非零相位投影的论证。真正联合非格点还需另证概率测度的三角不等式等号条件和每个原子严格正；本单元不偷换该概率接口。

## 待冻结导出声明

```lean
theorem dyadicMesh_tendsto_zero :
  Filter.Tendsto dyadicMesh Filter.atTop (nhds (0 : ℝ))

theorem addedAtom_tendsto :
  Filter.Tendsto addedAtom Filter.atTop (nhds (4 + Real.sqrt 10))

theorem eventually_zero_of_lattice_tendsto_zero (c : ℝ) (hc : 0 < c) (f : ℕ → ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    (hmem : ∀ j, ∃ m : ℤ, f j = c * (m : ℝ)) :
  ∀ᶠ j in Filter.atTop, f j = 0

theorem fixedAtom_no_projection_lattice (c : ℝ) (hc : 0 < c) (xi eta : ℝ)
    (hmem : ∀ i : AtomicIndex, ∃ m : ℤ,
      xi * (fixedAtom i - (4 + Real.sqrt 10)) +
        eta * ((fixedAtom i) ^ 2 - (4 + Real.sqrt 10) ^ 2) = c * (m : ℝ)) :
  xi = 0 ∧ eta = 0
```

零新定义、四目标。c 为任意正实格距，允许最终取2π；等式写真实整数m，不借总化取整或浮点近似。投影先减去同一固定旧原子 beta=4+√10 的相位，因此适合消费常相位模2π的概率结论。

## 验收风险

- 采用整个自然数新增族，源j≥1仍对应Lean k=j−1；不能把有限阶段原子误当无穷累积族。
- 实格点cℤ的趋零序列最终为0，须用c>0的固定离散间隔；不能只从整数存在就宣称各项0，也不能令c随j缩小。
- addedAtom严格小于beta且全新增索引单射已在U1证明，可用于非零因子的消去；不能仅从极限收敛推出任意两项不同。
- 从两个足够大的不同新增原子给出的线性关系，才可推出eta=0和xi=0；一条关系不足以排除非零投影。
- 没有概率测度、原子正质量、复积分或特征函数定义，故这里只认证相位格点投影排除；真正联合非格点、逃向无穷近共振及根A/B/C/D仍OPEN。
