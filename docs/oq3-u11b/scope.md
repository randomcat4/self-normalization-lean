# OQ3-U11b：补偿映射的显式尾质量界

冻结候选v1，PROPOSED；尚未实现。拟文件 `Shao/OQ3/AtomicTailControl.lean`，导入已审 `Shao.OQ3.FiniteStageMeasure`，namespace Shao.OQ3，open scoped Matrix，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，122–135、516–520的固定有界线性补偿门。当前U3a只给finiteBase趋于limitingBase，本单元给对全部阶段J、同一整条r的显式L1误差<=固定常数乘未来总质量。这是(29)的权重层输入，测度总变差桥仍须另证。

## 待冻结导出声明

```lean
def compensationTailConstant (ell : ℝ) : ℝ :=
  (4 + Real.sqrt 10) ^ 2 *
    (∑ i : Fin 4, ∑ k : Fin 4, |(constraintMatrix ell)⁻¹ i k|) + 1

def atomicMassL1 (w v : AtomicIndex → ℝ) : ℝ :=
  ∑' i, |w i - v i|

theorem compensationTailConstant_pos (ell : ℝ) :
  0 < compensationTailConstant ell

theorem infiniteAddedMoment_sub_prefix (ell : ℝ) (hell : 0 ≤ ell) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) (k : Fin 4) :
  infiniteAddedMoment ell r k -
      (∑ j : Fin J, r j.val * constraintFeature ell (addedAtom j.val) k) =
    ∑' j, r (J + j) * constraintFeature ell (addedAtom (J + j)) k

theorem addedMoment_tail_abs_le (ell : ℝ) (hell : 0 ≤ ell) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) (k : Fin 4) :
  |∑' j, r (J + j) * constraintFeature ell (addedAtom (J + j)) k| ≤
    (4 + Real.sqrt 10) ^ 2 * (∑' j, r (J + j))

theorem limitingBase_sub_finiteBase_tail (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) (i : Fin 4) :
  limitingBase ell p r i - finiteBase ell p r J i =
    -(∑ k : Fin 4, (constraintMatrix ell)⁻¹ i k *
      (∑' j, r (J + j) * constraintFeature ell (addedAtom (J + j)) k))

theorem limitingBase_finiteBase_l1_le (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) :
  (∑ i : Fin 4, |limitingBase ell p r i - finiteBase ell p r J i|) ≤
    (compensationTailConstant ell - 1) * (∑' j, r (J + j))

theorem atomicMassL1_limiting_finite_hasSum (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) :
  HasSum (fun i => |limitingMass ell p r i - finiteMass ell p r J i|)
    ((∑ i : Fin 4, |limitingBase ell p r i - finiteBase ell p r J i|) +
      (∑' j, r (J + j)))

theorem atomicMassL1_limiting_finite_le (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ) :
  atomicMassL1 (limitingMass ell p r) (finiteMass ell p r J) ≤
    compensationTailConstant ell * (∑' j, r (J + j))
```

## 来源、总化及系数范围

两定义、七目标。C(ell)只依赖先固定的ell与其实际四约束矩阵逆，且严格正；不依赖p、r、J或样本量n。无需额外hM非奇异门：这些仅是实际逆矩阵总化值给出的有限线性算子恒等式和界，源应用的非奇异性仍由既有source定理提供，未声称奇异矩阵下仍有四约束概率构造。

ell>=0门准确用于既有addedAtom_feature_bound，界B=(4+sqrt10)²只需新增点的feature，不将基点x=-1上的exp(9ell)错纳这个统一B。每个无限feature级数必须由真实Summable支持后分拆prefix与shift-tail；不能以不可和级数的tsum=0总化来作线性恒等式。

finite与limit的四旧质量之差是固定M^{-1}作用于未来feature尾的负值，p严格抵消。逐坐标abs界再求和给(C−1)尾量；新增侧在j<J时相同、j>=J时finite为0，所以完整AtomicIndex的L1误差精确等于旧四项abs和加未来r尾。HasSum目标真实证明此绝对误差可和，之后才用atomicMassL1的tsum；它本身不需ell>=0，因为旧四项为有限实数且自然数侧只剩r尾，不消费未证明的feature级数线性。

此处对象是权重的完整L1距离，不将它直接命名为测度TV。Mathlib实际tvDist对互相奇异的概率测度给2，源(28)常用归一化TV为1，后续须显式对齐二分之一与系数2；且实际测度必须有限/概率，不能借tvDist在非有限测度时toReal=0的总化分支。当前不导入TV新模块，不声称已经证明(28)、测度版(29)、常数连续性、LLT或最终对角。源族的正性/概率门仍由既有p/q/eps预算定理提供，四根OPEN。
