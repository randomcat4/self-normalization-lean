# OQ3-U3a：可求和原子质量与固定四约束极限

冻结候选 v1，PROPOSED；未实现，需独立声明审查。拟文件 `Shao/OQ3/SummableAtoms.lean`，导入冻结 U1/U2。不修改原稿、共享 Probability、根入口或缓存。

## 来源与目标边界

R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，113–135 行的可数新增原子、有限/无限补偿和同一个 q；137–145 行原律反倾斜留待 U4。U3a 只证明可求和实质量和所有四约束的 HasSum，不把实质量序列冒称已经构造的概率测度。概率测度的 Dirac 求和、逆倾斜、联合非格点及对角预算都未在本单元闭合。

全体原子采用同一可数索引类型 `Fin 4 ⊕ ℕ`。新增项仍是 source j=k+1；有限阶段以 Fin J 截断 k<J。给定固定的源 starter p/q 后，p、q 和总质量门 eps 在所有 r/J/n 外固定；r 是后来选择的整条序列，不能变成运行样本量 n 的函数。

## 定义候选（统一 noncomputable section，open scoped Matrix）

```lean
abbrev AtomicIndex := Fin 4 ⊕ ℕ
def fixedAtom : AtomicIndex → ℝ := Sum.elim baseAtom addedAtom
def infiniteAddedMoment (ell : ℝ) (r : ℕ → ℝ) : Fin 4 → ℝ :=
  fun k => ∑' j, r j * constraintFeature ell (addedAtom j) k
def limitingBase (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) : Fin 4 → ℝ :=
  p - (constraintMatrix ell)⁻¹ *ᵥ infiniteAddedMoment ell r
def limitingMass (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) : AtomicIndex → ℝ :=
  Sum.elim (limitingBase ell p r) r
def finiteBase (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ) (J : ℕ) : Fin 4 → ℝ :=
  compensatedBase ell p (fun i : Fin J => addedAtom i.val) (fun i : Fin J => r i.val)
```

tsum 与矩阵逆均是 Lean 总化运算；下列结论显式保留可求和或非奇异条件，不能凭定义删除这些门。

## 待冻结导出声明

```lean
theorem addedAtom_feature_bound (ell : ℝ) (hell : 0 ≤ ell) (j : ℕ) (k : Fin 4) :
  |constraintFeature ell (addedAtom j) k| ≤ (4 + Real.sqrt 10) ^ 2

theorem summable_addedFeature (ell : ℝ) (hell : 0 ≤ ell) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (k : Fin 4) :
  Summable (fun j => r j * constraintFeature ell (addedAtom j) k)

theorem finiteBase_tendsto (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : Summable r) :
  Filter.Tendsto (finiteBase ell p r) Filter.atTop (nhds (limitingBase ell p r))

theorem limitingMoment_hasSum (ell q : ℝ) (hell : 0 ≤ ell)
    (p : Fin 4 → ℝ) (r : ℕ → ℝ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hp : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (k : Fin 4) :
  HasSum (fun i => limitingMass ell p r i * constraintFeature ell (fixedAtom i) k)
    (constraintTarget q k)

theorem exists_limiting_radius (ell : ℝ) (hell : 0 ≤ ell) (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) :
  ∃ eps : ℝ, 0 < eps ∧ ∀ (r : ℕ → ℝ),
    (∀ j, 0 ≤ r j) → Summable r → (∑' j, r j) < eps →
    ∀ i, p i / 2 ≤ limitingBase ell p r i

theorem limitingMass_pos_of_lower (ell : ℝ) (p : Fin 4 → ℝ) (r : ℕ → ℝ)
    (hp : ∀ i, 0 < p i) (hr : ∀ j, 0 < r j)
    (hlower : ∀ i, p i / 2 ≤ limitingBase ell p r i) :
  ∀ i, 0 < limitingMass ell p r i

theorem exists_source_limit_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      (∀ i, 0 < limitingMass sourceEll p r i) ∧
      (∀ k, HasSum (fun i => limitingMass sourceEll p r i *
        constraintFeature sourceEll (fixedAtom i) k) (constraintTarget q k))

theorem exists_positive_small_summable (eps : ℝ) (heps : 0 < eps) :
  ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps

theorem fixedAtom_injective : Function.Injective fixedAtom

theorem fixedAtom_bounds (i : AtomicIndex) :
  1 ≤ |fixedAtom i| ∧ |fixedAtom i| ≤ 4 + Real.sqrt 10
```

五个定义加一个类型别名、十条目标。只有末尾固定源 family 消去 hM/hp，调用 U2 的真实 starter 和源矩阵非奇异性。更一般的极限矩仍允许有符号基点质量；只有半径与正序列等门合用后才宣称全索引质量严格正。`exists_positive_small_summable` 排除 family 的预算门只是空前提，并不宣称该几何示例序列就是最终反例的对角质量。

## 验收风险

- eps 在 r 之前，不能让 eps 或 p/q 依赖最终序列或阶段。
- 从有限 p_J>0 取极限只能得≥0，故保留固定 p_i/2 下界，随后才能导出极限严格正。
- ell≥0 是显式 feature 统一界的条件；根实例 ell=log(31/30)>0 已由 U2 给出。一般负 ell 未被本范围声明覆盖。
- HasSum 必须证明整条可数索引序列，不能只写 totalized tsum 的等式而忽略可求和。
- finiteBase_tendsto 的 J 截断必须保持 k=0,…,J−1，不能多一项或改 source 原子索引。
- fixedAtom_injective 要覆盖基点间、新旧交叉和新增之间三类，不只 addedAtom 单射。边界 beta 是旧基点与新增极限，新增项严格小于 beta。
- 仍未构造 Measure 或原律 P；不把此无限质量家族称为完成真正联合非格点反例，也不把一个任意小几何序列当作完成逐 witness 选尾的预算。
