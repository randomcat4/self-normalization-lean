# OQ3-U1：有限阶段四约束补偿和原子代数

冻结候选 v1，状态 PROPOSED / LEAN_TRANSLATION_UNAUDITED。作者 OQ3 lead。声明审核通过前不落目标证明。拟唯一实现文件 `Shao/OQ3/FiniteConstraints.lean`；命名空间 `Shao.OQ3`。只读共用模块，不改 Shao.lean、pins、audit 或缓存。

## 1. 对应原句

R1 SHA256 `3473D34FF20BD0D334B9EF3EA3C3EE167FBA4D5CC3A742849820CE54D639E662`：18–25 定义 ℓ,Y,f1,f2；66–109 基点、列矩阵和四约束；113–130 新原子、法向值及有限阶段补偿。补偿的是 π_J，绝不把此有限权重系统叫作已构造的原律 P。

U1 是源证明中“给定可逆 M 和正四点起始权重后可作精确有限补偿”的独立条件性子引理。M.det≠0 和实际起始权重存在由 U2 证明并消去，不是根 A 新增前提。U1 不含无限尾、真正非格点、最大 span、LLT 或根尾概率结论。

## 2. 定义的精确类型候选

以下是待审核接口，非已编译代码。有限向量采用 `Fin 4 → ℝ`，矩阵的行是约束、列是基点；`baseAtom 0=-1, 1=1, 2=4+√10, 3=2`。

```lean
def normalValue (x : ℝ) : ℝ := 8 * x - x ^ 2
def boundaryFeature (x : ℝ) : ℝ := x ^ 2 - 4 * x
def centeringFeature (ell x : ℝ) : ℝ :=
  x * Real.exp (-ell * normalValue x)
def constraintFeature (ell x : ℝ) : Fin 4 → ℝ :=
  ![1, boundaryFeature x, centeringFeature ell x, x ^ 2]
def constraintTarget (q : ℝ) : Fin 4 → ℝ := ![1, 0, 0, q]
noncomputable def baseAtom : Fin 4 → ℝ := ![-1, 1, 4 + Real.sqrt 10, 2]
def constraintMatrix (ell : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun k i => constraintFeature ell (baseAtom i) k
def dyadicMesh (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹
noncomputable def addedAtom (k : ℕ) : ℝ :=
  4 + Real.sqrt (10 - dyadicMesh (k + 1))

-- A fixed finite family of J added atoms; k=0 corresponds to source j=1.
def addedMoment {J : ℕ} (ell : ℝ) (x r : Fin J → ℝ) : Fin 4 → ℝ :=
  fun k => ∑ j, r j * constraintFeature ell (x j) k
noncomputable def compensatedBase {J : ℕ} (ell : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ) : Fin 4 → ℝ :=
  p - (constraintMatrix ell)⁻¹ *ᵥ addedMoment ell x r
def stageAtom {J : ℕ} (x : Fin J → ℝ) : Fin 4 ⊕ Fin J → ℝ :=
  Sum.elim baseAtom x
noncomputable def stageWeight {J : ℕ} (ell : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ) : Fin 4 ⊕ Fin J → ℝ :=
  Sum.elim (compensatedBase ell p x r) r
def stageMoment {J : ℕ} (ell : ℝ) (x : Fin J → ℝ)
    (w : Fin 4 ⊕ Fin J → ℝ) : Fin 4 → ℝ :=
  fun k => ∑ i, w i * constraintFeature ell (stageAtom x i) k
```

此处 `ell` 先允许任意实数是严格更一般的有限代数引理；源实例后续固定 `ell=Real.log (31/30)`。baseAtom 含 sqrt，相关定义须以 `noncomputable section` 统一包围。stageMoment 先是实权重有限和，不预设 Measure 或 PMF。

## 3. 待冻结的导出命题（所有参数都显式）

```lean
theorem compensated_stageMoment {J : ℕ} (ell q : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hp : (constraintMatrix ell) *ᵥ p = constraintTarget q) :
    stageMoment ell x (stageWeight ell p x r) = constraintTarget q

theorem compensatedBase_pos {J : ℕ} (ell : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hsmall : ∀ i, |((constraintMatrix ell)⁻¹ *ᵥ
      addedMoment ell x r) i| < p i) :
    ∀ i, 0 < compensatedBase ell p x r i

theorem stageWeight_pos {J : ℕ} (ell : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hsmall : ∀ i, |((constraintMatrix ell)⁻¹ *ᵥ
      addedMoment ell x r) i| < p i)
    (hr : ∀ j, 0 < r j) :
    ∀ i, 0 < stageWeight ell p x r i

theorem exists_compensation_radius (ell : ℝ) (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) (B : ℝ) (hB : 0 ≤ B) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (J : ℕ) (x r : Fin J → ℝ),
      (∀ j, 0 ≤ r j) →
      (∀ j k, |constraintFeature ell (x j) k| ≤ B) →
      (∑ j, r j) < eps →
      ∀ i, 0 < compensatedBase ell p x r i

theorem stage_mass_one {J : ℕ} (ell q : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hp : (constraintMatrix ell) *ᵥ p = constraintTarget q) :
    (∑ i, stageWeight ell p x r i) = 1

theorem stage_boundary_moment {J : ℕ} (ell q : ℝ)
    (p : Fin 4 → ℝ) (x r : Fin J → ℝ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hp : (constraintMatrix ell) *ᵥ p = constraintTarget q) :
    (∑ i, stageWeight ell p x r i * stageAtom x i) = q / 4

theorem addedAtom_normalValue (k : ℕ) :
  normalValue (addedAtom k) = 6 + dyadicMesh (k + 1)
theorem addedAtom_gt_four (k : ℕ) : 4 < addedAtom k
theorem addedAtom_lt_limit (k : ℕ) : addedAtom k < 4 + Real.sqrt 10
theorem addedAtom_injective : Function.Injective addedAtom
theorem normalValue_baseAtom :
  (fun i => normalValue (baseAtom i)) = ![-9, 7, 6, 12]
```

四条 scalar 约束是向量定理的 k=0,1,2,3 投影，必要时给独立导出名；mass_one 和 boundary_moment 是消费演示，后者须同时使用 Ef1=0 与 EX²=q，不偷假设 EX=q/4。半径定理独立于 J，输入 feature 的同一 B；不是“每个有限阶段各有一个无法统一的 eps”。它不要求 hM，因为即使 Lean 的总化逆矩阵在奇异处定义，纯小扰动正性仍成立；精确保持式消费 hM。源实际 x_j 的共同 featureBound B 由紧区间连续性在 U2/U3 提供，不把它假称首单元已消去的前提。

## 4. 最快反例/边界探针

1. 四列实际法向值必须为 `[-9,7,6,12]`；b4=2 的 12 不能漏。矩阵若误转置，输出质量投影与其他三投影不再同时成立。
2. J=0（Fin 0 空）补偿量为 0，原四点不变；J=1 的原子是 `4+√(19/2)`，法向为 13/2。j=0 约定不得把源第一格距误成 1。
3. 去掉 hM 时零/奇异矩阵不能普遍保持任意新增 feature；检测是否误把总化矩阵逆当无条件逆。
4. 任意正新增质量不自动保持基点正性。单个新增点等于某个 baseAtom i，hM 成立时该列补偿恰为 `-r e_i`，若 r>p_i 该基点变负。半径或 hsmall 必须保留。
5. 补偿符号必须是减；质量投影新增 Σr 与补偿 -Σr 精确抵消。对 p 的 positivity 和 r 的 strict positivity 要分开；r=0 允许前置半径引理但不能导出所有新增原子为正。
6. 不假设 stageAtom 单射来证明有限和约束；重复原子在推到 ℝ 的测度时要合并。源 addedAtom 单射/与 base 分离另有证明，有限索引权重可为正不等于已证二维协方差正定。

## 5. 最小依赖与验收

固定 mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，Lean `v4.36.0-rc1`。候选导入：`LinearAlgebra.Matrix.NonsingularInverse`、实数 exp/log 与 sqrt 基础、有限和/有限类型分割、实数绝对值与有序环战术。先检查已缓存模块，缺失缓存报 root；不 lake update/cache get。

声明审查检查：source j↔Lean k+1、M 行列方向、四约束同 q、半径不依赖 J、条件性 U2 依赖不藏入根定理、实权重有限和与概率律的区别。通过后才实现，服务器 targeted `lake env lean Shao/OQ3/FiniteConstraints.lean`；变更源扫描及全部导出 theorem 的传递公理审计由 root 的共享流程执行（白名单 propext/Classical.choice/Quot.sound）。另需 fresh proof reviewer；作者不能独立盖章。首单元通过也只记局部覆盖，根 A/B/C/D 仍 OPEN。
