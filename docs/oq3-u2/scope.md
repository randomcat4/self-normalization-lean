# OQ3-U2：固定源倾斜参数、起始律和补偿矩阵

冻结候选 v1，PROPOSED；尚未实现，等待独立声明审查。U1 作者冻结源 SHA256 `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` 不动。拟新文件 `Shao/OQ3/SourceStarter.lean`，只导入 U1 及已钉死的 Mathlib 基础；不动共享入口或版本锁。

## 原源和完整消费边界

实际源 R1 `current/oq3/proofs/r1/report.md`，SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`：18–62 是 u/ell、正三点和 q0 裕量；66–87 是加入第四点后的正初始律及新 q；89–108 是四约束矩阵的精确非零行列式。这里把这些源条件实例化，消去 U1 的条件性 hM、hp 与正初始 p。不是全 OQ3 根，也不构造原律 P。

源中的 q0 是三点二阶矩；新 q 是加入第四点后重新定义的二阶矩。U2 不要求它们相等，不把四点初始添加错误地放进“保持 q”的后续四约束补偿。δ 在整条有限阶段序列之前固定一次，不随 J/n 变化。

## 定义候选（统一 noncomputable section，open scoped Matrix）

```lean
def sourceU : ℝ := 31 / 30
def sourceEll : ℝ := Real.log sourceU
def sourceA : ℝ := (sourceU ^ 7)⁻¹
def sourceB : ℝ := sourceU ^ 9
def sourceC : ℝ := (sourceU ^ 6)⁻¹
def sourceDenominator : ℝ :=
  sourceB * (13 + 4 * Real.sqrt 10) +
  sourceA * (5 + 4 * Real.sqrt 10) +
  8 * sourceC * (4 + Real.sqrt 10)
def sourceZ : ℝ := (3 * sourceB - 5 * sourceA) / sourceDenominator
def sourceTripleMass : Fin 3 → ℝ :=
  ![3 / 8 - (13 + 4 * Real.sqrt 10) / 8 * sourceZ,
    5 / 8 + (5 + 4 * Real.sqrt 10) / 8 * sourceZ, sourceZ]
def sourceTripleQ : ℝ := 1 + (25 + 8 * Real.sqrt 10) * sourceZ
def sourceConstraint3 : Matrix (Fin 3) (Fin 3) ℝ :=
  fun k i => constraintFeature sourceEll (baseAtom i.castSucc) k.castSucc
def sourceTripleCorrection : Fin 3 → ℝ :=
  sourceConstraint3⁻¹ *ᵥ
    (fun k => constraintFeature sourceEll (baseAtom 3) k.castSucc)
def sourceStarterWeight (delta : ℝ) : Fin 4 → ℝ :=
  ![sourceTripleMass 0 - delta * sourceTripleCorrection 0,
    sourceTripleMass 1 - delta * sourceTripleCorrection 1,
    sourceTripleMass 2 - delta * sourceTripleCorrection 2, delta]
def sourceStarterQ (delta : ℝ) : ℝ :=
  ∑ i, sourceStarterWeight delta i * (baseAtom i) ^ 2
```

`i.castSucc` 将 Fin 3 的 0/1/2 映到 Fin 4 的 0/1/2，`k.castSucc` 同样只取前三条约束，不能误用 Fin.succ 而移成 1/2/3。sourceTripleCorrection 是三约束逆，不是 U1 的四约束逆。

## 精确导出签名候选

```lean
theorem sourceEll_pos : 0 < sourceEll

theorem source_base_centering_values :
  (fun i => centeringFeature sourceEll (baseAtom i)) =
    ![-sourceB, sourceA, (4 + Real.sqrt 10) * sourceC,
      2 * (sourceU ^ 12)⁻¹]

theorem sourceConstraint3_det : sourceConstraint3.det =
  -8 * (sourceC * (4 + Real.sqrt 10) + sourceB) -
  (sourceA + sourceB) * (5 + 4 * Real.sqrt 10)

theorem sourceConstraint3_det_neg : sourceConstraint3.det < 0

theorem source_constraintMatrix_det :
  (constraintMatrix sourceEll).det =
    -(20765025879526713743120420649631 : ℝ) /
      242243227707969139777546875000 -
    (20921320404866133143120420649631 : ℝ) /
      775178328665501247288150000000 * Real.sqrt 10

theorem source_constraintMatrix_det_neg : (constraintMatrix sourceEll).det < 0

theorem source_constraintMatrix_nonsingular : (constraintMatrix sourceEll).det ≠ 0

theorem sourceTripleMass_pos : ∀ i, 0 < sourceTripleMass i

theorem sourceTriple_constraints :
  sourceConstraint3 *ᵥ sourceTripleMass = ![1, 0, 0]

theorem sourceTriple_square_moment :
  (∑ i : Fin 3, sourceTripleMass i * (baseAtom i.castSucc) ^ 2) = sourceTripleQ

theorem sourceTripleQ_bounds : 1 < sourceTripleQ ∧ sourceTripleQ < 103 / 100

theorem sourceStarter_constraints (delta : ℝ) :
  (constraintMatrix sourceEll) *ᵥ sourceStarterWeight delta =
    constraintTarget (sourceStarterQ delta)

theorem exists_source_starter_delta :
  ∃ delta : ℝ, 0 < delta ∧ (∀ i, 0 < sourceStarterWeight delta i) ∧
    1 < sourceStarterQ delta ∧ sourceStarterQ delta < 103 / 100

theorem exists_source_starter :
  ∃ (p : Fin 4 → ℝ) (q : ℝ), (∀ i, 0 < p i) ∧
    1 < q ∧ q < 103 / 100 ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q
```

十四条均无新增数学前提。非奇异性是单独输出，随后与 exists_source_starter 合用；p/q 的选择放在所有 J 外。exists_source_starter_delta 给出原文“充分小 δ”的存在，不把作者额外算出的 δ=10^-6 强加为目标或新前提。

## 首先执行的边界攻击

1. 精确指数相位：基点法向值 [-9,7,6,12]，故 f2(-1)=-u^9、f2(1)=u^-7、f2(beta)=beta u^-6、f2(2)=2u^-12，符号/幂次必须全匹配。
2. Fin.castSucc 保留 0/1/2；若用 succ，三约束和三基点的语义同时错位。
3. δ=0 时第四权重为 0，所以正四点结论必须要求存在 δ>0；任意实 δ 的 constraints 仅为有符号代数恒等式。
4. 三点 q0 与四点 q 不同；检查证书不得把 q0 上界直接当作任意 δ 的 q 上界，必须小扰动保持。
5. 四点 det 的根号分支是正 √10；求值必须先证 `(√10)^2=10`，不得把方程两根都当同一源常数。
6. 行列式两个负系数与三点 q 裕量的两个正系数已有服务器精确探针匹配，但只有 Lean 内核接受证书才算形式证明；不得用 Python 输出替代实数等式证明。

## 可直接继续的库/证书检查

实读固定 Mathlib 的 `Matrix.det_fin_three` 位于 Determinant/Basic.lean:820；四阶没有对应 `det_fin_four`，用 `Matrix.det_succ_row_zero`（765）展开一次到三阶 minor。`Real.exp_nat_mul`、`Real.exp_neg`、`Real.exp_log` 已在服务器 APIProbe 检查。矩阵常数固定后，starterWeight 和 starterQ 都是 δ 的仿射函数，小正扰动可用显式有限系数界证明，或给完全核准的连续性证明；无须引入概率测度、一般渐近或额外矩条件。

本单元等待 fresh 声明审查，未实现目标。U1 正在等独立证明审查，两条审查不能互相代替。
