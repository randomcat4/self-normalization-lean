# OQ3-U9a：真实样本曲边界恒等式与似然权重界

冻结候选v1，PROPOSED；未实现。拟文件 `Shao/OQ3/SampleBoundary.lean`，导入U8 `FiniteNormalSpan` 和既有共享 `Shao.Probability.FiniteIID`（后者已导入 `Shao.Basic.FinitePath`）。不修改共享源；实际server两个共享源SHA分别为FiniteIID `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`、FinitePath `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`。namespace Shao.OQ3，open MeasureTheory，open scoped BigOperators，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，400–408的恒等式(18)和正尾符号门，以及495–510的真实n重积似然权重上界。使用已有 `Shao.Path n = Fin n → ℝ` 和真正能量 `Shao.energy z=Σ z_i²`。此单元不声明乘积换测度或TV不等式，先闭合其必需的精确样本几何与可测有界输入。

## 待冻结导出声明

```lean
def normalDeviation (q : ℝ) {n : ℕ} (z : Shao.Path n) : ℝ :=
  (∑ i, normalValue (z i)) - (n : ℝ) * q

def tangentDeviation (q : ℝ) {n : ℕ} (z : Shao.Path n) : ℝ :=
  (∑ i, z i) - (n : ℝ) * q / 4

def sourceTail (q : ℝ) (n : ℕ) : Set (Shao.Path n) :=
  {z | 0 < Shao.energy z ∧
    Real.sqrt q / 4 * Real.sqrt ((n : ℝ) * Shao.energy z) ≤ ∑ i, z i}

theorem normalDeviation_eq_sum_energy (q : ℝ) (n : ℕ) (z : Shao.Path n) :
  normalDeviation q z = 8 * (∑ i, z i) - Shao.energy z - (n : ℝ) * q

theorem curved_sample_identity (q : ℝ) (n : ℕ) (z : Shao.Path n) :
  (∑ i, z i) ^ 2 - (n : ℝ) * (q / 16) * Shao.energy z =
    (n : ℝ) * q / 16 * normalDeviation q z + tangentDeviation q z ^ 2

theorem sourceTail_measurable (q : ℝ) (n : ℕ) :
  MeasurableSet (sourceTail q n)

theorem sourceTail_iff_curved (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (z : Shao.Path n) :
  z ∈ sourceTail q n ↔ 0 < Shao.energy z ∧ 0 < (∑ i, z i) ∧
    0 ≤ (n : ℝ) * q / 16 * normalDeviation q z + tangentDeviation q z ^ 2

theorem sourceTail_on_normal_layer (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (z : Shao.Path n) (d : ℝ) (hd : normalDeviation q z = d) :
  z ∈ sourceTail q n ↔ 0 < Shao.energy z ∧ 0 < (∑ i, z i) ∧
    -((n : ℝ) * q / 16 * d) ≤ tangentDeviation q z ^ 2

theorem stage_sample_normal_layer (q : ℝ) (n J : ℕ) (z : Shao.Path n)
    (hz : ∀ i, z i ∈ Set.range (fun j : Fin 4 ⊕ Fin J =>
      stageAtom (fun k : Fin J => addedAtom k.val) j)) :
  ∃ k : ℤ, normalDeviation q z = dyadicMesh J * (k : ℝ) - (n : ℝ) * q

theorem fixedAtom_normalValue_lower (i : AtomicIndex) :
  -9 ≤ normalValue (fixedAtom i)

theorem atomicMeasure_ae_normalValue_lower (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂atomicMeasure w, -9 ≤ normalValue x

theorem originalMeasure_ae_normalValue_lower (ell : ℝ) (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂originalMeasure ell w, -9 ≤ normalValue x

theorem normal_likelihood_weight_bound (ell q : ℝ) (hell : 0 ≤ ell) (hq : q ≤ 2)
    (n : ℕ) (z : Shao.Path n) (hY : ∀ i, -9 ≤ normalValue (z i)) :
  Real.exp (-ell * normalDeviation q z) ≤ Real.exp (11 * ell * (n : ℝ))

theorem iid_normal_likelihood_ae_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (ell q : ℝ) (hell : 0 ≤ ell) (hq : q ≤ 2)
    (hY : ∀ᵐ x ∂mu, -9 ≤ normalValue x) (n : ℕ) :
  ∀ᵐ z ∂Measure.pi (fun _ : Fin n => mu),
    Real.exp (-ell * normalDeviation q z) ≤ Real.exp (11 * ell * (n : ℝ))

theorem source_atomic_iid_likelihood_ae_bound (q : ℝ) (hq : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) :
  ∀ᵐ z ∂Measure.pi (fun _ : Fin n => atomicMeasure w),
    Real.exp (-sourceEll * normalDeviation q z) ≤
      Real.exp (11 * sourceEll * (n : ℝ))
```

## 语义范围与边界

三定义、十二目标。sourceTail在q>0、n>0时为固定x0=sqrt(q)/4的正尾事件，明确排除能量0；这和将分母0时的学生化比值定0一致。sqrt门阈值严格正，所以平方后仍必须保留S>0，不可只留下S²条件。恒等式(18)的d和R分别是实际样本Y和X的居中和，不能用方差代替样本能量。

任意层d的判据保留能量和符号门；在d=-k且k>0时正好给R²>=nqk/16。阶段样本格点是h_J整数减nq，包含第零阶段和空样本；本单元不声称相位返回或任何条件极限。

Y>=-9来自真实fixedAtom的旧值[-9,7,6,12]及新值6+mesh，并非仅由1<=|X|<=4+sqrt10推导（该绝对值界不足以控制负端Y）。pi/P的AE下界都须来自实际原子值域与反倾斜绝对连续性。若所有Y_i>=-9且q<=2，实际d>=-11n，ell>=0给e^(-ell d)<=e^(11ell n)。真实n重积门由mu概率和每坐标相同AE界推出；不是假定坐标逐点都在支撑，也不是把不同样本量的律当同一对象。最后实际原子律以非负权/HasSum1保证真概率，sourceEll正，源q<1.03严格足够q<=2。

没有乘积换测度、产品TV、LLT/层支配求和、全局唯一率或对角闭合声明。x0/q/P仍须固定在n外，所有根A/B/C/D OPEN。
