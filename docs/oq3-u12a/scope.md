# OQ3-U12a：实际有限阶段的法向远弧收缩

冻结候选v2，PROPOSED；首轮实现尚未通过编译。拟文件 `Shao/OQ3/FiniteFarArc.lean`，导入 `Shao.OQ3.JointNonlattice`、`Shao.OQ3.FiniteNormalSpan`、`Mathlib.Topology.Order.Compact`、`Mathlib.MeasureTheory.Measure.Lebesgue.Basic`。namespace Shao.OQ3，open MeasureTheory，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，309–348，特别338–345。此单元证明真实固定有限阶段概率律在法向基本区间内离零紧集上的特征函数严格收缩，且对足够小切向频率统一保持；再给真实远弧幂积分的指数界。不是中心弧二阶展开、Fourier反演或完整条件LLT。

## 冻结定义与目标

```lean
def centeredNormalTangentCharacteristic (mu : Measure ℝ) (q a t s : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp
    (((t * (normalValue x - q) + s * (x - a) : ℝ) : ℂ) * Complex.I) ∂mu

theorem centeredNormalTangentCharacteristic_factor (mu : Measure ℝ)
    (q a t s : ℝ) :
    centeredNormalTangentCharacteristic mu q a t s =
      Complex.exp (((-(t * q + s * a) : ℝ) : ℂ) * Complex.I) *
        jointCharacteristic mu (8 * t + s) (-t)

theorem centeredNormalTangentCharacteristic_continuous (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (q a : ℝ) :
    Continuous (fun v : ℝ × ℝ =>
      centeredNormalTangentCharacteristic mu q a v.1 v.2)

theorem stage_centered_normal_modulus_one_iff (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a t : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ‖centeredNormalTangentCharacteristic mu q a t 0‖ = 1 ↔
      ∃ m : ℤ, t * dyadicMesh J = (2 * Real.pi) * (m : ℝ)

theorem stage_centered_normal_fundamental_lt (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a t : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (ht : 0 < |t|) (hband : |t| ≤ Real.pi / dyadicMesh J) :
    ‖centeredNormalTangentCharacteristic mu q a t 0‖ < 1

theorem stage_far_arc_uniform (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (J : ℕ) (q a : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (K : Set ℝ) (hK : IsCompact K) (hzero : (0 : ℝ) ∉ K)
    (hband : ∀ t ∈ K, |t| ≤ Real.pi / dyadicMesh J) :
    ∃ eta rho : ℝ, 0 < eta ∧ 0 < rho ∧ rho < 1 ∧
      ∀ t ∈ K, ∀ s : ℝ, |s| < eta →
        ‖centeredNormalTangentCharacteristic mu q a t s‖ < rho

theorem stage_far_arc_power_integral (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (J : ℕ) (q a : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (K : Set ℝ) (hK : IsCompact K) (hzero : (0 : ℝ) ∉ K)
    (hband : ∀ t ∈ K, |t| ≤ Real.pi / dyadicMesh J) :
    ∃ eta rho : ℝ, 0 < eta ∧ 0 < rho ∧ rho < 1 ∧
      ∀ s : ℝ, |s| < eta → ∀ n : ℕ,
        (IntegrableOn (fun t : ℝ =>
          centeredNormalTangentCharacteristic mu q a t s ^ n) K) ∧
        ‖∫ t : ℝ in K, centeredNormalTangentCharacteristic mu q a t s ^ n‖ ≤
          volume.real K * rho ^ n
```

一公开定义、六公开目标。定义保留真实中心化的q/a和两个频率，s以后可取固定切向频率除sqrt(n)；q/a在远弧步骤不需要等于均值，因为中心化只乘模为1的相位，绝不据此声称中心弧展开。第一个因式分解对任意measure成立，是逐点相位代数与常数乘积分，不涉及非可积处的概率解释；后五项明确要求实际概率律。

正质量门是所有真实有限阶段原子，而不是无限正原子；支撑门为同一stageAtom实际有限range。dyadicMesh J=2^-J，J=0包含四旧原子，J≥1还含最后addedAtom(J-1)。前向模1用已审U6b的真实积分三角等号桥，从两个正原子的相位相同得到 t*(Yx−Yy)∈2piZ。J=0选base1/base2的真实normal差1，J+1选addedAtom J/base2的真实差dyadicMesh(J+1)。反向用U8实际每个stage原子的Y∈hZ，所有相位相同，真实概率积分给模1。不能只引用“maximal span”字样而跳过这个实际整数频率刻画。

基本区间为闭[-pi/h,pi/h]；0<|t|≤pi/h内没有非零2pi/h整数频率，故严格小于1，两个端点同样严格。没有声称整个实线远离0都收缩：真实格点对偶整数周期处模仍为1。

连续性从参数相位逐点连续、模恒1、概率下常数1真正Integrable经dominated-continuity取得，不需要不存在的切向密度。紧K不含0且位于基本区间，连续模函数在K取最大值<1，空K单独取正eta与rho∈(0,1)。再对K×{0}的开邻域用紧集tube lemma取得一个统一切向|s|<eta；rho、eta先于全部t/s/n选择。此处只需正小切向窗口，不假称对任意切向频率统一收缩。

最后目标包括真正IntegrableOn：K紧而具有有限Lebesgue测度，相位积分连续，norm≤rho<1，故各n次幂在K可积。norm_integral≤integral_norm≤volume.real K*rho^n；n=0时为实际K长度界，空K亦成立。不是仅把不可积Bochner积分总化为0后写界；无需K正测度/非空。这个固定s窗口允许后继在s/sqrt(n)最终进入后应用，当前不含该极限序列或完整Fourier反演。

U6b/U8已完整审查，具体原子范围/严格正性可由实际finiteMass及四约束推出。本单元不选择另一组源参数、不假设强非格点、不把双侧格点法向错作非格点。根A/B/C/D保持OPEN。先独立声明/source gate，未经批准不实现；没有新公理/目标重编/缓存写入。

## v2显式勒贝格测度环境修订

首轮实际编译发现原三个导入没有提供MeasureSpace ℝ，因此最后一个目标的默认IntegrableOn测度、volume.real及频率积分不能elaborate。原v1文件SHA1dddd27330a06202fa0c8fe924c4bb32cfd26fdef54b110aa89fa8168ff40d8b及其声明票bb35c6145cf03ac92901f0bccd302296d4c497c112a63e7e7ed04ba6f04f5d35原样保留，不将首轮失败虚记成功。v2仅新增已cached的Mathlib.MeasureTheory.Measure.Lebesgue.Basic，将本来要求的实线Lebesgue测度实例显式导入；一个定义体和六个完整声明文本逐字不变，所有数学假设、量词和结论均不改变。须先独立重审v2实例环境，再继续实现检查。
