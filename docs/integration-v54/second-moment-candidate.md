# 真实 Lindley 调节量平方矩：待冻结候选 v1

状态：`CANDIDATE_NOT_FROZEN`。本文件只给完整候选定义与声明头，不是 Lean 实现，也未运行 Lean。主协调者冻结前不得生产证明代码。候选作者不担任此单元最终独立审查者。

拟议生产模块：`Shao.Probability.SourceLindleyRegulatorSecondMoment`。不依赖尚在生产的一阶矩模块，也不导入 OQ4 的布朗构造或生存生产者。拟议直接导入如下；冻结后的实际导入仍须按服务器已有缓存核对。

```lean
import Shao.Probability.LindleyTelescoping
import Shao.Probability.SourceFourierScale
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
```

下面所有声明均在该命名空间中。既有 `Shao.Path N = Fin N → ℝ`、`Shao.lindleyState`、`Shao.maxWithZero` 与 `lindleyRegulator` 保持原定义。自然语言第 `i` 步对应 Lean `j : Fin N` 的 `i = j.val + 1`。

## 候选定义（定义体也属于冻结范围）

`lindleyRegulatorSquareCost` 是实际前缀乘积律上的严格事件概率，乘以当前观测的真实负部平方；不是自由随机变量或自由核。

```lean
noncomputable def lindleyRegulatorSquareCost
    (ν : Measure ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  (max (-z) 0) ^ 2 *
    (Measure.pi (fun _ : Fin k => ν)).real
      {b : Shao.Path k | Shao.maxWithZero b < max (-z) 0}
```

`lindleyPrefixSurvivalBound` 仅把尚欠的真实概率不等式写成具名命题。它不是生存定理，不是源条件已支付的结论。这里只需上侧最大值；不额外要求反射负律的另一侧 Spitzer 输入。

```lean
def lindleyPrefixSurvivalBound
    (ν : Measure ℝ) (N : ℕ) (C : ℝ) : Prop :=
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂ν) / V
  ∀ k : ℕ, 1 ≤ k → k < N → ∀ r : ℝ, 0 ≤ r →
    (Measure.pi (fun _ : Fin k => ν)).real
        {b : Shao.Path k | Shao.maxWithZero b ≤ r} ≤
      C * min 1 ((r + gamma) /
        (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ)))
```

## 完整精确声明头

下列代码块刻意不含证明体；它们不是可编译的 `.lean` 文件。实现者不得改变任何前提、定义或量词。若发现声明不能按原义实现，应报告主协调者修订候选版本。

### 1. 原始严格事件上的逐路径平方支配

```lean
theorem lindleyRegulator_sq_le_strict_weight
    (N : ℕ) (a : Shao.Path N) (j : Fin N) :
    (lindleyRegulator a j) ^ 2 ≤
      if Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt) <
          max (-(a j)) 0
      then (max (-(a j)) 0) ^ 2
      else 0
```

### 2. 实际乘积样本中，反射前状态与当前坐标的联合律

这同时支付反转后的真实最大值律与当前坐标的独立性；不把两者作为调用方前提。

```lean
theorem iid_lindleyState_coordinate_map_eq_prod
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N : ℕ) (j : Fin N) :
    Measure.map
        (fun a : Shao.Path N =>
          (Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt), a j))
        (Measure.pi (fun _ : Fin N => ν)) =
      (Measure.map (fun b : Shao.Path j.val => Shao.maxWithZero b)
        (Measure.pi (fun _ : Fin j.val => ν))).prod ν
```

### 3. 仅由真实二阶矩得到所有调节量平方可积

```lean
theorem integrable_lindleyRegulator_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (N : ℕ) (j : Fin N) :
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => ν)
    Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2) P ∧
      (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
        ∫ z : ℝ, z ^ 2 ∂ν
```

### 4. 真正严格事件的乘积积分拆分与有限性

```lean
theorem iid_lindleyRegulator_sq_disintegration
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (N : ℕ) (j : Fin N) :
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => ν)
    let F : Shao.Path N → ℝ := fun a =>
      if Shao.lindleyState a j.val (Nat.le_of_lt j.is_lt) <
          max (-(a j)) 0
      then (max (-(a j)) 0) ^ 2
      else 0
    Integrable F P ∧
      Integrable (lindleyRegulatorSquareCost ν j.val) ν ∧
      (∫ a : Shao.Path N, F a ∂P) =
        ∫ z : ℝ, lindleyRegulatorSquareCost ν j.val z ∂ν ∧
      (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
        ∫ z : ℝ, lindleyRegulatorSquareCost ν j.val z ∂ν
```

### 5. 第一步的真实平方矩与 Lyapunov 界

有限三阶矩在概率律下内部推出有限二阶矩；不要求调用方再支付调节量可积性。

```lean
theorem iid_lindleyRegulator_one_second_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ν
    let P : Measure (Shao.Path 1) :=
      Measure.pi (fun _ : Fin 1 => ν)
    Integrable
        (fun a : Shao.Path 1 =>
          (lindleyRegulator a (Fin.last 0)) ^ 2) P ∧
      (∫ a : Shao.Path 1,
          (lindleyRegulator a (Fin.last 0)) ^ 2 ∂P) =
        ∫ z : ℝ, (max (-z) 0) ^ 2 ∂ν ∧
      (∫ a : Shao.Path 1,
          (lindleyRegulator a (Fin.last 0)) ^ 2 ∂P) ≤
        m3 / Real.sqrt V
```

### 6. 通用实际乘积律消费者：保留生存前提

`hM2` 是源版本会支付的真实二阶矩/方差比较，不是调节量的结论性假设。`h3` 是真实增量矩。`hSurvival` 是本单元唯一未实现的概率生产接口。所有索引上统一使用明确常数 `max 1 (3 * C)`，因此不必另强加 `1 ≤ C`。

```lean
theorem iid_lindleyRegulator_second_moment_of_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (hM2 : (∫ z : ℝ, z ^ 2 ∂ν) ≤
      2 * variance (id : ℝ → ℝ) ν)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hSurvival : lindleyPrefixSurvivalBound ν N C) :
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ν
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => ν)
    ∀ j : Fin N,
      Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2) P ∧
        (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
          max 1 (3 * C) * m3 /
            (Real.sqrt V * Real.sqrt ((j.val + 1 : ℕ) : ℝ))
```

### 7. 真正源截断律版本：不要求额外可积性、独立性或方差比较

只保留原始源归一化、原始零均值、已接受截断预算和显式生存前提。`rho` 是真正条件增量律；`P` 是该律的真实有限乘积。原始律不要求有限三阶矩。

```lean
theorem sourceTruncation_lindleyRegulator_second_moment_of_survival
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (N : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (N : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget nu N x ≤ epsilon ^ 3 / 8)
    (C : ℝ) (hC : 0 ≤ C) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let V : ℝ := variance (id : ℝ → ℝ) rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => rho)
    lindleyPrefixSurvivalBound rho N C →
      ∀ j : Fin N,
        Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2) P ∧
          (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
            max 1 (3 * C) * m3 /
              (Real.sqrt V * Real.sqrt ((j.val + 1 : ℕ) : ℝ))
```

```lean
end Shao.Probability
```

## 明确边界

- 第一步 `j.val = 0` 不调用生存前提；上面的生存命题只量化 `1 ≤ k < N`。第一步在完整 `P_N` 上的边际仍须由实际坐标律支付。
- `N = 0` 时没有 `j : Fin N`，通用积分与联合律声明无虚构调节量。源版 `hnorm` 排除 `N = 0`。`N = 1` 时生存前提为空，结论来自第一步。
- 通用平方可积与拆分适用于方差零及零路径；带除以方差平方根的界明确要求 `hV`。源版用既有 `sourceTruncation_variance_bounds` 支付 `0 < V`，不允许 Lean 的 `a / 0 = 0` 偷渡退化情况。负常数律的调节量平方为正，故不能删 `hV`。
- 拆分使用严格 `<`；生存前提保留源文的 `≤`。只使用事件包含，不作原子为零、严格/非严格概率相等的断言。阈值 `r = 0` 包括在生存前提内；严格事件此时为空。
- 常数是输入 `C` 的明确函数；没有声称从源条件存在统一 `C`，更没有声称调节量源引理或 C1/C2 根已经闭合。

## 接受要求

本轮无机械认证、无独立审查结果。冻结后若实施，须遵守实际服务器单锁/CPU/内存约束；成功产物必须经新鲜独立完整源到声明及证明审查，并有精确源哈希绑定的内核/全部所属声明传递公理收据。仅允许项目三项标准基础公理。
