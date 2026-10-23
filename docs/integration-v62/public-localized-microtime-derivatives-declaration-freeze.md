# Actual localized scalar-noise derivatives — ROOT FROZEN

The root fully read the complete candidate proof, all two selected public heads,
all literal local values and candidate checks once before implementation.
The exact selected heads and values are copied verbatim below. Author may not
change any assumption, constant, quantifier order, actual law/test/kernel or
literal value without an explicit root revision. Zero new definitions.

Override only the candidate administrative restriction on helper placement:
additional PRIVATE helper THEOREMS are explicitly authorized, with all their
actual private/generated types and transitive axioms included in the final
complete independent review. No new private/global def/abbrev/instance.
This permits opaque small proof units instead of a giant local-have chain.
Selected two public heads and all chosen literal values remain exact.

Source ownership: only Shao/Probability/SourceLocalizedMicrotimeDerivatives.lean
in the separately activated worktree, plus drafts/c12-localized-microtime-derivatives/.
No upstream source or another author's source changes. Existing producer checks
and qualified old reviews are reused. The not-yet-qualified bounded-y source may
be read as implementation reference, but is not an accepted theorem dependency.
Self-contained scalar FTC/Fubini is authorized. The source-tail module is fully
qualified and currently enters v61; its original exact successful object is reused.

Every new whole-source success must produce -o in the same command, then one
complete actual-owner/type/value/transitive-axiom audit. CPU10–13, root-heavy.lock,
-M8192/-j4, fixed toolchain/cache, no local Lean. Use original pending operations;
queue/transport timeout is not permission to replay. Keep writing local proofs
while actual server checks queue. Fresh independent complete review is mandatory.
All original microtime probability assembly/C1C2 roots remain OPEN.

Candidate immutable evidence SHA256:
- candidate-declarations.md: 95c454bb678c908d402b748965c2123e0b98595fd3dba60e41b1e19552b237a9
- proof-candidate.md: 28a8daf183820ce7f68a5997bee8a9084e73545780184717ac28275fed5c4ac3
- candidate-check.md: 2861da44bf03bc0b999e2d8bce86b9c761b2c19293d4098a2cb689f65fc1f452

## Complete selected candidate heads and literal values

# 待 root 冻结的完整候选声明

候选版本 1；尚未冻结、尚无 Lean 实现/检查。建议新生产模块
`Shao/Probability/SourceLocalizedMicrotimeDerivatives.lean`。两个 public theorem，零个
top-level private declaration，零个新 def/abbrev/structure/instance。所有辅助证明使用
局部 have；若实现确需新增顶层 private 头，必须先补齐其完整文本并重新提交冻结。

建议 imports：`Shao.Probability.SourceFutureNoiseFourier`、
`Shao.Probability.SourceGrowingMicrotimeTail`、
`Mathlib.Analysis.Calculus.ParametricIntegral`、
`Mathlib.Analysis.Calculus.Deriv.Support`、
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`。
不以尚未接受的 SourceBoundedYReflection 作为当前已证明依赖。

共同上下文：

```lean
set_option autoImplicit false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Topology
```

## 1. 同一实际完整噪声核：全局可微、局部真概率、外支撑及 m=0

```lean
theorem sourceFutureNoiseKernel_scalar_localized_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          let gamma : ℝ :=
            (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
          gamma ≤ 2 * h →
            ∀ (m : ℕ) (y : ℝ), 2 ≤ y →
              h ≤ 1 / (192 * (1 + y)) →
              let pi : Measure (Shao.Path m) :=
                Measure.pi (fun _ : Fin m => ν)
              let f : ℝ → ℝ → ℝ :=
                fun q w => sourceFutureNoiseKernel ν m y (w, q)
              (∀ q w : ℝ,
                DifferentiableAt ℝ (f q) w ∧
                  DifferentiableAt ℝ (fun r : ℝ => deriv (f q) r) w) ∧
              (∀ q : ℝ, 5 < q → ∀ w : ℝ,
                f q w = 0 ∧ deriv (f q) w = 0 ∧
                  deriv (fun r : ℝ => deriv (f q) r) w = 0) ∧
              (∀ q w : ℝ, q ∈ Set.Icc (1 / 16 : ℝ) 5 → |w| ≤ h →
                |deriv (f q) w| ≤ C / gamma *
                    pi.real {a : Shao.Path m |
                      y / 8 ≤ |Shao.prefixSum a m|} ∧
                  |deriv (fun r : ℝ => deriv (f q) r) w| ≤ C / gamma ^ 2 *
                    pi.real {a : Shao.Path m |
                      y / 8 ≤ |Shao.prefixSum a m|}) ∧
              (m = 0 →
                (∀ q w : ℝ, |w| ≤ 2 * h → f q w = f q 0) ∧
                  (∀ q w : ℝ, |w| ≤ h →
                    deriv (f q) w = 0 ∧
                      deriv (fun r : ℝ => deriv (f q) r) w = 0))
```

## 2. 原始二阶律的真实条件核：局部概率界和已验指数尾接合

L2、epsilon0 和其选择界在原始律之前量化。指数结论需要真实微小时钟；没有新的
微小时钟浓缩假设，T、pi、f 均逐字给出。

```lean
theorem sourceTruncation_growing_microtime_derivative_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ L2 epsilon0 : ℝ, 0 < L2 → 0 < epsilon0 →
        epsilon0 ≤ 1 / (192 * Real.sqrt (L2 + 1)) →
        ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
          ∀ n : ℕ, Integrable (fun a : ℝ => a ^ 2) ν0 →
            (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1 →
            (∫ a : ℝ, a ∂ν0) = 0 →
            ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon →
              epsilon ≤ epsilon0 / 2 →
              Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
              ∀ y : ℝ, 2 ≤ y →
                |y - x| ≤ 1 / (2 * (1 + x)) →
                ∀ m : ℕ, m ≤ n →
                  let h : ℝ := epsilon0 / (1 + y)
                  let ρ : Measure ℝ := ProbabilityTheory.cond ν0
                    {a : ℝ | |a| ≤ epsilon / (1 + x)}
                  let raw2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ρ
                  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ρ
                  let V : ℝ := variance (id : ℝ → ℝ) ρ
                  let gamma : ℝ := m3 / V
                  let T : ℝ := (m : ℝ) * raw2
                  let pi : Measure (Shao.Path m) :=
                    Measure.pi (fun _ : Fin m => ρ)
                  let f : ℝ → ℝ → ℝ :=
                    fun q w => sourceFutureNoiseKernel ρ m y (w, q)
                  T ≤ L2 * gamma ^ 2 →
                    (∀ q w : ℝ,
                      DifferentiableAt ℝ (f q) w ∧
                        DifferentiableAt ℝ (fun r : ℝ => deriv (f q) r) w) ∧
                    (∀ q : ℝ, 5 < q → ∀ w : ℝ,
                      f q w = 0 ∧ deriv (f q) w = 0 ∧
                        deriv (fun r : ℝ => deriv (f q) r) w = 0) ∧
                    (∀ q w : ℝ, q ∈ Set.Icc (1 / 16 : ℝ) 5 → |w| ≤ h →
                      |deriv (f q) w| ≤ C / gamma *
                          pi.real {a : Shao.Path m |
                            y / 8 ≤ |Shao.prefixSum a m|} ∧
                        |deriv (fun r : ℝ => deriv (f q) r) w| ≤ C / gamma ^ 2 *
                          pi.real {a : Shao.Path m |
                            y / 8 ≤ |Shao.prefixSum a m|} ∧
                        |deriv (f q) w| ≤
                          C / gamma * Real.exp (-4 * y ^ 2) ∧
                        |deriv (fun r : ℝ => deriv (f q) r) w| ≤
                          C / gamma ^ 2 * Real.exp (-4 * y ^ 2)) ∧
                    (m = 0 →
                      (∀ q w : ℝ, |w| ≤ 2 * h → f q w = f q 0) ∧
                        (∀ q w : ℝ, |w| ≤ h →
                          deriv (f q) w = 0 ∧
                            deriv (fun r : ℝ => deriv (f q) r) w = 0))
```

## 3. 局部证明中允许使用的全部对象 literal values

此段没有声明新的顶层定义或顶层私有头。以下是通用头证明中所选 local lets 的完整
值，避免把真实噪声/测试核藏在新的未展开名称后。M 与 C 通过存在消去得到，不是新定义。

```lean
let P : Measure ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) :=
  (quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν)
let pi : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => ν)
let μ : Measure
    (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) :=
  pi.prod P
let B : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) → ℝ :=
  fun c => (∑ j : Fin 8, (c.1 j).1) - (∑ j : Fin 8, (c.2 j).1)
let D : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) → ℝ :=
  fun c => (∑ j : Fin 8, (c.1 j).2) + (∑ j : Fin 8, (c.2 j).2)
let b : (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
  fun a => Shao.prefixSum a.1 m + B a.2
let R : (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
  fun a => q + Shao.energy a.1 + D a.2
let lo : ℝ →
    (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
  fun w a => (-y * Real.sqrt (R a) - w - b a) / gamma
let hi : ℝ →
    (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
  fun w a => (y * Real.sqrt (R a) - w - b a) / gamma
let F : ℝ →
    (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
  fun w a => ∫ t : ℝ,
    sourceFourierTest y (w + b a + gamma * t, R a) ∂sourceScalarLaw
let F1 : ℝ →
    (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
  fun w a => sourceKernelCutoff (R a) / gamma *
    (sourceScalarDensity (lo w a) - sourceScalarDensity (hi w a))
let F2 : ℝ →
    (Shao.Path m × ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ))) → ℝ :=
  fun w a => sourceKernelCutoff (R a) / gamma ^ 2 *
    (deriv sourceScalarDensity (hi w a) - deriv sourceScalarDensity (lo w a))
let E : Set (Shao.Path m) :=
  {a : Shao.Path m | y / 8 ≤ |Shao.prefixSum a m|}
```

第二头的局部对象与声明中同名 lets 完全相同，唯一额外的缩写为

```lean
let hcut : ℝ := epsilon / (1 + x)
```

数值常数不另建定义：第一头取由密度界得到的 `2 * M`；第二头取
`C0 * (2 * Real.exp 17 + 1)`，其中 C0 为第一头存在消去的常数。实现可以不用上述缩写
而逐字展开；不能改变其 literal value。若新增任何局部函数对象，应先在本段给出完整值。

## 4. 冻结前的精确检查边界

* 全部量词均指真实 `sourceFutureNoiseKernel`、同一 `quadraticFullNoiseLaw`、实际 πm。
* 通用头的 `gamma ≤ 2*h` 由第二头从已接受真实截断界推出，不是假设原始结论。
* q>5 分支是整个 w 实轴上的函数恒零；m=0 分支是半径 2h 的真局部常数和半径 h
  的闭区间导数零；没有错误地要求 m=0 时函数本身为零。
* 第一头不需要 T；第二头 T≤L2γ² 用于接合已验尾界。epsilon0 的选取在所有律之前。
* 没有把导数积分表示、端点支撑、尾界或未来和的密度加入输入。
