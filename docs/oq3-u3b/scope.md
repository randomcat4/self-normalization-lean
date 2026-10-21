# OQ3-U3b：固定可数原子概率测度与可积矩

冻结候选 v1，PROPOSED；未实现，需独立声明审查。拟文件 `Shao/OQ3/AtomicMeasure.lean`，导入已冻结 U3a 和 Mathlib Bochner.SumMeasure。命名空间 Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。不修改共享 Probability、入口、pins 或缓存。

## 来源与范围

R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，127–130行的极限概率律 π 与四个约束，143–145行的有界且远离零的支撑，以及149–153行的倾斜均值 a=q/4。这里 π 指 R1 的倾斜律；137–145行的逆倾斜原律 P 仍待后继单元。

用通用实质量 w 定义原子测度，非负和 HasSum=1 是成为概率测度的显式门。任意有符号 w 的定义只使用 ofReal 总化截断，不宣称恢复原有有符号质量。对非负 w 则逐原子实概率精确等于 w_i；U3a 的 fixedAtom 全索引单射保证没有合并质量。

## 定义候选

```lean
def atomicMeasure (w : AtomicIndex → ℝ) : Measure ℝ :=
  Measure.sum fun i => ENNReal.ofReal (w i) • Measure.dirac (fixedAtom i)
```

## 待冻结导出声明

```lean
theorem atomicMeasure_singleton (w : AtomicIndex → ℝ) (i : AtomicIndex) :
  atomicMeasure w {fixedAtom i} = ENNReal.ofReal (w i)

theorem atomicMeasure_real_singleton (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : AtomicIndex) :
  (atomicMeasure w).real {fixedAtom i} = w i

theorem atomicMeasure_isProbabilityMeasure (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
  IsProbabilityMeasure (atomicMeasure w)

theorem atomicMeasure_ae_range (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range fixedAtom

theorem atomicMeasure_ae_bounds (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂atomicMeasure w, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10

theorem integrable_atomicMeasure_iff (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) :
  Integrable f (atomicMeasure w) ↔
    Summable (fun i => w i * ‖f (fixedAtom i)‖)

theorem integral_atomicMeasure (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) (hf : Integrable f (atomicMeasure w)) :
  (∫ x, f x ∂atomicMeasure w) = ∑' i, w i * f (fixedAtom i)

theorem atomicMeasure_integral_of_hasSum (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) (z : ℝ)
    (hs : HasSum (fun i => w i * f (fixedAtom i)) z) :
  Integrable f (atomicMeasure w) ∧ (∫ x, f x ∂atomicMeasure w) = z

theorem atomicMeasure_constraints (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  ∀ k, Integrable (fun x => constraintFeature ell x k) (atomicMeasure w) ∧
    (∫ x, constraintFeature ell x k ∂atomicMeasure w) = constraintTarget q k

theorem atomicMeasure_mean (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  Integrable (fun x : ℝ => x) (atomicMeasure w) ∧
    (∫ x, x ∂atomicMeasure w) = q / 4

theorem exists_source_measure_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (atomicMeasure (limitingMass sourceEll p r)) ∧
      (∀ i, (atomicMeasure (limitingMass sourceEll p r)).real {fixedAtom i} =
        limitingMass sourceEll p r i ∧ 0 < limitingMass sourceEll p r i) ∧
      (∀ k, Integrable (fun x => constraintFeature sourceEll x k)
        (atomicMeasure (limitingMass sourceEll p r)) ∧
        (∫ x, constraintFeature sourceEll x k ∂atomicMeasure (limitingMass sourceEll p r)) =
          constraintTarget q k) ∧
      (Integrable (fun x : ℝ => x) (atomicMeasure (limitingMass sourceEll p r)) ∧
        (∫ x, x ∂atomicMeasure (limitingMass sourceEll p r)) = q / 4) ∧
      (∀ᵐ x ∂atomicMeasure (limitingMass sourceEll p r),
        1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10)
```

一个定义、十一目标。source family 中 p/q/eps 先于任意 r 一次固定；任意后来满足预算的 r 都给一份固定无限测度，整个定义没有运行样本量 n。U3a 的非空见证仍适用，但不指定其为最终对角序列。

## 验收风险

- 概率测度不能只由总化 tsum 等式推出；要消费真实 HasSum=1 与质量非负。
- singleton 结论是实轴上每个 fixedAtom 的质量，须用全索引单射；不能误用索引测度 singleton 代替。
- 任意 f 的可积性等价包含带权范数可求和；全部实矩输出分别包含 Integrable，不能把 Lean 不可积时的 integral=0 约定当作矩存在。
- atomicMeasure_integral_of_hasSum 使用实值无条件收敛等价绝对收敛；不能把条件收敛的自然数前缀极限当 HasSum。
- ae_range 表示测度集中在可数原子集合，不宣称该集合闭。极限旧点 beta 已在基点中；点集闭包与测度集中需区分。
- mean=q/4 属倾斜律 π。原律 P 的均值零、归一化 Z>0、逆倾斜与再倾斜恒等式尚未覆盖。
- 有限阶段测度/总变差收敛、独立样本 V_n>0、真正联合非格点、LLT、尖点和最终 witness 后选尾预算都未闭合；根 A/B/C/D 保持 OPEN。
