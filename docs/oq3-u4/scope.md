# OQ3-U4：逆倾斜原律、中心化与返回倾斜律

冻结候选 v1，PROPOSED；未实现，需独立声明审查。拟文件 `Shao/OQ3/InverseTilt.lean`，导入冻结 U3b、Mathlib MeasureTheory.Measure.Tilted 及所需连续/可积库。命名空间 Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。共享定义/入口/pins/cache不改。

## 来源与语义边界

R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，137–145行的原律公式、中心化、有界支撑与再倾斜；所需 π 四矩在89–108行、极限质量在127–135行，已由前序单元覆盖。本单元建立原律 P，不证明独立样本、鞍点唯一性、正KL、联合非格点或尾展开。

每条后来选定的 r 给一份固定 π 和固定 P，所有定义无样本量 n。一般定义对有符号 w 也总化，只有下面显式非负且 HasSum=1 的条件才给真正概率律。所有指数函数的 Integrable 与 Z>0 必须实际消去，不能使用 tilted 在不可积处为零的总化分支。

## 定义候选

```lean
def inverseNormalizer (ell : ℝ) (w : AtomicIndex → ℝ) : ℝ :=
  ∫ x, Real.exp (-ell * normalValue x) ∂atomicMeasure w

def originalMeasure (ell : ℝ) (w : AtomicIndex → ℝ) : Measure ℝ :=
  (atomicMeasure w).tilted (fun x => -ell * normalValue x)
```

## 待冻结导出声明

```lean
theorem integrable_continuous_of_fixed_bounds (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (f : ℝ → ℝ) (hf : Continuous f) :
  Integrable f mu

theorem inverseExp_integrable (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
  Integrable (fun x => Real.exp (-ell * normalValue x)) (atomicMeasure w)

theorem inverseNormalizer_pos (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
  0 < inverseNormalizer ell w

theorem originalMeasure_isProbabilityMeasure (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
  IsProbabilityMeasure (originalMeasure ell w)

theorem originalMeasure_ae_bounds (ell : ℝ) (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂originalMeasure ell w, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10

theorem originalMeasure_integrable_id (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
  Integrable (fun x : ℝ => x) (originalMeasure ell w)

theorem originalMeasure_singleton (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) :
  originalMeasure ell w {fixedAtom i} = ENNReal.ofReal
    (w i * Real.exp (-ell * normalValue (fixedAtom i)) / inverseNormalizer ell w)

theorem originalMeasure_real_singleton (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) :
  (originalMeasure ell w).real {fixedAtom i} =
    w i * Real.exp (-ell * normalValue (fixedAtom i)) / inverseNormalizer ell w

theorem originalMeasure_atom_pos (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) (hi : 0 < w i) :
  0 < (originalMeasure ell w).real {fixedAtom i}

theorem originalMeasure_centered (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  Integrable (fun x : ℝ => x) (originalMeasure ell w) ∧
    (∫ x, x ∂originalMeasure ell w) = 0

theorem originalMeasure_retilt (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
  (originalMeasure ell w).tilted (fun x => ell * normalValue x) = atomicMeasure w

theorem originalMeasure_forward_normalizer (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
  Integrable (fun x => Real.exp (ell * normalValue x)) (originalMeasure ell w) ∧
    (∫ x, Real.exp (ell * normalValue x) ∂originalMeasure ell w) =
      (inverseNormalizer ell w)⁻¹

theorem exists_source_original_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (∫ x, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
      (∀ i, 0 < (originalMeasure sourceEll (limitingMass sourceEll p r)).real {fixedAtom i}) ∧
      (∀ᵐ x ∂originalMeasure sourceEll (limitingMass sourceEll p r),
        1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
      (originalMeasure sourceEll (limitingMass sourceEll p r)).tilted
        (fun x => sourceEll * normalValue x) = atomicMeasure (limitingMass sourceEll p r)
```

两个定义、十三目标。再倾斜指数 `ell*normalValue x` 恒等于源的 `8*ell*x-ell*x²`；该恒等不依赖样本量或源质量选择。centered 的四个 HasSum 前提包含质量1和中心化特征0；不把 π 的一阶矩 q/4误用为P的一阶矩。

## 验收风险

- 对所有实 ell 的指数可积性来自固定紧支撑与连续性，不把 U3a 仅对 ell≥0 的新增特征界延伸到一般负 ell。
- generic 连续可积桥显式要求概率测度与a.e.有界支撑；不能凭连续性在无界支撑上推出可积。
- Z的严格正性、原律概率性和再倾斜等式须使用真实可积门。originalMeasure_ae_bounds 的无条件版本只输出支撑性质，允许总化零测度，不声称该情形为概率。
- singleton 在实线原子而非索引空间上求值；归一化Z必须与所用同一w完全一致。实单点正性还要求该索引质量严格正。
- centered 必须同时给真实 Integrable 与积分0；第三特征正是 `x*exp(-ellY)`，不能跳过Z归一化或把P与π互换。
- source p/q/eps在所有r/J/n之前；未来每条合格r给同一公式的固定P，不选择n依赖的原律。
- 有限阶段、独立样本V_n>0、正KL/唯一鞍点、联合非格点/近共振、LLT、尖点与对角仍OPEN。根A/B/C/D不因本局部单元而关闭。
