# OQ3-U9b：真实有限产品的精确换测度

冻结候选v1，PROPOSED；尚未实现。拟文件 `Shao/OQ3/SampleChangeOfMeasure.lean`，导入 `Shao.OQ3.AtomicProductControl` 和 `Shao.OQ3.PositiveRate`，namespace Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，499–520。接已有单点逆倾斜，将源(27)写为真实Measure.pi上的恒等式，再把已实现U11c的似然期望比较接到原律归一化尾系数。两定义、五公开目标；n=0亦包括。

## 冻结候选声明

```lean
def normalizedTailCoefficient (ell q : ℝ) (w : AtomicIndex → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * (n : ℝ)) * Real.exp ((n : ℝ) * saddleRate ell q w) *
    (Measure.pi (fun _ : Fin n => originalMeasure ell w)).real (sourceTail q n)

def tiltedTailCoefficient (ell q : ℝ) (w : AtomicIndex → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * (n : ℝ)) *
    (∫ z, (sourceTail q n).indicator (fun z => Real.exp (-ell * normalDeviation q z)) z
      ∂Measure.pi (fun _ : Fin n => atomicMeasure w))

theorem iid_inverseNormalizer (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) :
  Integrable (fun z : Shao.Path n => Real.exp (-ell * (∑ i, normalValue (z i))))
    (Measure.pi (fun _ : Fin n => atomicMeasure w)) ∧
    (∫ z : Shao.Path n, Real.exp (-ell * (∑ i, normalValue (z i)))
      ∂Measure.pi (fun _ : Fin n => atomicMeasure w)) = (inverseNormalizer ell w) ^ n

theorem original_iid_eq_tilted (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) :
  Measure.pi (fun _ : Fin n => originalMeasure ell w) =
    (Measure.pi (fun _ : Fin n => atomicMeasure w)).tilted
      (fun z => -ell * (∑ i, normalValue (z i)))

theorem iid_event_change_of_measure (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ)
    (E : Set (Shao.Path n)) (hE : MeasurableSet E) :
  Real.exp ((n : ℝ) * saddleRate ell q w) *
      (Measure.pi (fun _ : Fin n => originalMeasure ell w)).real E =
    ∫ z, E.indicator (fun z => Real.exp (-ell * normalDeviation q z)) z
      ∂Measure.pi (fun _ : Fin n => atomicMeasure w)

theorem normalizedTailCoefficient_eq_tilted (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (n : ℕ) :
  normalizedTailCoefficient ell q w n = tiltedTailCoefficient ell q w n

theorem finite_limit_normalized_tail_error_le (ell : ℝ) (hell : 0 ≤ ell) (q : ℝ)
    (hq : q ≤ 2) (p : Fin 4 → ℝ) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : Summable r) (J : ℕ)
    (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hl : ∀ i, 0 ≤ limitingBase ell p r i) (hj : ∀ i, 0 ≤ finiteBase ell p r J i)
    (n : ℕ) :
  |normalizedTailCoefficient ell q (limitingMass ell p r) n -
      normalizedTailCoefficient ell q (finiteMass ell p r J) n| ≤
    Real.sqrt (2 * Real.pi * (n : ℝ)) * Real.exp (11 * ell * (n : ℝ)) *
      (n : ℝ) * compensationTailConstant ell * (∑' j, r (J + j))
```

## 概率门、精确归一化与证明路线

前四条不需要ell>=0或q的均值约束：它们是任意固定逆倾斜原子概率律的精确换测度，saddleRate仅指既有定义ell*q+log Z，不额外声称此q处全局Legendre极值。hw/hs给真实原子概率、逆指数真实可积与Z>0，以及真实原律概率。有限重积是Measure.pi，不是对角推前。首目标须由单坐标inverseExp_integrable及真正可积的有限乘积得到；实数积分总化不能代替Fubini/有限产品公式。

第二目标可在可测矩形上用Measure.pi_eq、tilted_apply、restrict_pi_pi和真实可积的有限乘积积分证明：每坐标密度exp(-ell Y)/Z，联合密度exp(-ell sumY)/Z^n。必须明确Z>0，且只在首目标给出的真实联合归一化积分上操作。所有每坐标限制测度仍有限，限制后的指数乘积真实可积；不以未知可积性直接转换lintegral为ofReal integral。

第三目标要先用真实概率与非负可积密度将real事件概率化为实积分，再用exp(n(ell*q+log Z))/Z^n=exp(n ell q)，得到exp(-ell(sumY-nq))。E任意可测，没有把sourceTail概率替换成另一个事件。第四目标取E=sourceTail并乘相同非负sqrt因子，正是源(27)。n=0时空产品、Z^0=1、事件为唯一空路径的子集；等式与定义均正常。

第五目标从真实limit/finite非负、HasSum质量1、hM/hc约束门分别应用第四目标，再乘U11c似然期望误差。指数率分别使用两个实际原律的saddleRate，没有假设有限阶段与极限的率相等，也没有按n重选原律。所得误差为完整权重L1路线，系数与Mathlib全TV/源半TV的归一化差异无混淆。这里不定义TV符号，也不声称TV恒等式。

此单元若通过，将连接源(27)和(28)/(29)的直接误差界；仍未证明(30)常数连续性、LLT、尖点Euler–Maclaurin、相位见证或固定原律对角结论。根A/B/C/D保持OPEN；p/q/ell先于r/J/n固定，beta<2/5仍仅充分修复。
