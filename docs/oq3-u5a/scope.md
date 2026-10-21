# OQ3-U5a：实际原子律的相对熵与严格正指数率

冻结候选v1，PROPOSED；未实现，须先独立声明审查。拟文件 `Shao/OQ3/PositiveRate.lean`，导入冻结U4，以及所需严格Jensen/指数凸性库。命名空间Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。

来源R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，146–159行，尤其 `Lambda0=ell*q+log Z=D(pi||P)>0`。π是atomicMeasure w，P是originalMeasure ell w。二者都实际集中于同一可数、无重复的fixedAtom值域。下述熵定义是其标准离散相对熵公式，分子采用π的实际原子质量w，分母采用P的实际实轴单点质量；不把任意总化的实数tsum自动当成有限相对熵。HasSum目标需证明该对数似然序列确实可和。

本单元只处理已构造的无限律及其严格正指数率，不宣称已证明全局鞍点唯一性或尾渐近。最终starter参数仍先于所有后选r/J/n固定。

## 待冻结导出声明

```lean
def saddleRate (ell q : ℝ) (w : AtomicIndex → ℝ) : ℝ :=
  ell * q + Real.log (inverseNormalizer ell w)

def originalAtomEntropy (ell : ℝ) (w : AtomicIndex → ℝ) : ℝ :=
  ∑' i, w i * Real.log (w i / (originalMeasure ell w).real {fixedAtom i})

theorem originalMeasure_ae_range (ell : ℝ) (w : AtomicIndex → ℝ) :
  ∀ᵐ x ∂originalMeasure ell w, x ∈ Set.range fixedAtom

theorem atomicMeasure_normalValue (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  Integrable normalValue (atomicMeasure w) ∧ (∫ x, normalValue x ∂atomicMeasure w) = q

theorem original_log_atom_ratio (ell : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (i : AtomicIndex) (hi : 0 < w i) :
  Real.log (w i / (originalMeasure ell w).real {fixedAtom i}) =
    ell * normalValue (fixedAtom i) + Real.log (inverseNormalizer ell w)

theorem originalAtomEntropy_hasSum (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  HasSum (fun i => w i * Real.log (w i / (originalMeasure ell w).real {fixedAtom i}))
    (saddleRate ell q w)

theorem originalAtomEntropy_eq (ell q : ℝ) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  originalAtomEntropy ell w = saddleRate ell q w

theorem inverseNormalizer_gt_exp_neg_mean (ell q : ℝ) (hell : ell ≠ 0)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  Real.exp (-ell * q) < inverseNormalizer ell w

theorem saddleRate_pos (ell q : ℝ) (hell : ell ≠ 0) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < saddleRate ell q w

theorem originalAtomEntropy_pos (ell q : ℝ) (hell : ell ≠ 0) (w : AtomicIndex → ℝ)
    (hw : ∀ i, 0 < w i)
    (hm : ∀ k, HasSum (fun i => w i * constraintFeature ell (fixedAtom i) k)
      (constraintTarget q k)) :
  0 < originalAtomEntropy ell w

theorem exists_source_positive_entropy_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (∫ x, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
      originalAtomEntropy sourceEll (limitingMass sourceEll p r) =
        saddleRate sourceEll q (limitingMass sourceEll p r) ∧
      0 < saddleRate sourceEll q (limitingMass sourceEll p r) ∧
      0 < originalAtomEntropy sourceEll (limitingMass sourceEll p r)
```

两定义、九目标。实际原子律P中的零权重/不可积总化分支不能用于这里的相对熵结论；熵三目标明确要求每个原子w严格正，矩条件的首分量给HasSum w 1，U4提供Z>0、P真概率及分母严格正。ell不为零是严格正性的必要显式前提；ell=0时该率与熵都为零，不能删去hell。

严格Jensen用于实随机变量 `-ell*normalValue`，可积性须由实际有界支撑证明，严格性须排除AE常量。fixedAtom(inl 0)=-1与fixedAtom(inl 1)=1的normalValue分别为-9、7且都质量正，因此ell≠0排除常量。不能把π的均值q/4与原律P的均值0交换。

此处没有新共享KL定义，也不声称任意测度上的Radon–Nikodym相对熵框架已建立。对当前双方均集中在fixedAtom值域、fixedAtom单射、每个质量严格正的离散概率律，显式求和定义就是标准离散D(π||P)。审查须核对这层具体对应。有限阶段律、鞍点方程/全局极小唯一性、正定协方差、LLT、尖点和对角仍待后继单元；根A/B/C/D仍OPEN。
