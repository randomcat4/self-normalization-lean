# OQ3-U16b：真实正层权重和的一致几何尾界

冻结v1，DECLARATION_REVIEW_QUEUED，尚未批准或实现。拟Shao/OQ3/PositiveLayerTail.lean；imports Shao.OQ3.NormalLayerMassBound、Mathlib.Analysis.SpecificLimits.Normed及既有六tactic分模块；namespace Shao.OQ3、open MeasureTheory Filter、open scoped BigOperators Matrix、noncomputable section。一个公开定义、一个公开目标。

来源R1 SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，390–391的真实scalar层质量界、399–428的相位层d=h(k−theta)及正层几何权重支配。U16a是同一固定真实mu/J下、阈值在全部真实d前的最终C/sqrt n界；本单元从这一真实门完成正层的实际可求和及一致尾界。它不处理负层，也不从该界直接推出完整(19)。根ABCD全OPEN。

```lean
def positiveNormalLayerTerm (mu : Measure ℝ) (q ell h theta : ℝ) (n k : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.exp (-ell * (h * ((k : ℝ) + 1 - theta))) *
    (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = h * ((k : ℝ) + 1 - theta)}

theorem exists_stage_positive_layer_tail_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a ell : ℝ) (hell : 0 < ell)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      Summable (fun k : ℕ => positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
      ∀ K : ℕ, (∑' k : ℕ,
        positiveNormalLayerTerm mu q ell (dyadicMesh J) theta n (K + k)) ≤
          C * Real.exp (-ell * dyadicMesh J) ^ K /
            (1 - Real.exp (-ell * dyadicMesh J))
```

该定义直接使用真实n重产品层质量、实际指数似然权重与sqrt n，未新设替代概率。层位置为h(k+1−theta)：theta∈[0,1]时非负；实际源theta∈[0,1)时覆盖严格正层，theta=1亦保留零层边界。源theta0的d0是有限边界项，不因本单元而额外重复计数。定义对一般实h/theta有总函数意义，但目标仅实例化真实dyadicMesh J>0及theta∈Icc0 1。J0允许。C/同一最终n阈值在全部theta和全部尾起点K前，不能逐theta或逐K另选阈值。

数学路线（未实现）：U16a完整review后先选同一个C>0与eventual所有d的质量界。置h=dyadicMesh J>0，rho=exp(-ell*h)∈(0,1)。对于该eventual n、所有theta∈Icc0 1和k，定义项非负，且

`positiveNormalLayerTerm ... n k ≤ C * rho^k`。

原因是theta≤1使h(k+1−theta)≥hk，ell>0给指数权重≤exp(-ell*h*k)=rho^k；先用真实sqrt n质量界乘非负指数再交换乘法。这里不将总化积分/概率替代真正层质量，也不使用d有界或其n极限。

标准真实实几何级数在0≤rho<1下可求和；C*rho^k可求和。非负项比较给实际层权重项可求和，进而移位K后的序列亦可求和。对全部K，以实际求和单调性比较C*rho^(K+k)，拆pow_add、真实tsum乘常数及tsum_geometric，得到C*rho^K/(1−rho)。分母真>0，未在rho1或无穷totalized tsum上作除法。尾界趋0是直接后果，但本目标只输出精确尾界，不另把父推论计作节点。

真实库SpecificLimits.Normed已缓存，473–497行给hasSum/summable/tsum_geometric_of_norm/abs_lt_one；实际Summable非负比较、tsum_le_tsum、summable_nat_add_iff、tsum常数倍沿既有导入可见，唯一reviewer仍须逐个核对真实类型。U16a源冻结66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1、281行、两公开目标、24项目前置；当前完整review运行，lead全文读完其最终票后才派本声明审查，不在批准前实现。无需新Mathlib缓存，不重编旧成功模块。

本单元只完成固定mu/J的正层绝对权重和控制。未给紧倾斜族统一C，未给负层Chernoff/率二次下界/远区间隙、条件Levy/连续集LLT、完整层和极限、尖点EM、实际旋转hW；不关闭任何根，不声称最弱前提/最优性/新颖性。
