# OQ3-U16j：真实曲边尾事件的局部负层与统一几何尾和

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U16I_FINAL，尚未批准或实现。拟Shao/OQ3/LocalNegativeLayerControl.lean。imports Shao.OQ3.LocalNegativeLayerTail、Shao.OQ3.SampleBoundary、Mathlib.Analysis.SpecificLimits.Normed；namespace Shao.OQ3，open MeasureTheory Filter，open scoped BigOperators，noncomputable section。一个完整公开定义、两个公开目标。必须在I完整独立终票被lead全文读取后才派本声明门，批准前不实施/Leanprobe。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，361–391和400–429。I仅真实双侧事件局部概率；本单元把source a=q/4和真实曲边几何接上，保留局部截断，再生产同一theta/K外的几何尾和，不把局部结论冒充全负层。

```lean
def localNegativeNormalLayerTerm (mu : Measure ℝ) (q ell h theta delta : ℝ)
    (n k : ℕ) : ℝ :=
  if h * ((k : ℝ) + theta) / (n : ℝ) ≤ delta then
    Real.sqrt (n : ℝ) * Real.exp (ell * (h * ((k : ℝ) + theta))) *
      (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = -(h * ((k : ℝ) + theta)) ∧
          z ∈ sourceTail q n}
  else 0

theorem exists_local_source_negative_layer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ delta gamma C : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 0 ≤ k → k / (n : ℝ) ≤ delta →
        Real.sqrt (n : ℝ) * Real.exp (ell * k) *
          (Measure.pi (fun _ : Fin n => mu)).real
            {z : Shao.Path n | normalDeviation q z = -k ∧ z ∈ sourceTail q n} ≤
          C * Real.exp (-gamma * k)

theorem exists_local_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ delta gamma C : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J))
```

定义真实事件是同一个mu的同n重产品上M=-h(k+theta)且sourceTail q n，权重恰exp(ell*h(k+theta))，负层实际偏移用theta加号。if条件保留h(k+theta)/n<=delta的局部截断；不是把大负层质量设零作全事件断言，只定义了局部贡献。theta in[0,1]可含两端；theta0/k0包含零层上界合法，不能声称零层特殊极限完成。n0定义用实除法总化只是函数定义，所有证明中合法缩放都在eventual n>=1以后；不得据0除总化证明实际归一化。

首目标同一delta/gamma/C/eventualN先于全部非负实k，不缩成自然k。对I所得delta0/gamma/c/C，选delta=min(delta0,16delta0²/q)>0（亦可进一步缩小）；令r=sqrt(nqk/16)>=0。n>=1后r²=nqk/16且r/n<=delta0，由k/n<=16delta0²/q和正q/n平方比较严格推出。I的k/n,r/n门齐备。actual sourceTail_on_normal_layer q hq n hn z (-k) hd给r²<=tangentDeviation q z²，而hmeanX=q/4使I的R_a=sumX-n*(q/4)恰tangentDeviation q；r>=0后r<=abs R_a。故真实曲边事件包含I的双侧tail事件。mu产品真概率有限，measureReal_mono合法；权重非负，c*r²/n>=0使指数余项可舍去，得精确首目标。样本实际R不必局部有界；源尾条件包含energy/positive sum，不能把等式形式丢掉再错误推几何。

第二目标消费首目标同一delta/gamma/C/N，取h=dyadicMesh J>0和rho=exp(-gamma*h) in(0,1)。全部n在同N之后、全部theta in[0,1]及k自然，t=h*(k+theta)>=0。if true时首目标给局部真实层项<=C exp(-gamma*t)<=C rho^k（theta>=0）；if false时定义项0。所有项非负，Summable.of_nonneg_of_le与真实geometric Summable给可求和；对K平移用rho^(K+k)=rho^K rho^k，真tsum比较和几何和1/(1-rho)给冻结上界。C/N在全部theta/K之前，不能逐theta重选；K0/空tail/边界if等号均保留。定义完整体/publictypes必须独立逐项盲译先持久化，实际I和标准积分/概率/实质量/几何级数API随后核，机械最后。

本单元仍仅local cutoff贡献，不给大k/n远区或完整全负层Summable，不证明source3全局唯一最小、(19)完整支配、有限层LLT、hW/WC/KL或根闭合。远区一维energy mgf+Bernoulli finite试验+compact finitecover仅作者未冻结数学笔记，不作为本类型隐含前提或已完成结论。无最弱/最优/新颖性主张；根ABCD全部OPEN。不cachewrite/copyroot源码/rebase/merge。
