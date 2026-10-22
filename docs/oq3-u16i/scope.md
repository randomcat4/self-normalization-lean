# OQ3-U16i：真实局部负层的双侧概率与指数权重界

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U16H_FINAL，尚未批准或实施。拟Shao/OQ3/LocalNegativeLayerTail.lean。imports Shao.OQ3.NormalTrialCost、Shao.OQ3.CompactTiltLayerMassBound、Shao.OQ3.CenteredSampleTilt；namespace Shao.OQ3，open MeasureTheory Filter，open scoped BigOperators，noncomputable section。零新公开定义，一个公开目标。前置G当前完整proof审查中，H仅冻结待审；两者全部完成独立终票且lead全文读完后才派本声明门，批准前不实施/Leanprobe。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，350–389，尤其真实双向倾斜(16)和局部权重余量(17)。本目标从已接受actual显式normalTrialCost直接给(17)所需的充分局部概率界，不声称该cost等于Legendre上确界，也不声称源(16)的最优inf公式。使用相同充分gap ell<q/(32T)，不改变根假设。

```lean
theorem exists_local_negative_layer_tail_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = a)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ delta gamma c C : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ k r : ℝ, 0 ≤ k → 0 ≤ r →
        k / (n : ℝ) ≤ delta → r / (n : ℝ) ≤ delta →
          (n : ℝ) * q * k / 16 ≤ r ^ 2 →
            Real.sqrt (n : ℝ) * Real.exp (ell * k) *
              (Measure.pi (fun _ : Fin n => mu)).real
                {z : Shao.Path n | normalDeviation q z = -k ∧
                  r ≤ |(∑ i : Fin n, z i) - (n : ℝ) * a|} ≤
              C * Real.exp (-gamma * k - c * r ^ 2 / (n : ℝ))
```

完整类型的mu是真实固定概率及同一有限stage支持，真实EY/EX和同mu S/det正性保持。k是非负实数，不能悄悄改成自然数，从而保留真实有限格相位偏移；r是非负实阈值，不排除k0/r0。delta/gamma/c/C和eventual n阈值在全部k/r之前，同一C/N不可逐trial选取。仅要求trial位置k/n,r/n在中央邻域，实际事件内的样本偏差可以任意远；不得另加样本abs R<=delta*n。n0无需除0：eventual阈值包含n>=1，冻结目标没有作n0特定结论。

实际normalTrialTilt给S=normalVariance mu、T=transverseVariance mu=det/S>0、b=Cov(Y,X)/S。已接受U16e产出delta0,gamma,c>0及全部允许k/r上的 n*actualTrialCost(-k/n,+/-r/n)-ell*k>=gamma*k+c*r²/n。再缩小delta<=min(delta0,1,q/(64*(b²+1)))，严格正；不能静默假设b>=0。由k/n<=delta及nqk/16<=r²得b²k²<=r²/4，故|b|k<=r/2。正支切向s=(r+b*k)/(n*T)>=0，负支s=(-r+b*k)/(n*T)<=0；k0/r0仍合法，禁止除k/r/b。每支真正先证明这个sign门才可套tail点态下界。

选择固定参数方形Q=Icc(-1,1)×Icc(-1,1)，用实际连续线性映射 (y,z)->normalTrialTilt mu y z=(v,s)->(8v+s,-v) 得真实compact quadratic K。trial y=-k/n,z=+/-r/n全属于Q，K在n/k/r之前选定。G的actual compact二次tilt族给同一C0>0和eventualN先于全部p∈K与全实层d，不得改用逐p固定mu的旧U16a。H2先把真实centered projection tilt等于该quadratic tilt，H1/H3绑定真实同n重产品、正normalizer、真概率及事件指数比较。

定义R_a(z)=sum_i z_i-n*a（只作本段记号，不新增定义）。实际sampleProjection逐点有限求和恒等式为v*M+s*R_a；不能把tangentDeviation a误当R_a，因为已有tangentDeviation q以n*q/4为中心。正事件E+={M=-k,r<=R_a}、负事件E-={M=-k,R_a<=-r}真实闭可测，依据s正负得点态sampleProjection>=v*(-k)+s*(+/-r)。H3因此给真实指数比较。倾斜后E+/-都包含在同M=-k层，真finite概率measureReal_mono给事件质量<=层质量。每个tilt须保留H/G先证的exp真可积/正Z/真实概率，不得由不可积tilted=0或toReal top总化完成。

n>=1后，以真实normalTrialCost定义和合法n非零环恒等式把H因子写成exp(-n*actualTrialCost(-k/n,+/-r/n))，再乘sqrt n*exp(ell*k)，消费G的同C0以及U16e actualcost余量，得两支各<=C0*exp(-gamma*k-c*r²/n)。整个abs事件包含两支并，真实finite概率measureReal_union_le及mono给同一2C0。无需不交，r0两支重复计数保留正确上界。先给全部事件可测和各倾斜真实概率，再作积分/实质量比较；不得以形式指数公式代替真实换测度。

该目标尚非sourceTail上全部负层的(17)：后续source a=q/4、真实曲边恒等式及r=sqrt(nqk/16)才可在进一步小k/n区域给sourceTail的局部weighted exp(-gamma k)上界。大k/n区域仍需global strict rate gap，完整负层/(19)/LLT/hW及根ABCD继续OPEN。无Legendre最优性、最弱/最优/新颖性或全局率主张。不得cachewrite/copyroot源码/rebase/merge。
