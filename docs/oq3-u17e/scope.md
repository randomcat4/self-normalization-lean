# OQ3-U17e：真实全部负法向层的统一指数界

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U17D_FULL_FINAL；未批准/未实现。拟Shao/OQ3/GlobalNegativeLayerBound.lean。imports Shao.OQ3.SourceFarWeightedTail、Shao.OQ3.LocalNegativeLayerControl；namespace Shao.OQ3，open MeasureTheory Filter，open scoped BigOperators，noncomputable section。零公开定义、一个完整公开目标。D作者严格门完成/完整proof审查中；只有D终票lead全文读完接受才派本声明门，批准前不写本源/Lean probe，不动冻结前置源。

来源current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，378–391负层加权和远区衰减、400–408实际曲边/负层、421–429层尾控制。本目标真正取消局部k/n守卫，固定真实有限stage模型给全部实k>=0的负层加权指数界；不含完整LLT/全部层极限(19)、hW或一般KL/全局最优。

```lean
theorem exists_global_source_negative_layer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q H ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hellq : ell * q < 7 / 200)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 0 ≤ k →
        Real.sqrt (n : ℝ) * Real.exp (ell * k) *
          (Measure.pi (fun _ : Fin n => mu)).real
            {z : Shao.Path n | normalDeviation q z = -k ∧ z ∈ sourceTail q n} ≤
          C * Real.exp (-gamma * k)
```

必须独立盲译完整type再读本路线。保留J全部真实均值/同mu S/T/det/gap/AE有限支撑和正单点门，另有D充分参数范围/能量支持/ell*q严格gap。hsecond没有作为新隐藏假设：hb给真实x/x²/normalValue可积，actualY=8x−x²的实际积分等式与EX=q/4/EY=q必须显式推出EX²=q，再消费D。H的数值范围与actual能量区间由源模型将来专化，当前不默改或假定它自动由hb蕴含。gamma/C/N位于全部真实实k外；k0/ell0/J0保留，n只eventually，必须包含n>=1后做任何正除法。无k/n局部守卫。

J先给同delta0/gamma0/C0>0/N0的actual sourceTail局部负层界。D用同mu/q/H/ell、actualEX²=q和delta0给Cfar/cfar>0，对全部n>=1真实全weight Integrable和sourceTail∩{M<=−delta0*n}的weighted积分<=Cfar exp(−cfar*n)。这些常数都在n/k之前选，不把某个随n或k变化的概率族混进来。

从真实stage支撑给Y>=−9：每个stageAtom inl/base或inr/added确为对应fixedAtom，消费已接受fixedAtom_normalValue_lower；hrange传到mu-AE，再真实产品AE逐坐标提升/有限求和给M>=−(9+q)*n>=−11*n，q<103/100<2。注意**一般hb绝对有界不蕴含Y>=−9**，不可跳过有限支撑门。若k>11*n，层交sourceTail在产品AE支持上为空，先证明实际测度为0或AE非成员，再得real质量0；禁止利用ENNReal.toReal∞=0。

对k/n<=delta0用J局部界。否则k/n>delta0，n>0后负层集合真实包含D far集合。层交sourceTail可测，原weight真全可积先restrict，在该层M=−k上setIntegral_congr_fun实际等于exp(ell*k)，真实有限产品积分常数=exp(ell*k)*P_n.real(layer∩tail)，按真实非负/可积subset积分比较由D得weighted质量<=Cfar exp(−cfar*n)。不能只比较未加权概率然后漏exp(ell*k)。

在非零可能区k<=11*n，取gammafar=cfar/22，a=cfar/2>0，得到exp(−cfar*n)<=exp(−a*n)*exp(−gammafar*k)。真实统一prefactor界sqrt(n)*exp(−a*n)<=1/a+1可直接由sqrt(n)<=n+1、a*n<=exp(a*n)、exp(−a*n)<=1和正a/exp取消得到，无需新极限cache。也可用现成真正极限/有界性接口，但须只读核API/缓存，不写新cache。选择gamma=min(gamma0,gammafar)>0、C=max(C0,Cfar*(2/cfar+1))>0，N0合n>=1；分local/far/AEzero三种实际情况给完整冻结全k界。

该完整目标若proof过门可记真实全负层逐层(17)的充分producer；无if截断的全负层真Summable/theta-K几何尾须另冻，finite-layer LLT/所有正负层极限(19)/单侧rotation/cuspEM/hW仍OPEN；source3一般KL/RN/DPI/任意rho唯一鞍点也不由概率替代路线关闭。不能把D远负normal部分冒称整个joint外区都已控制。根ABCD开放，无最弱/最优/新颖性主张，beta<2/5仅充分修复，p/q/eps/P固定先于r/J/n。

资源：新作者Lean严格autoImplicit=false、CPU14–17、native-M8192-j4，本线一heavy；禁止ulimit-v/改心跳语义/干预用户0–9独立任务。reviewer只读noLean/probe/rebuild/spawn/cachewrite，完整type/source/proof/actual全部TYPE优先，最后hash/pins/cache，标准三axiom白名单propext/Classical.choice/Quot.sound，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。
