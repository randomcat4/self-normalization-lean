# OQ3-U17g：原有限stage源参数的实际负层尾

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U17F_COMPLETE_FINAL_IF_LEVY_CACHE_MISSING；未批准/未实施。拟 Shao/OQ3/StageSourceNegativeTail.lean，唯一import Shao.OQ3.NegativeLayerGeometricTail；namespace Shao.OQ3/open MeasureTheory Filter/open scoped BigOperators/noncomputable section。零公开定义、一个完整公开目标。F完整proof审中；必须lead全文读取其完整final后才能派本声明门，批准前不写本源/Leanprobe。更高优先级U18a真实conditionalLevy若root依赖就绪则先进入；若仍缺则本模块继续实际原模型承重工作，不等待cache或加无直接消费者包装。

原始目标→R1(17)378–391及R1(19)421–429固定源有限模型负层支配/截断；source current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。剩余关键义务→E/F显式充分门H/energy/hb/S/det/ellgap还未从原stage模型真证明后实际消费。本模块消除→在真实sourceEll及stage范围/正原子/两均值和q范围下，真正推出全部这些门并产实际未截断负层可和/统一尾界。直接消费者→原固定有限模型层求和19的负层截断；未完成→finite-layer conditionalLevy/移动阈值/sign尾、双侧phase/零层枚举和全19、generalKL/cuspEM/rotation/hW/全部根。它不能仅重述F或把缺门当隐含假设。

```lean
theorem exists_stage_source_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          negativeNormalLayerTerm mu q sourceEll (dyadicMesh J) theta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          negativeNormalLayerTerm mu q sourceEll (dyadicMesh J) theta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J))
```

独立审查先完整type盲译持久化，再正文/来源/actual库API，机械最后。q/mu/J固定、sourceEll是真实log(31/30)，没有H/energy/hb/S/det/ellgap作为新type假设；这些须在同mu真证明，不删或修改F已有任何完整前提。gamma/C/N仍先于全部theta/K/k，零层和phase接口与F真实定义相同。

实际stageAtom的inl i/inr j映同fixedAtom(inl i)/(inr j.val)；公开fixedAtom_bounds给1<=absX<=4+sqrt10，提升mu-AE全pair。选H0=25+8sqrt10，实际sqrt10非负且平方10给50<H0<51以及(4+sqrt10)^2=1+H0。AE lowerabs>=1及upperabs<=B真平方给1<=X²<=1+H0；不可从一般hb凭空推出lowerenergy。

stage正原子inl给实际base点正质量；公开normalVariance_pos/parabolaCovariance_det_pos/transverseVariance_pos/transverseVariance_le_variance_id应用同mu/hb/basepos，给S/D/T正与T<=VarX。真bounded连续X/X²可积先由Y=8X-X²、EY=q、EX=q/4推出EX²=q。MemLp.of_bound及AE abs转norm给真正MemLp2，再公开ProbabilityTheory.variance_eq_sub得VarX=q-q²/16；禁止用不可积总化variance或漏平方可积门。

T>0及T<=q-q²/16、q>1真实实代数给1/30<q/(32*T)，正32T先于跨乘（actual atomic_transverse_bounds的原数学使用sq_nonneg(q-1)，但其仅atomicMeasure版本不能直接套任意mu）。公开sourceEll_pos与sourceEll_lt_one_div_thirty给真实sourceEll>=0和严格ellgap；sourceEll决不等于1/30。正q乘ell<1/30再q<103/100给sourceEll*q<103/3000<7/200，严格数值gap真保留。然后完整实参消费F，输出该原源mu实际negativeNormalLayerTerm序列，不另造截断或替代measure。

J0/ell固定/θ0/1/k0/K0全部保留，F原/shift trueSummable与tsum门不重做不削弱。本定理不给q依J或n重选权限：在原p/q/eps/P构造链中该固定q必须先于未来r/J/n选定，旧source family存在性结果继续独立保持，不在此按J另择q。

当前实际所需fixedAtom_bounds、integrable_continuous_of_fixed_bounds、MemLp.of_bound、variance_eq_sub、一般mu covariance比较、sourceEll严格界均在F既有公开imports/现成依赖中；最终必须独立核公开可见性/真实cache，不能凭磁盘源码猜API。新target/Audit仅指定server -DautoImplicit=false、CPU14–17/native-M8192-j4/lane1heavy；无ulimit-v/改心跳语义/动外部CPU0–9/80GiB任务。reviewer只读noLean/probe/rebuild/spawn/cachewrite/raw完整日志下载；仅propext/Classical.choice/Quot.sound三传递公理，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。所有根A/B/C/D开放、beta<2/5只充分修复，无最弱/最优/新颖性主张。
