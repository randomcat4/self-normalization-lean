# OQ3-U17d：真实样本远区加权积分的指数衰减

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U17C_FULL_FINAL；未批准/未实现。拟Shao/OQ3/SourceFarWeightedTail.lean。imports Shao.OQ3.FarEnergyExponentialCover、Shao.OQ3.CenteredSampleTilt、Mathlib.MeasureTheory.Integral.Bochner.Set；namespace Shao.OQ3，open MeasureTheory，open scoped BigOperators，noncomputable section。零新公开定义、一个完整公开目标。C目前作者门完成/完整proof审查运行；只有C完整终票lead全文读取接受后派本声明门，批准前不写本源或Lean probe，冻结前置源不改。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，164–237充分energy/binary gap及386–391实际负层远区控制。这里消费充分标量energy试验路线来证明真实mu样本加权集合积分；不声称一般KL/RN/DPI、任意rho的唯一全局最小、Legendre最优或完整层(19)。

```lean
theorem exists_source_far_weighted_tail_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H ell delta : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hgap : ell * q < 7 / 200) (hdelta : 0 < delta)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 0 < n →
      Integrable (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z))
        (Measure.pi (fun _ : Fin n => mu)) ∧
      (∫ z : Shao.Path n in {z | z ∈ sourceTail q n ∧
          normalDeviation q z ≤ -delta * (n : ℝ)},
        Real.exp (-ell * normalDeviation q z)
        ∂Measure.pi (fun _ : Fin n => mu)) ≤ C * Real.exp (-c * (n : ℝ))
```

mu真概率、hb真AE固定界、同mu真实二阶矩q和AE平方支持；q/H/ell/delta与C完整接口相同。C>0/c>0在全部n之前，结论全自然n≥1，不要求eventual n。不含EX=q/4或EY=q假设，因为这里实际energy MGF和确定性样本曲边下界不需要它们；H1的中心qa允许任意实。后续与I/J局部负层接合仍必须满足它们真实均值/方差/有限stage等门，本目标不改变旧类型。ell0、energy端点和空far事件保留，n0明确不声称归一化几何。

审查先完整type独立翻译，之后再读以下可行性路线。C先于所有n给同c>0和有限T，每个t的actual exp真可积/单点Zt>0。取Cconst=(T.card:ℝ)+1>0，允许T空。每个坐标先Measure.tendsto_eval_ae_ae，再ae_all_iff把真实AE energy区间提升到每个n的真实产品AE全Fin坐标；不能将AE坐标门未经证明写成所有路径。

对n>0，记N=(n:ℝ)>0，E=energy z，M=normalDeviation q z，R=sourceEnergyRatio。产品AE能量门上若z属于实际far集合，B给R∈Kfar、R>0/R≠1及M≥−Nq(R−1)²。C有限cover给某个固定集合内t∈T满足N*c+N*ell*q(R−1)² < t*(E−Nq)−N*logZt；使用真实NqR²=E（证明可在B正q/n的实际定义下再合法推出，不能调用不可见private当公开API）。ell≥0下−ell*M≤N*ell*q(R−1)²，故实际weight exp(−ellM)≤exp(−cN)*density_t(z)，density_t=exp(t(E−Nq)−NlogZt)>0。

不能把逐z选择的t当成单个tilt law后直接积分。必须对每个真实样本将weight支配于**所有固定有限T的正density之和**。每个t的真实积分来自已接受H1 `iid_centeredSample_tilt`：在(q,a=q/4,v=−t,s=8t)真实单点projection=t(x²−q)、sampleProjection=t(E−Nq)，需显式环/有限和identity。该接口给真sampleexp Integrable和积分=Zt^n。C给Zt>0之后才能exp(nlogZt)=Zt^n，density_t真Integrable且全空间积分恰1；n虽正但正常化不得除以零Zt。对t0/负t均不改变这些门。

原weight的真实全空间Integrable由H1在(q,a=q/4,v=−ell,s=0)消费，sampleProjection=−ell*M必须精确证明。先真可积再restrict；不能利用Bochner不可积时积分总化成0使目标看似成立。有限density和真可积、点态非负，actual有限和积分为(T.card:ℝ)。真实far集合由sourceTail_measurable与M连续的闭不等式交给可测性，AE restrict成员和坐标门都应显式转移。积分比较后其受限集合积分≤全积分cardT，得≤cardT*exp(−cN)≤(cardT+1)*exp(−cN)。实际库setIntegral_le_integral/mono_ae_restrict需各自真实Integrable/AE非负条件，必须逐一满足，不能只写形式积分恒等式。

该单元完整proof若审过才可记真实far weighted概率机制的这一充分producer；它还不是每个负层的全17或负层真Summable/完整19。一般KL/唯一全局鞍点仍独立OPEN，真实finite-layer LLT/conditional Levy、单侧rotation、cuspEM/hW和四根亦OPEN。固定p/q/eps/P先于r/J/n，beta<2/5只充分修复，无最优或新颖性主张。

资源：新作者Lean/检查CPU14–17，本线一heavy，Lean原生-M8192-j4；禁止ulimit-v/改心跳或证明语义，不干预用户CPU0–9独立10核80GiB任务/全局cgroup。审查仅只读noLean/probe/rebuild/cachewrite/spawn。完整actualtype/source/proof语义优先，最后hash/pins/cache；标准transitive axioms propext/Classical.choice/Quot.sound，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。
