# U18a frozen declaration v3 — actual named weak-topology carrier

V3 changes only the first target's `nhds` application to explicitly supply the fixed API carrier `(X := ProbabilityMeasure ℝ)`. Compared with frozen v2's complete Lean fence, the sole character-level TYPE change is carrier binder name `α` to `X`. Compared with v1, the sole TYPE change is that explicit carrier argument. All four imports, both full mathematical statements/quantifiers/hypotheses/conclusions, zero public definitions and two public targets remain unchanged.

V1 scope6c2f3114 and whole154line CORRECT mathematical/API statement final3e1b61d8 remain immutable; its three actual complete source attempts all failed to infer TopologicalSpace of the anonymous probability subtype, and attempt01 also failed implicit frontier coercion. Retained logs corrected the author console-filter omission of coded errors. Targeted actual standard-topology API diagnostic exit0 was justified by those failures and is not a repeated root import smoke; no target object/Audit/accepted proof/commit/PR exists.

V2 scope2a7bdee5 and entire121line16324B INCORRECT final6c800d9d have been read in full and preserved. Actual fixed Topology/Defs/Filter.lean122 has `variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]`, and131 has `irreducible_def nhds (x : X) : Filter X`; source SHA700acc36eb3f275a42212da01f1c35b01010cef40b30300b9623e382e8146891. Actual IrreducibleDef generator preserves that binder, as independently reviewed. Thus v2's habitual `α` was invalid; this v3 uses actual `X`. No v2 source/probe was written/run, no old scope/review is edited.

The explicit carrier selects the existing standard ProbabilityMeasure weak topology, not a new or local instance/definition/topology/assumption/proof setting. Review first extracts both complete types and persists focused blind translation, then exact v2/v3 difference and actual nhds/weak topology/API, mechanical last. Reuse stable import-graph/root51 evidence without repeating successful scans or smoke; final source elaboration remains author's responsibility after complete independent CORRECT final lead-read. No v3 source/probe until that gate. All original obligations and OQ3 roots OPEN. Historical v1 body below is retained except this single explicit carrier insertion in its fence.

---

# OQ3-U18a：真实条件法向层的Lévy弱收敛与连续集概率

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U17F_COMPLETE_FINAL_AND_ROOT_CACHE；未批准/未实施。拟 Shao/OQ3/NormalLayerWeakConvergence.lean；imports Shao.OQ3.NormalLayerConditionalLaw、Mathlib.MeasureTheory.Measure.LevyConvergence、Mathlib.MeasureTheory.Measure.Portmanteau、Mathlib.Probability.Distributions.Gaussian.Real；namespace Shao.OQ3，open MeasureTheory Filter，open scoped Topology BigOperators，noncomputable section。零公开定义、两个完整公开目标。只有前序完整final全文读取，且root固定Levy/Portmanteau依赖就绪后才派声明门；批准前不写源/Leanprobe，lane不写cache或重编依赖。

原始目标→R1(15),309–348混合LLT（仅Y格点Fourier）；来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。剩余关键义务→U13c已审真实条件概率/Gaussian char极限尚未转成真正弱收敛/连续集概率。本模块消除→对同实际有限stage概率族的条件Lévy桥及真real连续集概率。直接消费者→固定法向层sourceTail曲边概率与远切向sign尾排除，再供R1(19)有限层极限；未完成→moving阈值/真实sign-tail、双侧phase/零层索引和正负支配层和19、cuspEM/rotation/hW/generalKL/全部根，均OPEN。

```lean
theorem stage_normalLayerConditionalLaw_weak_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    Tendsto (fun n : ℕ =>
      (⟨normalLayerConditionalLaw mu q a (d n) n,
        normalLayerConditionalLaw_isProbabilityMeasure mu q a (d n) n⟩ : ProbabilityMeasure ℝ))
      atTop (nhds (X := ProbabilityMeasure ℝ)
        (⟨ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu)),
          by infer_instance⟩ : ProbabilityMeasure ℝ))

theorem stage_normalLayerConditionalLaw_real_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ))
    (A : Set ℝ)
    (hfrontier : ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))
      (frontier A) = 0) :
    Tendsto (fun n : ℕ => (normalLayerConditionalLaw mu q a (d n) n).real A)
      atTop (nhds ((ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (transverseVariance mu))).real A))
```

独立审查必须先只读两个完整type盲译并持久化，再scope/R1/actual U13c/原库语义/API，机械最后。保留U13c同mu/J/q/a、hb、真实EX/EY、S/det正、AE stage范围/每实际原子正质量、全n有界d及eventual真实层相容；不将实d函数偷偷改成定值或漏相位。没有新增hsecond/energy/ell假设；本模块是mixedLLT条件law，不消费E/F指数率。d不必趋常数，因为U13c charlimit对全部有界相容d已给Gaussian极限。

真实ProbabilityMeasure subtype直接匿名封装normalLayerConditionalLaw及已审全n概率证明，不另加无消费者wrapper定义。零原层时其dirac0 fallback保留；晚期实际层质量正已由U13c保证，不额外假定每早期层非零。目标Gaussian确为gaussianReal0(T.toNNReal)，T=det/normalVariance由显式正hD/hS真正正；必须在Real.coe_toNNReal系数转换前证明T≥0，不能用toNNReal掩负variance。actual gaussianReal:Real.lean220定义、229真概率实例、481 charFun接口，Gaussian.Real现成cache已存在，无需Gaussian.CharFun额外模块。

固定实际LevyConvergence:201–203 ProbabilityMeasure.tendsto_of_tendsto_charFun对实有限维inner-product概率序列，消费U13c对每实s的实际charFun趋Gaussian charFun。第二目标对真实Gaussian(frontier A)=0，消费Portmanteau:334–341 prime版本的实际ENNReal测度收敛；无prime351版本apply值是NNReal，不冒称其直接给real。再用目标真概率measure_ne_top及ENNReal.tendsto_toReal（Topology/Instances/ENNReal/Lemmas:102）组成real质量收敛，避免∞总化。库prime版本不需额外MeasurableSet A假设，null frontier与目标概率/实拓扑提供接口全部门，不擅加局部n/非零层/有界测试族代替真实集合概率。

编译前置最后实测LevyConvergence.olean/Portmanteau.olean缺，source存在；请求已在coordination/inbox/oq3-requests.md，由root唯一cacheowner补固定依赖闭包。不得lane下载/重建cache/换pins/拷公共源/rebase。cache未就绪不派最终声明批准、不写源或probe；继续其他直接原始承重工作而非以缺cache结束任务。该静态候选冻结不计接受或已完成LLT。

所有新作者target/Audit须指定server -DautoImplicit=false、CPU14–17/native-M8192-j4、lane1heavy。禁止ulimit-v/改心跳语义/干预外部CPU0–9的10核/80GiB任务；reviewer只读noLean/probe/rebuild/spawn/cachewrite/raw完整日志下载，传递白名单仅propext/Classical.choice/Quot.sound，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。p/q/eps/P固定先于r/J/n，beta<2/5仅充分修复，无最弱/最优/新颖性主张；root A/B/C/D全部OPEN。
