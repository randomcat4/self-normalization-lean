# OQ3-U17i：实际有限层曲边条件因子与带权子列极限

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U17H_COMPLETE_FINAL_IF_LEVY_CACHE_MISSING；未批准/未实施。拟Shao/OQ3/StageCurvedLayerLimit.lean；imports Shao.OQ3.StageLayerDecomposition、Mathlib.Probability.Distributions.Gaussian.Real；namespace Shao.OQ3/open MeasureTheory Filter/open scoped BigOperators/noncomputable section。零公开DEF、两个完整公开目标。H完整301行proof终票lead已全文读取；fresh05:32UTC Levy/Portmanteau及原51项仍缺，不写cache/不等cache停工。批准整票全文读前不写本源/Leanprobe。

原始来源current/oq3/proofs/r1/report.md，SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，309–348与400–429。原始目标→R1(15)/(18)/(19)固定层曲边联合概率。剩余关键义务→真实条件Gaussian连续集概率不能直接应用于随n移动的曲边事件，sumX>0的线性远条件尾也不可删去，actual conditional map/cond仍须恢复原product交事件。本模块消除→actual sourceTail因子恒等式、移动阈值与零交界夹逼、严格正和符号远尾、真实带权固定层子列极限。直接消费者→H实际层和、U16b/G共同tail下原19。未完成→hcont的真实Levy生产者仍U18a缓存等待，完整series limit19/Phi改写/cuspEM/rotation/hW/generalKL及所有根OPEN。

第二目标的hcont是显式待接U18a实际连续集概率门，绝不是原模型新假设或本模块已证事实；接受本模块只消hcont之后的曲边/符号/消归一化义务，不得称15/19闭合。rootcache若及时到位，下一优先U18a，不增加替代Levy公理/公共模型。

```lean
theorem stage_source_layer_conditional_factorization (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q d : ℝ) (hq : 0 < q)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (n : ℕ) (hn : 0 < n)
    (hmass : 0 < (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = d}) :
    (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d ∧ z ∈ sourceTail q n} =
      (Measure.pi (fun _ : Fin n => mu)).real
          {z : Shao.Path n | normalDeviation q z = d} *
        (normalLayerConditionalLaw mu q (q / 4) d n).real
          {x : ℝ | -((q / 16) * d) ≤ x ^ 2 ∧
            -(Real.sqrt (n : ℝ) * q / 4) < x}

theorem stage_source_weighted_layer_subsequence_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ) (hq : 0 < q)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (d0 : ℝ)
    (hd0 : Tendsto (fun j : ℕ => d (m j)) atTop (nhds d0))
    (hcont : ∀ A : Set ℝ,
      (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu)))
          (frontier A) = 0 →
      Tendsto (fun n : ℕ => (normalLayerConditionalLaw mu q (q / 4) (d n) n).real A)
        atTop (nhds ((ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (transverseVariance mu))).real A))) :
    Tendsto (fun j : ℕ => Real.sqrt (m j : ℝ) * Real.exp (-ell * d (m j)) *
        (Measure.pi (fun _ : Fin (m j) => mu)).real
          {z : Shao.Path (m j) | normalDeviation q z = d (m j) ∧
            z ∈ sourceTail q (m j)})
      atTop (nhds (((dyadicMesh J / (2 * Real.pi)) *
          Real.sqrt (2 * Real.pi / normalVariance mu)) * Real.exp (-ell * d0) *
        (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))).real
          {x : ℝ | -((q / 16) * d0) ≤ x ^ 2}))
```

独立门先两个完整TYPE盲译并持久化，再此scope/真实R1/实际库和完整导入可达语义，机械最后；没有公开DEF。作者future/candidate/implementation notes不可读。当前本源不存在。所有实际前提必须逐项保留；d全n有界和最终实际格层门给真实s0层质量极限，不能假定d全n收敛。仅d(m j)沿m→∞趋d0，正好覆盖原phase子列，q/ell不按J/n重选。

第一目标n>0/q>0，stage productAE给energy>=n>0；真实层上sourceTail_on_normal_layer再在sqrtN>0、sq_sqrt后得到准确x=R/sqrtN的曲边阈值和严格正和阈值。normalLayerConditionalLaw零质量分支只能在真实hmass给actualENNReal非零后消。实际统计量/目标集合可测先于map_apply；实际cond_mul_eq_inter+toReal_mul及AE事件相等先于原real交质量恒等式，不以总化除法偷换。

第二目标先由stage双界/正基点推出一般mu hb/S/det/T>0，消费U13c实际最终层mass正及s0真实scaled层质量极限；不用atomic-only公式或未经证明条件矩。hcont须用于同一实际normalLayerConditionalLaw和实际Gaussian(0,Real.toNNReal T)，再comp hm得到子列门。

移动阈值a_j=-(q/16)d(mj)趋a0。固定square-threshold事件frontier包含{x²=a}，真实T>0先于gaussianReal的NullSingletonClass，有限至多±sqrt a边界零质量包含a0=0。必须先固定a0±epsilon的连续集合夹逼，再用真有限Gaussian的测度单调连续性令epsilon趋0，不能直接把移动事件代入hcont。严格正和只剔除x<=-sqrt(mj)*q/4；先以固定Iic(-K)支配、hcont取概率极限、再K→∞真实有限Gaussian尾质量趋0。禁止未证条件独立/Chebyshev/二阶或指数矩替代。最后第一目标实际乘法因子、sqrtN层质量极限和exp(-ell*d(mj))极限给声明常数。ell任意实在固定有界层合法，共同tail仍由U16b/G另供。

初始只读API依据：SampleBoundary81–86真实layer曲边、NormalLayerConditionalLaw12–18真实dirac/cond-map和103–138最终正质量、140–196真正char极限；ConditionalProbability255–263 cond_mul_eq_inter只要求可测层和finite measure；Map170–173 map_apply要求统计量/集合可测；Gaussian.Real233–236 nullSingletonClass_gaussianReal要求非零NNReal方差；Topology/Order/OrderClosed648–653 frontier_le_subset_eq要求两Continuous；Measure/Continuity198–203/220–229单调union/inter的ENNReal极限（inter另要null可测/一项有限）；ENNReal.tendsto_toReal有限limit门独立满足。这些只作初始source索引，独立门须核实际完整类型/public导入，不照抄作者主张。

05:28UTC候选双imports真实闭包含45Shao(含H)/2905Mathlib；源/现成olean无缺，metadata curved-layer-candidate-cache.json；仅静态只读，无Lean/probe/cache写入。正式声明门须重新独立核scopehash/pins、真实目标名无冲突及主API public可达，不能以H已过编译代替本单元实现审查。

新作者target/Audit只指定server严格-DautoImplicit=false，CPU14–17/native-M8192-j4/lane1heavy，禁止ulimit-v/心跳或数学语义弱化/干预外部0–9的10核80GiB任务。唯一reviewer只读，不Lean/probe/rebuild/cachewrite/raw全log复制/spawn/source或旧票编辑/commit。标准传递公理仅propext/Classical.choice/Quot.sound，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。完整19/Levy/hW/generalKL和根ABCD仍OPEN；beta<2/5仅充分修复，无最弱/最优/新颖性主张。
