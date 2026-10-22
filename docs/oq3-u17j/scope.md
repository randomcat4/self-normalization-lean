# OQ3-U17j：实际归一化系数的完整整数层级数极限

冻结v1，DECLARATION_REVIEW_REQUESTED_AFTER_U17I_ENTIRE_FINAL_READ；未批准/未实施。拟Shao/OQ3/StageLayerSeriesLimit.lean；imports Shao.OQ3.StageCurvedLayerLimit、Shao.OQ3.StageSourceNegativeTail、Shao.OQ3.PositiveLayerTail、Shao.OQ3.SampleChangeOfMeasure、Mathlib.MeasureTheory.Integral.DominatedConvergence、Mathlib.Topology.Algebra.InfiniteSum.NatInt；namespace Shao.OQ3/open MeasureTheory Filter/open scoped Topology BigOperators/noncomputable section。1公开DEF及1完整公开目标，单一目标的合取结论不拆作额外节点。I完整405行CORRECT终票lead已全文读；06:38UTC只读复查Levy/Portmanteau和原51项仍缺。正式批准整票全文读前不写源或Lean probe。

原始来源current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，309–348、400–429。原始目标→R1(19)实际有限模型原C_n沿真实phase趋0子列的全整数层极限。剩余关键义务→H真积分表示和I固定层极限尚未在共同正/负尾下合法交换无限和，尚未接回normalizedTailCoefficient与sqrt(2*pi)归一化。本模块消除→真实极限整数族Summable、actual全series极限、零层一次的整数重排与原C_n归一化常数。直接消费者→原finite模型19的概率表达式及后续连续常数/尖点比较。未完成→显式hcont实际生产者U18a、必要Phi等价改写、cuspEM/rotation/hW/generalKL及全部根。

hcont始终是同一actual normalLayerConditionalLaw的显式待接接口，不是已证原模型事实。本单元不能宣称完整15/19或任何根闭合。q/sourceEll/w/J在未来m/n/k外固定，p/q/eps/P先于r/J/n；beta<2/5仅充分修复，无最弱/最优/新颖性主张。

```lean
def sourceGaussianLayerWeight (mu : Measure ℝ) (q ell d : ℝ) : ℝ :=
  Real.exp (-ell * d) *
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))).real
      {x : ℝ | -((q / 16) * d) ≤ x ^ 2}

theorem normalizedTailCoefficient_stage_subsequence_tendsto
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hphase : Tendsto (fun j : ℕ => Int.fract ((m j : ℝ) * q / dyadicMesh J))
      atTop (nhds 0))
    (hcont : ∀ d : ℕ → ℝ,
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
      (∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
        d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) →
      ∀ A : Set ℝ,
        (ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (transverseVariance (atomicMeasure w)))) (frontier A) = 0 →
        Tendsto (fun n : ℕ =>
          (normalLayerConditionalLaw (atomicMeasure w) q (q / 4) (d n) n).real A)
          atTop (nhds ((ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (transverseVariance (atomicMeasure w)))).real A))) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
        (dyadicMesh J * (k : ℝ))) ∧
      Tendsto (fun j : ℕ => normalizedTailCoefficient sourceEll q w (m j))
        atTop (nhds ((dyadicMesh J / Real.sqrt (normalVariance (atomicMeasure w))) *
          ∑' k : ℤ, sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
            (dyadicMesh J * (k : ℝ))))
```

独立门先读完整DEF体及完整TYPE独立盲译并持久化，再读scope解释、真实R1、实际前置/固定库/API/public导入图；依赖hash/pins/cache/机械证据最后。作者future/candidate/implementation notes不可读。1DEF是实际Gaussian事件带权概率；q>0/T>0下正位移对应全空间概率1，负位移对应N(0,T)双侧平方阈值，和原kappa=sqrtq/(4sqrtT)两正态尾一致。正式scope语义审查必须独立检查；这里不冒称Phi/CDF公式已经Lean证明。

hw/hs通过atomicMeasure_isProbabilityMeasure给真概率；真实stage范围和各原子正质量推出一般mu的hb及S/det/T正。hcont对所有全n有界、eventual格层相容的d给同一实际条件律连续集概率极限，正好由U18a目标生产，不偷偷假定每早期层mass正或d全n趋常数。

实际正位移d_n=h(k+1-fract(Nq/h))、非正位移d_n=-h(k+fract(Nq/h))须由floor/fract真证全n有界与格层相容；只有沿m相位趋0。I逐层极限后，必须用G真实负项共同尾及U16b原始正项共同尾控制。H正项含sourceTail、U16b raw正项不含，须以真有限measureReal_mono及非负权重支配，不能说两者相等。原actual/raw及shift族真Summable先于实tsum比较；共同常数和eventualn门保留于theta/K/k之外。

无限和交换须建立真实可和主控及极限可和性，不以实tsum总化0证明Summable。可用现成count-measure DCT：integrable_count_iff、Countable型integral_countable、tendsto_integral_filter_of_dominated_convergence的真实Integrable/可测/eventual界/逐点极限全部门；不能误用仅Fintype的integral_count。也可用真实finite-K部分和加共同尾。早期未界项保持真实概率，不以if截断假装零。

整数重排在真Summable之后；正k0为+h，负k0为0，仅数零一次。最后真实sourceTail_measurable/indicator-setIntegral、normalizedTailCoefficient_eq_tilted及sqrt(2*pi*N)=sqrt(2*pi)*sqrtN接原系数；S>0和pi>0后核sqrt(2*pi)*(h/(2*pi))*sqrt(2*pi/S)=h/sqrtS。T=det/S是方差，不是标准差。

初始只读缓存闭包metadata stage-layer-series-candidate-cache.json：51份Shao/2905份Mathlib源和现成olean齐全。Tannery.olean缺失，不作为本scope导入；不写cache、不编依赖、不换pins。正式独立门仍重新核实际完整依赖和主API公开可达，不能以旧单元成功代替本单元证明。

所有作者Lean仅指定server严格-DautoImplicit=false、CPU14–17/native-M8192-j4/lane1heavy。reviewer只读，不Lean/probe/rebuild/cachewrite/raw全log复制/spawn/commit/source或旧票编辑。禁止ulimit-v/心跳或语义弱化/干预外部CPU0–9的10核80GiB任务；root唯一cachewriter与共享集成owner。传递公理仅propext/Classical.choice/Quot.sound；禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。根A/B/C/D全部OPEN。
