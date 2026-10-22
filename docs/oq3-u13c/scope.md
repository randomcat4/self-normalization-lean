# OQ3-U13c：真实条件层概率与特征函数（冻结v1声明候选）

冻结v1，DECLARATION_REVIEW_QUEUED；尚无声明批准、尚无实现，不计已接受节点。拟NormalLayerConditionalLaw.lean，导入Shao.OQ3.FundamentalFourierAsymptotic、Mathlib.Probability.ConditionalProbability、Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic；namespace Shao.OQ3，open MeasureTheory Filter，open scoped BigOperators Matrix，noncomputable section。

源R1 report.md309–345的条件特征函数步骤。目标先把未归一化层积分变成真正概率：零层质量时显式dirac0补定义，正层质量时才用actual cond限制归一化再推送切向统计量。补定义仅处理有限前项；正层质量eventually成立后就是源真实条件律。不调用尚缺失cache的LevyConvergence；弱收敛、连续集概率与完整(15)仍待后续。

```lean
def normalLayerConditionalLaw (mu : Measure ℝ) (q a d : ℝ) (n : ℕ) : Measure ℝ :=
  if (Measure.pi (fun _ : Fin n => mu)) {z : Shao.Path n | normalDeviation q z = d} = 0 then
    Measure.dirac 0
  else
    Measure.map (fun z : Shao.Path n => ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ))
      (ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => mu))
        {z : Shao.Path n | normalDeviation q z = d})

theorem normalLayerCharacteristic_zero_eq_mass (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a d : ℝ) (n : ℕ) :
    normalLayerCharacteristic mu q a d 0 n =
      ((((Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d}) : ℝ) : ℂ)

theorem normalLayerConditionalLaw_isProbabilityMeasure (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (q a d : ℝ) (n : ℕ) :
    IsProbabilityMeasure (normalLayerConditionalLaw mu q a d n)

theorem charFun_normalLayerConditionalLaw (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a d : ℝ) (n : ℕ)
    (hpos : (Measure.pi (fun _ : Fin n => mu))
      {z : Shao.Path n | normalDeviation q z = d} ≠ 0) (s : ℝ) :
    charFun (normalLayerConditionalLaw mu q a d n) s =
      normalLayerCharacteristic mu q a d s n / normalLayerCharacteristic mu q a d 0 n

theorem eventually_stage_normalLayer_mass_pos (mu : Measure ℝ)
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
    ∀ᶠ n : ℕ in atTop, 0 < (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = d n}

theorem stage_normalLayerConditionalLaw_charFun_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (s : ℝ) (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    Tendsto (fun n : ℕ => charFun (normalLayerConditionalLaw mu q a (d n) n) s)
      atTop (nhds (Complex.exp ((-(transverseVariance mu * s ^ 2) / 2 : ℝ) : ℂ)))
```

一个冻结公开定义体与五个完整公开目标签名。首目标由可测层和s0指数1给真实层概率的复嵌入；每个产品measure为概率，层质量有限，真可积由U13a提供。第二目标分零质量dirac与非零质量actual cond两支，后者需真正有限非零层质量、可测层和可测切向统计量，才能给真概率及其推送概率；n0按总化除法但推送仍可测。

第三目标只在真实层质量非零时展开cond，先立真实相位在原产品概率/限制measure/cond下的可积，再用实际积分推送和标量measure积分。ENNReal倒数toReal与真实正质量的倒数严格核对；以首目标识别复分母，不能从总化复除法猜正质量，也不能把normalized restriction与原未归一化层积分混同。

第四目标用U13b的s0缩放层极限，其系数h/(2pi)*sqrt(2pi/S)>0。取真实复数实部得sqrt n乘层质量的实极限，最终严格正且sqrt n≥0，推出实际层概率严格正。层相容仅最终；没有声称全部n层可达，不把格点相容直接视为正层质量。

第五目标同时用s与0两个缩放层极限，分母极限严格非零；在n≥1及真实层概率最终正后，同一sqrt n因子在实际复比值中消去。第三目标将其识别为actual conditional charFun，常数比化为exp(−tauSquared*s²/2)。所有对象始终同一mu/J/q/a/d；零质量dirac补定义在尾部不再触发，且正性定理不依赖s。这里只得概率特征函数收敛，不能据此省略Levy而记弱收敛或完整混合LLT。

静态已知ConditionalProbability.olean与CharacteristicFunction.Basic.olean均有缓存，ProbabilityTheory.cond是(μA)⁻¹乘真实restrict；charFun_apply_real以exp(t*x*I)积分。固定库cond_isProbabilityMeasure153–164和integral_smul_measure1047–1048已静态读核；待U13b完整最终报告由lead全文读取后再由同一reviewer独立声明审查，批准前不实施。根A/B/C/D OPEN；无实际hW或对角闭合主张。
