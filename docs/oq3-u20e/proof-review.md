# U20e v2 SourceSmoothMeanMap 完整独立证明审查

STATUS: IN_PROGRESS

唯一reviewer lease1；仅拥有本新报告及授权remote报告。先仅读actual公开完整TYPE及全部21owner TYPE，逐义盲译并持久化，再读完整proof／原库／机械证据。已有声明票与作者成功说明不代替新证明审查；旧v1／v2票不改。

## Actual公开完整TYPE（实际源截取，不含proof）

```lean
theorem source_log_partition_and_tilted_mean_smooth
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    let P : Measure ℝ := originalMeasure sourceEll w
    let Z : (Fin 2 → ℝ) → ℝ := fun theta =>
      ∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P
    let K : (Fin 2 → ℝ) → ℝ := fun theta => Real.log (Z theta)
    let tilt : (Fin 2 → ℝ) → Measure ℝ := fun theta =>
      P.tilted (fun x => theta 0 * x + theta 1 * x ^ 2)
    let mean : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun theta =>
      ![∫ x : ℝ, x ∂tilt theta, ∫ x : ℝ, x ^ 2 ∂tilt theta]
    let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
    IsProbabilityMeasure P ∧
      (∀ theta : Fin 2 → ℝ,
        Integrable (fun x : ℝ => Real.exp (theta 0 * x + theta 1 * x ^ 2)) P ∧
        0 < Z theta ∧ IsProbabilityMeasure (tilt theta) ∧
        Integrable (fun x : ℝ => x) (tilt theta) ∧
        Integrable (fun x : ℝ => x ^ 2) (tilt theta)) ∧
      ContDiff ℝ ∞ K ∧ ContDiff ℝ ∞ mean ∧
      ∀ theta : Fin 2 → ℝ,
        HasFDerivAt K
          ((pr 0).smulRight (mean theta 0) + (pr 1).smulRight (mean theta 1)) theta
```

## 全部actual owner TYPE（所有续行）

```text
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.momentSlope.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ),
  Shao.OQ3.momentSlope✝ mu k theta =
    Shao.OQ3.weightedMoment✝ mu (k + 1) theta • Shao.OQ3.coordinate✝ 0 +
      Shao.OQ3.weightedMoment✝ mu (k + 2) theta • Shao.OQ3.coordinate✝ 1
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.normalizedMoment.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ),
  Shao.OQ3.normalizedMoment✝ mu k theta = Shao.OQ3.weightedMoment✝ mu k theta / Shao.OQ3.weightedMoment✝ mu 0 theta
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.weightedMoment_hasFDerivAt
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (k : ℕ) (theta : Fin 2 → ℝ), HasFDerivAt (Shao.OQ3.weightedMoment✝ mu k) (Shao.OQ3.momentSlope✝ mu k theta) theta
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.logPartition_hasFDerivAt
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (theta : Fin 2 → ℝ),
      HasFDerivAt (fun t => Real.log (Shao.OQ3.weightedMoment✝ mu 0 t)) (Shao.OQ3.partitionGradient✝ mu theta) theta
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.normalizedMoment_tilt
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ),
  Shao.OQ3.normalizedMoment✝ mu k theta = ∫ (x : ℝ), x ^ k ∂mu.tilted fun x => theta 0 * x + theta 1 * x ^ 2
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.weightedMoment.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ),
  Shao.OQ3.weightedMoment✝ mu k theta = ∫ (x : ℝ), x ^ k * Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂mu
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.weightedMoment._proof_1
TYPE NeZero (1 + 1)
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.weighted_integrable
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (k : ℕ) (theta : Fin 2 → ℝ),
      MeasureTheory.Integrable (fun x => x ^ k * Real.exp (theta 0 * x + theta 1 * x ^ 2)) mu
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.momentSlope._proof_1
TYPE ContinuousAdd ℝ
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.momentSlope._proof_2
TYPE SMulCommClass ℝ ℝ ℝ
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.weightedMoment_contDiff
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) → ∀ (k : ℕ), ContDiff ℝ (↑⊤) (Shao.OQ3.weightedMoment✝ mu k)
DECL Shao.OQ3.source_log_partition_and_tilted_mean_smooth
TYPE ∀ (w : Shao.OQ3.AtomicIndex → ℝ),
  (∀ (i : Shao.OQ3.AtomicIndex), 0 ≤ w i) →
    HasSum w 1 →
      have P := Shao.OQ3.originalMeasure Shao.OQ3.sourceEll w;
      have Z := fun theta => ∫ (x : ℝ), Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P;
      have K := fun theta => Real.log (Z theta);
      have tilt := fun theta => P.tilted fun x => theta 0 * x + theta 1 * x ^ 2;
      have mean := fun theta => ![∫ (x : ℝ), x ∂tilt theta, ∫ (x : ℝ), x ^ 2 ∂tilt theta];
      have pr := fun i => ContinuousLinearMap.proj i;
      MeasureTheory.IsProbabilityMeasure P ∧
        (∀ (theta : Fin 2 → ℝ),
            MeasureTheory.Integrable (fun x => Real.exp (theta 0 * x + theta 1 * x ^ 2)) P ∧
              0 < Z theta ∧
                MeasureTheory.IsProbabilityMeasure (tilt theta) ∧
                  MeasureTheory.Integrable (fun x => x) (tilt theta) ∧
                    MeasureTheory.Integrable (fun x => x ^ 2) (tilt theta)) ∧
          ContDiff ℝ (↑⊤) K ∧
            ContDiff ℝ (↑⊤) mean ∧
              ∀ (theta : Fin 2 → ℝ),
                HasFDerivAt K ((pr 0).smulRight (mean theta 0) + (pr 1).smulRight (mean theta 1)) theta
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.normalizedMoment
TYPE MeasureTheory.Measure ℝ → ℕ → (Fin 2 → ℝ) → ℝ
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.momentSlope
TYPE MeasureTheory.Measure ℝ → ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.momentSlope._proof_3
TYPE ContinuousConstSMul ℝ ℝ
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.partition_pos
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) → ∀ (theta : Fin 2 → ℝ), 0 < Shao.OQ3.weightedMoment✝ mu 0 theta
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.coordinate
TYPE Fin 2 → (Fin 2 → ℝ) →L[ℝ] ℝ
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.coordinate.eq_1
TYPE ∀ (i : Fin 2), Shao.OQ3.coordinate✝ i = ContinuousLinearMap.proj i
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.partitionGradient
TYPE MeasureTheory.Measure ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.weightedMoment
TYPE MeasureTheory.Measure ℝ → ℕ → (Fin 2 → ℝ) → ℝ
DECL _private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.partitionGradient.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (theta : Fin 2 → ℝ),
  Shao.OQ3.partitionGradient✝ mu theta =
    Shao.OQ3.normalizedMoment✝ mu 1 theta • Shao.OQ3.coordinate✝ 0 +
      Shao.OQ3.normalizedMoment✝ mu 2 theta • Shao.OQ3.coordinate✝ 1
```

## 独立翻译及先行疑点

1. 唯一公开定理只输入同一w的非负性和真实HasSum w 1，没有q／完整四矩／正原子／caller概率或光滑性前提。
2. P为同w的originalMeasure sourceEll w，Z是其真实二次指数配分，K是literal log Z，tilt为同P实际二次倾斜。
3. mean为各实际tilt下X和X²两个真积分组成的Fin2向量，不能换未绑定归一化代理；pr是真CLM投影。
4. 结论先给P真概率，对全部实theta给exp真Integrable／Z严格正／实际tilt真概率／X及X²真Integrable。
5. 后给K与actual mean的C∞，最后对每个theta给真Fréchet梯度等于actual mean的两投影组合。
6. actual TYPE显示ContDiff ℝ (↑⊤)，需要与source显式ContDiff的内ENatTop核对，不能误作外层ω解析性。
7. 所有theta包括0／任意大参数，权w允许部分0和退化law；不能加非退化Hessian／均值inverse输入。
8. private coordinate类型为Fin2->CLM，预期对应坐标投影；需后读完整body确认。
9. private weightedMoment类型为mu,k,theta到实数，eq_1实际给∫x^k exp(theta0*x+theta1*x²)dmu，是总化定义但分析定理必须有真实可积门。
10. private momentSlope类型为mu,k,theta到CLM，eq_1给M_(k+1)*coordinate0+M_(k+2)*coordinate1；所有索引／阶数须真匹配参数求导。
11. private normalizedMoment为M_k/M0，eq_1无概率或M0非零前提；不能靠总化分母制造实际均值／光滑。
12. private partitionGradient类型为mu,theta到CLM，eq_1给normalizedMoment1、2的两坐标组合。
13. 五private DEF均需读全body，而非只据这些函数签名猜含义；五eq_1逐项核。
14. weighted_integrable在任意真概率mu和AE |x|<=4+sqrt10下，对全部k／theta给真实指数加权矩Integrable。
15. partition_pos有同概率／AE界门，给所有theta M0>0；不能在log／inverse后才补此门。
16. weightedMoment_hasFDerivAt有同概率／AE界门，对所有k／theta给真实全Fréchet导数momentSlope。
17. 该proof需共同紧参数窗的真实operator norm主控，AE样本之后forall参数，不得逐参数临选常数。
18. F／F'可测、中心F真Integrable、可积主控和AE全窗点态导数必须全真实产生后用parametric integral API。
19. weightedMoment_contDiff有同概率／AE界门，对全部k给C∞；须所有k同时对自然n归纳，IH用于k+1／k+2而无循环。
20. normalizedMoment_tilt没有任何caller概率／可积门，给M_k/M0等于真实tilted积分；即使原库总化公式使该无条件等式真，也不能把它当作公开概率／可积生产者。
21. logPartition_hasFDerivAt在真概率／AE界下给所有theta的literal log M0导数，需M0非零先于log链式／inverse系数化简。
22. 六authored private theorem各自门均应在public由实际P/hw/hs消去，不能只停在泛型mu。
23. generated NeZero(1+1)是数值索引门，需核其实际域／类型；不能误列为新的OQ3假设。
24. generated ContinuousAdd ℝ、SMulCommClass ℝ ℝ ℝ、ContinuousConstSMul ℝ ℝ是标准实结构证明，不应隐藏额外law／光滑假设。
25. 其余五generated是上述五DEF的eq_1；actual21=5DEF+6privateTHM+1publicTHM+9generated，仍需owner Audit实际枚举核实。
26. weightedMoment0=Z必须是全参数函数身份；hmean也必须是整个actual mean函数身份，才能迁移K／mean的C∞和真实梯度。
27. 公开必须先真P概率／exp可积／Z正／tilt概率，再真实继承AE界生产tilt下X/X²可积，不能由无条件积分等式绕过。
28. 最后CLM smulRight的坐标次序及scalar乘法需与M1/Z、M2/Z一致，不漏因子／交换X与X²。
29. 必须本module局部重证所有k求导；旧PR151私有名字不可跨模块调用，已有点态一二阶也不推出全阶。
30. 这是全参数C∞／真实mean的生产者，不是局部逆／全族谱界／一般无界根B或其他根关闭。
31. 后续先全237行proof与每个local／所有TYPE值，再receipt／history／formal5／git机械绑定；不预报kernel或最终CORRECT。

--- END IMMUTABLE BLIND PREFIX ---

## 完整独立证明终票（v2实现）

STATUS: CORRECT

JUSTIFICATION: 全237行真实源码、全部5个private DEF body、6个authored private证明及21个actual owner完整TYPE已审。共同紧参数球主控后真实积分求导、所有k同时自然阶归纳、内ENatTop的C∞、正Z后的log／div、实际tilt均值全函数身份及全theta真实梯度均成立；公开概率与可积性由独立真实门生产，未以总化积分身份绕过。机械历史与同一冻结source／scope／formal5／owner公理完整绑定，未发现关键缺口。本票只接受本光滑生产者，不宣称均值inverse／谱统一／任何原根因此关闭。

不可改写盲前缀152行／11473B，SHA256 `869004038ad5ac4467d92c71d453a880e88ce5b2d6ec263850ede0dc76ce8cbd`。先读actual完整public TYPE和全部21实际所属TYPE并持久化，再读proof／实际库，receipt最后。下文仅追加，初始IN_PROGRESS保留为历史检查点。

### 1. 精确实现与来源范围

SourceSmoothMeanMap.lean完整237行已读：1–17 imports／显式ContDiff header，19–35五private DEF，37–145六private theorem，147–167完整public TYPE，168–234主proof，236–237尾部。实际public TYPE及四imports与冻结v2两Lean fences逐字一致；不是新增q／四矩／正基点／caller光滑性版本。

本源对应R1 137–159的同原逆倾斜P及有界支撑、R2 38–60的W=(X,X²)、真实K／tilt／m=gradient，和root-contract对真配分域的门。R1 SHA `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`；R2 SHA `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。

仅质量条件的w仍给同一有界概率P，足以做全部参数正则性；没有四矩时不声称P中心化、指定q鞍点／正率。R2的均值局部逆及统一谱／矩条件是后续消费者，不能由本C∞输出自动计入完成。

16行显式`open scoped ... ContDiff`，故164及111的∞是FTaylorSeries.lean120定义的内ENatTop嵌入。actual TYPE也显示`ContDiff ℝ (↑⊤)`；它不是外层ω解析性。旧v1 scope及CRITICAL票未被倒改，v1未实施；这两次source尝试均是v2批准后的实现。

### 2. 五个private DEF完整body：19–35

- coordinate 19–20精确为ContinuousLinearMap.proj，domain是同Fin2实参数空间。
- weightedMoment 22–23精确为同mu的∫x^k*exp(theta0*x+theta1*x²)，没有归一化／中心化／自由替代积分。
- momentSlope 25–28精确为M_(k+1) • coordinate0 + M_(k+2) • coordinate1，是CLM值而非两个形式偏导。
- normalizedMoment 30–31精确为M_k/M0。此定义对任意mu总化，分析结论必须另有真实M0>0／可积门。
- partitionGradient 33–35精确为normalizedMoment1／2的两投影组合，坐标保持(X,X²)。

五DEF都是本模块private，实际owner与源body相符；没有公开竞争性canonical K定义，也没有调用PR151私有weightedMoment／momentSlope等符号。所有后续同名私有helper均在本模块重新证明。

### 3. 真加权可积／正配分：37–47

37–41在任意真实概率mu、同mu AE |x|≤B=4+sqrt10下，用公开`integrable_continuous_of_fixed_bounds mu hb`和实际连续性证明，给每个自然k、全部实theta的真实加权指数矩Integrable。x^k为自然幂，实指数、乘法均连续；无全局参数紧性或样本有限支持假设。

43–47取k=0，先由上述真可积化为exp可积，后用`integral_exp_pos`和概率非零给M0>0。不是以Lean不可积积分0或非零口头假设处理log。退化权重／单原子law仍是真概率且指数正，正性正确。

### 4. 全部k/theta真实Fréchet导数：49–95

52–56的F(t,x)、F'(t,x)完整读过。F'给x^(k+1)*exp相位乘第0坐标及x^(k+2)*exp相位乘第1坐标；对theta1求导产生x²，不是对样本x求导的2x。

57–67先用两个实际CLM投影的hasFDerivAt／mul_const相加，构造参数线性相位的导数，再exp链式并乘参数常量x^k。ext v、pow_add和ring精确把x^k*x／x^k*x²整理为k+1／k+2。该hdiff对全部实x/t成立，不只对一个AE集合给形式可微性。

68–74证明F'在((Fin2→ℝ)×ℝ)上的联合CLM连续，在`closedBall theta 1 × Icc(-B,B)`真紧集上取一个operator norm界C。参数空间有限维，所用closedBall紧性／区间紧性真实适用；不是将无穷参数空间说成紧集。

75–78是关键量词：先filter_upwards hb得到同AE样本x，然后对全部t∈ball(theta,1)给‖F' t x‖≤C；球包含于所选闭球。窗口不依赖x；C可依赖k和中心theta，不要求全theta／全k同一个数值界。

79–84由连续性分别生产每个F(t,·)的AEStronglyMeasurable及中心F'(theta,·)的AEStronglyMeasurable。85–88调用真实ParametricIntegral.lean206–212的接口：
- ball(theta,1)真实属于nhds theta；
- eventual F可测由更强的∀t可测给出；
- 中心F真Integrable由37–41给出；
- 中心F'可测由82–84给出；
- AE x后∀t∈窗口的共同范数主控由75–78给出，integrable_const C因概率finite成立；
- AE x后全窗口真实HasFDerivAt由全x/t的hdiff给出。

独立读该原库proof213–226：它正是从共同导数界在球上得Lipschitz主控，再真实交换积分和导数；不偷偷索取源未提供的joint可积／逐参数不同邻域假设。这里bound只需Integrable，不需另输入C严格正；库使用nnabs bound处理符号。

89–93在拆积分前先由k+1／k+2真实加权可积生成两项CLM smul_const可积，才用integral_add与integral_smul_const得到∫F'=momentSlope。94–95改写hd给准确weightedMoment导数。没有先拆总化积分再补可积，也没有跨私有helper调用。

### 5. 真log导数：97–107

101调用刚审的M0全点导数，102先用partition_pos的非零门再作`.log`。103–107通过CLM ext、真实normalizedMoment定义和实代数，把M0^-1倍momentSlope整理为partitionGradient；坐标／归一化因子均正确。

这个private有概率／AE界前提，且全部前提真实供给；不是对任意总化M0套log链式。实际结果针对整个函数t↦log(M0 t)在任意theta的Fréchet导数。

### 6. 所有k同时自然阶归纳到C∞：109–127

112的归纳命题是∀n:ℕ，∀j:ℕ，ContDiff ℝ n (M_j)，不是先固定j后错误引用更高j待证结论。115–120的阶0由全部theta真实HasFDerivAt给Differentiable，再给Continuous并套contDiff_zero。

121–126后继步IH已包含所有j，分别取j+1／j+2的C^n；对固定CLM coordinate作ContDiff.smul_const并相加，得到整个momentSlope mu j函数C^n。再用∀theta真实导数套自然n版`contDiff_succ_iff_hasFDerivAt`。

实际Defs.lean1171–1173是存在C^n导数函数且∀x HasFDerivAt iff C^(n+1)，正与源对应。没有输入手工C2、没有循环高矩阶光滑性、没有只给方向导数替代全Fréchet导数。

127用Defs.lean1114的`contDiff_infty`合成全部有限阶，正确为内层∞。不是解析ω；也不需要一个同时支配无穷多阶的共同C或Taylor半径。IH中的n是可微阶，不是样本量或law变化索引。

### 7. 无条件normalizedMoment_tilt的真实含义：129–145

该private TYPE没有概率／可积／分母非零前提，源码确实只用原库无条件积分公式。132–137展开M_k/M0并用Tilted.lean230–232的integral_tilted，把实际tilt积分写为同mu下exp密度除M0后乘x^k。

138–144的全样本函数外延等式只是交换实数乘法并把固定分母提出，不取消可能0的分母，ring在总化实域仍合法。145用Bochner/Basic.lean295–297的integral_div；其真实声明对任意r和f成立（由固定r^-1的积分线性），所以不缺某个未提供的可积／Z非零假设。

因此该无条件恒等式本身正确，允许mu=0或其他总化情形；但不能据此推实际tilt概率／可积性。下面public中这些分析门有独立生产，本proof没有用等式“反证”它们或以总化均值代替真实概率均值。

### 8. 公开P／Z／K及整个函数身份：168–191

168–169实际由公开originalMeasure_isProbabilityMeasure sourceEll w hw hs建立同P概率。178–179从同P公开AE界提取上界。没有另取mu或暗用正基点／q约束；P的原f2中心化不是当前输出。

180–181把真实partition_pos整理为literal Z(theta)>0。182–184明确证明整个函数weightedMoment P 0=Z，不只比较一个theta值。185–187先用这个函数身份转移M0的C∞到Z，188再以全部theta Z非零给literal K=logZ的C∞。

189–191对任意k用M_k和M0全参数C∞及partition_pos的处处非零得到normalizedMoment P k的C∞。没有全参数共同下界输入；log／div只需每点非零，实际API适用。该hZeq是02对01的真实函数别名修复，不是新数学假设。

### 9. 真actual mean全函数绑定及梯度：192–218、231–234

192–197对每个theta，分别用normalizedMoment_tilt的对称式和x^1=x、Fin2向量实际索引simp，得到actual mean0=M1/M0、mean1=M2/M0。198–203通过funext theta及Fin2穷尽，把这个身份提升为整个mean函数的等式。

204–210先用完整hmean重写，再套contDiff_pi并分两个坐标使用hnormal 1/2。没有只在鞍点θ0比较值而迁移邻域／全局光滑；本TYPE没有指定θ0。

211–218用真实CLM ext v展开coordinate／pr／smulRight，借同theta的hm0／hm1并ring，得到partitionGradient恰是公开actual mean的两投影组合。smulRight与scalar•CLM通过实乘法交换相符，未交换X和X²或漏exp归一化因子。

231–234以同P/hb的logPartition_hasFDerivAt，先用hgrad改写，再展开M0的真实定义，与literal K defeq匹配，交付∀theta的真实HasFDerivAt。不是把m=∇K作为caller前提。

### 10. 公开概率／可积门独立消去：219–230及代码顺序说明

219交付P概率实例及K／mean光滑后，220–230对任意theta显式构造公开分析合取：221–222由真实weighted_integrable(k0)给exp Integrable，223用isProbabilityMeasure_tilted hi和已在169生产的P概率／NeZero建立实际tilt概率。224–225把同P的AE界沿真实tilted_absolutelyContinuous正确转到该tilt。

226交付hi、hZpos、真实tilt实例，227–230在该真概率及同AE界下，用公开integrable_continuous_of_fixed_bounds分别证明x和x²真Integrable。均不从normalizedMoment_tilt或hmean反推概率／可积性。

源码书写上192–210先构造无条件积分身份与mean光滑，220–230才填公开每theta概率子目标。这里不是循环或偷门：P概率／真实加权可积／M0正性早已独立生产；无条件积分身份本来对所有mu正确，而后续actualtilt概率／两项可积又完全独立由hi与绝对连续给出、不引用hmean。不能把这种合法合取构造顺序误报为在totalized tilt0上制造假均值，也不能虚称223的实例在192前已经写出。

最终公开输出是同一个P、同一个实际tilt(theta)、其两个真实积分mean；退化非负权和任意实theta均保留，没有隐藏Hessian正定／可逆／caller光滑性门。

### 11. 所有21 actual TYPE／DEF值／generated覆盖

以下名字除公开一项外，都有实际完整前缀`_private.Shao.OQ3.SourceSmoothMeanMap.0.Shao.OQ3.`。表给actual-types.txt真实行范围；全部完整TYPE已先行读80行并在盲前缀保全，非只读此摘要。

| owner后缀／公开名 | TYPE行 | 实际内容与核查 |
| --- | --- | --- |
| momentSlope.eq_1 | 1–5 | 任意mu/k/theta展开k+1／k+2两投影和，匹配25–28 body |
| normalizedMoment.eq_1 | 6–8 | 任意mu/k/theta展开M_k/M0，匹配30–31 |
| weightedMoment_hasFDerivAt | 9–12 | 真概率／AE上界后的全k/theta Fréchet导数，49–95已审 |
| logPartition_hasFDerivAt | 13–17 | 同概率／AE门的全theta log导数，97–107已审 |
| normalizedMoment_tilt | 18–20 | 任意mu/k/theta无条件totalized积分身份，129–145已审 |
| weightedMoment.eq_1 | 21–23 | 原始加权exp积分精确展开，匹配22–23 |
| weightedMoment._proof_1 | 24–25 | NeZero(1+1)，源Fin2索引的数值Nat2非零门，无law参数 |
| weighted_integrable | 26–30 | 真概率／AE上界的全k/theta真Integrable，37–41已审 |
| momentSlope._proof_1 | 31–32 | ContinuousAdd ℝ，标准实结构闭命题 |
| momentSlope._proof_2 | 33–34 | SMulCommClass ℝ ℝ ℝ，实标量结构闭命题 |
| weightedMoment_contDiff | 35–37 | 真概率／AE上界的全部k C∞，109–127已审 |
| Shao.OQ3.source_log_partition_and_tilted_mean_smooth | 38–58 | 唯一公开完整目标，所有let／正性／实际mean／C∞／梯度已逐项交付 |
| normalizedMoment | 59–60 | private DEF：mu,k,theta→M_k/M0 |
| momentSlope | 61–62 | private DEF：mu,k,theta→实际两加权投影CLM |
| momentSlope._proof_3 | 63–64 | ContinuousConstSMul ℝ ℝ，标准实结构闭命题 |
| partition_pos | 65–67 | 真概率／AE上界后的M0严格正，43–47已审 |
| coordinate | 68–69 | private DEF：Fin2坐标投影CLM |
| coordinate.eq_1 | 70–71 | 任意i展开为ContinuousLinearMap.proj，匹配19–20 |
| partitionGradient | 72–73 | private DEF：mu/theta→两normalized矩的CLM |
| weightedMoment | 74–75 | private DEF：mu/k/theta→真实加权积分 |
| partitionGradient.eq_1 | 76–80 | 任意mu/theta展开normalizedMoment1／2投影和，匹配33–35 |

五eq_1分别只是五DEF的实际body展开，无新的概率／光滑假设。四结构generated的完整TYPE均为闭合标准实数／Fin2实例门，不带mu／w／theta／导数假设；没有藏一个额外分析前提。生成proof body由既有kernel验收和逐常量公理审计保障，本门未另起Lean打印值；其数学内容由完整TYPE、对应源定义展开及标准结构语义核实。

实际21owner=5private DEF+6authored private THM+1public THM+9generated THM，恰16theorem。没有遗漏private实例或额外new axioms。owner Audit用getModuleIdxFor?与精确moduleName筛选，不依赖namespace／private名字模式。

逐常量AXIOMS实读：weightedMoment._proof_1仅`[propext]`；其余20项均实际`[propext, Classical.choice, Quot.sound]`。不把“允许集合”误写为每项必用三公理，也没有新axiom／sorryAx。actual-types.txt与audit.log的21 DECL名字集合一致、完整TYPE无⋯或...。

### 12. 最后机械绑定与完整历史

以下仅在数学／整源／全部TYPE之后核既有产物，不重跑任何成功source、Audit、import smoke、图／pins／缓存。raw logs留server，仅选诊断和owner／axiom块；actual TYPE完整交付80行可读。

| 产物 | 行／字节 | SHA256 |
| --- | --- | --- |
| 当前source（local／own／source-02一致） | 237／11797 | d376655f6d53c7e7204f375a2dfc4a4fde1e2af43496186d14fc2660434d9681 |
| receipt.json（local／remote一致） | 332／12019 | 4141009f96510b7fc8e915bf9a7dd8976bd282126d36934a8de9aece87e62cfc |
| Audit.lean | 44／1839 | 987fc3ec3dae6d55f4ec55d3e723ff0ea627d2853d89222e8d9b52d557eb27e6 |
| audit.log | 106／6701 | 204cbf86738070b9fce82a6578d43bff9f8a72f320acc763c89f35ae6b431674 |
| actual-types.txt | 80／5628 | 4e80fb2465482828b07bdf24345eb874cff74d5f314b86bed19f1d9f0188afae |
| build-history.json | 46／1187 | 534612c70e99deda76e1c7d1ea4927d2287b91fd2b3d9d2fc67a51d971598231 |
| source-01 | 233／11793 | 37ceb95f3bfd0e707036017ddba7ccbcce714bfb9f8b02efd0e940e00d140592 |
| build-01.log | 116／6832 | 7cd9b223c02b43ac1302b8fb378d02a974a5bc46dbacb6f4da05691109da8ac1 |
| build-02.log | 92／5349 | 4414e80dda6d6d14115a1ebdd0c1b4d67c7a305dd522500025ee070bfbf8afe5 |
| lead-source-and-types-read.json（仅行政） | 28／915 | de5cbc126e49fd38c40171f4bddca982550cd0969694a764fb798fdebc6582a3 |

01是完整233行v2源码，exit1／7.642179s：hZ整体函数别名及Fin2两个坐标C∞ simp目标不匹配。独立diff确认02只加hZeq全函数identity并以其rewrite hZ、把两处过窄simp改为正常simp；公开TYPE／imports／分析假设未变，没有partial success或proof设置弱化。

02为当前完整源首次exit0／6.740715s。日志非空5349B，实际16warning：6弃用add_apply／smul_apply，4unused simp，4semicolon／unnecessary sequence提示，2处letI风格建议（169／223）。没有error，未为清warning改动成功源或重复编译。01的16warning与3实际error均保留，未把01记成部分成功。

首次owner Audit exit0／5.800628s，实际ALL_DECLARATIONS21／ALL_THEOREMS16／FROZEN_PUBLIC1／PUBLIC_DEF0／AXIOM_GATE PASS。它从第一次就设置pp.deepTerms true／pp.maxSteps1000000以完整打印；这两个仅打印选项，不改proof语义。无额外TYPE-only失败／重跑target；不与此前原A的独立打印历史混淆。

正式5项prerequisite文件local／remote SHA `80514fe6d11f32c7fd5b30225777c7e8ed7ae542eeb6a0a5f9d7d69de37b6508`（7行／510B）；canonical5 `5d1b1c34f11a05f81e8636f3809e739b4942d03d2d5f7f82dabbb7fff8e28307`。独立比较其字典为刚接受原A正式74字典的同五项精确子集，v39源不变；按任务复用已成功源／对象／图／pins证据，没有重复重算旧sourcehash或扫描cache目录。

v2 scope SHA `f2daa316ffcbb81fd564f4bdc51f5e991818af98449bb4b3ca8a83609f3d3c8e`；旧v1 scope SHA `439e2740c2968acda75ceb7b980a27554e6d72a498e1268913c78ea00e3300da`保持，旧202行CRITICAL票`20484a5393042bacdb8606c839cddda9deb3fce56f6ae9d4fc2beb306546bc47`及新168行声明票`1c0fa34ab1c2bcdbf34c3f85e1b4b42bffa3b85710584cf77a7901596910ac35`两端均原字节保存。未倒改v1历史，也未称v1曾实施。

实际branch `feat/oq3-source-smooth-mean-map`，HEAD accepted v39 `59a531b89eff7c11e4fc53583067f2cd3b53a517`；status仅`?? Shao/OQ3/SourceSmoothMeanMap.lean`。没有本单元commit／PR或下一声明，原A161冻结head独立保留。

构建及Audit记录CPU14–17、native8192MiB／j4、autoImplicit=false、one heavy；无成功源／Audit重复。本人全部server命令均只读CPU14–17，无Lean／probe／build／cache写／新agent／commit／pub，不触外部CPU0–9／80GiB。仅写本新报告及授权remote报告，不改source／scope／旧票／receipt／shared。

### 13. 消除义务与剩余

本完整实现真实补齐同有界sourceP的全参数C∞ literal K、实际tilt均值C∞和每theta的真实梯度身份，并在公开结论独立交付所有概率／exp可积／正Z／tilt矩可积门。不是从点态Hessian直接包装出的C2结论，也不依赖被隐藏的151private。

直接consumer可在同最终w／hm0下使用此公开hs版本，再接实际非退化Hessian及均值导数识别／等价来建立真正局部逆。当前没有输出局部inverse、统一谱／矩／标准化WC、一般无界law正则性、根B/C/D组合，亦不创建竞争canonical K公共定义。

原A161的正式root验收是独立流程，本proof不更新它的账，也不给它新增前提。旧v1环境拒绝仍保留历史。数学内容没有最优beta／解析ω／整体OQ3完成主张。

FINAL STATUS: CORRECT — v2冻结公开目标、全部237行proof／5private DEF值／6private THM／9generated实际TYPE及标准公理、真实机械历史绑定通过本独立完整proof门；等待lead整份读取后决定接受／发布。均值inverse及其他未交付原根义务仍OPEN。
