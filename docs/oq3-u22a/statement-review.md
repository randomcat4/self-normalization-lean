# U22a SourceCounterexampleRoot 独立声明／来源／API审查

STATUS: IN_PROGRESS

审查身份：唯一reviewer lease1；仅新增本报告及授权remote报告。先只提取冻结Lean fences，不读scope路线／行政凭据／作者笔记。以下完整TYPE及独立量词翻译为不可改写盲审前缀；后续发现追加，不回改本前缀。

## 冻结精确imports与唯一完整TYPE

```lean
import Shao.OQ3.SourceRemainderNotBigO
import Shao.OQ3.SourceCanonicalSaddle
```

```lean
theorem exists_fixed_jointNonlattice_saddleExpansion_counterexample :
    ∃ (q : ℝ) (w : AtomicIndex → ℝ),
      (1 < q ∧ q < 103 / 100 ∧ (∀ i, 0 < w i) ∧
        ∀ k : Fin 4,
          HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
            (constraintTarget q k)) ∧
      let P : Measure ℝ := originalMeasure sourceEll w
      ∃ hP : IsProbabilityMeasure P,
        letI : IsProbabilityMeasure P := hP
        let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
        let x0 : ℝ := Real.sqrt q / 4
        let a0 : ℝ := q / 4
        let s0 : ℝ := 8 * sourceEll
        let t0 : ℝ := -sourceEll
        let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
        let Dtail : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ x0 * Real.sqrt z.2 ≤ z.1}
        (Integrable (fun x : ℝ => x) P ∧ (∫ x : ℝ, x ∂P) = 0) ∧
          (∀ᵐ x ∂P, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
          0 < P.real (Set.Ioi 0) ∧
          (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic P xi eta‖ < 1) ∧
          Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
            Filter.atTop Filter.atTop ∧
          Filter.Tendsto (fun J => ‖jointCharacteristic P (resonanceXi J) (resonanceEta J)‖)
            Filter.atTop (nhds (1 : ℝ)) ∧
          bivariateMGFDomain P W = Set.univ ∧
          (∀ theta : bivariateMGFDomain P W,
            (0 < ∫ x : ℝ, Real.exp
              ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P) ∧
            bivariateLogMGF P W theta =
              Real.log (∫ x : ℝ, Real.exp
                ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P)) ∧
          ∃ lift : (Fin 2 → ℝ) → bivariateMGFDomain P W,
            (∀ theta, (lift theta : ℝ × ℝ) = (theta 0, theta 1)) ∧
            let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
            let theta0 : Fin 2 → ℝ := ![s0, t0]
            let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
            let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
              (pr 0).smulRight a0 + (pr 1).smulRight q
            let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
              ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
            let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
            let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
            let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
            let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
            let nu : (n : ℕ) → Measure (Shao.Path n) :=
              fun n => Measure.pi (fun _ : Fin n => P)
            let Tail : (n : ℕ) → Set (Shao.Path n) := fun n =>
              {z | x0 ≤ (∑ i, z i) / (Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z))}
            let C : ℕ → ℝ := fun n =>
              Real.sqrt (2 * Real.pi * (n : ℝ)) * Real.exp ((n : ℝ) * lambda0) *
                (nu n).real (Tail n)
            (∀ theta, K theta =
              Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
            HasFDerivAt K gradient theta0 ∧
            HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
            (∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < dotProduct u (D *ᵥ u)) ∧
            0 < x0 ∧ x0 < 1 / 2 ∧ 0 < a0 ∧
            q = a0 ^ 2 / x0 ^ 2 ∧ s0 = -2 * a0 * t0 / x0 ^ 2 ∧ t0 < 0 ∧
            lambda0 = saddleRate sourceEll q w ∧ 0 < lambda0 ∧
            0 < D.det ∧ 0 < lambda1 ∧ 0 < vCorr ∧
            correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹ ∧
            (a0, q) ∈ Dtail ∧
            bivariateLegendreRate P W (a0, q) = (lambda0 : EReal) ∧
            (∀ z ∈ Dtail,
              bivariateLegendreRate P W (a0, q) ≤ bivariateLegendreRate P W z ∧
              (bivariateLegendreRate P W z = bivariateLegendreRate P W (a0, q) ↔
                z = (a0, q))) ∧
            (∀ n : ℕ, MeasurableSet (Tail n)) ∧
            (∀ n : ℕ, 0 < n → ∀ᵐ z ∂nu n, 0 < Shao.energy z) ∧
            (∀ n : ℕ, 0 < n → sourceTail q n =ᵐ[nu n] Tail n) ∧
            (∀ n : ℕ, normalizedTailCoefficient sourceEll q w n = C n) ∧
            (∃ nseq : ℕ → ℕ, StrictMono nseq ∧
              Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
              ∀ J : ℕ, 0 < nseq J ∧
                (J : ℝ) < Real.sqrt (nseq J : ℝ) * (C (nseq J) - vCorr⁻¹)) ∧
            ¬ Asymptotics.IsBigO Filter.atTop
              (fun n : ℕ => C n - vCorr⁻¹)
              (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
```

## 独立完整量词／语义翻译及首轮疑点

1. 此定理没有任何caller前提；直接存在同一实数q和同一AtomicIndex实权w。
2. 第一合取无条件交付1<q<103/100、每个原子w_i严格正，以及四个真实HasSum矩约束。
3. 四矩被积是w_i*constraintFeature(sourceEll,fixedAtom_i,k)，不是把函数特征当作仅k的未绑定对象。
4. P随后固定为originalMeasure sourceEll w；一切余下对象必须使用这一个w/q/P。
5. 明确存在hP:IsProbabilityMeasure P，再以该证明生成局部概率实例；不是caller可替换的概率律。
6. W(x)=(x,x²)，x0=sqrt(q)/4，a0=q/4，s0=8*sourceEll，t0=-sourceEll。
7. D是同w的atomicMeasure下实际parabolaCovariance；未来要证明它是该P在theta0重倾斜后的Hessian，而非自由矩阵。
8. Dtail是c>0且x0*sqrt(c)<=a的完整弱尾域；不把c=0偷偷纳入，也不把边界改成严格不等式。
9. 给P下X真Integrable且均值0、AE 1<=|X|<=4+sqrt10，并给真实P(X>0)的real质量严格正。
10. 对所有非零二维频率，实际jointCharacteristic P范数严格小于1；不是仅一维非格点。
11. 另给显式resonance频率的绝对值和趋atTop，并沿同频率序列实际特征范数趋1。
12. 不能以另一个opaque存在非格点family取代P；逃逸性质也必须来自相同w。
13. bivariateMGFDomain P W等于univ；全部域内theta都给实际正指数配分与canonical log等于真实实积分log。
14. 要先真可积／正配分再用log；不能把域外总化积分0当作该结论。
15. 随后存在lift，把Fin2参数真正送入同canonical域；其底层pair必须处处等于(theta0coord,theta1coord)。
16. K是沿该lift拉回的实际canonical log，不是另外独立命名的局部代理函数。
17. theta0是![s0,t0]；pr是真CLM坐标投影。
18. gradient是a0*pr0+q*pr1；hessian是由同actual D两层有限和构造的真实双线性CLM。
19. 导数结论必须是HasFDerivAt K及HasFDerivAt(fun theta=>fderiv ℝ K theta)，不是形式偏导／仅方向二阶展开。
20. D对全部非零u有u·Du>0；必须由同law实际矩生产，不能只输入det>0或调用奇异逆总化。
21. v=![1,2a0/x0²]；lambda0=s0*a0+t0*q-K(theta0)；lambda1=2t0/x0²+v·D^-1v。
22. vCorr=(-t0)*sqrt(detD)*sqrt(lambda1)；必须严格正且与已有correctedInverseScale互为倒数。
23. 给0<x0<1/2、a0>0、q=a0²/x0²、s0=-2a0*t0/x0²和t0<0；所有除法应有真实正分母。
24. lambda0等于已有saddleRate且严格正；detD、lambda1、vCorr均实际严格正。
25. candidate(a0,q)属于同完整Dtail；其canonical扩展实Legendre率恰等于有限lambda0的EReal嵌入。
26. 对全部z∈Dtail，candidate率不大于z率且相等当且仅当z=candidate；包含off-support和所有c>0，不局限局部凸邻域。
27. 不能从局部Hessian正定直接宣称全域唯一极小；必须真实消费既有全域公开producer。
28. nu(n)是固定P的n重实际Measure.pi，不是另选的三角阵／时间变律。
29. Tail(n)是原比例尾事件x0 <= sumX/(sqrt(n)*sqrt(actual energy))，使用真实Shao.energy和约定的实除法总化。
30. C(n)=sqrt(2πn)*exp(n*lambda0)*nu(n).real(Tail(n))，并非预先定义成已有normalizedTailCoefficient。
31. Tail每个n都必须MeasurableSet；连续性可含sqrt0、除法0处，不能不检查分母便声称全局连续。
32. 对n>0，同实际nu(n) AE energy>0；需要从P AE|X|>=1逐坐标提升到真产品律。
33. 对n>0，sourceTail(q,n)与该比例Tail(n)在同nu(n)下AE相等；要用真实energy正和sqrt(n)>0作等价变形。
34. general sourceTail中心／样本energy必须实读，不能把另一个曲边事件或其他a中心当作它。
35. 对全部n包括0，已有normalizedTailCoefficient(sourceEll,q,w,n)必须等于上述实际C(n)。
36. n=0时比例Tail和sourceTail未必相同；目标只要求系数相等，可由真实sqrt0前因子分别归零，但不能假装事件相等。
37. 存在同一nseq:Nat->Nat，StrictMono且Tendsto atTop atTop；每个索引J都有nseq J>0和真实缩放误差sqrt(nseq J)*(C(nseq J)-vCorr^-1)>J。
38. nseq不能输入为caller见证，也不能只证明任意晚单点而漏掉严格增递归选取；保留每步原gap。
39. 真正BigO否定在同一次w/q/lift/P/C/vCorr存在量词内部，使用标准Asymptotics.IsBigO atTop和inverse sqrt(n)。
40. 标准BigO含范数和eventual门；要先nseq正再消sqrt，不能靠n0总化构造反例。
41. lift如何选择不应改变K值：底层pair身份和canonical函数性应保证与已验收literal K／theta0结果一致。
42. 所有let和合取均在同w/P内部；必须核parse没有把无条件q窗口／正权／约束推成某个蕴含的前件。
43. actual ratio bridge、alln coefficient、一次law及strict witness是本次新组装门；已有接口名称／CORRECT记录不自动证明这些桥。
44. 本TYPE没有C∞／均值逆／邻域Hessian谱假设或输出；不因U20e未实现就暗加该门。
45. 暂不预报原A或其他根闭合；待来源契约、全部真实公开API、边界和环境绑定完成后独立裁决本声明。

--- END IMMUTABLE BLIND PREFIX ---

## U22a 独立完整声明／来源／API终票

STATUS: CORRECT

JUSTIFICATION: 冻结唯一TYPE忠实给出同一次选定q/w/P的原A反例所需性质。真实公开PR153、PR156、PR158接口能在同w/q上实例化；新比例事件桥有真实产品AE正能量、全n可测性、正分母等价及n=0分支的完整可实现路径。没有caller假设、未消去的hcont/hW、另一个law或仅局部率最小代理。当前只批准声明，尚无本根实现／server build／module-owner Audit或完整proof接受；原A此刻仍OPEN。

本节追加于先行持久化的143行／10518字节盲前缀。前缀SHA256 `bbd84ec54d54db531ec5b21c6cc9c047cfd54be90c6a6a9e114308df6931029d`；未改前缀、冻结scope、旧票或任何生产源。初始IN_PROGRESS是历史检查点，本节是最终声明裁决。

### 1. 来源契约与实际目标范围

实读`drafts/oq3/root-contract.md`§3（44–62）：原A要一个固定有界中心律、固定x0∈(0,1/2)、真实联合非格点却有逃逸近共振、正则鞍点／正定／正率／正曲边常数、完整正尾域唯一全局率极小，以及递增趋无穷样本量上的缩放误差至少线性增长，故不是标准O(n^-1/2)。P与x0必须在全部n外一次量化。

实读R1原件的起始补偿构造、137–159逆倾斜和鞍点、161–257全局率与协方差／尺度、259–307联合非格点和显式近共振、309–345有限模型Fourier／条件极限、348–429层支配及全层常数、431–483连续常数和正h^(3/2)差、484–558对角转移和(31)。完整链的源义是固定最终P，不是随n变化的有限阶段律。

固定原件R1 SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。本票不改原件，不把源中未整体形式化的一般rho KL(9)/(10)、精确ζ系数(24)或可选(14a)当成既有定理。root v39独立报告§7明确：已接受的真实有限指数分离器和严格正h^(3/2)充分下界足够供固定律反例；这些替代路径不等于声称原中间公式全部已形式化。

实读`coordination/integration-v39/oq3-review.md`全文及§7：本批153/156/158已接受的范围是同律标准否大O、全c>0规范率最小性和实际Hessian／正定／尺度；尚缺一次量化后的组装、实际P^n的正能量及比例尾事件桥。scope77恰补这些明确缺口，不把辅助声明数量当根闭合。

源ICM固定x误差问题与另一个x变化的一致性问题分开；本TYPE只为一个固定x0提供反例。使用root-contract、R1/R2/RP的修正vCorr，不照抄已发现有误的印刷常数。没有最弱条件、历史首次、beta端点或最优性主张。

### 2. 完整量词、真实对象与无真空箭头

唯一TYPE没有前提箭头。存在q/w后，q窗口／全部严格正质量／四条真实HasSum是无条件第一合取；随后P为该同w的originalMeasure。`∃ hP`交付同P的概率证明，`letI`只让后续规范对象得到真实概率／NeZero实例，不是在caller处加入可自行选择的law。

给定hm0和hw，可由`constraintFeature`／`constraintTarget`的第0坐标确切化简得到HasSum w 1。`originalMeasure_isProbabilityMeasure`产生hP。与其他公开producer内部生成的概率证明的区别只是Prop证明项，不能改变P或其积分／率值；类型类中的证明依赖不造成选择不同概率律。

W、x0、a0、s0、t0、D、Dtail随后都为确定表达式。`∃ lift`放在同P内部，坐标身份对全部theta成立；K定义为该lift的真实canonical log。所有lambda／vCorr／nu／Tail／C以及最终nseq、BigO否定均在同一w/P/lift之内，不存在为不同性质分别取存在族后拼接。

Dtail实际为`{(a,c) | 0<c ∧ x0*sqrt(c)≤a}`。它保留弱尾边界和全部c>0，包括不可实现点；不纳入c=0，不把它误叫全R²中的闭集。比较值用EReal，无需也不允许把+∞先toReal来比较。

### 3. 一次取律：直接公开producer消费表

| 新TYPE部分 | 实际公开接口 | 输入消除／同律约束 |
| --- | --- | --- |
| q窗口、全正w、完整四HasSum、真实P概率／中心／AE界／正半轴／联合非格点／近共振／nseq与标准notIsBigO | `exists_source_fixed_law_not_isBigO`，SourceRemainderNotBigO.lean44–72 | 只destruct这一个存在见证，保留其q/w/P；不重取非格点family |
| 全域domK、全域内正配分和literal log、完整正尾域canonical唯一最小 | `source_canonical_rate_unique_minimizer`，SourceCanonicalRate.lean17–46 | 对上述同q/w实例化；strict hw给nonnegative hw，四HasSum原样传递 |
| lift／全函数K身份、真正一阶与fderiv二阶、D二次型严格正、鞍点方程／lambda0／尺度 | `source_canonical_saddle_hessian_and_scale`，SourceCanonicalSaddle.lean19–57 | 对同q/w及严格hw/hm实例化；使用它返回的一个lift，不换law |
| 源曲边事件与概率系数的字面定义 | `sourceTail`、`normalizedTailCoefficient` | 分别在SampleBoundary.lean25–27和SampleChangeOfMeasure.lean19–21，是真P有限产品概率 |
| 新桥 | 原库有限产品AE／Borel／sqrt／AE测度同余API | 本根局部真实证明，不调用外部私有引理、不输入新事件等价假设 |

PR153已经公开存在StrictMono／Tendsto／每个J正样本量及严格gap，不需要本根重新递归选择nseq。其接受生产链先用任意晚、任意大同律见证递归取时刻，并在最终P上消除了hcont／hW输入；本根只保留该已经无条件的公开输出。私有`not_isBigO_inv_sqrt_of_scaled_witness`不能被跨模块调用，亦无此必要，因为标准否定已在公开结论中。

### 4. 同P的概率／非格点／显式逃逸性质

PR153的实际公开TYPE完整保留q∈(1,103/100)、w_i>0、四HasSum，P=originalMeasure sourceEll w；其后是同P下X真Integrable且均值0、AE1≤|X|≤4+sqrt10、真实P.real(Ioi0)>0、每个非零二维频率范数<1及指定resonance序列的两个Tendsto。新TYPE逐项照同对象交付，无量词强化错误。

中心化来自同倾斜律的完整f2约束，而非把atomicMeasure的均值q/4当作原P均值；D的来源相反，是重倾斜后的atomicMeasure。两种实际测度在TYPE中没有混淆。正半轴性质是真实P下的质量，而非只说某个抽象索引权重正。

所有非零二维频率的严格模界不等于一维非格点。显式逃逸的绝对值和趋atTop与同序列模趋1同时输出，故不仅是有某个有限共振。没有把有限阶段法向格点律当成无限最终律的联合非格点见证，也没有声称可选“失败每个多项式WC”已经包含在本TYPE。

### 5. Canonical全域、全局最小与lift一致性

已接受PR156的源先从真实有界P生产全部实(s,t)的exp Integrable和严格正配分，证明`bivariateMGFDomain P W=univ`，再使用规范域subtype上的`bivariateLogMGF`。新TYPE同样明确正配分和literal log身份；不对未证明可积的域外值套总化log0。

PR156给候选(a0,q)属于完整Dtail，并给EReal候选率=saddleRate、全部Dtail比较及相等当且仅当候选。实际生产链使用有限指数测试的候选上界／达到和每个非候选点严格分离，覆盖off-support c<1、c>1+H、Bernoulli端点及弱尾边界；没有以局部Hessian正定推全局最小。

PR158的lift底层对全部theta等于(theta0coord,theta1coord)，其完整K身份先成立，再把真实literal K的一阶／fderiv二阶转移给canonical pullback K。新TYPE保留这个全函数身份，故不是只在theta0相等便错误转移导数。

源矩阵D=Cov_atomic(X,X²)确是该P在theta0=(8ell,-ell)倾斜后真实Hessian；这由接受的导数接口和逆倾斜恒等式生产，而不是caller输入任意正定矩阵。PR158给全部u≠0的u·Du>0及正det；没有靠奇异矩阵逆的总化值作几何论证。

新结论的(a0,q)率为lambda0，而PR156给saddleRate。PR158明确lambda0=saddleRate，因而可在有限实嵌入EReal之后直接改写，未使用EReal.toReal。其他点可为+∞，仍满足比较和唯一等号。

### 6. 鞍点方程及实际修正几何常数

q>1首先给q>0，故sqrt(q)>0、x0>0和x0²=q/16>0。a0=q/4>0只是这一实数正性推论。PR153已有x0<1/2，或可由q<103/100直接证明；不从图示猜取窗口。

PR158实际输出q=a0²/x0²、s0=-2a0*t0/x0²、t0=-sourceEll<0，并给lambda0=saddleRate>0。清分母使用真实q／x0正性；不是利用实除0的总化简化。D和v的坐标与TYPE逐字相同。

同接口输出detD>0、lambda1>0、vCorr>0和`correctedInverseScale sourceEll q (atomicMeasure w)=vCorr⁻¹`。lambda1是2t0/x0²+v·D^-1v，真实负32ell/q修正没有被漏掉。vCorr是(-t0)*sqrt(detD)*sqrt(lambda1)，采用正根和严格正域，而非自由正尺度。

因此从PR153来的normalizedTailCoefficient／correctedInverseScale误差与本根C／vCorr^-1误差只差两个明确可证的函数身份；不能只凭常数名称一致来替换。

### 7. 新核心桥之一：全部n的比例事件Borel可测

真实`Shao.Path n`是`Fin n→ℝ`（Shao/Basic/FinitePath.lean18），`Shao.energy z=∑i,(z_i)^2`（同源31），不是方差代理。有限和及每坐标平方连续，energy、sum都是Borel可测；sqrt连续，因此sqrt(n)*sqrt(energy)可测。

比例函数在能量0处通常不连续，不能用`fun_prop`不加分析地宣称它全局连续。固定库`MeasureTheory/Constructions/BorelSpace/Basic.lean`601–603的ContinuousInv₀.measurableInv把0处分开而给真实可测逆；乘以sum得到全局Borel比例函数。等价可用`MeasureTheory/Group/Arithmetic.lean`269–271的Measurable.div，在实数相应可测乘除实例下成立。

`MeasureTheory/Function/SpecialFunctions/Basic.lean`150的Measurable.sqrt及measurableSet_le可构造Tail(n)的MeasurableSet，对n=0也成立。这个门不依赖AE能量正，也不把几乎处处连续误当全局连续。

### 8. 新核心桥之二：真实nu(n)下n>0的AE正能量

先以同P的hP建立每个`nu n=Measure.pi(fun _ : Fin n=>P)`真概率。固定`MeasureTheory/Constructions/Pi.lean`311–313的pi.instIsProbabilityMeasure正是该有限产品实例，含空指标情形；有限性及SigmaFinite由概率实例提供，不添加caller假设。

同文件425–426的`Measure.tendsto_eval_ae_ae`把P下的AE1≤|x|逐坐标拉回真实nu(n)。用`ae_all_iff`／有限全称合并，在一个共同AE集合上得到∀i,1≤|z_i|；不是“各坐标分别AE所以未经证明就同一个样本都成立”。

对这些样本逐坐标平方，1≤z_i²；有限求和得到(n:ℝ)≤energy z。n>0给(n:ℝ)>0，故energy z>0。只在n>0使用正下界；不为Fin0虚构一个坐标，也不声称任意实向量都有正能量。

原R1所谓支持离0保证正能量，在实际乘积测度语义中正是这个AE结论；无需在零概率的全空间异常样本上改变统计量定义。

### 9. 新核心桥之三：保留正尾符号的AE事件等式

令S=∑z_i、E=energy z、d=sqrt(n)*sqrt(E)。在n>0、E>0时，sqrt(n)>0且sqrt(E)>0，所以d>0。固定`Analysis/Real/Sqrt.lean`365–366的`Real.sqrt_mul`先消费0≤(n:ℝ)，给sqrt(n*E)=sqrt(n)*sqrt(E)。

实际sourceTail定义是`E>0 ∧ x0*sqrt(n*E)≤S`，含真实正能量门和未平方的正尾不等式。上述样本上它等价于`x0*d≤S`，再由正d的`le_div_iff₀`等价于`x0≤S/d`，即本TYPE的Tail。无需平方两边，所以不会把负尾符号丢掉。

将该点态iff用propext提升到同nu(n)的AE集合等式，得到TYPE的`sourceTail q n =ᵐ[nu n] Tail n`。它不是换测度等式，也不是对另一finite stage law的事件身份。

固定`MeasureTheory/OuterMeasure/AE.lean`321–324的`measure_congr`／EventuallyEqSet.measure_eq把AE集合等式转为实际ENNReal质量相等，再对toReal作同余得到real概率相等。nu(n)为概率，质量真实有限；不从无限质量的toReal总化获取概率结论。

### 10. 全n系数恒等式、n=0和真正标准Landau否定

`normalizedTailCoefficient`的实际定义是sqrt(2πn)*exp(n*saddleRate)*该同P产品下sourceTail的real概率。对n>0，用上一节同nu(n)质量身份和lambda0=saddleRate，便得到本根C(n)。没有另选自由数列或只在nseq上重写。

n=0单独展开，两边sqrt(2*pi*0)=0，故系数均为0；不除sqrt0，不使用n>0事件等式。盲前缀36只是待查的风险提醒；在当前q>1下两事件其实也均为空（energy0=0；比例0且x0>0），但系数证明不需借这个更强事件事实。

故可得到整个函数n↦normalizedTailCoefficient与C逐点相等，及correctedInverseScale=vCorr^-1。PR153已经给同w/q的StrictMono／atTop nseq和全部J严格gap；直接用这些全函数身份改写，原nseq原样保留。没有重新选r/q/P，没有假设原有限阶段见证时刻已经单调。

同理，公开标准`¬Asymptotics.IsBigO atTop`结论通过函数外延身份改写为本根最后一项。原库IsBigO包含范数和eventual门，接受的PR153已在正nseq时刻用sqrt>0合法约分并矛盾于J>B；本根没有把带符号单点差当作标准Landau定义，也没有利用n=0的逆数总化。

新TYPE的每个J都有严格差>J，较root-contract“最终≥bJ”足够强，可取b=1并从J≥0使用弱化。StrictMono与atTop／正样本量同时输出，固定P和x0在所有索引外，满足真正固定律反例的量词要求。

### 11. 公开可达、私有边界与新scope环境

精确imports为SourceRemainderNotBigO与SourceCanonicalSaddle。前者公开给无条件存在律和真实概率系数定义链，后者公开给canonical域／梯度／Hessian／几何及其Rate依赖。所需SampleBoundary、FinitePath、FiniteIID和原库Pi／Borel／sqrt／AE同余均在实际接受链可达，不需新增共享定义或新缓存。

本根不调用PR153私有BigO helper、PR158自动congr_simp／私有先前证明、SourceFixedLawRemainder私有递归或其他模块private名字。可在本模块局部证明产品AE／比例Borel／sqrt事件等价几个新helper；这些是实现义务，尚未有本根源码可审。

namespace Shao.OQ3，open MeasureTheory Shao.Probability，open scoped Matrix Topology BigOperators与本TYPE的canonical名字、Fin2向量／矩阵／拓扑／有限和记号相符。TYPE不出现ContDiff∞；U20e冻结环境缺口没有被偷补，也不是本TYPE的隐含输入。均值inverse或邻域C∞不在原A最后组装§7要求之列。

### 12. 机械／源码／只读环境绑定（数学之后）

scope两端107行／10670字节SHA256 `69ed5bbb5bccadc3b552c75f09b090f775164d4eb0fe9eaa8a1cf0f65f59308b`。本门没有改scope字节／header／TYPE。

独立从已接受正式字典复现74并集：
- PR153的67项正式`u20b-prerequisite-hashes.json`，文件SHA `1ae7cdb8cb304d5b86be29fd1130d85004c1d6f840cb11441db178ab8416ef26`；
- PR158的25项正式`u20d-prerequisite-hashes.json`，文件SHA `a5f2b8d3549f9cdef4f66e0cf600b2f6e1f4698359b2f921ed64542c2608160d`；
- 两个公开seed SourceRemainderNotBigO与SourceCanonicalSaddle本身。

并集无冲突，74条canonical source-relative path键。独立compact SHA256 `c0e75a48979e6cf28bcd1f232624543b313425df2d0280da7057c32ede836703`。未读作者candidate JSON正文来确定数学／依赖图，也未重新扫描已接受Mathlib图。

直接seed源码绑定：SourceRemainderNotBigO.lean `620bd072fc799b1684a5d54b1912d3abb5c26833a20d680d354185bc9eea633f`；SourceCanonicalSaddle.lean `24200d85b6c4d13862ab166da8c7e6221ef87601216a125d5e8dc3260d0a7941`；其共同Rate源`fc492cbacca9a8df208b9a20ea47d7e84e71c1c48e1f87448adbd925f5378d92`包含在正式并集中。

服务器对accepted integration-bearing-v39目录74条源逐项fresh SHA：缺失0／差异0。该accepted commit `59a531b89eff7c11e4fc53583067f2cd3b53a517`的实际git tree为`43577d0d66de8325a756c9ac25e43e53809c3525`，与绑定一致。此为源／行政核对，不重跑root组装Lean／旧成功门。

已有只读单Shao-root import-view内全部74对象路径存在，缺失0：OQ3链接own lead-oq3 build，Probability链接accepted integration-bearing-v38 build，Basic链接own build。只核路径可读及已接受源绑定，没有复制二进制、改cache、重算whole-cache hash或把路径存在当本根证明。Probability所需旧公共源在v39并集中SHA一致。

候选union文件只核hash：`55584f88d8f05b3616147818250113799d8fa99f7a412f2c61cbba019ba67925`。readiness正式摘要hash `deaec5a5039afba553ab36b95eb78e565a50da87a7b4b4ac571e1305976e4194`；其74源／对象记录由上述独立并集与定向fresh检查复核，不借其true标签推数学。

实际当前own工作树仍`feat/oq3-compact-tilt-weak-cramer`，HEAD `53694dec89a2834522e48ab36954fc4528cfee06`，status clean；`Shao/OQ3/SourceCounterexampleRoot.lean`不存在。没有本根source／probe／Audit／新branch／构建结果。未来从accepted v39正常新branch属于实施阶段，不把预期分支说成已经存在。

既有pins及root成功机器凭据复用，不重跑图／smoke／Lean／Audit。全部remote项目只读命令经broker并限CPU14–17，未触外部CPU0–9／80GiB任务；未新agent／commit／pub，未改旧源／旧票／scope／receipt／shared／cache。仅写本新报告与授权remote报告。

### 13. 原target→消除义务→直接consumer→剩余

本声明准确聚合原A四组性质，并将原normalized系数桥接到字面S_n/(sqrt(n)*V_n)事件与same lambda0/vCorr。产品AE正能量、比例事件Borel、正分母事件等价、全n系数身份都有明确真实公开API／局部证明路径；没有新的外部分析定理缺口、手给globalmin或隐藏hcont/hW。

直接consumer是root原A的最终固定律反例接口，以及对原固定x O(n^-1/2)余项的正式否定。尚须未来本根完整实现、首strict targeted server检查、精确module-owner所有TYPE／公理Audit、独立完整proof终票及root正式验收。声明CORRECT本身不关闭A。

U20e v1仍原字节CRITICAL GAPS／未实施，未来需独立ContDiff环境修订；均值inverse／邻域正则性及根B的谱、统一矩／WC、Song／格胞／远区组合不由此自动获得。根C的完整标准化稳定性、根D的特定丢番图见证仍独立。一般KL9/10、精确ζ24、可选14a及全部随x变化一致性均不被本TYPE声称完成。

FINAL STATUS: CORRECT — 准许此冻结原根声明进入后续实施／完整proof门；本票不是proof验收或根关闭。当前原A仍待最终源／机器／独立proof／root验收，其他B/C/D与均值inverse仍OPEN。
