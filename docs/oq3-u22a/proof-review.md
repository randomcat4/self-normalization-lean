# U22a SourceCounterexampleRoot 完整独立证明审查

STATUS: IN_PROGRESS

唯一reviewer lease1。仅拥有本新报告与授权remote报告；不改source／scope／旧票／receipt／cache。先仅读取actual公开完整TYPE及全部5个actual owner TYPE（所有续行），独立翻译并持久化，再读整个实际proof与机械证据。已有声明CORRECT、作者说明、成功标签均不代替此门。以下为不可改写盲审前缀。

## Actual公开完整TYPE（从真实源截取，未读proof）

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

## 其他全部actual owner TYPE（完整续行）

```text
DECL _private.Shao.OQ3.SourceCounterexampleRoot.0.Shao.OQ3.product_energy_pos_ae
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, 1 ≤ |x|) →
    ∀ (n : ℕ), 0 < n → ∀ᵐ (z : Shao.Path n) ∂MeasureTheory.Measure.pi fun x => mu, 0 < Shao.energy z
DECL _private.Shao.OQ3.SourceCounterexampleRoot.0.Shao.OQ3.sourceTail_ae_ratio
TYPE ∀ (q : ℝ) (n : ℕ),
  0 < n →
    ∀ (nu : MeasureTheory.Measure (Shao.Path n)),
      (∀ᵐ (z : Shao.Path n) ∂nu, 0 < Shao.energy z) →
        Shao.OQ3.sourceTail q n =ᵐ[nu] {z | √q / 4 ≤ (∑ i, z i) / (√↑n * √(Shao.energy z))}
DECL Shao.OQ3.normalizedTailCoefficient.eq_1
TYPE ∀ (ell q : ℝ) (w : Shao.OQ3.AtomicIndex → ℝ) (n : ℕ),
  Shao.OQ3.normalizedTailCoefficient ell q w n =
    √(2 * Real.pi * ↑n) * Real.exp (↑n * Shao.OQ3.saddleRate ell q w) *
      (MeasureTheory.Measure.pi fun x => Shao.OQ3.originalMeasure ell w).real (Shao.OQ3.sourceTail q n)
DECL _private.Shao.OQ3.SourceCounterexampleRoot.0.Shao.OQ3.ratio_tail_measurable
TYPE ∀ (x : ℝ) (n : ℕ), MeasurableSet {z | x ≤ (∑ i, z i) / (√↑n * √(Shao.energy z))}
```

## 独立逐义翻译与待核门

1. 公开根定理没有caller数学前提。存在同一个q与同一个全索引w，先无条件给q窗口、全部严格正权和四条真实HasSum。
2. 特征被积为w_i*constraintFeature sourceEll(fixedAtom_i)k；每个k的目标值是constraintTarget q k，不能遗漏fixedAtom绑定。
3. P随后固定为originalMeasure sourceEll w；存在同P概率证明hP并建立letI。概率实例不是重新选law。
4. W=(x,x²)，x0=sqrtq/4，a0=q/4，s0=8ell，t0=-ell，D=同w的atomicMeasure协方差。
5. 先给原P真实可积零均值、AE离0有界、实际P正半轴正质量；不把atomic π均值当P均值。
6. 真正二维非格点是所有xi≠0或eta≠0的jointCharacteristic范数<1，并在显式同频率序列有逃逸和模趋1。
7. 这些属性都在同q/w/P下，不允许分别destruct别的family来填缺项。
8. Canonical domK=univ且全部域内实配分严格正、canonical log等于同P实际exp积分log，排除log0总化。
9. 存在lift，全部Fin2坐标都保持底层pair；K是真canonical pullback，而非自由局部代理。
10. gradient真实CLM为a0 pr0+q pr1；hessian为Σij D_ij u_i v_j形式的真实双线性CLM。
11. 两项分别是真HasFDerivAt K与HasFDerivAt(fderiv K)；必须先全函数身份才能迁移第二项。
12. 对所有非零u有u·Du>0，不能只用det>0或奇异矩阵逆总化充当正定性。
13. x0、a0和所有除法分母须真实正；给q=a0²/x0²、s0=-2a0t0/x0²及t0<0。
14. lambda0是s0a0+t0q-K(theta0)，必须等于saddleRate且正；不是另给一个不相干正数。
15. lambda1是真2t0/x0²+v·D^-1v，其中v=![1,2a0/x0²]；包含负32ell/q项。
16. vCorr=(-t0)sqrt(detD)sqrt(lambda1)>0，既有correctedInverseScale恰为其倒数。
17. Dtail是全部c>0的弱正尾域，保留不可实现点和可能+∞的EReal率，不先toReal。
18. candidate=(a0,q)在该域，其规范率有限等于lambda0；全部其他域点比较与唯一等号都必须真实生产。
19. nu n字面同P的Fin n有限产品，不是n依赖律或抽象概率序列。
20. Tail n字面是x0<=sum/(sqrt n*sqrt(actual energy))，C n字面是修正尺度前归一化的真实尾概率。
21. Tail每个n均须MeasurableSet。分母可为0时不能声称比例函数全局连续；应核真实Borel乘除API。
22. n>0时同nu n AE energy>0，不能对全部实向量强称正，也不能先除sqrt0。
23. n>0时sourceTail与比例Tail在同产品律下AE相等；须正分母并保留正尾方向，不能平方丢符号。
24. 对全部n的normalizedTailCoefficient=C要求n0分支真实处理，不能只在nseq上重写。
25. 最后同nseq StrictMono且Tendsto atTop，每J正样本量并给真实缩放差>J；所有固定参数均在n/J外。
26. 同函数标准¬IsBigO含范数／eventual语义，不是自定义带符号增长谓词。
27. 全n C身份和同尺度身份足以改写已有同律标准否定，但必须在proof实际建立，不能凭定义名认同。
28. 私有product_energy_pos_ae对任意真实概率mu：AE |x|>=1就给每个正n的真实产品AE energy>0，无q或源律假设。
29. 该私有引理必须把各坐标AE合并为共同AE样本，然后从平方和得正；概率用于真实产品投影门。
30. 私有sourceTail_ae_ratio对任意实q、正n、任意样本测度nu及AE正energy成立；不要求nu为产品概率。
31. 第二private即使q<=0也应成立：sqrtq总化可为0，但正分母等价不需除sqrtq／q；不得暗用q>0。
32. 私有ratio_tail_measurable对任意实阈值x和全部n含0；必须允许空Fin0及能量0。
33. generated normalizedTailCoefficient.eq_1对任意ell/q/w/n只是实际原定义展开，没有概率／可积／正率假设。
34. 该generated虽名字在旧定义namespace，仍须按实际module owner纳入本单元；不能按namespace猜漏。
35. actual类型共1public+3private+1generated，全为theorem、无DEF；需完整源与owner Audit交叉核实，不靠作者计数。
36. prettyprinter把公开嵌套let显示为have、隐藏部分instance参数；源TYPE中的hP/letI已单独完整保全，不能误判为少一个概率门。
37. 单次q/w存在见证，Saddle／Rate全称实例化应不改P；不同概率证明项只可能是proofirrelevance，不是换measure。
38. 原R1/root-contractA需要实际固定x反例与同律概率桥，本根应完成这组对象的组装而非重复generic helper。
39. C∞、meaninverse、一般KL9/10、精确ζ24及可选14a不在公开TYPE中，不能因本proof成功宣称它们完成。
40. 待核整个209行proof、全部locals及实际库门，再核机械receipt／history／source／74依赖绑定；不预报最终CORRECT或根关闭。

--- END IMMUTABLE BLIND PREFIX ---

## 完整独立证明终票

STATUS: CORRECT

JUSTIFICATION: 当前209行实际源实现了冻结原A完整无条件接口。只取一次已构造最终q/w/P，再对同q/w实例化规范率与实际鞍点；三个新私有引理真实补全比例尾Borel、同产品AE正能量及正分母事件等价；全部n的系数身份和同实际vCorr把原StrictMono见证与标准否大O原样迁移。全部5个实际owner TYPE及每一续行、各自传递公理已核。未发现数学／来源／实现关键缺口。此为原根源的独立proof接受建议，root正式关闭A仍须lead全文读取、发布和root最终验收，不由本报告擅自更新全局状态。

不可改写盲前缀：155行／11375字节，SHA256 `660d7fa38057b58cd845a8f7a6c0ed3716ab4873e1ddc638a5a7ff43a2d06bcd`。先读实际公开完整TYPE及所有actual owner TYPE并持久化，再读全源proof／原API，机械receipt最后。本节仅追加；初始IN_PROGRESS为历史盲译检查点，不倒改前缀以掩盖审查顺序。

### 1. 冻结范围及原义务对应

实际文件`Shao/OQ3/SourceCounterexampleRoot.lean`完整209行已逐行读完：1–15 imports／namespace，17–65三个authored private，67–144公开完整TYPE，145–206主证明，208–209关闭section／namespace。没有公共DEF，也没有未展开审查的额外源码尾部。

公开TYPE从真实source提取，与冻结scope77第二Lean fence逐字相同；没有新增caller条件、hcont／hW／手给率最小／自由概率序列。107行scope SHA `69ed5bbb5bccadc3b552c75f09b090f775164d4eb0fe9eaa8a1cf0f65f59308b`；直接imports保持SourceRemainderNotBigO及SourceCanonicalSaddle。

原义务取`root-contract.md`§3的固定P／固定x0、中心／离0支持、实际鞍点与全域唯一最小、联合非格点与逃逸近共振、递增时刻缩放误差和标准O(n^-1/2)失败。R1原件137–159、161–257、259–307、(19)/(20)/(25)–(31)及539–558的最终固定律语义已与当前目标对照；原件SHA `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。

root v39 `oq3-review.md`§7明定的未完成部分恰为：一次q/w/P实例化153/156/158，加真实P^n的AE正能量、比例尾事件及同lambda0/vCorr概率系数桥。当前实际proof完成这些明确新增门。原件的一般rho KL9/10、精确ζ24、可选14a不是本root proof的隐含调用；接受链已用真实有限指数分离和严格正h^(3/2)充分差生产所需反例见证。

本门重用已完整独立接受的承重生产链，不声称在本209行模块中重新逐行证明全部74旧模块；实际消费的每个公开接口与新桥则均独立逐义核对，不能以旧CORRECT标签替代本次组装验证。

### 2. 私有 ratio_tail_measurable：17–24

TYPE为任意实阈值x、全部自然n的比例尾MeasurableSet；没有n>0／energy非零输入。20–23先把`Shao.energy`展开为真实有限平方和，目标是Measurable而不是Continuous，`fun_prop`消费有限和／平方／sqrt／实乘除的Borel接口。24由`measurableSet_le measurable_const hratio`构造尾事件。

这里除法在0处按实数总化处理，仍是Borel函数：固定库BorelSpace/Basic.lean601–603的ContinuousInv₀.measurableInv在单点0外用连续逆，并给全局可测逆；乘除可测与Measurable.sqrt连接至实际hratio。它不需要“分母处处非零”，亦未把有0点的比例函数误称全局连续。任意阈值／Fin0和任意能量0样本均被TYPE覆盖。

这是实际所需全n Tail Borel门，不能用已有sourceTail可测性代替；源码确实直接证明了新的比例事件。

### 3. 私有 product_energy_pos_ae：26–45

输入mu真概率及同mu下AE1≤|x|。29–32在真实`Measure.pi(fun _ : Fin n=>mu)`下，以`Measure.tendsto_eval_ae_ae`逐坐标拉回hb，再经`ae_all_iff`得到共同AE样本上的∀i界。不是把多个单坐标AE事实未经合并当作同一事件。

实际库Pi.lean425–426的投影ae滤子接口对应此真产品；概率实例给所需finite／SigmaFinite门。Pi.lean311–313也生产该产品的真概率，故后续real概率不是无限质量toReal总化值。

33–38对共同好样本使用`sq_le_sq₀`：1与|z_i|均非负，hb给1≤|z_i|，从而1²≤|z_i|²=z_i²。没有把任意signed不等式直接平方；`sq_abs`真实消去绝对值平方。

39–43对整个Fin n求和得到(n:ℝ)≤∑z_i²=energy z。44把hn>0真实转换为正实数，45传递得energy>0。n>0只在最后正性门使用，没有为Fin0选一个不存在坐标。TYPE对任意概率mu成立，也不依赖本源q／均值／独立原子质量。

### 4. 私有 sourceTail_ae_ratio：47–65

输入任意实q、正n、任意样本测度nu及同nu的AE正energy；不要求nu为产品或概率。52先限制到实际hE好样本，53用propext把点态iff提升为集合值的等式。

54–55精确展开实际sourceTail：`energy>0 ∧ (sqrtq/4)*sqrt(n*energy)≤sum`，保留原正尾方向。56–58由n>0与hz先得到sqrt(n)*sqrt(energy)>0，之后才调用`le_div_iff₀`。

61–65两方向用`Real.sqrt_mul (Nat.cast_nonneg n)`把sqrt(n*energy)改为sqrt(n)*sqrt(energy)；其实际原库Sqrt.lean365–366前提是乘积第一个因子非负，源码明确提供。前向从h.2得到正分母比例不等式；反向补回hz并改写同乘积，不进行平方，因此不会把负尾混入。

该private不需要q>0，实际proof也没有除q或sqrtq。q≤0时sqrtq总化为0，正分母变形仍然正确；当前原根实例q>1只是其一个合法特例。energy0样本只在nu零测集上排除，未改统计量或声称全空间点态等价。

### 5. 主证明一次取律：145–165

145–147只调用一次`exists_source_fixed_law_not_isBigO`，完整取出q、w、q窗口、严格hw、四HasSum、P概率、中心、AE界、正半轴质量、真正二维非格点、逃逸及模趋1、x0窗口、同nseq／hmono／htop／hn及hnot。取出的旧正率／旧正尺度字段命名_hrate／_hscale但不依赖它们拼另一个尺度。

148首先无条件输出这同q/w及四条真实约束，再把同P的hP作为存在概率证明交付。149–157的P/W/x0/a0/s0/t0/D/Dtail只是上述同对象的本地let。150的letI与producer内部的概率证明不同只涉及Prop证明项；P始终definitionally为同`originalMeasure sourceEll w`，没有换measure。

158由严格hw逐项取le给PR156的非负版本。159–160对同q/w/hm调用`source_canonical_rate_unique_minimizer`，获得完整domK／正literal log／candidate／EReal率与全域唯一最小。161–163对同q/w/hw/hm调用`source_canonical_saddle_hessian_and_scale`，取一个lift及其全部K／导数／正定／几何结论。它们是全称producer，不再求一个独立family的存在见证。

PR156返回的thetaStar等私有局部见证被忽略，不会损坏率结论：candidate率和全域比较由同P的canonical函数确定，与本根选用的Fin2 lift无关。164–165直接输出首组六个原律属性、hdom/hlog及所选lift坐标身份，没有重新构造频率序列或替换非格点律。

### 6. 规范K／实际Hessian／全域最小：159–177、196–201

PR156实际公开TYPE17–46提供同P/W的domK=univ、全部域参数正配分及literal log、候选有限EReal率=saddleRate和全Dtail唯一最小；它的承重源码用真实可积有限指数测试的上界／达到及非候选严格分离器，覆盖全部c>0及off-support点。当前root没有用局部正定性假造全局最小，亦没有对+∞调用toReal。

PR158实际TYPE19–57给全theta的K函数身份，而后给真实HasFDerivAt K和HasFDerivAt(fderiv K)，D来自同w的atomicMeasure实际Cov(X,X²)。新root的166–175保持整个K／theta0／gradient／hessian／v／lambda0／lambda1／vCorr表达式，而不是只在theta0替换一个数值。

该公开producer的承重数学已独立接受：真实P在theta0重倾斜回atomicMeasure，正配分及真矩可积先于一／二阶；基点真实正singleton与中心二次多项式排除给∀u≠0的u·Du>0；同D的逆矩阵／normalVariance／横向界给lambda1>0及正确修正常数。当前实例的严格hw、q窗口和完整hm实际满足全部输入，不增加caller分析条件。

176的`change lambda0=saddleRate at hvalue`及177的`change correctedInverseScale= vCorr⁻¹ at hscaleeq`只把同定义展开式fold为本地let。旧source-01与02的差正是这两行，未改公开TYPE、生产者、lambda或尺度公式；它们不是新假设、cast捷径或数学修补。

196–198在EReal候选率目标中用真实hvalue改写lambda0，再精确使用hRate。没有把无限率toReal；hUnique直接保留同canonicalRate和完整Dtail的比较／唯一等号。候选(a0,q)仍保留c=q>0和弱边界；不同P概率证明的proofirrelevance不会改变domain或EReal函数。

199–201实际交付hK、hfirst、hsecond、hpd、同x0正性／上界；a0>0由q>1再除正4给出；hqeq、hseq、ht0、hvalue、hlambda0、hdet、hlambda1、hv、hscaleeq、hcand、hRate0、hUnique顺次匹配公开合取。所有分母及正根的实域门由同输入下的已生产结论满足，没有奇异逆／sqrt负数总化当正性。

### 7. 同nu的AE正能量与事件桥实例：178–187

178的nu(n)字面为同P在Fin n上的Measure.pi。179–183的Tail与C字面为原根所要求的真实比例事件及其归一化概率，不定义成已有抽象normalized系数来回避桥。

184–185把同P的hb通过`hb.mono (fun _ hx=>hx.1)`提取AE离0下界，交给刚审过的本模块product helper，得到所有正n的真实nu(n) AE energy>0。186–187以该同nu和同hE实例化sourceTail helper。没有换成atomicMeasure产品、finite stage产品或n依赖律。

从公开nu(n)及hP也得到真概率／finite，故这些事件的real概率是实际有限概率。能量是Shao/Basic/FinitePath.lean31的∑z_i²，原sourceTail是SampleBoundary.lean25–27的真实曲边正尾事件。当前root把两者完整连接起来，而不是将同名对象默认认作等价。

### 8. 全n系数身份：188–195

188的hcoeff对全部自然n陈述normalizedTailCoefficient=C。189–192显式分n=0，展开两边定义并用Nat.cast_zero／mul_zero／sqrt_zero／zero_mul归零。这一步没有调用仅适用于n>0的hTail或除sqrt0，也没有要求Fin0样本能量正。

n≠0时193取得hnpos，194只展开normalizedTailCoefficient、C、nu；195先用真实hvalue替换同lambda0，再以`measureReal_congr (hTail n hnpos)`改写同nu产品下两事件的real质量。

独立核实际原库`MeasureTheory/Measure/Real.lean`179–181：measureReal_congr的输入正是同mu下AE集合等式，输出mu.real两质量相等，由Measure.real与measure_congr证明。代码没有以不相关测度的AE等式改写概率。该API虽可无条件对totalized real质量陈述，当前nu真概率已在上下文实际生产，不借无限质量toReal=0造结论。

C使用lambda0而normalized使用saddleRate，其相等不是只凭名称，而由176保留的hvalue真实改写。nu与原定义产品的P也严格相同。因此hcoeff是整个时间函数的身份，覆盖n0而不只是见证子列。

### 9. 同strict子列及标准否大O：202–206

202给每个n的Tail可测性（实际调用本模块ratio helper）及hE/hTail/hcoeff。203保留原取出的同nseq、hmono、htop，只待每J的旧hn改写。

204–205以`simpa only [hcoeff,hscaleeq] using hn J`把每个J的原实际normalized差换成C-vCorr^-1；正nseq、StrictMono、Tendsto及严格>J同时保留，没有以nseq值等于J或C单调作输入。

206同样在整个lambda函数下用这两个全时间／同尺度身份改写hnot，得到真正标准Asymptotics.IsBigO atTop否定。它不是仅声明某个带符号子列增长，也不依赖n0的逆数总化。原PR153公开hnot的已审证明沿真实atTop子列拉回范数最终界，先sqrt(nseq)>0再合法消逆，矛盾于J>B；本root只进行合法函数等价转移，未跨调用其private名字。

严格每J缩放差>J蕴含root-contract最终≥bJ（可取b=1），且same P/x0在所有J/n外一次固定。两个概率系数已经全n实际相等，所以这里确实回答原固定x尾展开余项失败，而非抽象数列性质。

### 10. 全部5个实际owner TYPE及公理（完整续行均已读）

| 实际所属常量 | 完整TYPE所在行（actual-types-02.txt） | 语义／裁定 |
| --- | --- | --- |
| `_private.Shao.OQ3.SourceCounterexampleRoot.0.Shao.OQ3.product_energy_pos_ae` | 1–4 | 任意概率mu、AE abs(x)≥1、正n的真产品AE正energy；26–45证明正确 |
| `_private.Shao.OQ3.SourceCounterexampleRoot.0.Shao.OQ3.sourceTail_ae_ratio` | 5–10 | 任意q／正n／任意nu的AE正energy门下集合等价；47–65无隐藏q正性 |
| `Shao.OQ3.exists_fixed_jointNonlattice_saddleExpansion_counterexample` | 11–105 | 完整全部let／概率／canonical／几何／nu/Tail/C／strict子列／notBigO；67–206逐项生产 |
| `Shao.OQ3.normalizedTailCoefficient.eq_1` | 106–110 | 任意ell/q/w/n的旧normalized定义精确展开；无额外概率／正率假设，非独立分析结论 |
| `_private.Shao.OQ3.SourceCounterexampleRoot.0.Shao.OQ3.ratio_tail_measurable` | 111–112 | 任意阈值和所有n的Borel尾事件；17–24处理除0可测性 |

完整原TYPE已在盲前缀保全，表中仅作语义索引而未删减类型前提。所有实际TYPE不存在省略号；公开prettyprinter用have显示let并隐藏部分实例表达，源中完整hP/letI已先保存并与其逐义核对，没有把隐藏显示误认作漏概率门。

实际Audit.lean用env.getModuleIdxFor?对应moduleNames精确owner==Shao.OQ3.SourceCounterexampleRoot枚举，不按namespace／private前缀猜测。源中3private+1public与owner共5THM一致，额外generated eq_1虽名称位于旧定义namespace仍实际归属本模块，已纳入核查。

generated eq_1与SampleChangeOfMeasure.lean19–21原定义体逐项一致：sqrt(2πn)*exp(n*saddleRate)*同originalMeasure有限pi.real(sourceTail)。不偷加条件、不改P、不替代原定义；本模块hcoeff处展开该定义，不能把它排除在owner清单外。

actual-types-02完整清单112行／8756字节，SHA `8230b32559957991ac6e97c965528f7a3b06bc3dc7e3b1b4972596f6e6a8edc7`。本地交付与remote清单一致，全部5 DECL名与原Audit中的5名集合一致，未只读首行／摘要。

逐项Audit AXIOMS均实际为`[propext, Classical.choice, Quot.sound]`，不是仅声称允许集合；0新axiom、0DEF，1公开根THM+3authored privateTHM+1generated THM。没有其他新owned类型／实例／opaque义务。新209行源扫描未见sorry/admit/axiom/unsafe/native_decide/implemented_by/set_option；正文逐行审查也无这些机制。

### 11. 原根而非helper包装的独立裁定

公开主定理无caller前提；真实最终w的四HasSum／严格正权、同P概率及所有源性质均由一次存在producer交付。它不是“假定存在某个好law或假定误差失败则失败”的逻辑包装。

三个新private有一般接口，但主证明184–195由真实P的已生产hb／hP把它们的全部输入实际消去。它们将旧真实sourceTail概率连接到原问题字面比例尾概率；最后same lambda0／实际vCorr接canonical鞍点和相同规范率。新根因此真正把反例生产链、规范参数和原始统计量接在同一次存在量词下。

root-contract的中心／有界离0／正半轴、联合非格点与逃逸模趋1、正则鞍点实际导数／Hessian正定／正率曲边尺度／全Dtail唯一极小、固定law时间子列及标准余项失败均已输出。无需将原R1精确ζ渐近或一般KL中间路线补为caller假设。

这不表示均值映射邻域逆、全参数C∞或根B的一整套正则族条件已交付。原A本次明确契约是上述实际固定反例接口；root v39§7明确将它与B的邻域逆／谱／矩／Song等义务分开。U20e旧环境缺口未被本proof静默修复或计为接受。

### 12. 最后机械绑定与真实历史

以下在数学／完整源码／全部TYPE审查之后只读核验。未重跑任何成功source、Audit、smoke、图／pins／缓存检查；原raw logs保持remote，只选诊断行／owner及公理块和hash，完整TYPE来自独立无省略清单。

| 产物 | 行／字节 | SHA256 |
| --- | --- | --- |
| 当前source（local／own remote／run source-02一致） | 209／11189 | 13b3da0fa68dd12ffdc8357dae609629d8a95219d4e205417e92899493f37a59 |
| scope77 | 107／10670 | 69ed5bbb5bccadc3b552c75f09b090f775164d4eb0fe9eaa8a1cf0f65f59308b |
| 正式receipt（local／remote一致） | 196／10373 | 5607fdbcd7de41b80a2f02aa7c4bda7b6d2bfea200c7292a9b96b8bbe8a926bf |
| Audit.lean | 41／1814 | 534b2784eb7e69c3f58569aaa771bf1e26003b44e046c78077ced35e3c527dfb |
| audit.log（实际文件名小写audit） | 91／6014 | fcb8711223a24e11d77139d059c1d1151eb20faa4ff260d0c442eed7662f931e |
| 完整TYPE-only清单02 | 112／8756 | 8230b32559957991ac6e97c965528f7a3b06bc3dc7e3b1b4972596f6e6a8edc7 |
| build-history.json | 54／3875 | c68019598cec6bfe3e387310f052634bf968dac64ecd11942d82c620cf2e4cb0 |
| source-01 | 207／11049 | 4804f6e7875b3c2ba553aef93f749bcbed6b00ddd68f09782fc0dcae16a01a7f |
| build-01.log | 295／15790 | 8631978797604a07ea14d44777b7e7883ed6b693f5ca76eb70c840af41d18a5b |
| build-02.log | 8／360 | 0b2a95876f2658cddda1d6c2d3c19bf60e5b1273d6bbfeaf09e0812df1e63331 |

完整attempt01 exit1／5.630280s，两个rewrite未匹配局部lambda0展开式；完整attempt02在唯一新增176–177两条definitionally same change后，首次完整exit0／5.560555s。独立diff核实仅这两行，无公开TYPE／import变化、无partial success、未重复成功source。02非空日志360B，仅line150一条style.haveILetI建议；不是空log，也没有把一条提示内部文字当第二条warning。

第一次owner Audit exit0／5.642328s，明确ROOT_A_FROZEN_DEFINITIONS 0、FROZEN_THEOREMS 1、ALL_THEOREMS 5、ALL_DECLARATIONS 5、AXIOM_GATE PASS。Audit检查目标为theorem、owner新axiom拒绝、所有owned逐项collectAxioms白名单；其成功记录与实际hash／全TYPE集合对应。

原Audit的默认打印深度使公开TYPE有⋯，不能假称那份log已完整保全root类型。独立TYPE-only extractor01因pp.maxDepth／pp.width为未知选项而exit1，证据保留；02源码只设置固定版本支持的`pp.deepTerms true`及`pp.maxSteps 1000000`，按同module owner打印，exit0／5.205214s。实际02清单无⋯或...，本门已完整逐行读112行。打印资源设置不改变root proof或公理；没有重跑source或axiom Audit。

正式receipt透明记载DOTALL名字解析器在formal74核验后发生计数断言失败，随后仅用bounded正则解析原Audit。它不等于一次source失败／重编，也没有修改scope／旧成功证明。本人先误以大写Audit.log读路径发生只读FileNotFound，随后按实际小写audit.log读取；没有因此启动任何Lean或改变产物。

74项正式prerequisite文件local／remote SHA `862533c563930da3ef9a34cc892ebb0172a48ab79411b9e0026eda1b9cb6f1aa`（76行／8014字节）；canonical source-relative compact为`c0e75a48979e6cf28bcd1f232624543b313425df2d0280da7057c32ede836703`。本门定向fresh读取当前own74源，缺失0／SHA差异0；与声明时独立复现的PR153正式67字典、PR158正式25字典及两seed并集一致。没有重做完整Mathlib图或旧成功源检查。

当前branch实际为`feat/oq3-source-counterexample-root`，HEAD `59a531b89eff7c11e4fc53583067f2cd3b53a517`，parent accepted v39 tree `43577d0d66de8325a756c9ac25e43e53809c3525`；status仅`?? Shao/OQ3/SourceCounterexampleRoot.lean`。未有本root commit／PR或新下一scope；旧冻结heads未由本review修改。

构建历史与Audit记录均为CPU14–17、native8192MiB／j4、autoImplicit=false、只读U20c单Shao-root import-view，原Mathlib Lakepaths保留。沿用已经实际验证的view／accepted objects，不复制cache、不重扫pins或root成功门；既有Lean4.36.0-rc1及mathlib807d3836固定。本人全部server命令只读且限CPU14–17，无Lean／probe／build／Audit／cache写／spawn／commit／pub，未触外部CPU0–9／80GiB任务。

### 13. 最终消除及剩余边界

消除的原A最后义务：一次最终law量化，真实规范鞍点／Hessian／全正尾域唯一率极小与同lambda0/vCorr；真实P^n的全n Tail Borel、n>0 AE正能量、未平方丢符号的实际比例事件桥；全n归一化系数身份及同strict子列／标准notIsBigO。当前源是原始固定x反例根接口的完整实现，不是仅generic helper。

独立proof verdict为CORRECT，建议lead全文核读后接受／发布并交root按原根流程最终验收。发布和root验收尚未发生于本次观察，不以本报告直接改root账。数学上原A明确固定律接口的所有公开合取均已真实生产，没有剩余caller分析门。

其他原B/C/D、均值inverse／全参数邻域正则性、一般KL9/10、精确ζ24、可选14a、随x变化一致性仍不在此proof结论内。U20e保留CRITICAL环境缺口／未实施；U21a已接受部分也不自动关闭完整C。没有最弱条件、beta最优或整项OQ3完成主张。

FINAL STATUS: CORRECT — 冻结209行原A实现、全部5实际所属TYPE与标准公理、真实机械历史绑定均通过本独立完整proof门；等待lead整份读取／发布及root正式验收，当前不擅自宣布A/B/C/D全局账关闭。
