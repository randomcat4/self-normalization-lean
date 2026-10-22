# U19c SourceLogPartitionDerivatives 完整独立证明审查

STATUS: IN_PROGRESS

## 不可改写盲审前缀：实际唯一公开TYPE

本轮先仅提取actual源的公开完整TYPE，不读该源private／proof体、作者route／notes或receipt／build／Audit证据。已有声明上下文存在，但不把先前声明CORRECT视为实际proof正确。该模块无公开DEF。

```lean
theorem source_log_partition_first_and_second_derivatives
    (q : ℝ) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    let K : (Fin 2 → ℝ) → ℝ := fun theta =>
      Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)
    let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
    let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
    let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
      (pr 0).smulRight (q / 4) + (pr 1).smulRight q
    let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
      ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
    HasFDerivAt K gradient theta0 ∧
      HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0
```

独立完整量词及类型翻译：

1. 对全部实数q成立；没有qwindow或正q的额外输入。
2. w为同一个AtomicIndex→ℝ函数，所有w_i非负，允许零权重。
3. 对每个Fin4约束行，真实w_i*feature(sourceEll,fixedAtom_i)的HasSum等于同q的target行。
4. P结论内固定为originalMeasure sourceEll w；不是caller可任选law。
5. K结论内固定为P上的quadratic exponential integral的标准实log。
6. 参数空间Theta=Fin2→ℝ，指数按theta(0)*x+theta(1)*x²排列。
7. 鞍点theta0结论内固定为(8sourceEll,−sourceEll)。
8. D固定为同w的atomicMeasure之actual parabolaCovariance，而不是P的协方差。
9. pr_i为Theta到ℝ的连续线性投影。
10. gradient是Theta→Lℝℝ，作用于h给h0*q/4+h1*q。
11. hessian是Theta→Lℝ(Theta→Lℝℝ)，因此是有序双线性连续映射。
12. pr_i.smulRight(pr_j.smulRight(Dij))作用h、k为h_i*k_j*Dij。
13. 第一合取要求实际K在实际theta0有这个真实Fréchet导数。
14. 第二合取要求实际函数theta↦fderiv ℝ K theta在同theta0有这个真实Fréchet导数。
15. 第二项不是方向二阶导数或单点值展开；必须识别theta0邻域里的真实fderiv函数。
16. 所有P/K/theta0/D/pr/gradient/hessian用同w/q/sourceEll，次序无存在量词或换law。
17. 没有输入IsProbabilityMeasure、Integrable、配分正性或C²假设；proof必须生产这些门。
18. 没有基点严格正、det>0或非退化假设；不得在证明中偷偷加强。
19. K本身为总定义表达式；不能用非可积积分归0或log0来冒称真实logMGF导数。
20. 证明方向上应从第0约束获得真HasSum w 1，再真实π／P概率及AE固定界。
21. AE有界支持应足以给全参数指数加权多项式真Integrable，而不只给theta0。
22. 需要共同参数邻域：先AE样本，再全部邻域theta的同一导数范数主控；不能逐theta另选AE集合。
23. 积分微分要核F的最终AE强可测、F(theta0)真可积、F'强可测、主控可积和真实点态Fréchet导数。
24. 若以M_j(theta)=E_P[X^j exp(theta·(X,X²))]作局部记号，M0必须真实严格正再求log／inverse导数。
25. 所有theta的一阶公式可识别fderiv K函数；其后才能用商／scalar-CLM规则证明第二项。
26. 在theta0，归一化M_j/M0应通过实际P.retilt=π还原为π矩；不能把未归一化M_j直接换成π矩。
27. 真L²门必须先于variance_eq_sub／covariance_eq_sub；两交叉项方向需要用actual D对称性核清。
28. 即便库积分倾斜恒等式总定义，实际语境仍必须已生产weighted moment有限性与正分母。
29. 需完整审所有privateDEF body、privateTHM及actual generated TYPE，不能按名字／作者统计预猜。
30. 本目标不定义root canonical K，不证明domK／扩展sup／局部均值逆／全局唯一性或root闭合。

以上为读实现之前的独立审查目标及疑点清单；后续来源与证明审查只追加，不改写此前文本。

## 盲审前缀续：真实来源的独立数学重建（仍未读实现）

R1真实140–145行给P=π exp(−ellY)/Z及exp(8ellX−ellX²)倾回同π；149–153行给同π的EX=q/4及同theta0鞍点坐标；239–245行给Delta=Covπ(X,X²)。因此本TYPE要求的是原P真实log配分在theta0的梯度和Hessian身份，不能把P直接当π或用别的协方差矩阵。
独立预期：M_j=E_P[X^j exp(theta·(X,X²))]，所有theta真可微后fderiv K=(M1/M0)pr0+(M2/M0)pr1；在theta0归一化矩还原π矩，商导数的系数为EX²−EX²的平方／EX³−EX·EX²／EX⁴−(EX²)²，即真实D四项。此处第一项的准确含义为Eπ[X²]−(Eπ[X])²，不是两个相同数相减。
需警惕：M0>0、共同邻域算子范数主控、局部fderiv身份先于二阶、同law retilt归一化、真MemLp2先于方差、输出双线性项的外内方向；全q／允许零权重／退化D均不应清分母除q或det。
已逐字比对actual public TYPE与scope70唯一fence完全相同。scope的路线只作为待核义务清单；此时仍未读actual private／proof体或作者receipt／build／Audit。
下文实现审查将追加于此前；盲审前缀完整字节不得改写。

## 一、审查顺序、冻结含义与来源

前70行5667B为不可改写盲审前缀，SHA256=9aa6e232a7061a91e8b5cff1c736ea316897d099701aebdbecfcb52b14745f5f；其中先落盘的实际TYPE盲译62行4455B，SHA256=f404f99c10eae09e5d61f5ac7620a3f42d824850700ab1fa70a519695333de1c。页首IN_PROGRESS是历史状态，末节为最终裁决。
本轮顺序实际为：仅actual公开TYPE并持久化→R1及scope对照并追加来源盲审→完整253行源及主API→全部23 actual DECL／TYPE完整114行→最后receipt／build／Audit程序／绑定机械证据。未读作者implementation／future／candidate／scanner笔记。
公开TYPE与scope70唯一fence逐字相同，包括P、K、theta0、D、pr、gradient、hessian全部let；三imports和namespace／scopes亦未改变。
R1真实140–145行的反向倾斜与正向重倾斜、149–153行的q/4和theta0、239–245行的实际协方差含义，均由同w/q/sourceEll兑现。此处提供的是这些身份的真实解析证明，不自行把R1全局最小性叙述当成已验证前置。
本票审查253行全部implementation，包括6privateDEF完整body、6privateTHM完整proof、公开main全部locals与10实际生成项；未将statement CORRECT或kernel绿灯代替语义。

## 二、六个私有定义的实际完整意义（源20–43）

coordinate i=ContinuousLinearMap.proj i，是真实Theta→Lℝℝ坐标投影，Theta=Fin2→ℝ；没有自定义范数或拓扑。
weightedMoment mu k theta=∫ x^k exp(theta(0)x+theta(1)x²) ∂mu，使用同一个mu和标准实Bochner积分。
momentSlope mu k theta=M_(k+1)•coordinate0+M_(k+2)•coordinate1，是真实CLM，不是数值向量代理。
normalizedMoment mu k theta=M_k/M_0，分母由后续partition_pos在实际使用环境证明正，不是随意归一化常数。
normalizedSlope mu k theta=(R_(k+1)−R_k R_1)•coordinate0+(R_(k+2)−R_k R_2)•coordinate1，正是归一化矩的一阶商导数。
partitionGradient mu theta=R_1•coordinate0+R_2•coordinate1；这仅是private指定表达式，后续必须证明它等于真实fderiv K。
全部private名称只在本module消费。没有公开新K／domK／globalRate，也没有借跨模块private helper生产解析假设。

## 三、六个私有证明的逐门核查

### 1. weighted_integrable及partition_pos（45–55）

weighted_integrable的实际输入为同mu真概率、AE |x|≤beta、任意自然k与任意实参数theta，beta=4+sqrt10。
它调用公开integrable_continuous_of_fixed_bounds mu hb；x↦x^k exp(theta(0)x+theta(1)x²)真实连续，fun_prop解决的是这项实际连续性，不是把Integrable当成自动公理。
已接受InverseTilt.lean26–34的该公开helper先在固定实紧区间取连续函数界，再Integrable.of_bound，消费真概率有限性和同AE支持；适用于全theta，而非把小球结果扩充到全参数。
partition_pos把k=0化成原指数积分，随后用integral_exp_pos；该库命题在概率所给NeZero及真实exp Integrable之后给严格正M0。没有log0／不可积tilt0捷径。
这两个证明保留k=0、theta=0及退化law；不需要严格正基点或非奇异协方差。

### 2. weightedMoment_hasFDerivAt（57–103）

源60–64把实际F(t,x)=x^k exp(t0*x+t1*x²)及CLM值F'完整写出，没有抽象caller输入导数。
65–75的hdiff先用两个真实坐标CLM的hasFDerivAt、常数乘和add，给指数中线性式的Fréchet导数；再exp链式及乘x^k。
pow_add及ring把系数x^k*x、x^k*x²精确改为x^(k+1)、x^(k+2)，对全部实x、全部t成立，负x和k0均无绝对值替代或符号丢失。
76–78的hcont是(t,x)↦F'(t,x)进入实际CLM空间的联合连续性；有限个连续实系数乘固定CLM再相加成立。
79–82先构造closedBall(theta,1)×Icc(−beta,beta)这个完整紧乘积，然后才取一个C控制联合算子范数。
Finite Pi的ProperSpace来自真实ProperSpace.lean132–136的pi_properSpace；其closedBall按标准Pi范数紧致，Icc为真实实紧区间。没有引入新局部instance或换范数。
实际Analysis/Normed/Group/Bounded.lean91–95以to_additive产生IsCompact.exists_bound_of_continuousOn；结论是∃C,∀p∈紧集,‖F'(p)‖≤C，证明经连续像的有界性。不是只给逐参数有界。
83–86的hbound先filter_upwards同一hb得到AE x，再intro任意t∈ball(theta,1)，由ball_subset_closedBall和abs_le把同(t,x)送入hC。
因此量词实际是∀AE x,∀邻域t，共同C先固定；没有把“每t各自AE”非法交换。C只需有限并满足真实范数界，不需要另加C>0假设。
87–92分别建立所有t的F(t) AE强可测和F'(theta) AE强可测；后者为实际连续CLM值函数，而非只证明实坐标可测后省略输出空间。
93–96调用的ParametricIntegral.lean206–212完整输入逐项实有：ball_mem_nhds、最终AE强可测F、weighted_integrable、F' AE强可测、共同hbound、integrable_const C、以及全x/t真实hdiff。
原库实现213–226把同一邻域内真实导数上界转成Lipschitz主控后使用积分微分；它给真正HasFDerivAt，不是标量方向deriv或形式微分。
97–101独立用两个weighted_integrable的smul_const给F'两项真Integrable，先于integral_add及integral_smul_const把积分导数识别为momentSlope。
所以hd输出的确是实际weightedMoment函数及其真实CLM导数；没有以CLM积分总化或非可积拆分凑出momentSlope。
本lemma对任意k及任意theta成立，这是后续识别全fderiv函数的关键强度。

### 3. normalizedMoment_hasFDerivAt（105–119）

108由严格partition_pos取得实际M0(theta)≠0。109–110用Deriv/Inv.lean56–57的hasDerivAt_inv（导数−(x²)^-1）与真实weightedMoment0 Fréchet导数复合。
111再与M_k的真实导数相乘；113–114逐函数把M_k*M0^-1识别为actual normalizedMoment。
115–119在CLM ext v之后用实际momentSlope／normalizedSlope展开并field_simp [hz]，唯一清分母为已真实非零M0；不除q、detD、方差或原子权重。
所得系数正好是M_(k+1)/M0−(M_k/M0)(M1/M0)及k+2对应项，负号来自逆导数，未把归一化导数误作未归一化矩导数。

### 4. logPartition_hasFDerivAt（121–131）

125–126先用所有theta的真实weightedMoment0导数，再用Log/Deriv.lean150–152的HasFDerivAt.log及partition_pos非零门。
127–131在CLM ext v后把M0^-1•momentSlope0改成partitionGradient；这是标准实log的实际导数。M0严格正的概率意义已先生产。
lemma仍对全部theta成立，绝不是仅在theta0的形式梯度值。

### 5. source_normalized_moment（133–159）及总化审计

实际输入只为同w的hw≥0与真HasSum w 1，输出每个自然k、同P/theta0下normalizedMoment=同π的x^k积分。
137建立同P真概率，138建立同P AE界；139–141明确构造weighted_integrable的hi和partition_pos的hp。
hi/hp虽然最后rw／algebra没有直接消费，但它们是真正由当前假设生产的命题，证实该语境所有加权积分有限且分母严格正；不是把缺失门藏在unused变量名后。
142–145的he对所有实x精确证明theta0(0)*x+theta0(1)*x²=sourceEll*(8x−x²)，正向重倾斜符号正确。
146–152先展开normalizedMoment／weightedMoment、k0分母与he，再用公开originalMeasure_retilt把π识别为同P.tilted(ellY)，然后实际MeasureTheory.integral_tilted。
已接受InverseTilt.lean116–127的retilt内部先有同π真概率及反向exp Integrable，再用tilted_neg_same，不以零measure总定义分支取等。
库Measure/Tilted.lean230–232确实是无额外前提的总定义积分恒等式；这里不会仅因它无前提就允许虚假概率解释，因为137–141已另立真实有限／正门。
153–159的hf只是(expf/A)*x^k=(x^k*expf)/A的实恒等式；Bochner/Basic.lean295–297的integral_div为固定实常数除法恒等式，没有重新选择normalizer。
最终输出是M_k/M0=EπX^k，绝非M_k直接等于π矩。π的x^k也由相同固定支持和概率真可积；main后续更建立了全部幂的真L²界。
hi/hp未进入最后等式的形式依赖是一项可见实现事实，非证明缺口；它们的真实性以及全参数partition_pos／weighted_integrable在本module其他导数中实际消费，阻止总化捷径解释。

## 四、公开main全部locals及两个最终真实导数（178–250）

178–179由hm0真实给HasSum w1；182–183分别建立同P与同atomicMeasure w概率，不更换w/q或要求所有w>0。
184–187同P AE界及source_normalized_moment给每k的hR；188–192公开atomicMeasure_mean和真实第四约束积分给EXπ=q/4、EX²π=q。
193–198以连续x^k、实际atomicMeasure AE界及MemLp.of_bound证明全部k的MemLp(x^k)2；界为beta^k，abs_pow和非负幂单调对负x仍成立。
199–200由此得到真实X和X²的L²门。它们先于201–219的variance_eq_sub及covariance_eq_sub，没有借总化方差值凑协方差。
201–204给D00=EX²−(EX)²；205–212给D01=EX³−EX*EX²；213–214的D10=D01是actual parabolaCovariance定义的rfl；215–219给D11=EX⁴−(EX²)²。
Covariance.lean54–65真实消费两L²及概率以确保乘积／差的积分合法；Variance.lean226–228也消费MemLp2。x³和x⁴由先前全部k界真实有限。
220–224把partitionGradient(theta0)通过hR/hmean/hsq识别为指定pr0.smulRight(q/4)+pr1.smulRight(q)；这不是把数值梯度冒充CLM身份。
225–237对两个CLM方向ext v u，完整展开Fin2两重和、smulRight_apply及normalizedSlope，再用hR1–4／h10／h00／h01／h11和ring。
左侧作用于(v,u)为u0*[v0(D00)+v1(D01)]+u1*[v0(D01)+v1(D11)]，右侧为Σ_i,j v_i*u_j*Dij；交叉项由实际D10=D01对齐，既未转置出错也未漏去一个交叉项。
238得到theta0的真实一阶hfirst；239–240用fderiv_eq(logPartition_hasFDerivAt P hb)建立整个参数函数的真实fderiv等式。
实际FDeriv/Basic.lean420–423的fderiv_eq消费∀theta HasFDerivAt并逐点唯一性识别，故这里不是仅单点值相等后非法对等号求导。
241–243用两条normalizedMoment_hasFDerivAt的smul_const并add，真实证明CLM值partitionGradient函数的Fréchet导数。
244用完整hHess身份替换第二导数CLM，245用hgrad替换第一导数；249才用整个函数等式←hfderiv将hsecond改成真正theta↦fderiv K的导数。
246–250仅消结论let及weightedMoment0的pow_zero／one_mul、P/theta0/coordinate定义，完整回到冻结public K/gradient/hessian；没有另造一个Taylor K或代理law。
本proof不除q、detD或方差，不求D逆，不消费正基点、qwindow或非退化假设；全q／零基点／退化D的声明前提没有被加强。

## 五、全部23 actual DECL／TYPE与公理

我在上述完整proof和主API审查后，实际逐项读完server actual-declarations.txt的114行全部长续行；没有只看首行、作者计数或生成名字。
该选块SHA256=3a448fce8e660993cbe82076464c6420ed66e4a78ad5d21c9b5324f1afd46a97；后期核它逐字等于真实Audit.log前114行DECL／TYPE／AXIOMS选块。
6privateDEF为coordinate／weightedMoment／momentSlope／normalizedMoment／normalizedSlope／partitionGradient，完整body已在本票第二节及source20–43审明。
6privateTHM为weighted_integrable／partition_pos／weightedMoment_hasFDerivAt／normalizedMoment_hasFDerivAt／logPartition_hasFDerivAt／source_normalized_moment，全部真实输入条件及结论与上节逐门审查相符。
唯一publicTHM完整TYPE保留全部q/w/hw/hm及全部let和两HasFDerivAt合取，没有把二阶目标变成标量deriv。
10生成项实际为：上述6DEF各自eq_1；另momentSlope._proof_1:ContinuousAdd ℝ、._proof_2:SMulCommClass ℝ ℝ ℝ、._proof_3:ContinuousConstSMul ℝ ℝ，以及weightedMoment._proof_1:NeZero(1+1)。
这些四个proof是实际标准实例类型，不是隐藏额外导数／可积假设；NeZero(1+1)是实际输出中的标准数值非零实例，不要求q≠0；本票不从pretty-printer省略的参数额外猜测其通用载体。
所有23项中22项传递公理恰为[propext,Classical.choice,Quot.sound]；weightedMoment._proof_1仅[propext]。不能误说每项都有完整三公理。
以下原样保留官方选出的全部23实际类型与各自公理，便于独立复核：

```text
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.weightedMoment_hasFDerivAt
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (k : ℕ) (theta : Fin 2 → ℝ), HasFDerivAt (Shao.OQ3.weightedMoment✝ mu k) (Shao.OQ3.momentSlope✝ mu k theta) theta
AXIOMS [propext, Classical.choice, Quot.sound]
DECL Shao.OQ3.source_log_partition_first_and_second_derivatives
TYPE ∀ (q : ℝ) (w : Shao.OQ3.AtomicIndex → ℝ),
  (∀ (i : Shao.OQ3.AtomicIndex), 0 ≤ w i) →
    (∀ (k : Fin 4),
        HasSum (fun i => w i * Shao.OQ3.constraintFeature Shao.OQ3.sourceEll (Shao.OQ3.fixedAtom i) k)
          (Shao.OQ3.constraintTarget q k)) →
      have P := Shao.OQ3.originalMeasure Shao.OQ3.sourceEll w;
      have K := fun theta => Real.log (∫ (x : ℝ), Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P);
      have theta0 := ![8 * Shao.OQ3.sourceEll, -Shao.OQ3.sourceEll];
      have D := Shao.OQ3.parabolaCovariance (Shao.OQ3.atomicMeasure w);
      have pr := fun i => ContinuousLinearMap.proj i;
      have gradient := (pr 0).smulRight (q / 4) + (pr 1).smulRight q;
      have hessian := ∑ i, ∑ j, (pr i).smulRight ((pr j).smulRight (D i j));
      HasFDerivAt K gradient theta0 ∧ HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.partitionGradient
TYPE MeasureTheory.Measure ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.normalizedMoment_hasFDerivAt
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (k : ℕ) (theta : Fin 2 → ℝ),
      HasFDerivAt (Shao.OQ3.normalizedMoment✝ mu k) (Shao.OQ3.normalizedSlope✝ mu k theta) theta
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.momentSlope._proof_1
TYPE ContinuousAdd ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.weighted_integrable
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (k : ℕ) (theta : Fin 2 → ℝ),
      MeasureTheory.Integrable (fun x => x ^ k * Real.exp (theta 0 * x + theta 1 * x ^ 2)) mu
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.coordinate
TYPE Fin 2 → (Fin 2 → ℝ) →L[ℝ] ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.normalizedSlope.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ),
  Shao.OQ3.normalizedSlope✝ mu k theta =
    (Shao.OQ3.normalizedMoment✝ mu (k + 1) theta -
          Shao.OQ3.normalizedMoment✝ mu k theta * Shao.OQ3.normalizedMoment✝ mu 1 theta) •
        Shao.OQ3.coordinate✝ 0 +
      (Shao.OQ3.normalizedMoment✝ mu (k + 2) theta -
          Shao.OQ3.normalizedMoment✝ mu k theta * Shao.OQ3.normalizedMoment✝ mu 2 theta) •
        Shao.OQ3.coordinate✝ 1
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.momentSlope._proof_2
TYPE SMulCommClass ℝ ℝ ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.momentSlope._proof_3
TYPE ContinuousConstSMul ℝ ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.weightedMoment._proof_1
TYPE NeZero (1 + 1)
AXIOMS [propext]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.normalizedSlope
TYPE MeasureTheory.Measure ℝ → ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.momentSlope
TYPE MeasureTheory.Measure ℝ → ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.partitionGradient.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (theta : Fin 2 → ℝ),
  Shao.OQ3.partitionGradient✝ mu theta =
    Shao.OQ3.normalizedMoment✝ mu 1 theta • Shao.OQ3.coordinate✝ 0 +
      Shao.OQ3.normalizedMoment✝ mu 2 theta • Shao.OQ3.coordinate✝ 1
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.weightedMoment
TYPE MeasureTheory.Measure ℝ → ℕ → (Fin 2 → ℝ) → ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.normalizedMoment
TYPE MeasureTheory.Measure ℝ → ℕ → (Fin 2 → ℝ) → ℝ
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.weightedMoment.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ),
  Shao.OQ3.weightedMoment✝ mu k theta = ∫ (x : ℝ), x ^ k * Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂mu
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.logPartition_hasFDerivAt
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (theta : Fin 2 → ℝ),
      HasFDerivAt (fun t => Real.log (Shao.OQ3.weightedMoment✝ mu 0 t)) (Shao.OQ3.partitionGradient✝ mu theta) theta
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.source_normalized_moment
TYPE ∀ (w : Shao.OQ3.AtomicIndex → ℝ),
  (∀ (i : Shao.OQ3.AtomicIndex), 0 ≤ w i) →
    HasSum w 1 →
      ∀ (k : ℕ),
        Shao.OQ3.normalizedMoment✝ (Shao.OQ3.originalMeasure Shao.OQ3.sourceEll w) k
            ![8 * Shao.OQ3.sourceEll, -Shao.OQ3.sourceEll] =
          ∫ (x : ℝ), x ^ k ∂Shao.OQ3.atomicMeasure w
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.partition_pos
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) → ∀ (theta : Fin 2 → ℝ), 0 < Shao.OQ3.weightedMoment✝ mu 0 theta
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.momentSlope.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ),
  Shao.OQ3.momentSlope✝ mu k theta =
    Shao.OQ3.weightedMoment✝ mu (k + 1) theta • Shao.OQ3.coordinate✝ 0 +
      Shao.OQ3.weightedMoment✝ mu (k + 2) theta • Shao.OQ3.coordinate✝ 1
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.coordinate.eq_1
TYPE ∀ (i : Fin 2), Shao.OQ3.coordinate✝ i = ContinuousLinearMap.proj i
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceLogPartitionDerivatives.0.Shao.OQ3.normalizedMoment.eq_1
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (k : ℕ) (theta : Fin 2 → ℝ),
  Shao.OQ3.normalizedMoment✝ mu k theta = Shao.OQ3.weightedMoment✝ mu k theta / Shao.OQ3.weightedMoment✝ mu 0 theta
AXIOMS [propext, Classical.choice, Quot.sound]
```

## 六、数学后才核的机械凭据与绑定

Audit.lean实际用公开target stem及_private.Shao.OQ3.SourceLogPartitionDerivatives前缀枚举，检查target确为theorem、全部选中常量无新axiom、Lean.collectAxioms均在白名单。
它不是module-index穷举证明；本票把完整253行源的所有声明与23实际输出联合核对：6DEF＋6privateTHM＋1publicTHM＋10generated=23owned／17THM，未见其他公开声明或私有辅助遗漏。
作者receipt数学叙述在本轮全部proof／TYPE审查后才读取，仅作执行历史与绑定记录，不作证明依据。
本地draft、server worktree、run快照及source-02.lean同253行13173B，SHA256=18c42fc0bea7cdaf1fb69acba96caf452a35eddc9819e29d211fe94a4aa32f07。
local／remote scope70同37行7667B，SHA256=66a18870fa58a2f4ca0853c5fe9ac0f6d27b292972a8feb6f6c089c0c502d6b9；完整actual publicTYPE与scope fence逐字一致。
正式声明票207行19423B SHA256=e1807e44328e5374523ca0b8dafa68ac9fb6da6318c569ae55ae20b1448055a9原字节保留；本票没有覆盖它。
local／remote正式receipt同374行13533B，SHA256=6e61368fed021ce463371c837e051072074889173be8c276e3472fe67431ce78，状态仍为AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW，正确区分作者门与本票。
Audit源39行1699B SHA256=4e5590c8dfc36319f8fb5e2dddae63112a5c42fcdda2cef774504294560a68a5；Audit.log119行7653B SHA256=7ec6611f64589bfbc09ad563a781b1dbbdf585c52c0ea2f5aaa9da43142cbc83。
actual-declarations.txt114行7537B SHA256=3a448fce8e660993cbe82076464c6420ed66e4a78ad5d21c9b5324f1afd46a97；真实Audit摘要打印0publicDEF／1target／17THM／23owned／AXIOM_GATE PASS。

完整build01为252行source9fe32f2a71e7af39b82376943bc7e06db10bc0807fa6d5182e0cefaec270c66f，exit1；日志140行8842B SHA256=98adcd27bcf8c24d6032fb58ab9658979f9dc67c2a2d93f5f913dd562db9138b。
我只在server读取必要错误摘要及两源diff：6条错误诊断均来自同一紧乘积表达式换行点记号解析链；改动只把紧集合命名为显式hcpt后再取exists_bound。
完整build02为当前253行源首次完整success，exit0／5.608817秒；日志132行7865B，SHA256=acb4088ba6995447f238ac26d758f9678d821798b4592b7badaf844171a05d50。
该日志不是空日志：server逐条按实际文件:行:列warning记录核得23条、error0。类型为弃用simp别名、unused simp args、tactic sequencing及let-instance建议；不把hint中的文本重复算作独立error。
这23条非阻塞warning透明保留，不修改冻源清理、不降低proof设置或把warning写成0；01失败及02成功快照均保留，无partial success或未改源重复成功记录。
正式命令为CPU14–17 taskset下lake env lean -M8192 -j4 -DautoImplicit=false，target02首次成功后首Audit亦exit0；本轮只读现成产物，没有重新执行Lean／probe／build／Audit／root smoke。
当前target olean实际存在；本票不对整个共享cache目录宣称hash冻结，也没有下载完整原始build／Audit日志到本地。

8正式前置prerequisite-hashes.json为10行821B，文件SHA256=c90c1ebd9d25345ff17457101e14be62995788ebf49a596027fd0b43e6f31536。
我在本门机械阶段fresh逐项核8个当前server源SHA与该字典全部匹配；canonical相对路径键sorted compact SHA256=07ac7a5a474ea797a09196c33283033d7200dec1693cd15350e53abb6f39181a。
其中实际承担本proof的AtomicMeasure59ddc48f、InverseTiltc7e7d19e、RegularCovariance0add3476、FiniteConstraints800d9db8等均保持声明门所核同源；其余FiniteStageMeasure1a32fb90、PositiveRate8e727078、SourceStarter0e2a0816、SummableAtoms0ea4c64f亦一致。
沿用本审查者已完成的精确三imports公开图／pins／缓存证据：8Shao2777Mathlib physical、public2531内部＋189外部停止；未为本门重新扫描图、哈希稳定51对象或重复成功smoke。
Mathlib实际HEAD=807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA256=d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4；lake-manifest.json SHA256=40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。
实际Git观察为branch feat/oq3-source-log-partition-derivatives、HEAD ded5b45059cf80861712f61c86170243d5e87fc2；status仅?? Shao/OQ3/SourceLogPartitionDerivatives.lean，尚无本单元commit／PR。
该HEAD是root批准v37 accepted正常新建分支的基线，不把B148旧head到此head的正常建分支误判为前置漂移；本票未merge／rebase／reset／fetch／retarget。
所有本轮remote项目读取均taskset -c 14-17；未启动重型进程、触碰CPU0–9／80GiB外部任务、ulimit-v、共享cache／pins或其他作者文件。只新写本报告及授权远端报告。

## 七、最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: 已独立审查全部253行实际proof、6privateDEF body、6privateTHM／main全部locals、固定主API以及全部23 actual TYPE／各自传递公理。共同紧乘积界确实先于AE x后的全部邻域参数，真实weighted Integrable与M0>0先于log／inverse导数；全theta一阶HasFDerivAt先识别整个fderiv函数，再求实际CLM值梯度导数。归一化moment通过同P真实retilt还原同π，真MemLp2先于actual variance／covariance，双线性两交叉项及全部冻结let精确对齐。未加强q／权重／非退化前提，未发现数学、声明对应或公理缺口。现成首次成功build及首Audit仅作为数学审查后的机械确认，23条warning不改变此结论。

原target→本次消除：R1(146–159／239–257)实际逆倾斜原律log配分的gradient=(q/4,q)与Hessian=同π的Cov(X,X²)，现已有真正HasFDerivAt K及HasFDerivAt(fderiv K)，而非标量二阶方向／Peano代理。
直接consumer→root canonical K的同P/w/q/sourceEll鞍点及Hessian身份适配，并可把U19b字面几何常数桥接到同一D；本模块0publicDEF，不创竞争shared K／domK。
仍OPEN→本票不自动证明root canonical domK／扩展值sup桥、均值映射局部逆、全局鞍点唯一性／最优性、general KL9/10或完整原始反例组装；这些须各自actual接口与证明。原根A/B/C/D全部OPEN。独立CORRECT供lead全文读取后决定接受／提交／发布，本审查不执行commit或PR。
