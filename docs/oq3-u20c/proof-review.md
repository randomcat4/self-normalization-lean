# U20c v2 SourceCanonicalRate 完整独立证明审查

STATUS: IN_PROGRESS

## 不可改写 actual TYPE 盲审前缀

本前缀先仅从当前实际源码提取完整公开类型，未读取本次实际证明体、Audit／actual声明输出或author receipt。
我已有本单元v1数学声明及v2环境审查上下文；此处独立重新解释实际类型，不把此前声明CORRECT或环境门当作证明已正确。
0公开DEF，唯一公开THM的实际完整类型如下；`: = by`之后的证明体未读（此处符号说明不属于源码）。

```lean
theorem source_canonical_rate_unique_minimizer
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w hw
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    let D : Set (ℝ × ℝ) :=
      {z | 0 < z.2 ∧ (Real.sqrt q / 4) * Real.sqrt z.2 ≤ z.1}
    bivariateMGFDomain P W = Set.univ ∧
      (∀ theta : bivariateMGFDomain P W,
        (0 < ∫ x : ℝ, Real.exp
          ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P) ∧
        bivariateLogMGF P W theta =
          Real.log (∫ x : ℝ, Real.exp
            ((theta : ℝ × ℝ).1 * x + (theta : ℝ × ℝ).2 * x ^ 2) ∂P)) ∧
      ∃ theta0 : bivariateMGFDomain P W,
        (theta0 : ℝ × ℝ) = (8 * sourceEll, -sourceEll) ∧
        ((theta0 : ℝ × ℝ).1 * (q / 4) + (theta0 : ℝ × ℝ).2 * q -
          bivariateLogMGF P W theta0 = saddleRate sourceEll q w) ∧
        (q / 4, q) ∈ D ∧
        bivariateLegendreRate P W (q / 4, q) = (saddleRate sourceEll q w : EReal) ∧
        ∀ z ∈ D,
          bivariateLegendreRate P W (q / 4, q) ≤ bivariateLegendreRate P W z ∧
          (bivariateLegendreRate P W z = bivariateLegendreRate P W (q / 4, q) ↔
            z = (q / 4, q))
```

### 独立完整量词／语义翻译

1. q是调用者给定的同一个实数，要求严格窗口1<q<103/100。
2. w是调用者给定的同一个AtomicIndex→ℝ函数，各权重非负。
3. 不假设每个权重严格正，也不向调用者索取非退化协方差。
4. 四个真实HasSum约束对全部Fin4索引成立；权重乘的是fixedAtom上的实际constraintFeature。
5. 原律P固定为originalMeasure sourceEll w，后面全部域／log／率使用这一P。
6. P的IsProbabilityMeasure实例由完整TYPE中的letI证明体生产，实际消费hw与hm0化简后的HasSum w 1。
7. 不是另外一个手工概率假设，也不能在proof里换一个有利的law。
8. 统计量W确切为x↦(x,x²)。
9. D的点z=(a,c)要求c>0以及(sqrt q/4)·sqrt c≤a，包含弱尾边界。
10. 第一个结论是P／W真正的指数可积域等于整个实平面。
11. 不能以不可积时总化积分0来“证明”domK全域。
12. 第二个结论量化该域中所有subtype参数theta，生产真实指数积分严格正。
13. 同项要求canonical bivariateLogMGF与真实P下字面log∫exp(theta₁x+theta₂x²)完全相等。
14. 从TYPE看这一相等应是实际定义体化简，仍须核对真实可积及非零概率门。
15. 存在真正属于该MGF域的theta0，其底层参数对为(8sourceEll,−sourceEll)。
16. theta0在候选z0=(q/4,q)的有限实指数测试值等于同一个saddleRate sourceEll q w。
17. 候选z0的D成员资格必须生产，不由调用者输入。
18. 候选canonical EReal率等于有限实saddleRate的嵌入，不只是候选测试不超过率。
19. 对D中全部z，候选率≤该点率。
20. 同一全域比较中，率等于候选率当且仅当z=z0。
21. 率在其他点可能为+∞；不允许对它取toReal后忽略无限值。
22. 此目标没有假设globalmin、KL／entropy duality或局部Hessian正定。
23. 各个存在／forall结论都位于原q/w之后，不容重新选择q/w/P。
24. q>0必须实际用于sqrt恒等式；候选D边界应为(sqrt q/4)·sqrt q=q/4。
25. 对非候选pair，必须从pair不等生产至少一个坐标不等，匹配真实separator的前提。
26. separator应覆盖全部c>0的弱尾域，包括c<1、c超过支撑上界、c=q但a>q/4等。
27. separator给出的有限(s,t)必须连真实Integrable证明一起组成domain witness，不能只交付一个实对。
28. 真正的canonical上确界比较应使用有限EReal嵌入严格次序及test≤iSup。
29. 已接受root通用唯一极小API若被调用，必须逐项生产其hz0/hupper/theta0/hattain/hsep，而不是把其名称当结论。
30. hm0概率、域全性、literal log、达到值与分离器必须始终消费同一P/W/L。
31. 本实际类型没有导数、Hessian、局部均值映射逆或修正常数的结论。
32. 原R1 161–237／root A的本义是整个正能量弱尾域的唯一全局率极小点，不是只在边界附近的临界点。
33. 本轮需要核所有locals、所有实际所属声明与其传递公理，不能以声明／环境票或编译PASS代替。
34. v2视图是已独立审查的环境约束；当前proof审查不重复Lean或对象路径检查。
35. 待核：实际proof是否先给P概率与任意二次指数可积，然后才定义域成员。
36. 待核：原公共source_saddle_exponential_value_bound是否完整消费同q/w/hw/hm，达到值是否精确相同。
37. 待核：pairneq及完整弱尾门是否正确传给exists_source_tail_exponential_separator。
38. 待核：每个实际TYPE和标准公理是否与源内唯一声明相符，有无隐藏private/generated遗漏。
39. 本前缀不预报kernel／完整proof裁决，全部根A/B/C/D仍OPEN。

--- END IMMUTABLE BLIND PREFIX ---

## 完整来源与实际proof逐门审查（receipt之前）

顺序：上述86行5944B actual TYPE盲前缀先持久化，SHA256 `4594eb3eb92b1e2a94f1e8357e6db564960b893c81245adeb2ef08b6b8b13dd0`；随后才读完整99行当前源码、scope-v2的完整TYPE／正文、真实R1 161–237，并实读公共BivariateLegendre全部114行及直接生产者相关实际定义／公共类型／生产体。尚未以receipt、build或Audit PASS裁定数学。没有读取作者implementation/candidate/future/scanner笔记。

### 原始义务与准确数学对象

R1 161–237的原义务是鞍点为整个正能量弱尾域唯一全局率极小点；原叙述用相对熵和Bernoulli下界。本模块没有把尚未接通的KL／熵对偶当作输入，而是消费已完整独立接受的PR146有限实指数测试，再落实root公共canonical EReal上确界。实际D={c>0且a≥sqrt(q)/4·sqrt(c)}保留弱边界及全部c>0，没有加上“矩可实现”限制，也不把c=0偷纳其中。该D在整个R²未必是闭集，所谓closed positive tail只指尾不等式为弱不等式。

公开类型没有新增P概率、globalmin、hupper、hsep或Hessian前提。所有这些充分门均在proof内从相同q/w/full4hm生产。无需每个基点质量严格正；本结论不是协方差非退化性结论。

### 1–15行：实际imports、namespace与语义

两导入恰为SourceGlobalExponentialTests与Shao.Probability.BivariateLegendre，namespace Shao.OQ3，open MeasureTheory Shao.Probability，scoped Matrix；所以所有未限定bivariate*都指已接受的公共canonical定义。没有第三个全局率定义或自建axiom。scope-v2注释为当前冻结版本。1–15行除了导入／注释／作用域，没有额外数学声明。

公共BivariateLegendre.lean20–33实际定义域为Integrable(exp(theta·W))的实参数集，log只接受这个域的subtype成员及NeZero P，率是域内所有有限实测试标准嵌入EReal后的真正iSup。因而后面域成员证明、正积分与全部domain参数上界不可省略。

### 17–46行：完整目标保真

这30行是唯一公开target，从q窗口、w≥0、完整四HasSum到P／概率实例／W／D／全域／所有正配分与literal log／真实theta0／达到／候选D／EReal候选率和全部D上的等号唯一性。证明未删任何合取或替换law。letI使用hm0的冻结simp证明体，没有把实质性质移到可真空成立的蕴含前件。全部结论位于同一q/w之后。

### 47–55行：hm0真实质量与P概率，获取同律实际上界

48–49行的hs不是总化tsum等式：FiniteConstraints.lean35–38明确feature首项1、target首项1，Matrix.cons_val_zero和mul_one把hm0精确还原为HasSum w 1。50–54行局部P／W／D与目标中的let逐体相同；51行消费hw/hs调用公开originalMeasure_isProbabilityMeasure。该API实际InverseTilt.lean51–55先给atomicMeasure概率，再由真实inverseExp_integrable生产非零倾斜概率，不把不可积tilted=0当概率。相同命题的概率证明体差异只属证明无关性，不是改变测度。

55行只解构一次source_saddle_exponential_value_bound q w hw hm，得到hvalue和hattainRaw，始终是原P／同L=saddleRate sourceEll q w。直接producer的公共119–133类型给所有实s/t的真实Integrable、严格正积分、候选测试≤L，以及(8ell,−ell)达到L的实际等式。其生产体134–151先由hs和bounded support给真实二次exp积分，再用同π原矩约束及forward normalizer公式，不需要调用者输入globalmin。当前本模块只消费该公开接口，不引用其private helper。

### 56–63行：全域及实际theta0成员

hmem对任意实参数对theta，使用hvalue(theta.1)(theta.2).1，所给Integrable函数经P／W定义化简恰为canonical domain成员条件。没有先把domain改成univ再反推可积。

hdomain以Set.ext逐点给双向包含：domain→univ平凡，univ→domain实际调用hmem。其覆盖全部实(s,t)，不是U16d的小球界。62–63行theta0为带hmem证明的真实subtype对，底层参数恰(8sourceEll,−sourceEll)；达到值之前已生产可积。

### 64–70行：有限实上界与精确达到

hupper的每个domain参数消费hvalue的`.2.2`，即同一有限实测试≤L；canonical log定义展开后的积分完全相同，不是对所有点的率作上界。hattain以hattainRaw直交，theta0底层对和P／W／bivariateLogMGF均可定义性还原为生产者的字面测试。没有符号错误：实际theta0线性项为8ell·(q/4)−ell·q=ellq，配分log的负号与saddleRate=ellq+log(inverseNormalizer)一致。

### 71–77行：正q和候选完整D成员

hq由0<1<q严格得出。hz0 change为0<q与(sqrt q/4)·sqrt q≤q/4；实际ring先改写为(sqrt q·sqrt q)/4，再用Real.mul_self_sqrt hq.le得q/4，故候选精确落在D弱边界。没有除以sqrt q，也没有把sqrt总化用于负q。分母仅为非零常数4。q窗口端点仍为开区间。

### 78–91行：完整弱尾域的真实有限严格分离器

对任意z∈D且z≠(q/4,q)，84–87行按z.1=q/4分情况：第一坐标相等时第二坐标若也相等，Prod.ext ha hc给pair相等并直接矛盾；否则直接用第一坐标不等。故hne'精确为separator要求的坐标不等析取，没有把pair不等错误加强成两个坐标都不等。

88–89行exists_source_tail_exponential_separator明确消费同q/hq0/hq1/w/hw/hm和hz.1(c>0)、hz.2(弱尾不等式)、hne'。其公共153–167类型不要求c位于能量支撑内，不要求非零w_i或额外可实现性。实际旧生产体228–255分别处理c<1与c>1+H；其余1≤c≤1+H时包含p=0/1端点，c=q非候选则由a>q/4与sourceEll>0给严格测试，R≠1由Bernoulli有限实指数测试生产。因此本hsep确实覆盖完整D，不能误读为只覆盖原R1可实现矩边界。

90行用separator的hi组成实际theta=⟨(s,t),hi⟩域成员；91行hstrict经P／W／log定义化简即所需同L严格不等式。这里忽略separator同时给出的正积分证明并非失去正性：hi加P的NeZero实例足以在最后bivariateLogMGF_spec真实重建严格正配分，且hstrict本身来自已经证明正积分后使用的log。没有以仅实参数对取代domain witness。

### 92–96行：公共全局最小定理每个前提均已消去，返回全部合取

实际调用bivariateLegendreRate_unique_minimizer_of_tests P W D z0 L hz0 hupper theta0 hattain hsep；全部实质输入均由前面本proof生产。没有给root定理添加手工全局率前提。公共实现56–71先用iSup_le及EReal.coe_le_coe_iff给候选率≤(L:EReal)，再用theta0真实test≤iSup及达到值给反向不等，得到精确有限候选率。

公共实现73–110对非候选点用hsep的有限L<test，经EReal.coe_lt_coe_iff提升严格比较，再接test≤canonical iSup。故即使该点率为+∞也仍严格大于候选；没有使用toReal、无穷减法或处处有限性。z=z0分支自反；z≠z0分支严格性排除等号，给精确双向唯一性。结论不是局部凸性或另一个率函数的最小性。

94行refine完整返回hdomain、全部domain参数正配分／literal值、theta0底层rfl、hattain、hz0及hcanonical的两个结论。95–96行对任意domain theta，bivariateLogMGF_spec P W theta的`.1`在真实theta.property Integrable和NeZero P下给积分>0；其证明为integral_exp_pos，再以实际exp_log只处理正值。literal log等式由真实definition和W展开rfl，不是新假设。P概率的实例在此仍来自51行的同一个P。

98–99行仅结束section／namespace。99行全部已读；本源无private定义、private定理、局部递归、额外宏声明或显式generated命题。locals为证明项，不按名字猜它们有没有生成所属常量；后续仍需实际owner Audit枚举覆盖。

数学阶段裁决：完整实际proof逐项消除了公开目标要求的全部门，未发现数学／来源／类型漏洞。接下来才核实际唯一DECL／TYPE及传递公理，再末读receipt／build／hash等机械凭据。

## 全部actual所属DECL／TYPE与传递公理

数学阶段后才只读服务器actual-declarations.txt，完整31行1869B，SHA256 `ad697138682ba7011ac982c0aa2d91dec33c889cc97294573b9c878ff84852d6`。所有续行逐项读取，唯一实际DECL及完整TYPE／AXIOMS原样如下，不只核首行或计数：

```text
DECL Shao.OQ3.source_canonical_rate_unique_minimizer
TYPE ∀ (q : ℝ),
  1 < q →
    q < 103 / 100 →
      ∀ (w : Shao.OQ3.AtomicIndex → ℝ) (hw : ∀ (i : Shao.OQ3.AtomicIndex), 0 ≤ w i)
        (hm :
          ∀ (k : Fin 4),
            HasSum (fun i => w i * Shao.OQ3.constraintFeature Shao.OQ3.sourceEll (Shao.OQ3.fixedAtom i) k)
              (Shao.OQ3.constraintTarget q k)),
        let P := Shao.OQ3.originalMeasure Shao.OQ3.sourceEll w;
        have W := fun x => (x, x ^ 2);
        have D := {z | 0 < z.2 ∧ √q / 4 * √z.2 ≤ z.1};
        Shao.Probability.bivariateMGFDomain P W = Set.univ ∧
          (∀ (theta : ↑(Shao.Probability.bivariateMGFDomain P W)),
              0 < ∫ (x : ℝ), Real.exp ((↑theta).1 * x + (↑theta).2 * x ^ 2) ∂P ∧
                Shao.Probability.bivariateLogMGF P W theta =
                  Real.log (∫ (x : ℝ), Real.exp ((↑theta).1 * x + (↑theta).2 * x ^ 2) ∂P)) ∧
            ∃ theta0,
              ↑theta0 = (8 * Shao.OQ3.sourceEll, -Shao.OQ3.sourceEll) ∧
                (↑theta0).1 * (q / 4) + (↑theta0).2 * q - Shao.Probability.bivariateLogMGF P W theta0 =
                    Shao.OQ3.saddleRate Shao.OQ3.sourceEll q w ∧
                  (q / 4, q) ∈ D ∧
                    Shao.Probability.bivariateLegendreRate P W (q / 4, q) =
                        ↑(Shao.OQ3.saddleRate Shao.OQ3.sourceEll q w) ∧
                      ∀ z ∈ D,
                        Shao.Probability.bivariateLegendreRate P W (q / 4, q) ≤
                            Shao.Probability.bivariateLegendreRate P W z ∧
                          (Shao.Probability.bivariateLegendreRate P W z =
                              Shao.Probability.bivariateLegendreRate P W (q / 4, q) ↔
                            z = (q / 4, q))
AXIOMS [propext, Classical.choice, Quot.sound]
```

逐项核对：q窗口、非负w、完整四HasSum、同原P、W、完整D、全域、所有正积分／literal log、真实theta0、候选达到／D／有限EReal率，以及D内比较和等号唯一性全部在actual类型中。打印器隐藏了概率／NeZero实例的证明参数，并把部分let打印为have；这不是额外caller概率前提。完整source23–26和48–51已经实际审查该实例生产，不能因打印器省略证明就误报漏门。

所属覆盖不是名字stem猜测：末阶段读Audit.lean41行1773B，21–25行遍历env.constants并由env.getModuleIdxFor?取实际module owner，仅保留owner恰为Shao.OQ3.SourceCanonicalRate；没有private前缀白名单漏查。26行排除新axiom，27–30行Lean.collectAxioms逐所属常量收集完整传递依赖并拒绝标准三项之外的公理。31行打印每项完整TYPE，32–34行统计全部声明／定理／目标。实际Audit.log32–36行输出0 frozen DEF、1 frozen THM、1 ALL THM、1 ALL DECL、AXIOM_GATE PASS。

因此完整覆盖为1public THM、0private THM、0generated、0DEF，总所属1／定理1；与全99行源码联合相符。该唯一定理实际公理集合恰为[propext, Classical.choice, Quot.sound]，不是只凭“白名单通过”笼统推测，也没有遗漏生成义务。没有sorryAx／新项目axiom；全部标准公理传递覆盖，非只核直接引用。

## 最后机械绑定与历史

本节最后才读正式receipt／history／依赖字典及现有日志摘要；没有用其implementation描述取代此前独立proof。所有服务器项目读取均经共享broker、taskset -c 14-17。未运行Lean／#check／probe／smoke／target／Audit、未重算已通过导入图、pins或稳定对象hash；未触外部CPU0–9／80GiB任务。没有源／缓存／分支／旧票修改或新agent。

### 冻结版本及源身份

- 当前local源码、remote worktree源码、run/SourceCanonicalRate.lean及source-02.lean均99行4662B，SHA256 `fc492cbacca9a8df208b9a20ea47d7e84e71c1c48e1f87448adbd925f5378d92`。
- 精确scope-v2.md为63行7847B，SHA256 `d716c2d9c356f3e3562605885394e75f95565c8649bc66c40a88853d11d1e351`；完整public TYPE（含letI hm0证明）白空格规范比较PASS。
- 原R1 SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。v1数学声明票191行／SHA `cf2f5e05d4e34c6dc2a4d3fca637092001537bca5aaa9282d08dec804b147270`及v2环境票158行／SHA `a60368937a4ca0c8d8cccb38a848b6ba5a330e1b64ed56ea92a16b8f56789648`均保留，没有倒改v1错误路径推断。
- 当前branch `feat/oq3-source-canonical-rate`，HEAD `ffdedd610d0af501c3dd4672cf7f78d80eee543c`，tree `433377aee492752840f9396896bd00f668634442`；status仅`?? Shao/OQ3/SourceCanonicalRate.lean`。这是root接受v38上的正常新分支，不把旧153旧树或其他冻结leaf head当作当前HEAD。

### 首次构建和环境修正的准确历史

完整build01的99行source-01.lean仍为cbf43455e2d182fc0a342736d415190c4898878e622f6778c96a7b4e60c7cdae；它在v1并列Shao搜索路径下import失败，exit1、1.9492265s，242B log SHA256 `260cc7c835654100a3cb9b99dd704774a04f9d735d2f06db59e5a0809565dbd6`。该失败未进入proof，不被记作部分成功或已通过证明。

v2静态独立环境终票整份读完后，source只把头部注释scope hash改为d716；我对source-01与当前source从namespace Shao.OQ3到EOF实际文本比较，结果完全一致。无proof repair／签名修复，也不是重编同一已成功源。

完整build02是当前源首次成功，exit0、4.3598615s；8行354B日志SHA256 `ce4cbd4ec47005a0d924acceac601f98e2a34626d98b5d9f74fb4f91a32748fa`。只选读诊断，实际唯一warning是51行letI写法建议，0error；不能写成空log。提示中关于可关闭linter的文字不是实际关闭设置，source未用set_option降低检查强度。

正式命令记录是taskset 14–17 → lake env → env LEAN_PATH=view:既有Lake paths → lean -M8192 -j4 -DautoImplicit=false；view真正位于最终Shao查找首根，Mathlib等原路径保留。仅元数据视图链接读root接受对象，无binary复制／既有cache写。import-view.json SHA256仍为`d060d63c06c0dcd5da7469194ac2016cfd98ed06982c32251acf2eb14c489c20`；本门复用已独立审查的视图，不重查13对象或缓存hash。

build-history.json为52行3794B，SHA256 `b9a0d4c75740884d24a7c60ad68926f8e405a2155e851326fa205bc7321bc51e`，实际恰两次完整版本：01 import失败、02首次成功。没有partial、probe或成功重跑；没有增加heartbeat或弱化数学命题来通过。

### 首次module-owner Audit及正式receipt

首次Audit exit0、5.0886954s，未重跑；Audit.lean SHA256 `73e18c8b291fbd4130a886481db0577bf1442dcf05b1852dab36da5c5bb903ac`，Audit.log36行1983B SHA256 `6373f2d127ac31a5683d3cf7b8765f643aa626fcc25606af45b63c9204886ced`。全部实际TYPE与其覆盖方式已在上节独立核实。raw完整日志留服务器，仅打印实际声明选块／诊断／小机械摘要。

正式receipt.json为266行16519B，SHA256 `670a4854c3bc5c7e5373e0356bafd6a1c439288e55e9a8fc44fb762590112939`。其状态AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW准确区分作者门与本次独立终审；nonclaims没有把一般KL、处处有限率、所有非负权重的正率、ambient canonical梯度／Hessian、均值逆或根完成误记为已闭。作者implementation字段仅最后作行政一致性读取，不作为数学依据。

prerequisite-hashes.json实际15行1373B，SHA256 `73d47bbf6d015aa4a478496a58cd4c95e8de1dc89746101f5a4dac12ae1007cf`。最后按其13个canonical相对源路径逐项重新读取当前own v38源码hash，缺项／不符均0；独立compact重算为`f158e2cad3e7a0dc5f0c7c31d85c111820fb38cb483188a4e9fe653e8ec2ecd2`，与正式字典及此前声明图相同。包括直接SourceGlobalExponentialTests源24c70292…13df和公共BivariateLegendre源d8bd5dc7…5f58。这里只做正式fresh源绑定，没有重算已通过全图／对象／缓存／pins或重复成功smoke。

固定工具链和Mathlib沿用已独立绑定的Lean v4.36.0-rc1／Mathlib807d3836b165983210ee2ecf3cd28f239436949c；receipt设置与此前绑定一致，本门未重哈希稳定pins。资源native8192MiB、j4、autoImplicit=false、CPU14–17；不使用ulimit-v，不干预其他任务或全局资源。

## 独立最终裁决及义务边界

STATUS: CORRECT

此终裁绑定scope-v2 d716c2d9完整SHA、当前99行fc492cba完整SHA、实际唯一完整module-owner TYPE及真实首次build02／Audit证据。来源、完整声明、逐行proof、实际公共API消费、全部所属常量／传递公理与机械门均独立通过。它不是只凭环境票、作者receipt或通用唯一极小定理名称作出的判断。

原target→实际消除：R1 161–237/root A的同一源原律P的完整真实MGF域、域内正配分和literal canonical log、候选(q/4,q)的真实theta0达到、有限canonical EReal率=saddleRate，以及整个c>0弱尾域的全局比较／等号唯一性。当前proof对任意合法同q/w成立，未来可直接施于已接受U20b最终同w/q/P，不重择law。

直接consumer：root canonical A组装在同一最终法则上接本全局率结论，并另接真实ambient Fin2梯度／完整Hessian、几何常数和标准余项失败。剩余：这些canonical导数／常数适配、均值映射逆邻域、最终A装配、统一far率间隙及概率界、一般KL9/10及其他根义务仍分别待闭；本节点不声称处处有限率、所有非负w的正率或完整OQ3完成。U21a仍是声明正确、DEFERRED_UNIMPLEMENTED，不纳入proof验收。全部原A/B/C/D仍OPEN。

本报告初始IN_PROGRESS只记录盲前缀落盘时点；本节CORRECT为完整独立终裁。盲前缀86行5944B／SHA256 `4594eb3eb92b1e2a94f1e8357e6db564960b893c81245adeb2ef08b6b8b13dd0`逐字保留。本报告外没有修改source／scope／receipt／Audit／旧票／pins／cache／branch或任何他人文件，没有新代理、Lean执行、commit或PR。尚须lead整份终票全文读取后才进行本lane接受／发布。
