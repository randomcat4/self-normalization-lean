# U20b SourceRemainderNotBigO 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 不可改写盲译前缀：完整冻结TYPE及标准大O疑点

先仅提取scope72的唯一完整Lean fence并独立翻译；尚未读其说明、作者路线／候选图或新机械凭据。前置审查上下文存在，不等于本新Landau断言自动批准。0publicDEF／1publicTHM。

```lean
theorem exists_source_fixed_law_not_isBigO :
    ∃ (q : ℝ) (w : AtomicIndex → ℝ),
      1 < q ∧ q < 103 / 100 ∧ (∀ i, 0 < w i) ∧
      (∀ k : Fin 4,
        HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
          (constraintTarget q k)) ∧
      let P : Measure ℝ := originalMeasure sourceEll w
      let x0 : ℝ := Real.sqrt q / 4
      IsProbabilityMeasure P ∧
      (Integrable (fun x : ℝ => x) P ∧ (∫ x : ℝ, x ∂P) = 0) ∧
      (∀ᵐ x ∂P, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
      0 < P.real (Set.Ioi 0) ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic P xi eta‖ < 1) ∧
      Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun J => ‖jointCharacteristic P (resonanceXi J) (resonanceEta J)‖)
        Filter.atTop (nhds (1 : ℝ)) ∧
      0 < x0 ∧ x0 < 1 / 2 ∧ 0 < saddleRate sourceEll q w ∧
      0 < correctedInverseScale sourceEll q (atomicMeasure w) ∧
      (∃ nseq : ℕ → ℕ, StrictMono nseq ∧
        Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
        ∀ J : ℕ, 0 < nseq J ∧
          (J : ℝ) < Real.sqrt (nseq J : ℝ) *
            (normalizedTailCoefficient sourceEll q w (nseq J) -
              correctedInverseScale sourceEll q (atomicMeasure w))) ∧
      ¬ Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => normalizedTailCoefficient sourceEll q w n -
          correctedInverseScale sourceEll q (atomicMeasure w))
        (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
```

本轮独立量词／let／合取／大O语义翻译：

1. 直接存在一个实q及一个全AtomicIndex实权重w，不输入手工gap或大O否定。
2. 同q严格在(1,103/100)，同w全部索引严格正。
3. 同q/w对sourceEll的全部四条实际feature序列HasSum到真实target。
4. 以上为存在交付的合取，不是可任取不合法q/w而真空成立的前件。
5. P内定为originalMeasure sourceEll w，x0内定为sqrtq/4，均不可另选。
6. 同P是真概率，X真Integrable且积分0。
7. 同P AE 1≤|x|≤4+sqrt10，真实离0及有界。
8. 同P在Ioi0有正实质量。
9. 全部非零联合实频率对下，同P实际jointCharacteristic范数严格小于1。
10. 指定resonanceXi/Eta的绝对值和沿J趋+∞。
11. 同P沿同指定频率对的范数趋实1。
12. 同x0在(0,1/2)，同sourceEll/q/w的saddleRate及actual correctedInverseScale严格正。
13. 同法则内保留一个完整存在时间序列合取。
14. 该nseq:ℕ→ℕ严格增，趋atTop，并且全J含0满足nseqJ>0。
15. 每个实J严格小于sqrt(nseqJ)乘实际同law系数减同actual corrected scale。
16. nseq的存在被显式括号完整封闭，随后另合取否定标准Asymptotics.IsBigO。
17. 大O否定在nseq存在之外，但仍在同q/w/P固定范围内；不能误读成更换law或每个nseq选新的q。
18. 大O左函数是自然n上的真实normalizedTailCoefficient sourceEll q w n减同correctedInverseScale。
19. 右函数是真实实sqrt(n:ℝ)的逆数；不是caller函数或n的任意重标号。
20. 过滤器是自然时间atTop；要求否定标准最终上界，而非只否定所有n全局上界。
21. 标准IsBigO必须按真实库定义核：存在有限实常数乘右函数的norm，最终控制左函数norm；不能只控制有符号误差。
22. 右函数在n0因逆数总定义可为0，但最终上界否定不能靠单独n0失败。
23. 应从同一次20a存在交付保留nseq，再用其Tendsto把真正eventual大O上界拉到J。
24. 必须选一个J既满足拉回的最终时间门，又有实J大于大O常数；不要求误差函数单调。
25. 真实0<nseqJ给sqrt(nseqJ)>0，先证明此门才约去sqrt及其逆。
26. 有符号误差≤绝对值norm，乘正sqrt后大O应给scaledgap≤常数，与当前J严格gap矛盾。
27. 常数是否非负及norm乘法的准确格式须读实际IsBigO定义，不能凭记忆省去。
28. 所有步骤不得用另一个opaque family、自由序列或新的概率law替代20a原P。
29. 声明无新公开DEF，不定义rootcanonicalK／domK／EReal rate或全局最优。
30. 仍需区分字面标准Landau余项失败与root最终反例全部假设／接口闭合，A/B/C/D仍须独立组装。

当前仅为完整TYPE盲译检查点；后续只能追加，不能改写此前字节以迎合实现或作者路线。

## 一、冻结完整声明与原始来源

前74行4829B盲译原字节保留，SHA256=44f1efdafaaaf23012cd7011c0c1df7bb07e3a1b9d81debd978283de653402e4；页首IN_PROGRESS只记录先行检查点，末节为最终裁决。
本轮在该完整TYPE盲译落盘之后才读scope72说明、R1真实原件、实际20a公开完整接口与固定库定义；独立数学／API核定后，最后才作一次新exact2import图／绑定。
这是声明／来源／API门，0publicDEF／1publicTHM；当前无U20b实现或Audit，故不预报target elaboration、kernel或proof通过。
本报告完整fence与冻结scope72逐字相同，包括P/x0两个let、全部20a性质、括号封闭的nseq存在及最后标准IsBigO否定。

R1实际539–548行给同一个最终固定P的sqrt(nJ)*(C_nJ−v_corr^-1)≥bJ趋无穷，550行明确“Incompatible with an O(n^-1/2) remainder”。
554–558行再次约束P/x0及全部支持质量固定，均不随样本量变化，且实际支持有界离0。
因此新TYPE新增的是这句结论的标准Landau形式，而不允许把“非大O”改成一个自由序列、换law或自定义渐近关系。
右比较函数sqrt(n:ℝ)^-1在正自然n上就是n^-1/2；n0的逆数总化值不会影响atTop语义，且实际选用见证全为正。
actual normalizedTailCoefficient仍是同P有限n重产品sourceTail概率乘原source指数及sqrt(2πn)归一化；correctedInverseScale仍是同q／atomicMeasure w的实际原常数。
R1原件SHA256=3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，未以作者candidate／route／receipt叙述替代来源。

## 二、同一已接受20a见证及完整量词保持

实际SourceFixedLawCounterexample.lean37–61公开exists_source_fixed_law_counterexample是无输入存在命题，恰交付新TYPE除最后否定以外的全部合取。
它一次固定q/w，1<q<103/100、全AtomicIndex w严格正及full4HasSum；其后P=originalMeasure sourceEll w、x0=sqrtq/4均是指定let，不能另择。
同law公开性质为真概率、Integrable X／EX=0、AE 1≤|X|≤4+sqrt10、P.real(Ioi0)>0、所有非零联合频率严格模界、指定频率逃逸与同P模趋1、x0窗口、正saddleRate及正corrected scale。
同公开输出最后是真实nseq:ℕ→ℕ，StrictMono、Tendsto atTop atTop、全J正样本量与实J严格小于实际sqrt(nseqJ)余项。
本新声明只需destruct此存在一次，保留同q/w及全部属性与原nseq见证；无需调用另一opaque family、C的存在重选器或任何跨模块private helper。
不存在新caller hcont／hW／gap／BigO-failure输入。真实20a完整独立proof已接受，但其接口仍按本轮实际public TYPE核对，而非凭标题推断。

新TYPE用括号明确封闭(∃nseq,...∀J...)，后面的¬IsBigO与它并列、仍在同q/w/P范围内。
证明可保留原存在见证作为一项，同时用其htop／hn推出最后否定；不需要否定断言依赖一个在范围外不可见的nseq，更不需要∀nseq。
StrictMono虽然可由自然严格增推出Tendsto，原输出已显式给htop；新否定可直接消费htop，不误套“实严格增序列一定趋无穷”的错误命题。
所有原20a量词、概率门和定量见证完整保留；新增结论不是以一个弱口头无界结论替换它们。

## 三、标准Asymptotics.IsBigO的真实定义／接口

指定固定Mathlib/Analysis/Asymptotics/Defs.lean73–74实际定义为irreducible_def IsBigOWith c l f g := ∀ᶠx in l,‖f x‖≤c*‖g x‖。
85–86的IsBigO也是irreducible_def，内容为∃c:ℝ,IsBigOWith c l f g；c默认是有限实数，不在定义上要求正。
96–97的公开isBigO_iff精确给IsBigO l f g↔∃c:ℝ,∀ᶠx in l,‖f x‖≤c*‖g x‖；139–140的IsBigO.bound给同方向。
因此应通过这些真实接口提取eventual norm界，不假定irreducible_def可直接按普通可约定义拆解，也不把原定义误写成全n上界。
100–114的isBigO_iff'在g值域为真实SeminormedAddGroup时还可取得c>0，证明以max c 1替换原c；本type两函数均ℝ值，满足这一标准门。
本票用该正c版本说明可行证明路径；也可保留原任意实c，因为后续乘正sqrt与常数消去本身不要求c非负。
实函数norm是真实绝对值；不能把标准大O偷换成f≤c*g的有符号最终界。下面只从f≤|f|推导有符号上界，逻辑方向正确。
此模块实际public section/expose公开这些定义和定理，exact第二import足以直接写全名Asymptotics.IsBigO；不需要新定义或自定义Landau缓存。

## 四、独立完整反证路径与全部正性／最终门

在一次固定的20a q/w/P上，设f(n)=normalizedTailCoefficient sourceEll q w n−correctedInverseScale sourceEll q(atomicMeasure w)，g(n)=(sqrt(n:ℝ))^-1。
反设标准hO:IsBigO atTop f g，由isBigO_iff'取一个实B>0及hB:∀ᶠn in atTop,‖f n‖≤B*‖g n‖。
原htop:Tendsto nseq atTop atTop允许用Filter.Tendsto.eventually htop hB，真实得到∀ᶠJ in atTop,‖f(nseqJ)‖≤B*‖g(nseqJ)‖。
实际Order/Filter/Tendsto.lean46–48的完整API正是沿Tendsto拉回eventual断言；不需要错误地说上界从某n对所有J立即成立。
Order/Filter/AtTopBot/Basic.lean80的eventually_atTop给∃J0,∀J≥J0,上述norm界；它是自然atTop的真实阈值，不是假定界全时间统一。
Algebra/Order/Archimedean/Defs.lean76–77的exists_nat_gt B给J1:ℕ且B<(J1:ℝ)；取J=max J0 J1可同时进入最终区间并满足B<(J:ℝ)。
这个选择没有借f、C_n或nseq gap的任何单调性；只用自然索引的max与实Nat.cast单调性。
原20a hn J给0<nseqJ及(J:ℝ)<sqrt(nseqJ)*f(nseqJ)，是当前这个J的真实定量见证，不是从别的J传来的下界。
先由正自然数cast得到0<(nseqJ:ℝ)，再Real.sqrt_pos给b=sqrt(nseqJ)>0，故b≠0及b^-1>0。
因此‖g(nseqJ)‖=|b^-1|=b^-1，norm界真实化为|f(nseqJ)|≤B*b^-1；这里先证了逆数的符号与非零。
由f(nseqJ)≤|f(nseqJ)|，乘b>0保持方向，得到
b*f(nseqJ)≤b*|f(nseqJ)|≤b*(B*b^-1)=B。
最后等式只在b≠0门之后用实交换乘法与b*b^-1=1，未对n0、任意可能为0的sqrt或q作非法约分。
当前gap给(J:ℝ)<b*f(nseqJ)≤B，而选择给B<(J:ℝ)，矛盾；因此目标标准¬IsBigO成立。
该推导对误差有符号值不作额外假设，即使未先证明f沿见证正也成立；f≤norm f足够。若B原来为负，取正B版本已经合法消去该无关边界。

nseq0也明确正，但证明否定依赖真正eventual大J，不以单独n0失败作为反例；改变有限初项不会影响这个反证。
大O常数先固定，再拉回eventual，再选共同J；没有将“每J某个常数”误当一个标准统一常数。
全程同q/w/π/P和同corrected scale、同实际tail coefficient；未借新的Gaussian law或任意G来代替原概率序列。
可用一个私有generic反证helper组织实现，但main必须把当前真实20a nseq／htop／hn代入，不能只导出helper而声称原counterexample已证。当前只是声明门，并无此实现可验收。

## 五、实际新静态图与行政事实（数学后核）

本审查者在指定server独立一次扫描exact2imports SourceFixedLawCounterexample／Mathlib.Analysis.Asymptotics.Defs；未读取作者candidate scanner或JSON作为图凭据。
扫描剥离嵌套块注释／行注释／字符串，识别ordinary／public/private／meta imports，传统非module普通import按公开处理；physical走全部内部边，public走公开边。
只展开Shao／Mathlib，外部Lean/Batteries等节点停止并另计，不冒称其内部闭包也已扫描。
独立physical=67Shao＋2973Mathlib＋211外部停止=3251；public=2712内部＋189外部停止=2901。全部内部source／olean存在，缺0。
canonical67相对源路径键sorted compact SHA256=b89b6ad627672a072361be255f994133e4607630d3ec6bd9ca8e59ca2e811a04。
公开可达实际20a、Asymptotics.Defs、Filter.Tendsto、AtTopBot.Basic、Archimedean.Defs及Analysis.Real.Sqrt，足以提供以上真实接口。
这是一轮新target静态read-only图及对象存在性检查，不是新Lean／proof PASS，也不声称全cache目录hash不变。

实际20a源本地／server103行5065B同SHA256=3d402b62362c4394eb50a6ade2f512ab90c3d19982ce19ca143c706257c5c571；其完整独立proof票224行22472B SHA256=741362e81acd4e59a9f31e31f0505917d782911b95c000e0d95b89bf14a5211a保持原字节。
新scope72本地／remote同45行7252B，SHA256=a52d7fe2fa52fd79c0476775c1760f5e6229f15bfa5696850f644a5898cb58d9；本报告完整TYPE与该fence逐字相同。
真实R1 SHA256=3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。
Mathlib实际HEAD=807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA256=d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4；lake-manifest.json SHA256=40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。
当前实际branch仍feat/oq3-source-fixed-law-counterexample，HEAD5a82f9e0587a93fc413f83f22713f7e6ec1d8ec5，status--short为空；没有U20b新branch、source／Audit／receipt。
67前置可用是当前冻结152 checkout中实际源／对象的存在事实，绝不等于已全67整合root main；root新BivariateLegendre proposal不是本target的生产依赖，未读取或使用它的未接受实现。
后续正常新分支所用基线由lead／root在批准后决定；本审查未fetch／reset／rebase／merge、改旧PR目标、复制source或重写冻结head。
所有server项目读取taskset -c 14-17；未运行Lean／#check／probe／build／Audit／smoke，没有重做任何旧成功门或写cache／pins／source／旧票；CPU0–9／80GiB外部任务未触。

## 六、最终裁决及仍OPEN义务

STATUS: CORRECT

JUSTIFICATION: 完整新TYPE准确保留同20a全部实际法则／性质／递增定量见证，在同q/w范围内额外要求标准norm-based、eventual Asymptotics.IsBigO否定，括号／量词无真空或换law问题。一次消费实际公开20a见证后，标准IsBigO定义确实给一个统一实常数及最终norm界，真实nseq趋atTop允许拉回，再选一个同时足够晚且大于常数的自然J。正样本量先给正sqrt与非零逆数，合法乘法／约分得scaledgap≤B，与当前J严格gap矛盾，无误差单调、n0总化或自由序列捷径。新exactimports静态公开API及source／olean无缺项，未发现声明或环境阻塞；尚无actual实现验收。

原target→消除义务：R1(31)及550行的“非O(n^-1/2)余项”由实际同law定量见证转成标准库字面Landau否定，同时保留更强的全J StrictMono见证及全部source条件。
直接consumer→root在这个同w/q/full4HasSum witness上接canonical rate／saddle／Hessian／常数适配，然后完成原根最终counterexample陈述；不另选opaque law。
仍OPEN→本声明门不自动定义或证明root canonical K／domK／EReal rate／全局最优、general KL9/10或完整原根组装。全部原根A/B/C/D仍OPEN；actual proof、private／generated完整TYPE及公理须下一独立proof门审。lead整份final读且接受后才实施。
