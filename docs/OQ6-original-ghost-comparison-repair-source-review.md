# 单元201 repair01 独立受影响源码审阅

STATUS: SOURCE_CORRECT

本裁决覆盖精确新源码的三个完整修改 helper、全部44个隐式求和闭包的词法组合、三个受影响 intro、一个新增匿名普通 Prop，以及两条完整声明头、22个实数 let 初始化和未变源码的精确复用。未发现关键数学、陈述或源码绑定缺口。qualified=false；actualOwned=UNKNOWN；actualTYPE=UNKNOWN；actualNonTheoremVALUE=UNKNOWN。静态回读通过不代表 Lean elaboration、内核或传递公理审计通过。

## 独立性、所有权与版本

审阅上下文为全新 /root/oq56_ghostcmp201_repair_review，配置 gpt-6.1-sol/xhigh，未参与作者实现、父级冻结或原完整 SOURCE 审阅。实际模型、努力和 input/cachedInput/output/reasoningSubset 遥测未暴露，全部记 null。本轮只写 C:/game/shao lean/drafts/oq56/unit201/final-review-01/repair-source-01/；未修改 source、旧报告、冻结、作者 seal、shared 或 library。服务器、Lean、AX、上传、Git、网络/API 和 child 调用均0。

已读当前 AGENTS、math-theorem 及其必要参考、streamlined acceptance、SERVER、TEAM 所需段、REGISTRY 当前 OQ56 字段与 successor ACTIVATION。当前唯一 OQ56 owner 为01a17665-2e41-7ed1-9911-57f16fe889fa；当前 ROOT_OQ56_32 阶段不改变本审阅的零重命令权限。作者 RELEASE0 SHA256 7bff750d4a271e7520fbc2e5a625e2140c3468ec300a452a1ba35ecedc2d3680 的 writer/execution/heavy/inflight/pendingExternal/children 均0，绑定的 manifest、DONE、CHECKPOINT、RUNTIME-ACK 精确匹配。

唯一新被审源码是 author-01/stage2/repair-01/OriginalGhostComparison.lean，SHA256 45119bf03fae2df0fac15f380b6283b131dafd6cb00646de55e30c0bf4e5ed35，11538B/255LF/0CR/UTF-8无BOM。事前父冻结 SHA256 6e462613a6364fd6238028d96232ab1a629d8d7bd2a602ba6ba4eed903fc987b。保留旧源码 SHA256 ae0c788f6d25b698d617140fe81a8487d73295ed352a08a1ed10f14dd6dfc777，11526B/254LF。

完整新源码已读；三个旧/新完整 helper、父冻结和差异已读。作者10项 payload、原作者18项与原审阅7项 payload 的散列/字节均独立回读匹配。affected-map 的重复 raw 用新源码精确切片验证，完整44项类型、初始化、正文、捕获、父闭包关系与3项 intro/6项 calc/1项匿名 Prop 的非重复数学内容均已读；未把作者的静态自述当作独立正确性证据。

## 未变声明、假设和旧证据的复用边界

T01 完整头散列 e9b21814e524fecb0eab10953a385e41549a8aa88b68e2eb2760cd96058b0a79；T02 完整头散列6349206513ad78a0a2a2f80973425d99d818e47f25efed6cea35e41389e1075b。两头逐字未变。T01仍对所有 n:ℕ、a b:Fin n→ℝ证明平方和根的三角界。T02仍对同样向量和 t:ℝ，在 ht:1≤t、ha:t(√Σa²+4√n)<|Σa|、hbSum:|Σb|≤2√n、hbSq:Σb²≤4n 下证明 t√Σ(a−b)²<|Σ(a−b)|。没有增加 n>0、正能量、非负坐标、t>1 或分布条件。

六个 import、namespace、autoImplicit=false、完整 theorem 头、T01的10个和T02的12个实数 let 及其全部初始化逐字未变。22个完整初始化、直接/传递捕获和新位置在 SOURCE-COVERAGE.json 中逐项列出。没有新增全局数据定义、实例、选择器或函数参数。所有44个隐式函数均为现存 Fin n→ℝ 与 Finset.univ 的标准有限求和闭包。

原 SOURCE-REVIEW.md SHA256 7c0340d5cb202a7745c1a001b0b8944fd14ac859933ef56a6131561f6da53d96 与 SOURCE-COVERAGE.json SHA256 e9e6c6ccc12fece2f5049238abeb04301526bd1aabe7dfa52c8895e57a553b25 已读并精确绑定。原数学推导和原源到确定性陈述的范围判断只对本次逐字未变部分复用；没有重审旧 producer 或重跑旧 proof/leaf AX。原报告对三处修改 proof 及 SUM20/SUM21/SUM29 的词法正确性结论失效，不沿用其旧 SOURCE_CORRECT 总结来替代本轮检查。

四段未变区间的新 UTF-8 字节范围分别为 [0,3263)、[4244,5394)、[5968,10781)、[10949,11538)，各段与 source-delta 中旧源对应段逐字相等。它们的 SHA256 依次为 a22ed5bc8c2608025ac6e9a8d7ea8ad494732f7b52771c0cac86a442f7018d55、99d07a92f893e6768a0ae96126d49791b01cd3ccb700a6166cc1a0ac7b4f881f、357bd806746df7991f49bf3137f13258ed995d92d9b658f020cca2cd3bdfcd30、6c144cacc2eb55c911dacae663c73074d1393f5e0533d5ed45b62c439663e70c。四段加三个完整 helper 恰好无缝、无重叠覆盖两个版本；正向三次冻结替换精确得到新源，反向替换精确恢复旧源。不是只比较去空白文本。旧偏移继续只指旧源；hghostScaled 后的当前行号比旧源增加1。

## 三个完整新 helper 的证明

T01.hlagrange，84–106行，类型仍为 lagrange = 2·(qa·qb−cross²)。其新完整块 SHA256 7172c152b01ff066b686bd95051e08853857a26a249d2d36c33d3e7aade25475。

固定 i,j:Fin n，令 x=a i·b j、y=a j·b i。ring 的点态目标是

    (x−y)² = (a i)²(b j)² + (a j)²(b i)²
              − 2((a i·b i)(a j·b j)).

右侧交叉项确实等于2xy，只用实乘法交换结合和平方展开，没有不等式前提。第一处 sum_congr 在同一 Finset.univ 上引入 i 和普通成员证明，第二处在固定 i 下引入 j 和成员证明；ring 只证明该坐标等式。显式括号从当前88行第一个额外左括号延续至90行最后一个额外右括号，将三个完整多项式项都纳入内层 j 正文。该内和又完整位于外层 i 正文。

第二个 calc 等式用 sum_sub_distrib、sum_add_distrib 对内外两层有限和分配，得到 ΣΣa_i²b_j² + ΣΣa_j²b_i² − ΣΣ2(a_i b_i)(a_j b_j)。第三步精确使用同一不变上下文中的 hproductAA、hproductBB、hproductCross，得到 qa·qb + qb·qa − 2(cross·cross)。最后一步 ring 给2(qa·qb−cross²)。本块完整检查了全部四个 calc 等式，不只检查新增括号。类型捕获 lagrange,qa,qb,cross；初始化额外使用原 n,a,b 与三条 hproduct 事实；最终全部数据来自原 n,a,b。没有新前提、数据、实例或选择。

T01.hdiffIdentity，128–140行，类型仍为 diffEnergy = qa+qb−2·cross。新完整块 SHA256 f1130942c769a5236858e18b6929da47c95aaf509ff90da46dcddf698cbba2c4。

dsimp only 展开原四个 let 后，sum_congr 在同一 univ 上引入 i:Fin n 和普通成员证明。ring 完整证明 (a i−b i)²=(a i)²+(b i)²−2(a i·b i)。当前132–133行显式括号使整个加减式都成为 SUM29 的正文，最后一个 a i·b i 没有自由 i。随后 sum_sub_distrib 抽出减法，sum_add_distrib 分离两个平方和，反向 mul_sum 将 Σ_i2(a_i b_i)改为2Σ_i a_i b_i，恰好还原原 qa+qb−2cross。初始化只捕获原 n,a,b 和 diffEnergy,qa,qb,cross，没有引用待证结论或新引理。

T02.hghostScaled，238–241行，类型仍为 t(rootA+rootB)≤t(rootA+2rootN)。新完整块 SHA256 fec9ea014657d6c216509da966493689115bfb1f1d793fbc1bad72ca3a379e52。

apply mul_le_mul_of_nonneg_left ?_ htNonneg 的唯一剩余普通 Prop 目标是 rootA+rootB≤rootA+2rootN。其类型捕获三个原实数 rootA,rootB,rootN；初始化 linarith only [hghostRoot] 只使用原 hghostRoot:rootB≤2rootN。目标两边减去同一个 rootA 后恰是该已知不等式，故是合法的实线性推理。外层随后仅以原 htNonneg:0≤t 乘左侧 t。这里没有使用根为正、能量为正、额外分支或新数学数据。rootA,B,N 的初始化仍为 √qa、√qb、√nReal；hghostRoot 只承接原 hbSq 与已审平方根界，htNonneg 只承接 ht。匿名证明只存在于该定理应用的第一个证明参数中，不向外输出数据或实例。

旧 add_le_add_left 在 native01 中实际返回 rootB+rootA≤2rootN+rootA，与要求的两边加在左侧的写法不定义相等。本次直接证明精确目标，避免沿用旧调用方向。该历史诊断用于识别错误及核对这里所需的实乘法单调性目标形状；没有把历史未报错处推断为机器成功。

## 44个求和闭包与三个 intro 的词法组合

已完整读取钉死 primary Defs 源1–343行。其实际语法是 syntax (name := bigsum) "∑ " bigOpBinders BigOpWith ? ", " term:67 : term；该文件明确记录乘法70、加法65与大算子67的优先级。无 with 的宏展开为 Finset.sum s (fun x ↦ v)，有类型的 binder 使用 (Finset.univ : Finset t)。所以旧未括号加减正文的失败有真实语法依据，本轮不能把意图上的长正文当作已绑定。

当前44处 ∑ 的位置从新源码独立枚举，恰与44项映射一一对应；每项完整正文、完整 fun i/j : Fin n => ... 初始化、Fin n→ℝ 类型、UTF-8/字符范围和捕获已核对。只有 SUM20、SUM21、SUM29 的原始正文变动；它们的旧词法结论明确丢弃。所有当前44项都重新作词法组合审阅，其余41项再以精确旧 raw 绑定说明未变。

10个内部 j 闭包及对应外层依次为 SUM09/08、11/10、13/12、15/14、17/16、19/18、21/20、23/22、25/24、27/26。每个 j 函数只自由捕获原 a,b,n 与所属外层 i；自身 j 被绑定。每个外 i 函数的内部 j 由其内层求和绑定，外函数只捕获原 a,b,n，不捕获自由 i 或 j。其余单 i 闭包按实际正文只捕获 a 或 b 或二者，并因 Fin n 类型捕获 n。全部结果为ℝ，索引集和既有 Fintype 实例均不变。

两个修改 T01 helper 内共有13处求和：hlagrange 的 SUM20–27 共8处，hdiffIdentity 的 SUM28–32 共5处；hghostScaled 内无求和。SUM21 与 SUM29 的完整多项式被成对平衡括号包住；SUM20 的正文是完整 SUM21，故两层索引覆盖全部多项式。其余双和正文只有高优先级的乘法/平方或已括号的减法平方，不在未括号加减处截断。其余单和中减法已经括号化，T02的短正文 a i、b i、(a i−b i) 与各平方正文边界正确。

三条受影响 intro 是93行 i、95行 j、135行 i。它们分别绑定 Fin n 坐标和 i/j∈(Finset.univ:Finset(Fin n)) 的普通 Prop 证明，只在对应 sum_congr 子证明内使用，作用域分别到96、96、136行。93行的点态目标是两个 j 有限和相等；95行是上述完整两坐标多项式恒等式；135行是完整单坐标平方差恒等式。没有把任意坐标变成新选择器，也没有索引从子证明逃逸到后续 calc 行。

## 已有接口、退化情形与机器门

钉死 Lean 为 leanprover/lean4:v4.36.0-rc1，mathlib 为807d3836b165983210ee2ecf3cd28f239436949c。没有新 API。原完整 SOURCE 的六份 primary 全源散列和15个声明块/完整时间顺序前缀散列均精确再绑定；保留其已完成的原上下文审阅，未把局部 section/classical 作用域任意拼接。当前实际需要的 sum、sum_congr、sum_add_distrib、sum_sub_distrib、mul_sum、sum_mul_sum 的原始块、真实作用域与实特化已经逐项重看。to_additive 的原乘法头和属性作为生成证据保留，不把推导的实特化说成已反射 actualTYPE。当前索引为 Fin n，值域ℝ满足相应有限索引、实加法交换群和环实例。

新 proof 只用已有 Linarith、Ring 及原有实乘法单调定理。hghostScaled 所需实特化为 u≤v、0≤t 推出 t·u≤t·v；其精确应用目标与已保存 native01 期待类型相同，匿名目标已在源层完整证明。实际生成名、类型、非定理值和公理集仍全部待新对象反射，不猜测 actualTYPE。

n=0 的有限恒等式仍成立，T02 的原 ha 在空向量时不可能为真；零平方和不需要求逆或正性。t=1、hbSq/hbSum 等号边界均保留。新 helper 没有除法、平方根输入域变化、无限和交换、概率极限或独立性步骤。未变完整数学链与原报告精确复用；本源仍只证明点态确定性向量比较，不证明 A/B/D 可测性、乘积概率或 S11 尾界。

静态禁止项扫描无 sorry/admit/axiom/unsafe/native_decide。由新源码直接派生2个 theorem、22个实 let、59个显式普通 Prop 头、10个显式 lambda、44个隐式求和函数和138个显式注型数学数值位置。新增匿名普通 Prop 为1，没有新增数学数据。标准公理白名单仍仅 propext、Classical.choice、Quot.sound；这里未执行 AX，也未声称其实际依赖已合格。

原 native01 明确是自然 RC1、10个 source errors、0 source warnings、无对象；诊断 SHA256 8c4d461ec8388fdf94b18cc204822bbf1f7eb583baf6e06b2f5ffa539a7dae10 保留。9个错误是旧正文的自由 i/j，另1个是旧加法方向造成的应用类型不匹配。本报告不将原源码或新源码写成机器已过。

本轮无 CRITICAL_GAPS。父级下一精确依赖是在既有服务器授权/锁/资源内执行新源 native02；仅成功后，对同首次成功原对象做全部实际所属 TYPE、非 theorem VALUE 与递归 AX，再与本报告及精确未变的旧数学审阅组合。只有这套实际机器证据完成且核对通过，才能升级 qualified。S11、C2/C12/OQ56 保持 OPEN；原 C1 immutablev85 完成范围保留；OQ3保持 PAUSED_BY_USER。外部 Shao–Zhou(2016)(92) 与 Jing–Shao–Wang(2003)Lemma6.4 路线归因沿用原精确范围，不声称新颖性或开放根完成。

本目录最终 RELEASE0 将审阅 writer/execution/heavy/inflight/pendingExternal/children 全部释放为0。最终答复结束本普通审阅回合，不构成持续后台执行机制。
