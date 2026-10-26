# 单元200 repair-01 独立受影响源码审查

STATUS: SOURCE_CORRECT

五个完整新辅助证明及其新增闭包、局部 Prop 证据、捕获、作用域和全部字节组合审查通过。sourceReviewAccepted=true，qualified=false，actualOwned=UNKNOWN。本结论是精确源码层裁决，不是 Lean elaboration 或机器资格结论。没有发现需要改源、改冻结或增加数学前提的关键缺口。

## 精确对象与独立性

修复源码：C:/game/shao lean/drafts/oq56/unit200/author-01/stage2/repair-01/OriginalGhostGoodEvent.lean，SHA256 fc4127fadfab83ff08605b50b0cfa0525084201b7a5b78293d42d9826d82e83a，15804字节、370个LF、无BOM/CR。父事前冻结：C:/game/shao lean/drafts/oq56/unit200/parent-repair-freeze01-five-helper-interfaces.json，SHA256 50c81ddad2e934c8b00332d5a327e81c00cbea0af40f16ebf9a05cfe25742e1d，9032字节。重新对原源码应用冻结文件的五段完整替换，所得每个字节均与待审修复源码相等；作者实现没有超出冻结。

本上下文是恢复 canonical 独立审查角色 oq56_ghost200_final_review 的全新上下文，没有参与作者实现、父冻结或源码修改。原作者、原审查和补充审查的 RELEASE0 均保持全零。本次只在 final-review-01/repair-source-01/ 写新审查工件，未改旧源码、报告、封存或共享文件，未创建子实例。

旧完整源码审查只按精确未变字节复用：SOURCE-review.md SHA256 561c6487ffd3ff21c64f554285cb1d17eae3070be56a69462c72d9b8fd87a16e（10701字节），SOURCE-coverage.json SHA256 91ec41a0a6402279df0a8b3f8577e1c513a73b92042e89c83236eed80eab440c（41462字节）；两条分支覆盖补充 coverage-addendum.md SHA256 7b6af7eff471b1119255ee8250c764ff91eccc1dc500106fa0b7b83d63dcadc2（1737字节）及 coverage-addendum.json SHA256 ea8bfc76d0e0b7cff22c39066760a4b9e01f6d279029e8073e525d4d6bd7e0f2（8559字节）。对应旧源码 SHA256 23a1f72752bfc8e6681069f3ecafe58a2b4d44727bdeb025ead4c93dfd41226a（15138字节/362LF）。这些报告和覆盖表已完整读取；五个被替换证明体不继承旧证明通过结论。

## T01.hSMeas：新57–61行

完整类型仍为 Measurable S。S 的初始化是 sampleSum n g，因此 change 的目标 x↦∑ i:Fin n,g(x i) 与冻结 RHS 定义相等。对任意 i:Fin n，measurable_pi_apply i 给出从乘积可测空间到 Ω 的坐标投影可测性；hg.comp 恰好给 x↦g(x i) 可测。Finset.measurable_sum 在 s=Finset.univ、值域ℝ上合并全部坐标，返回目标可测性。

新证明 lambda 的完整源码层类型为 ∀ i:Fin n, i∈(Finset.univ:Finset(Fin n)) → Measurable(fun x:Fin n→Ω => g(x i))。其初始化是源码60–61行的完整 lambda；自由捕获为 n、Ω、已有 mΩ、g、hg。i 与成员证明始终是全称绑定变量，没有选择坐标。对应数学函数族为 Fin n→(Fin n→Ω)→ℝ，初始化 (i,x)↦g(x i)，仅捕获 n、Ω、g；固定 i 的函数为 (Fin n→Ω)→ℝ，另捕获 i。它们是原 sampleSum RHS 的确定性显式表达，不是新增命名数据、样本选择器或实例。

全部构造只在该有限和应用内绑定；返回的 hSMeas 是原来的 Prop 证据，供后续 T01 使用。n=0 时有限和为空，证明参数对空 Fin 0 全称量化，既不需要 Ω 非空，也不选样本。

## T01.hQMeas：新62–67行

完整类型仍为 Measurable Q。change 把 Q 展开为 x↦∑ i:Fin n,(g(x i))^(2:ℕ)。每个 hg.comp(measurable_pi_apply i) 先得到坐标复合可测，再由 pow_const(2:ℕ) 得到同一坐标的自然数平方可测，有限和定理给目标。

该新证明 lambda 的完整类型是 ∀ i:Fin n, i∈(Finset.univ:Finset(Fin n)) → Measurable(fun x:Fin n→Ω => (g(x i))^(2:ℕ))，自由捕获仍为 n、Ω、mΩ、g、hg；i 与成员证明不外逃。数学函数族为原先已冻结的 squareFamily：Fin n→(Fin n→Ω)→ℝ，初始化 (i,x)↦(g(x i))^(2:ℕ)；固定坐标函数捕获 i。新用法没有改变该族或原 coordinateSq_i 的初始化。这里的2是自然数幂指数，未混同 MemLp 参数，也没有引入四阶矩、额外可积性或 Ω 拓扑条件。

## T02.hAprob：新279–283行

完整类型保持 M.real A≤(1/4:ℝ)。反证假设 hnot 的完整类型是 ¬(M.real A≤1/4)。实数线性序给 1/4<M.real A，sub_pos 得 0<M.real A−1/4，既有 hH:0<H 使281–282行初始化生成 hprod:0<H*(M.real A−1/4)。

另一方面，既有 hMarkA:H*M.real A≤N 和 hQuarter:H*(1/4:ℝ)=N 给
H*(M.real A−1/4)=H*M.real A−N≤0。
因此与 hprod 矛盾；nlinarith only 使用的恰好是这三个显式输入，环正规化即可闭合，不需要额外符号或乘法消去假设。新 hprod 类型捕获 H、M、A，传递地包含 n、Ω、mΩ；初始化另依赖 hH 与本块 hnot。hnot、hprod 只在279–283行反证块内有效，283行结束后不外逃。外层 hAprob 的原 Prop 类型及后续 hDprob 消费方式不变。

## T02.hCprob：新284–288行

完整类型保持 M.real C≤(1/4:ℝ)。该块自己的 hnot:¬(M.real C≤1/4) 给 1/4<M.real C，故差 M.real C−1/4 为正；既有 hH 使286–287行得到 hprod:0<H*(M.real C−1/4)。

此处使用的是 hMarkC:H*M.real C≤N。与 hQuarter 结合，H*(M.real C−1/4)=H*M.real C−N≤0，和本块 hprod 冲突。因此288行 nlinarith only 的三个输入足够。它没有误用 A 的质量或 hMarkA。类型捕获 H、M、C 及其 n、Ω、mΩ，初始化另捕获 hH 和本块 hnot；两个局部证据的作用域只到288行。它们与更早 hDA 证明中的两个旧 hprod 作用域互不混淆。

两个概率界都仅在已有 T02 正 n 前提下使用已建立 H>0；没有除以零、补充事件独立性或改动任何严格/非严格阈值。

## T03.hBMeas：新316–321行

完整类型仍为 MeasurableSet B。B 定义展开后恰是 |S x|≤2*sqrt N 与 Q x≤4*N 的交集。continuous_abs 在这里专化为 Continuous(abs:ℝ→ℝ)。实数的既有 Borel 可测空间把它转为可测函数，再与 hSMeas 复合，结果完整类型为 Measurable(fun x:Fin n→Ω => |S x|)。

绝对值函数本身的类型为 ℝ→ℝ、初始化 r↦|r|，没有新自由数学参数。复合函数类型为 (Fin n→Ω)→ℝ、初始化 x↦|S x|，捕获 n、Ω、S；其证据另用 mΩ、hSMeas。它只出现在第一个 measurableSet_le 的函数参数中，不产生全局函数、选择器或新实例。两个阈值均为实常数函数，第二项沿用 hQMeas。实数满足比较集合接口需要的有序拓扑、可测开集和第二可数条件，源空间 Ω 仍只需原可测空间。两个比较集合相交，定义上就是原 conjunction 事件；等于阈值的点完整保留。

hBMeas 在 n=0 分支之前构造，未依赖正 n；其结果可供后续零样本与正样本分支使用。

## 固定库接口与有效上下文

已核对冻结绑定的两个 primary packet：8b0093e4c53ce02e143201f21b89e0b41c8df2a8ea1c94b31f18c767bd23501c（51915字节）及 a7c4324ce1bc6bfdd4efb1008b5ff9de5dc9f56b9133809a19ea2615f80d3ff9（51775字节）。四份嵌入 raw source 的全部字节数和哈希均匹配，Mathlib pin 为 807d3836b165983210ee2ecf3cd28f239436949c。

Arithmetic.lean 第830–834行的 root Finset.measurable_prod 带 to_additive 属性，生成本次使用的 Finset.measurable_sum；完整有效前缀包括797行 CommMonoid 段及799–800行的全部变量、可测空间与二元可测乘法条件。加性版本在ℝ上专化为有限可测和。没有把附近 measurable_fun_sum 或 compositional apply 变体当成此接口。pow_const 的完整192行头、179–180行 Pow 上下文和168–175行自然数幂实例也已读。

measurable_pi_apply 的真实定义来自第二 packet 的 Constructions.lean 第584–585行，完整前缀明确结束此前所有段后进入570行 Pi 段，574–575行提供乘积可测空间。它不继承此前证明局部的 Countable/Nonempty/选择内容；δ=Fin n、X=(fun _=>Ω) 给本次坐标投影。第一 packet 的 Pi.lean 仅导入 Constructions，不能冒充定义所在文件。

Topology/Algebra/Order/Group.lean 的完整前缀到58行显示 root continuous_mabs 在28–29行的有序交换群及序拓扑背景下由 to_additive 生成 continuous_abs；本次在ℝ上专化，未向 Ω 添加拓扑。原已完整审查的 measurableSet_le 头与完整前缀精确复用并在本次确认ℝ的专化条件。全部接口详情、原头与完整前缀哈希记录在 PRIMARY-API-REVIEW.json。以上均为固定源码层接口核对；没有把生成头的源码推导写成实际 TYPE 探针。

## 全部字节、声明与作用域组合

独立回读核对了作者11个载荷、47个受保护直接绑定及33个旧封存载荷。原642字节的五段完整 helper 被本次1308字节替换；其余14496字节在六个不重叠未变分区中逐字相同。五个改变区与六个未变区在新旧文件上均无缺口、无重叠，合成15138→15804字节。

6个完整公开头、3个定义RHS、4个导入及开闭上下文全部不变。31个书写let逐项核对类型、初始化、捕获及原冻结作用域，其中2个为公开头内M、3个为hProbM局部实例、26个为其余证明let；三项 hProbM 初始化均保持字面值 inferInstanceAs(IsProbabilityMeasure(Measure.pi(fun _:Fin n=>μ)))。26项原承重数字的位置迁移与数字类型保持。原 c 的 Exists.elim 仍仅在新116–154行正 T01 分支，WOld/q及原数学数据初始化未改，旧尾项未被新增消费。

原57个书写have中，52个完整构造逐字不变、5个完整证明在本文重审；新增2个局部 hprod，故新源总数是59。原55项表与两条分支 hn 的覆盖均完整组合；两个 hn 分别移到新116行和334行，初始化仍是 Nat.pos_of_ne_zero hn0，作用域保持对应正分支。12个旧完整分支、14类原匿名数学表达式及4类原Prop闭包都逐字映射到相同词法绑定范围。五个替换块只在自己的 by 证明中新增绑定，没有改变外层任何绑定的可用性、返回类型或局部实例搜索。

这些59/31/6等计数是源码语法或审查映射计数，绝不是实际模块所属常量数。所有实际所属 TYPE、非定理完整 VALUE 与递归公理仍为 UNKNOWN。

## 失败保留、资格边界与下一依赖

原 native01 的失败是已知自然结束 RC1、7 errors、4 warnings、无对象；对应诊断与原 stdout/stderr/receipt 绑定完整保留。旧7个错误均落在本次五个完整替换块：两个 fun_prop 未展开、两次错误 mul_le_mul_left 应用各两条诊断，以及旧 abs 字段。本文没有把旧源码源码层审查误当成其内核通过，也没有重播失败请求或运行 native02。

本单元仍只给原幽灵样本固定好事件及二阶矩的局部接口；不推出 S11 指数上尾，C2/C12/OQ56 仍 OPEN，C1 immutablev85 完成，OQ3 仍按用户指示暂停。p54 修复、外部结果归因和原源意图边界不变；124统一机制不是前提。

父级下一依赖是对精确 fc4127… 修复源运行新的 native02；若首次成功，保留同一 FIRST 原对象，取得无命名空间过滤的全部实际所属 TYPE、所有非定理 FULLVALUE、名称组件/层级/完整体及递归公理服务器回执，再在新的 machine 子目录完成机器审查。公理白名单仍限 propext、Classical.choice、Quot.sound。本件封存后不回写旧 SOURCE 或本件。

本上下文 Lean/AX/server/upload/Git/API/child 调用均为0。一次本地 Python 入口解析失败没有进程或写入效果，已单独保留读取失败账，随后使用已有 Node 运行时完成确定性核对。配置模型/推理为 gpt-6.1-sol/xhigh；实际模型、实际推理与 input/cachedInput/output/reasoningSubset 用量没有可见遥测，全部记 null。
