# 单元186独立完整源码审阅

`STATUS: CORRECT`，仅指下述精确版本的原文到陈述、完整证明候选、数据和作用域审阅。`qualified=false`；186的服务器原生内核与全部实际所属声明的类型、非定理完整值及递归公理证据均待到达，实际所属声明数量为未知。本报告不声称已经展开或编译成功。

审阅绑定 `author-01/stage2/FiniteMatrixSignEnergy.lean`，SHA256 `920a18830fe17b36684a3c4f27787db74b85800edf968b0556675102ae370515`，5516字节、101个LF、无CR/BOM、单个终结LF。审阅者为新独立上下文 `/root/oq56_matrix186_final_review01`，没有参与作者实现，没有修改作者文件。全部输出限于 `drafts/oq56/unit186/final-review-01/`。

## 结论与唯一证据映射修正

没有发现本固定矩阵接口的数学、前提、实际库接口或证明逻辑缺口。9个完整声明头、4个完整定义值、原前缀和后缀均与父级冻结文件逐字相同；独立检查全部声明的字符和UTF-8字节区间、声明哈希均一致。120条本地证据引用的字节数和哈希比较全部通过；这些是引用记录数，不能当作独立文件数、Lean声明数或机器检查次数。

发现作者 `source-local-scopes.json#/actualSubstantiveEmbeddedExpressions/9/sourceRegion` 将 `rademacher_matrix_moment_bound/producerColumns` 记为85–70行，终点倒置。独立 `evidence-mapping-correction.json` 保留原文件哈希和原条目，绑定正确85–86行、UTF-8零起始半开字节区间 `[4701,4799)`、完整调用、`column n D` 的完整类型与初始化可见性。单独表达式 `column n D` 位于86行、字节 `[4782,4792)`。这项独立覆盖补足证据定位；作者源、冻结值和作者元数据均未改写，也不需要重复185证明或Lean检查。

## 原文范围与形式陈述

已完整阅读实际只读输入 `p44.md`、`p51.md`、`p54.md`。本单元对应p44第一节固定向量符号矩不等式(3)及紧随的点态Hilbert–Schmidt包络界。p44的原随机矩阵来自鬼样本、对称且零对角；这里的点态适配允许任意实矩阵，删除这两个条件后本段代数与固定向量矩不等式仍成立。它没有把随机交换不变性、条件Jensen或外层积分隐藏在前提里，也没有宣称已经实现这些概率步骤。

精确对象是任意自然数 `n`，实矩阵 `D : Fin n → Fin n → ℝ`、权重 `W : Fin n → ℝ` 和实数 `q`。两份矩界仅增加显式 `∀i, 0≤W i`、`∀i j, |D i j|≤W i*W j`、`2≤q`。行坐标公式和列能量恒等式不要求这些不等式前提。定义 `S=Σi W i²`、`E=ΣjΣi D i j²`；结论为 `E≤S²`、`sqrt E≤S`，以及完整欧氏行向量范数的有限符号平均和真实Rademacher积分的q次矩根都不超过 `2*sqrt q*S`。积分版本同时返回真正 `Integrable`，没有仅依赖Lean在不可积情形下的默认积分值。

常数为字面实数2，在所有n、D、W、q之前固定。q是任意实数，未改成自然数或偶整数。没有对称、零对角、n>0、正能量、严格正权重、额外矩条件或新增概率法则。`weightEnergy` 是权重平方和；没有把它误写为权重和的平方再取一次矩根。

## 完整数据与实际库实例

`column` 的完整冻结值是 `WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ) (fun i : Fin n => D i j)`。`rowAction` 是真实欧氏列的有限向量和 `Σj w j • column n D j`。`matrixEnergy` 固定外j内i的所有元素平方和，`weightEnergy` 是同一 `Fin n` 上的权重平方和。这4个值均已完整阅读，没有新增局部数据、函数、实例、选择器或私有helper。

已读取哈希绑定的完整主源中的全部承重声明、值和环境：WithLp第1–244行中的结构、构造器、投影、加法群/标量/模实例及 `ofLp_sum/ofLp_smul/ofLp_toLp`；PiLp的类型别名、函数强制转换、`toLp_apply`、有限索引条件、Norm定义、二范数公式及范数群/范数空间实例；PiL2第1–169行中的内积实例、`EuclideanSpace` 别名及 `real_norm_sq_eq`。三个嵌入完整主源文件的哈希、字节和行数独立一致，钉死Mathlib为 `807d3836b165983210ee2ecf3cd28f239436949c`。

具体地，`EuclideanSpace ℝ (Fin n)=PiLp 2 (fun _=>ℝ)=WithLp 2 (Fin n→ℝ)`；函数强制转换用 `WithLp.ofLp`，代数结构从普通函数空间继承，范数则是PiLp的二范数。`Fin n` 对每个n都有Fintype，二范数的Fact(1≤2)不要求维数非空。没有把底层普通函数空间的上确界范数带入列能量或矩界。`EuclideanSpace.real_norm_sq_eq` 的完整实际主源只要求Fintype并取真实欧氏向量，恰适用于每一列。

基础实有序环、有限和、平方根及乘法保序接口均按33条使用点记录逐一核对其完整预期契约与实际实例类型，包括 `sq_le_sq₀` 的两个非负前提、`sqrt_sq` 的S非负前提，以及最终 `mul_le_mul_of_nonneg_left` 的非负系数。没有以这些预期契约冒充186尚未产生的机器实际TYPE。

另外定向读取既有只读库中 `Shao.Path`、`RademacherGrid.radMeasure`、`RademacherCosine.halfENNReal/law` 的完整定义及环境：路径确为 `Fin n→ℝ`，真实法则是既有 `Measure.pi (fun _ : Fin n=>law)`，边缘是各半权重的±1 Dirac和。只读 `FiniteRows/ResidualRowExpansion` 的模块范围和有关行定义亦确认属于p39的有限确定性行/jackknife代数；本报告不把它们宣称为本单元的符号矩或概率依赖。

## 五个证明的逐项审阅

1. `rowAction_apply`（21–26行）：`change` 只展开真实行作用和PiLp的函数强制转换。`WithLp.ofLp_sum` 在底层 `Fin n→ℝ` 加法交换群上取出整个有限和；`Finset.sum_apply` 再在坐标i求值，`ofLp_smul` 和 `Pi.smul_apply` 把实标量作用取到坐标，`ofLp_toLp` 与 `smul_eq_mul` 得 `Σj w j*D i j`。i始终是公开参数，j只在相应求和中绑定；没有转置成 `D j i`。
2. `column_energy_eq`（28–33行）：展开185能量和本单元矩阵能量后，在同一外j上用 `Finset.sum_congr rfl`。对每列应用完整主源 `real_norm_sq_eq`，再以 `column/PiLp.toLp_apply` 化简每个坐标，得到 `‖column j‖²=Σi D i j²`。列数和坐标维数均为原n，没有维数损失或只取对角。
3. `matrix_energy_bound`（35–62行）：先由有限平方和给 `hS:0≤S`。`hE` 对外j、内i两层有限和保序；逐项用 `Dij²=|Dij|²`，由 `abs_nonneg` 和 `mul_nonneg (hW i) (hW j)` 满足 `sq_le_sq₀` 的全部条件，把 `hD i j` 提升到平方界，实环运算得到 `Wi²Wj²`。逆向有限分配律先提内和、再提出外和，得到 `S*S=S²`。这只是有限代数，不需要Fubini。最后 `sqrt_le_sqrt hE` 和 `sqrt_sq hS` 得第二分支；没有除以S或E。
4. `finite_matrix_sign_moment_bound`（64–81行）：把185已合格的固定Hilbert向量矩定理特化到 `n n (column n D) q hq`。两个维数都精确是原n，完整向量族类型为 `Fin n→EuclideanSpace ℝ (Fin n)`。`hilbertConstant` 的完整实际值为2，列能量恒等式把右侧变成 `2*sqrt q*sqrt E`。第76–77行的 `rfl` 有真实定义支持：185的moment是cubeMean中的signSum范数q次实幂，而 `rowAction(signPath s)` 展开后同为 `Σj signValue(s j) • column j`，包括相同加法/标量实例。最后以 `0≤2*sqrt q` 将 `sqrt E≤S` 乘入，得到冻结结论；没有借新的矩假设。
5. `rademacher_matrix_moment_bound`（83–97行）：`hbase` 是185同一真实测度定理的完整合取Prop。第一分支只展开 `pathSum/rowAction` 返回实际被积函数的可积性。第二分支对同一积分函数、同一radMeasure和同一q使用hbase的矩根界，以完整常数值和列能量恒等式化简，再乘入 `sqrt E≤S`。没有替换成代理测度，没有单独对各行取绝对值，也没有暗加全局可测性条件。

这五份证明完整覆盖当前源码，没有归纳或循环依赖。相同有名 `hbase` 属于两个不同定理的局部Prop，互不共享；当前较后结论只使用较前已完成声明。

## 初始化、索引与退化边界

已完整核对53个冻结作用域记录的类型、全部函数值与可见参数；200个有序词法事件独立检测顺序和嵌套栈，均平衡、无前向或同级索引泄漏。9个全局声明只在各自完整声明结束后登记。此数量是源码计划的词法记录，不能替代机器的binder或owner清单。

当前源码4个普通Prop初始化全部完整核对：`hS:0≤weightEnergy n W` 只见n,D,W,hW,hD；`hE:E≤S²` 在初始化时另可见已完成hS，但不能用自己；有限矩hbase只见该定理完整参数；真实积分hbase的完整类型包括同一函数和测度的Integrable与矩根界，初始化时也不能见自己。hbase完成后仅在本定理内可用。普通Prop不需要额外行政冻结。

所有实际显式证明索引的类型均为 `Fin n`：列能量证明的j与univ成员Prop；双重求和比较中的j、i和各自成员Prop；hS证明lambda中的i和匿名成员Prop。11条嵌入表达式记录只是冻结列、求和函数或公开被积函数的重复/束缚变量改名，未构造新的局部数据函数。第9条的行范围采用本独立纠正项；表达式的类型和值、完整Prop调用、初始化可见性均已补足。

n=0时，列索引无元素，欧氏向量唯一且为0，所有行/矩阵/权重能量都是空和；布尔函数空间有唯一空函数，cubeMean权重为1。q≥2使0的q次实幂及其正矩根为0，185接口本身覆盖空维数。全部或部分权重为0、矩阵零能量均不触发能量除法；若全部权重0则支配强制D=0，若E=0也由平方和非负得到D=0。非对称和非零对角均在精确公开范围内。

## 上游复用与未支付义务

185精确源SHA256为 `f5e4f873f4e6a2b10dfad014a2e3ac0341fb277bf970a206091342c95121350a`，原成功对象SHA256为 `bdb6542999a10e63f19e9c14d0e98e39cd648821edd95e5ec3a3e2f8ca24e39d`。父级资格与独立资格、完整最终报告、作者/审阅者释放以及实际元数据的哈希绑定全部核对。186材料中的13项公开实际TYPE及8项非定理完整FULLVALUE逐项等于该实际元数据条目；已完整阅读其类型、值、实例、条件与递归公理项。

复用185已完成的独立完整证明/全部67实际owner资格，不重审其不变内部证明。原native04及同对象全owner审计均RC0、零错误；30/1警告、严格包装器false、非FIRSTEMPTY及此前17/3/1错误的三次失败均保留。185的成功不能作为186内核或186公理通过，也不能把9个186源码声明误当作186实际owner数量。

本单元未支付随机鬼样本D构造、双侧符号交换的联合分布不变性、条件Jensen、外层随机积分/Fubini、原随机行能量尾、标量二阶混沌、DC或研究根结论。p51 S18的原非线性基核行集中仍归属Shao–Zhou Lemma6.1；p54对条件p矩变化率的反例、仅收敛/统一有界修正和实际上尾严格余量付款保持原范围。本次没有审定p51/p54整条概率链，也不作新颖性声明；无183/184数学依赖。C2/C12/OQ56仍OPEN，OQ3仍PAUSED_BY_USER。

后续同一独立上下文只需承接精确186原生内核及整个实际module-index所属声明的完整TYPE、非定理FULLVALUE、递归AX，核对私有和生成项及完整源/对象绑定，才可最终资格。公理白名单仅 `propext`、`Classical.choice`、`Quot.sound`。任何源变化仅重审受影响范围。本审阅全部Lean、服务器、网络、Git、上传、缓存、子代理和锁活动均为0；请求配置为gpt-6.1-sol/xhigh，平台不可见的实际模型、effort及分项token均记null。
