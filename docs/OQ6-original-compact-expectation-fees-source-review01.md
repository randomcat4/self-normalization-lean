# 单元216独立完整 SOURCE 审查

结论：**CORRECT_SOURCE_ONLY_UNQUALIFIED**。完整新源码中的四个冻结声明和四段证明在数学及公共接口层面正确，未发现关键缺口、额外模型前提或未冻结的非命题数据。本结论只覆盖本报告绑定的源码；216尚无本轮服务器内核、实际所属声明 TYPE/FULLVALUE 或递归公理收据，故 `qualified=false`，实际编译声明数量为 `null`。

审查者是与作者分离的新鲜 SOURCE 上下文，指定 `gpt-6.1-sol/xhigh`。实际 provider、model、effort 及 input、cachedInput、output、reasoningSubset 遥测均不可得，分别记为 `null`。已使用 math-theorem 技能并读取其验证角色、工作流及 Lean 验证要求；项目的服务器独占权限约束优先，本轮仅本地读取和写入本审查目录。没有 Lean、服务器、网络、上传、Git/API、子代理、跨聊天消息、自动化或 Goals 操作，也没有修改作者、冻结、原文或只读 library。

## 精确对象和完整覆盖

审查源码为 `drafts/oq56/unit216/author-01/stage2/OriginalCompactExpectationFees.lean`，SHA256 `e7bb2776751571d424c9dea142ff5df7760b89e47ee65e49984e57748167bf65`，16022字节、348行/348个LF。它是无BOM的UTF-8、仅LF、恰有一个最终LF。完整读取了1–348行，并独立从源码提取四个头，与 `parent-freeze-v1.json`（`c55680f16fa5a139556df337ca9e94c80cd6d9bdeddfba24918fa3d2c39d993f`）逐字核对；前导环境也精确相同。源码三项导入、`autoImplicit false`、宇宙、命名空间、noncomputable段及两个scope均在冻结中，无section变量。

四个完整头/证明范围分别为23–29/30–47、49–57/58–59、61–67/68–91、93–161/162–344。已逐项覆盖全部21个公开头let、36个公开证明体let及6个辅助头let，共63个有类型数据出现位置；21个证明体镜像和15个新增别名均与冻结的完整类型和值相同。每项直接及有效外部捕获见 `COVERAGE.json`。

作者清单的42个have/haveI来自行首匹配；第42行另有 `· have hproduct`。本独立清单显式覆盖全部43个站点，包括该分支内事实；它们均为派生命题或派生Prop实例。这里补全的是审查清单，源码及冻结无须改变。四个源码定理头（1公开、3私有）、63个let、43个have站点均只是来源级清单，不能替代编译后的所属声明数量。

审查完整读取了阶段1的PROPOSAL和SOURCE-MAP；DATA-LEDGER的完整文本包含于已完整读取的冻结中，并验证嵌入文本与独立文件字节对应的文本完全相同。阶段1/2各6个载荷、阶段1的19项输入和阶段2的30项输入均经本地哈希及字节数核对。列示新封存文件、其216内部引用及145/212资格文件直接本地端点共124个引用出现、58条不同路径，全部精确；新的封存依赖图为17个节点、35条边且无环。范围界限及每个实际引用见 `bindingvalidation.json`；远端物理对象沿用旧资格收据，本轮没有探测远端。

## 原文、模型及公共接口

完整读取只读 `C:/game/shao/current/oq56/inputs02/p51.md` 的355行（SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`）。9–41行给出真实投影/典范残差模型及原始n统计量，83行固定删除后原n系数，115–123行给出无倾斜连续cap，130–163行给出原名B_y及其删除预算，272–311行说明真实L1及截断边界，313–323行是下游S27/CDF应用。216精确对应其中合并紧水平期望费用这一局部目标。

公开输入是任意可测观测空间、概率测度μ、真实实值核h、产品可测性、产品L2、逐点对称性、产品均值0、投影二阶矩1，以及n≥4、0≤z≤1、C₀≥0。g由同一μ的截面积分定义，r=h−g−g′，rho由同一产品残差二阶矩的平方根定义，P₀是原始Fin n上的μ乘积律。没有另外输入典范核、改变投影、变更概率律或样本数；实际模型的分析事实由已合格145的同一公共接口承载。原文关于任意可测空间的可观测因子说明并不要求本费用定理另加标准Borel假设；216也未声称实现编码或恢复整个原sigma域。

145资格文件精确SHA为 `52209bb4c43af677e77d1553d133c2589d69270e9747793f378872d2c059d44b`，源码为 `a7ab6509e2008e568c8707d4d07b517bd94797218347589193e65f7242dca111`，实际元数据为 `e28cd7f5e543cf50153825a45b31c96fc4d2621af73911f8fe2eb139524af623`。完整读取了其所用公开定理的413行实际TYPE（32040字节，SHA `c270b2a43d2c66bc6a3f61c1e8729bc8d9b6131509a17b27781206977b2a2b71`），包括全部模型、实例、24个局部数据及13个输出的展开结构。该字符串没有最终换行，故是413个逻辑行、412个物理LF；保留原字节。

212资格文件精确SHA为 `610607716c6ca99e343280596f0b50176bdf7446bcea3bc75e8338edfa35efdb`，源码为 `2a74d49a472f6015212a18db330ce7e81f31bae2885019219d10cf10ef35b5a0`，实际元数据为 `0c4558fa78ee42fc9d01c13a079d7c1da623473cd5a48e78db315031c33c7a2f`。完整读取了所用 `residualEnergyJ_eq_rowSqSum` 的TYPE、三个删除定义各自的TYPE和FULLVALUE，以及原D/J的实际定义方程TYPE；与145合计为7条TYPE、451个逻辑行/450个物理LF，3条FULLVALUE、43行。每条字符串独立重算SHA、字节和逻辑行数，均与阶段1所绑实际接口相同。

同时完整读取了本次需要的公开定义值：原 `residualStatisticD/residualU/residualEnergyJ`、原名 `studentizerClipBudget`、`originalUpper/originalRows`、`unorderedPairSum`、`rowSum/eraseIncident`、`truncationF`、三个删除定义及145完整公开头。没有重审145/212旧完整证明，也没有重跑旧producer或叶公理审计。

## 四段证明的独立核对

**分母控制（23–47）。** n≥4给q≥4，从而q>0、q−2>0及N=√q>0。除以正q−2得到1≤q/(q−2)≤2。下界使用 `(ratio−1)²≥0` 和ratio≥1给ratio²≥1；第42–47行的乘积 `(2−ratio)(2+ratio)≥0` 给ratio²≤4。这两步均为明确多项式不等式，故1≤kappa≤4，未以错误的平方单调性跳步。

**预算平移（49–59）。** 在q、q−2、N、sigma均非零时，Cprime=C₀(q/(q−2))²使其平方和项系数精确变为原C₀/((q−2)²sigma N)。减去delta=(Cprime−C₀)sigma/N只取消常数项的增量，因此对任意实L确有

\[
C_0\left(\frac{\sigma}{N}+\frac{L/(q-2)^2}{\sigma N}\right)
=C'\left(\frac{\sigma}{N}+\frac{L}{\sigma q^2N}\right)-\delta.
\]

`field_simp`所列的四个非零前提覆盖全部新除法。没有除以rho、C₀或L；恒等式不要求L非负，也没有把原预算冒充成145在原C₀处的预算。

**标量128界（61–91）。** C₀≥0和kappa≤4给 `1+C₀*kappa≤4(1+C₀)`；z的范围给0≤1+z≤2；rho≥0给0≤1+rho≤1+rho+rho²。每次乘不等式所需的因子非负均由显式前提提供，最后按正N同除。系数是16·4·2=128；辅助头中未使用的kappa下界不会增添公开前提。

**公开定理（93–344）。** 162–222行先还原全部冻结数据。223–244行从输入概率实例推出同一P₀的规范概率实例，rho≥0及sigma>0；分母辅助引理给q、q−2、N正及kappa范围；进而Cprime≥C₀≥0、delta≥0并推出n≥3。这里没有额外输入的概率、矩、独立性或正性前提。

245–268行只在Cprime处调用一次145公开定理，μ、h、全部模型假设、n、z都不变。`change`所需对应确实为定义相等：原D的 `originalUpper` 与 `unorderedPairSum` 都是Fin n上同一双和 `if i<j then r(x_i,x_j) else0`；Ddel是同一擦除关联边双和；两个分母均是√n(n−1)。A/Adel均为对应D的绝对值。原始律、投影测试、真实截断和及连续cap也逐字对应145数据；其预算改用Cprime后正是216的Bprime/Bprimedel。不存在依赖未证的“相似性”改写。

269–280行所用212公开恒等式不带额外条件，给J=LambdaSq/(q−2)²；Jdel的同式直接来自完整删除定义。原名完整/删除预算均在y=1处简化为 `C₀*(sigma/N+J/(sigma*N))` 及其Jdel版本。删除仍在Fin n上进行，原n−2没有替换为n−3或n−1，预算也没有插入好事件指示。

281–300行对两个平方和应用同一标量平移引理，得到 `B₁=Bprime−delta` 和 `B₁del=Bprimedel−delta`。因此删除差逐点完全相等，绝对值及cap加权之后也相等。这个抵消不是期望意义的近似，也不要求两个平方和相互独立。

301–316行先从145的真实Bprime/Bprimedel可积性减去可积常数，得到原名B₁及每个B₁del的真实L1；常数可积性由P₀概率性给出的有限质量支持。再用精确删除差搬运cap加权差及合并删除测试的可积性。A、Adel及投影的L1直接来自相同145输出。没有用Lean全域化积分的一个实数值冒充可积性，也没有引入混合四阶矩。

317–327行是在上述可积性之后使用 `integral_sub`；P₀总质量为1，使常数积分恰为delta。因此预算积分差精确为delta，删除测试之和精确不变，合并起来

\[
\mathrm{residualFee}=\mathrm{residualCostPrime}-z\delta.
\]

328–335行用z≥0和delta≥0得到原费用不大于prime费用，再接145的16界及标量128界。336–340行由 `(1−z)(3+z)≥0` 精确推出 `(1+z)²≤4`。341–344行的最终元组依次提供全部16个冻结结论；最后一项只在已证费用上界两侧加真实Lcompact，没有把截断和丢掉或替换成p矩衰减率。

## 数据、捕获及边界

唯一外部非Prop实例是公开的 `MeasurableSpace Ω`。产品/有限乘积可测结构由它规范生成；Fin n的Fintype、序和可判等、实数的有序域/范数/可测/积分结构均为既有规范结构。`IsProbabilityMeasure μ`和唯一新局部 `IsProbabilityMeasure P₀` 都是Prop；后者仅通过同一乘积律的既有实例推导。classical作用域只提供可判定性，没有选择出的新样本、选择器、改造的sigma域或替代测度。三个私有头绑定其全部标量参数，均无模型/实例的ambient捕获。所有局部ξ、i都是逐点命题或funext内的绑定变量，没有逃逸或加入公开假设。

n=4时q=4、N=2、q−2=2、kappa=4、n−1=3，所有实际分母正。rho=0时sigma=1，证明没有除rho；C₀=0时Cprime=delta=0且两个预算恒为0，证明没有除C₀。z=0时cap阈值1且zdelta=0；z=1时阈值1/2、1+z=2且Lcompact≤4。一般0≤z≤1还保证1+z≥1。cap及真实truncationF连续，截断边界原子无需排除；没有原子性、零边界质量、额外四阶矩或good-event前提。

`COVERAGE.json`逐项记录全部数据完整类型/值、捕获、43个局部命题、18个rcases命题绑定及16个输出。实际编译后产生的私有/生成/外前缀所属声明与其捕获仍需服务器输出核对；本轮没有由来源级名字预测这些数量。

## 资格边界和后续核对

此单元只给原始无倾斜、连续cap的**合并紧水平期望费用**及真实Lcompact恒等式/二阶界。原p51的 `UNCERTIFIED_REPAIR_CANDIDATE` 状态、Shao–Zhou(2016)外部归属和继承的p54修复边界均保留。sharp individual rho/rho² S26叶子、Lcompact的p矩速率、S14倾斜/部分倾斜费用、随机区间定理/CDF/SZ Theorem2.2应用、零分母付款、S11、general S15、DC、full OQ56/root closure及新颖性均未由本单元关闭。

本地绑定助手的首次断言把145 TYPE的逻辑行数413误当物理LF数412，未写出任何审查结果或改动输入。失败及更正保存在 `local-validation-attempt01.json`；更正后全部绑定通过，原字符串无须修改。

本报告可作为该精确源码的完整独立SOURCE覆盖。下一步由父级在当前资源/锁约束下执行新源码native，成功后对**同一个首次原始对象**输出所有实际所属TYPE、所需非定理FULLVALUE及递归AX；届时由本同一独立审查者核对全部实际输出、源码/对象/收据绑定和标准公理白名单。未变源码沿用本次完整SOURCE覆盖，不自动重读旧完整证明、不重跑旧145/212producer或叶AX。任何后续证明字节变化须单独界定受影响证据。

本轮完成后无自动继续、排队操作或延期补写。writer/heavy/inflight/pendingExternal/uncertain/children均为0；普通final将结束当前审查回合。
