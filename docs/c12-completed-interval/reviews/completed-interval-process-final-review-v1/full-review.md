# 两个实际区间完成单元的独立完整终审

STATUS: CORRECT

本结论仅认证下列两个精确冻结版本的局部陈述、完整源证明、实际所属类型和定义值。不存在关键缺口。它不认证完整 C1/C2 停止补偿定理，也不扩大任何原始根命题的已闭合范围。审查者为独立新上下文 `/root/completed_interval_process_final_review`，实际指定 `gpt-6.1-sol / xhigh`；没有参与实现、修改冻结或生产源码、运行 Lean、重跑公理审计、重审已合格旧证明。

## 精确版本和覆盖

| 单元 | 生产源 SHA256 | 冻结 SHA256 | 对象 SHA256 | 回执 SHA256 |
|---|---|---|---|---|
| `Shao.C2.SourceIntervalCompletion` | `7a00c4b90e69cc4d39362e7822c4d621a18cc94c602c60fbf8c58d0033470dc2` | `fb417e90562eed1e37f58379b1bd11497949176924cc5fbfdeb515c1d57fb68c` | `9c0d93e9b459380e2068cae5a7e6175d1fd4cdf7efe5d81680306b33d84f6c0d` | `7c44171fa88b71391701506141af2bc0448984a29dce18c35383453f982bfb74` |
| `Shao.C2.CompletedIntervalProcess` | `4eb92978f511cb1c26a35b56dfd1e6e59d46f230852813ce38c500898f62f076` | `39b75f60f37a023fafd328a2b78dd9fe3afe4e8668a8a20befc661a43edb7db0` | `5edfd0e16a2d8e3a1acd962cd371d2d722a51be5ae94b24b774160dae3d2c15f` | `0db9b3b0e70470e8e37a500fe4a524e58a291ef9660e24bc76e72007a999f6d8` |

完整读完两份生产源的全部 17 个公开源定理证明和 3 个定义；全部冻结头与完整定义值和成功源码逐声明去除空白后相同。第一单元为 10 个实际所属常量：9 定理、1 定义，其中 2 个生成定理。第二单元为 15 个实际所属常量：13 定理、2 定义，其中 3 个生成定理。共 25 个完整实际类型、3 个完整非定理值均已审查。

完整类型/值的阅读采用 TEAM 许可的无损相同子表达式字典：39 项字典全部阅读一次，全部非重复上下文、绑定、实例、目标和定义值完整阅读；四份新单元文件及 6 份消费依赖文件均逐字节恢复原文，见 `lossless-reading-manifest.json`。这不是声称逐字重读重复的原始字节。类型原始文件分别为 84278、102702 字节；值文件分别为 7590、9899 字节。未省略任何声明、绑定或值，也未把巨大的已核验定理内核证明项当作必读展开值。

所有者依据实际 `env.getModuleIdxFor?` 映射选择，不使用命名空间或源定理数代替覆盖。特别是 `Shao.C2.BridgeDomination.intervalCompletion.eq_1` 实际属于第一新单元，`Shao.C2.RawInitialCompletion.rawInitial.eq_1` 实际属于第二新单元，二者均完整审查并计入 25。

## 原文到定义

完整读取 `C:/game/shao/current/c12/main.tex` 871–956、1038–1076 和 `supplement.tex` 4192–4252。原文正剩余时间下的严格区间桥事件、外端点及等号杀死、原始墙和平方和、固定全样本后的标签揭示，与实现一致。

第一单元定义正 T 为既有 `intervalCompletion ν a y T z`；T=0 只在 y=z 且 |y|<a 时取 1，其余取 0；负 T 赋 0 是原文剩余能量域外的显式全定义约定。它没有把不同端点的零方差确定性插值移植到实际停止过程；原文仅在终端包络允许该插值。对任意 ν 的通用噪声族不等同于已证明 Brownian 杀死核/自由核商，后者仍开放。

第二单元在固定完整有限原样本 z 和标签排列 σ 上定义 V。`strictLive` 检查所有自然数 j≤k 的实际重排前缀和，包括 j=0；墙始终为 x√Q，Q 为原样本真实平方和，终点始终为原样本总和。剩余量严格是 Q−Qk，不是确定性方差。V 同时具有 Q>0、全前缀严格存活、原终点内部三个守卫。固定 z 后总 Q、总终点和墙可在时刻零获知，吻合原文条件揭示信息；这里没有宣称原 iid 自然滤过的停止性质或独立同分布重排律。

## 第一单元逐证明核验

1. `sourceIntervalCompletion_pos`：正 T 消去第一条件分支；ν 无概率假设也成立。
2. `sourceIntervalCompletion_reachable_zero`：T=0、重合端点恰余严格内部条件，内部 1、壁上及外部 0。
3. `sourceIntervalCompletion_zero_nonreachable`：T=0、不同端点拒绝第二条件分支，得到 0，未误用插值。
4. `sourceIntervalCompletion_exterior`：从严格区间事件在实际 t=0、1 的值和已合格 `bridgePath_endpoints` 得到两端严格内部；否定此条件使事件为空。正时间的任意测度对空集为零；零时间重合分支同样与外端点假设矛盾。没有忽略边界原子。
5. `sourceIntervalCompletion_nonpositive_wall`：|y|≥0 与 a≤0 排斥 |y|<a，再消费外端点结论；覆盖 a=0。
6. `sourceIntervalCompletion_bounds`：正时间消费已合格 `completion_bounds` 的最后两项；其余两分支为 1 和 0。概率测度前提完整保留。
7. `measurable_sourceIntervalCompletion_parameters`：参数准确为 a,(y,(T,z))；正时间集合、T=0、y=z、|y|<a 均可测，嵌套分段函数消费已合格四参数可测接口。保留 SFinite ν，没有偷偷要求概率律或删去零时间面。

两个生成定理分别展开 `sourceIntervalCompletion` 与既有 `intervalCompletion`，其完整实际类型准确保留上述分支和 `ν.real strictInterval`。

## 第二单元逐证明核验

1. `measurableSet_strictLive`：排列坐标映射逐坐标可测；每个前缀绝对值和固定原始墙的严格比较可测；对 j 及 j≤k 证明索引取可数交。源中的 `setOf_forall` 转换与完整实际目标一致。
2. `measurable_completedValue`：四参数映射为 (x√Q,(Sσk,(Q−Qσk,Sn)))；三个守卫均可测，正分支消费第一新单元的精确接口。ν 的 SFinite 前提与实际产品可测结构无缺失。
3. `completedValue_bounds`：守卫成立时消费第一新单元界，失效时为零；结论对任意 x、n、k、σ 有效。
4. `integrable_completedValue`：在概率 P 上由常数 1 可积支配；独立提供可测性/几乎处处强可测及 |V|=V≤1，不将有界性本身误作一般无限测度下可积性。ν 和 P 的概率前提分别完整保留。
5. `completedValue_initial`：x>0、Q>0 时 x√Q>0，秩零全部前缀只含零，初始严格存活成立；内部终点直接得到原始 `rawInitial`，外终点由桥事件为空消去；非正 Q 分支双方都零。未替换原墙、总能量或总终点。
6. `completedValue_dead`：已有任一 j≤k 触壁或越界使全前缀存活失败，条件分支为零。之后回到内部也不会复活。
7. `completedValue_exterior`：原总终点不满足严格内部时直接使守卫失败，包含等号。
8. `completedValue_zero_energy`：Q=0 直接否定严格正能量守卫，所有参数下为零。
9. `completedValue_terminal`：`Equiv.sum_comp` 对实际排列分别给出满秩前缀和=原总和、满秩前缀平方和=原 Q；故 T=0 且端点重合。存活在 j=n 的条件确保内部，再以可达零时间值给出 1；其余守卫为零，恰得 Q>0 且 strictLive 的指示量，无噪声律条件。
10. `completedValue_reveal_observable`：固定完整 z；前 k 个位置上的标签相等给出每个 j≤k 的前缀和相等及第 k 个平方和相等，进而全部存活守卫等价；分别处理条件真、假，并保持全样本原始 Q、Sn、墙固定。重复坐标值不影响标签证明；没有从数值相等推出标签相等，也没有把结论加强为原 iid 滤过可测。

三个生成定理完整审查：`strictLive.eq_1` 保留 ∀j、j≤k、严格不等式；`completedValue.eq_1` 保留三个守卫及真实四参数；`rawInitial.eq_1` 保留 Q>0 的原始值和零分支。

## 冻结上下文与边界攻击

终端定理前的 `open scoped Classical in` 只为冻结的 if-命题提供 `Classical.propDecidable strictLive`。已完整阅读的实际类型没有新增 `Decidable` 参数、数学假设或新公理；完整 if 目标仍与冻结陈述相同。`maxHeartbeats 1500000` 仅局部作用于 `measurable_completedValue` 的 elaboration，不改变类型、定义或内核规则。

检查 n=0 时 Q=0，V0=Vn=0；没有隐含 n>0。Q=0、x≤0 或墙非正均不可能产生严格 rank0 存活，Q 守卫亦明确归零。墙上等号及两端外部均被严格杀死。先越界后返回的路径不会因当前端点在内部而复活。对重复值仅使用标签的双射及前缀标签一致性。k 未限制在 n 内的推广仍有定义，因为基础前缀按 i.val<k 饱和；源应用只消费 k≤n 的秩。中间 k<n 且剩余 Q−Qk=0 的可达端点重合证明尚未包含在本次认证，不能从终端 n 情形冒充该结论。

## 复用接口与机械证据

已核对三个既有独立完整审查 JSON 的精确哈希和其源、对象、回执；没有重审旧证明。消费的 12 个完整实际接口类型和 9 个完整透明值均通过无损阅读完整检查：BridgeTime/BridgeNoise/bridgePath/strictUpper/strictLower/strictInterval/intervalCompletion、bridgePath_endpoints、completion_bounds；CompletionParameters 和四参数区间可测性；rawInitial。基础有限路径及可测路径源码的完整消费头、路径/前缀和/平方和/能量值也已阅读并与服务器相应已接受文件绑定。`PermutationCompensation` 是导入环境，没有在本单元宣称其完整停止结论。

复用审查哈希分别为 BridgeDomination `568c781dac68a0ecb79e401897d30ceaa70dead2966fa77f47f9972406b29ed2`、CompletionMeasurability `6f2a03f8ce7c54772ca4fd966558bbd986b26471a6401741b0eada31e7e08ff7`、RawInitialCompletion `36e16656f749cc5d38d2746e5470303c264afa0c91685a4f463022b10678c559`。

通过现有 `tools/server.py` 做一次只读绑定，核实 34 个服务器工件，包含两个成功源码、对象、全部回执工件、失败版本和日志、依赖源码/对象以及消费的共享源码。完整实际类型/值的每个块与原审计日志连续文本精确一致，无省略标记。两个原成功命令为 attempt002 / attempt003，内核退出码和公理审计退出码均为 0。全部 25 个实际所有者递归 `collectAxioms` 均仅含 `propext`、`Classical.choice`、`Quot.sound`。禁止的 sorry/admit/新增 axiom/unsafe/native_decide 均未出现。

工具链仍为 `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，已接受只读 package view 为 `shared-v34/packages`。服务器观察 head `6fcd7beb1e4fcc586c32b205956b576952799962`、branch `author/c12-integrated-telescope-v71`。日志只有既有 package 本地变动提示和弃用名称警告，没有失败。未重建、取缓存或改变环境。原失败 attempt001/002 及其哈希均保留；修复只有证明形式和上述局部 elaboration 上下文，完整冻结头和值不变。

## 接受范围与释放

接受源约定的实际区间完成扩展，及实际有限原路径上的严格存活完成过程之可测性、有界性、概率测度下可积性、原始初值恒等式、死亡/外端点/零能量归零、终端存活指示量和固定全样本的标签前缀可观测性。

中间零剩余能量的可达性、完整 FY 构造和导数/PDE/杀死核商、完整停止补偿实例、重排 iid 律传递及终端/越界解析估计均仍开放。全部原始 C1/C2/OQ3/OQ4/OQ56 根组保持 OPEN；无新颖性主张。

只释放本独立审查者的报告/证据写入及执行权。无在途调用、无活跃重型进程、无生产写权；C12 lead 的所有权不释放。交回 `01a16c4c-25a6-7740-a10e-12635a13edae` 消费两个精确合格版本，并继续下一实际源依赖。实际 token 分项不可见，input/cachedInput/output/reasoningSubset 均记 null。
