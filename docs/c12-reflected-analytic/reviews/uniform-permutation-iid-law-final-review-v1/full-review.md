# 独立终审：均匀排列后的完整独立同分布律

STATUS: CORRECT

JUSTIFICATION: 最终冻结的三个定理和一个完整定义均得到对应证明；原始标签样本与排列使用独立乘积测度，重排后的完整路径律由原 iid 假设推导，而非作为新假设。给定原乘积律下的可积性先被传递到联合空间，再使用 Fubini。未发现关键缺口。

## 审查对象与独立性

本审查者为全新独立上下文 `/root/uniform_permutation_iid_law_final_review`，配置为 `gpt-6.1-sol` / `xhigh`。没有参与声明设计、证明实现或修改；只写本审查目录。作者已精确释放源码和执行权，`RELEASE.json` 的 SHA256 为 `5af77f8c29b39c5ffcc66fd82d8c26dbb115a424248a3c4e344744e31ef3b909`，其源码、对象、收据绑定及零在途状态均已核实。未启动子代理，也未调用 math-ultra。

最终源码为 [UniformPermutationIIDLaw.lean](<C:/game/shao lean/drafts/c12-lane/uniform-permutation-iid-law-v1/author/UniformPermutationIIDLaw.lean>)，SHA256 为 `981224211cc8601efb0bdddc85d332ae6b1d5f669d9549fb4e5b8a1527e8092e`；服务器对象 SHA256 为 `d16844a157b7a52aed2cf268315c472884ebe370b2ba58c42a1d3c2451dd5436`。冻结文件 SHA256 为 `c3c080bdff0f37d4820e1f8b6a08db3cadf3479c0a843caa57c2dcf13c0cdc82`。审查者独立逐字节比较了全部 imports、三个完整定理头以及 `reorderedSample` 的完整定义，均与冻结版相同；最终源码为无 BOM 的 UTF-8、LF，CR 数为零，禁用项扫描通过。

## 原文到形式陈述

完整读取了只读 `C:/game/shao/current/c12/main.tex` 第 902–955 行，包括第 915 行开始的“期望同时包括样本及其独立排列”说明，以及第 950–955 行的无条件重排律说明；另核对第 150–152 行原 iid 背景。原文件 SHA256 为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`。本单元只承接“无条件重排序列仍有原完整 iid 顺序律，因而可平均转移确定性秩估计”这一依赖。

形式化保留任意原概率空间 `(Ω, μ)`、实数共同概率律 `ν`、每个原坐标的可测性、整个原族的 `iIndepFun X μ`，以及每个坐标与 `id` 在 `μ, ν` 下的 `IdentDistrib`。排列使用已实现的 `uniformPermutationLaw n`，原空间扩展为 `μ.prod (uniformPermutationLaw n)`。因此随机标签确实独立于原样本。函数的实际完整值正是 `X (σ i) ω`，没有排序、去重、数值置换或样本依赖的选择器。

结论是真实 `HasLaw`，其第二字段为完整推前测度等于 `Measure.pi (fun _ : Fin n => ν)`，并非只给若干坐标的边际或有限测试函数相等。积分定理的左侧保持先在固定原样本上对独立均匀标签积分、再对原样本积分；右侧是原完整 iid 路径律下的 `F` 积分。`hFint` 是原律下给定的可积性，不是待证联合律或待证期望等式。

原文更强的中心化、正有限方差及 `n ≥ 1` 背景不被此通用重排事实使用；本声明在更一般的分布和任意自然数长度下证明同一转移事实，未将原根定理的其他条件移除或声称原根已闭合。

## 全部证明与实际声明审查

已直接完整阅读 3176 字节生产源码中的全部证明、6665 字节四个无省略实际类型及 535 字节唯一完整非定理值。实际所属清单与类型块逐项相等；四个类型块和一个值块还分别与成功服务器审计日志中的连续原文精确匹配。

| 实际所属声明 | 完整审查结论 |
| --- | --- |
| `reorderedSample` | 实际类型只有自然数长度、任意宇宙的原空间、原坐标族及样本/排列对；完整值逐点为 `X (p.2 i) p.1`，与冻结定义及原文标签重排一致。 |
| `measurable_reorderedSample` | 源码第 14–19 行按固定排列逐坐标可测，再使用可数第二因子的联合可测性引理；没有添加原空间可数性或拓扑条件。 |
| `iid_reorderedSample_hasLaw` | 源码第 21–43 行先证明联合可测性，再逐固定排列由原 iid 族得到完整截面律，最后对独立的真实概率排列律平均并用测度外延性闭合。实际完整类型中的概率实例、独立性及边际律均与冻结版相同，没有把重排律当作前提。 |
| `iid_iterated_reordered_integral` | 源码第 45–59 行先消费已证 `HasLaw` 得到联合可积性，再应用有可积性前提的 Fubini 与分布积分公式；实际完整类型保留 `F` 的可测性和原乘积律下的可积性。 |

联合可测性步骤已核对固定 mathlib 源码 `MeasurableSpace/Constructions.lean` 第 506 行附近的完整引理：`measurable_from_prod_countable_left` 要求第二因子可数且具有可测单点，本单元的有限排列空间满足这两个条件。每个截面的 `Measurable.of_eval` 仅使用 `hX (σ i)`，且输出路径空间确为 `Fin n → ℝ`。

分布证明中，第 32–33 行对任意可测路径集合 `s` 使用 `Measure.map_apply hm hs`，并对其可测原像使用 `Measure.prod_apply_symm`。第 34–42 行固定任意排列 `σ`；`σ.injective` 使 `hIndep.precomp σ.injective` 正好表示重新编号的原独立族，各坐标律仍为 `hLaw (σ i)`。已接受的 `iid_samplePath_map_eq_pi` 给出固定截面的推前律；对测度取在 `s` 上的值并再用可测映射公式，得到截面原像的测度恒为同一 `pi ν s`。这个截面正是 `(ω, σ) ↦ X (σ i) ω`，不是原样本函数的另一个替代定义。第 43 行以真实排列概率测度的总质量一消去常数的下积分，故完整联合推前律成立。

积分证明第 55–56 行的顺序至关重要：先得到 `hlaw`，再以 `hlaw.integrable_comp hFint` 得到 `F ∘ reorderedSample X` 在 `μ.prod U` 上的可积性。已核对 mathlib `HasLaw.integrable_comp`、`HasLaw.integral_comp` 与 `integral_prod` 的完整相关接口。`integral_prod` 的对称等式把左侧迭代积分接到联合积分；随后 `hlaw.integral_comp hF.aestronglyMeasurable` 接到原路径积分。`Function.comp_apply` 只做函数合成展开。对实数值空间，Fubini 的完备性与范数空间条件均由标准实数实例提供；两个测度的有限性由概率实例提供。因此没有不可积积分取默认零、循环使用待证结论或交换积分缺条件的问题。

## 已验收依赖与整合范围

已读取 `Shao.Path` 的完整透明缩写值、`samplePath` 的完整透明值，以及 `measurable_samplePath`、`iid_samplePath_map_eq_pi` 的完整来源接口和继承上下文。`FiniteIID` 只提供固定重新编号后的原 iid 路径推前律；本次联合随机排列律和迭代积分均由新证明补齐，没有把旧接口误读为已含该新结论。

`FiniteIID.lean` 源 SHA256 为 `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`，对象 SHA256 为 `751221ecc043004a49a0905626c512b878ba2621a797ff7b6466b2a7ae60fb5c`。它与 `FinitePath` 的源和所需对象均与 accepted-v71 基线映射吻合；基线映射 SHA256 为 `2d21a615db45ce0d85388bfdabfd9b5579b23db197065739fe2e791481342419`。五个新增的本工作树叶子链接逐项核实指向 accepted-v71 原对象，目标及链接读取的字节哈希均等于原映射，目标模式仍为 `0644`。本次未重编译旧生产模块，未改动缓存。所谓只读复用在这里指消费方只读取既有对象，没有声称目标文件的 Unix 写权限位已经移除。

另直接完整读取已合格 `uniformPermutationLaw` 的实际类型和透明值，以及 `uniformPermutationLaw_isProbability` 的实际完整类型。其值为整个 `Equiv.Perm (Fin n)` 的基数倒数乘 `Measure.count`，没有原样本参数；概率证明对任意自然数长度成立。复用其既有独立完整审查，报告 SHA256 为 `6f2a03f8ce7c54772ca4fd966558bbd986b26471a6401741b0eada31e7e08ff7`，作者收据 SHA256 为 `2f6234e531a2bf04f4b93fe7e1711096e7e7c9cf74111b3ec7c47a0852e2d5eb`。当前依赖源码 `db9490e5e0b5ccff6be55ac22705a7fd18dd69d20f9a6a1e9f652879daadbb17`、对象 `2fa2a407f7395225eedf6cc58ed68765071e0172373343791d97f24f61b65522` 及完整类型/值导出均与原合格证据相同；没有为未变旧证明另行要求完整复审或复编。

新模块命名空间独立，imports 与冻结版一致，没有改共同定义、原接口或根导入。本次只关闭实际 iid 重排律及可积函数平均转移这一依赖。它不证明具体确定性秩估计，不建立原自然 iid 过滤下的停止性，不覆盖样本依赖排列，也不补足实际核/PDE/解析导数或其他未闭合义务。

## 边界检查

证明未使用 `0 < n`；空路径只有一个取值，`Equiv.Perm (Fin 0)` 仍有恒等排列，均匀概率律没有基数为零的问题。所有重新编号按标签而非按数值进行，重复观测值不被合并。边际可以带原子，无须无原子性、矩条件、中心化或正方差。函数 `F` 可以任意实值，只需声明中的可测性和可积性；证明不要求有界性或符号条件。原测度没有因依赖某个排列而被条件化。

## 内核、公理及精确证据

复用作者成功服务器检查 002 和实际所属递归公理审计 003，退出码均为零。作者收据 SHA256 为 `fb87fa27139b4fe484ce0d71125f1b8c1ae99782fea9f190d233e4bfbdb0d470`。审查者核实了收据中全部十二项服务器工件及十项本地作者工件；成功日志、源快照、对象、导出和审计程序的哈希/大小均相符。工具链为 `leanprover/lean4:v4.36.0-rc1`，mathlib 为 `807d3836b165983210ee2ecf3cd28f239436949c`，仍消费已接受包视图。检查资源绑定为 CPU14–17、`c12-heavy.lock`、`-M8192 -j4`。

完整读取的 `OwnedAudit.lean` 遍历环境常量并按 `env.getModuleIdxFor?` 的实际模块归属选择，包括私有/生成常量，未按命名空间或公开清单过滤。实际结果恰为四项：三个定理、一个定义，没有额外未读项。每项递归 `Lean.collectAxioms` 结果均仅为 `propext`、`Classical.choice`、`Quot.sound`。没有新增 sorry/admit/axiom/unsafe/native_decide。完整源证明、全部实际类型及唯一完整非定理值均已覆盖，未把三个公开定理误记为全部实际所属数。

失败检查 001 的源码和日志仍在原服务器路径，其失败为最后一个 Fubini 函数合成重写的语法匹配；002 只修正证明写法及提示风格，冻结接口不变。旧失败不被隐藏或改记成成功。审查过程一次只读检索因服务器未安装 `rg` 失败，原响应保存在本目录，随后使用只读 Python 搜索得到同一引理；这不是 Lean 检查，也未重跑任何已成功检查。

作者检查时的 HEAD 为 `7f87319d95bb64d00972b0d8a08a8d521b836077`，后续父协调者对前序单元的纯 Git 提交与分支切换使当前 HEAD 为 `fe32939af989d80cfebfb9c245d456a63b262ce6`、分支为 `author/c12-uniform-permutation-law-v71`。本次源码和对象字节、时间及成功源快照保持相同；Git 管理元数据变化不构成重编译理由。审查者执行 Lean 次数、审计重跑次数、旧生产者重编译次数、缓存写入次数均为零。

## 裁决与释放

CRITICAL GAPS: 无。

正确性：冻结目标的证明完整，原文到形式陈述忠实，完整机械检查覆盖此精确局部目标。机械状态为 `LEAN_FULLY_CHECKED_FOR_EXACT_FROZEN_LOCAL_TARGET_REUSING_AUTHOR_SUCCESSFUL_SERVER_RECEIPT`。

研究范围：这是有限 iid 族重排不变性的来源依赖及形式化接口，不提出数学新颖性或论文根定理闭合主张；所有原 C1/C2/OQ3/OQ4/OQ56 根组继续为 OPEN，OQ3 的人工暂停不受影响。

全部逐项绑定与完整类型/值块哈希见 [evidence.json](<C:/game/shao lean/drafts/c12-lane/uniform-permutation-iid-law-final-review-v1/evidence.json>) 和 [full-review.json](<C:/game/shao lean/drafts/c12-lane/uniform-permutation-iid-law-final-review-v1/full-review.json>)。审查者在报告完成后释放本次审查文件写入与执行权；没有生产源码写入权，没有在途命令或重检查，未进行 Git/PR/共享文件变更。输入、缓存输入、输出及推理子集使用量未由接口暴露，均记录为 null。
