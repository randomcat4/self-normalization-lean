# 单元30、31独立完整终审

STATUS: CORRECT

两份最终冻结局部目标均通过独立完整源码—陈述—证明审查，未发现关键缺口。机械结论复用作者已成功的服务器内核和全所属递归公理收据；本审查没有执行Lean、重复审计、重编旧生产模块或写入缓存。原始C12/OQ3/OQ4/OQ56根组状态仍为OPEN。

## 审查身份、输入及范围

新鲜独立终审上下文`/root/completion_profile_heat_final_review`，按任务配置`gpt-6.1-sol/xhigh`，与作者独立。仅写本审查目录，未编辑生产源码、冻结、共享文件或Git。无子代理。输入、缓存输入、输出、推理子集计数均不可取得，记录为null，不换算订阅百分比。

直接完整读取原文`C:/game/shao/current/c12/supplement.tex`第4192–4253行，完整两份生产源码和全部源证明、全部冻结及说明、两份审计实现与所有实际所属结果。原文全文件SHA256为`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，精确节选SHA256为`7c114b02812a59089a18904d502318e4ac65a8574c7a80f735aa16dc3a8283f2`（2624字节）。

| 单元 | 源码SHA256 | 成功对象SHA256 | 最终冻结SHA256 |
|---|---|---|---|
| 30 CompletionFirstProfile | `5e378043eccc8e052ad34ba36c8c98d143270f706d285ae1c9f8750c6a0830fc` | `510d5315cd625d6d49ff71bab285b4b1a1d3e73149d94c47a757a5f43161e128` | `158a1a35419b560cc111fbc495a19b3f7e7e3d6c7b87b6a8cc68977dc49f78ea` |
| 31 HalfLineHeatEquation | `cbd04d920bb87e31fc35e5aba4e5bf41a785796b661f3ba661c28c9f43bfd87b` | `8633ffb98d7a445c2840f208f64baeab0a367f4e7f761a905a748f760e73f4fe` | `8870b5be9d2cf2c9f10bebf431f5bda99075b3a4ee048f2ca5a154f3a1f2e8be` |

单元30的6个完整公开定理头、3个完整透明值及整个导入/命名空间上下文与冻结精确匹配。单元31原冻结`e7a66f12ffa57880f0c78f8bb0c182e0405dacbdb072e8321de59cb8339a6eb2`保留，最终冻结仅增加`Mathlib.Analysis.Calculus.Deriv.Inv`导入；6个完整头未变，没有数学假设变化。

## 单元30逐项判断

令上墙`u=a-y,v=a-z`，下墙`u=a+y,v=a+z`。三个新定义分别为`exp(-uv/T)`及双墙和，精确对应原文P，绝非任意可选函数。

1. `reflection_deficit_le_profile`：`u,v,T>0`推出`-2uv/T≤-uv/T`，指数单调性给出缺陷界。没有端点距离下界。
2. `positive_reflection_slope_profile`：以`2T`消费已接受的C4界，得`(v/T)e^(-uv/T)≤4/sqrt(2T)*(1+|u-v|/sqrt(2T))`。由正平方根单调性扩大至T包络，乘2及正指数`e^(-uv/T)`，恢复精确`8T^(-1/2)D*e^(-uv/T)`。所有乘除单调性符号正确。
3. `upperReflection_deriv_profile`：真实`HasDerivAt.deriv`、负号绝对值和正`2v/T`将上墙导数化为正标量斜率；`u-v=z-y`与原文D一致。
4. `lowerReflection_deriv_profile`：下墙一阶导数为正系数乘指数；`u-v=y-z`，绝对值交换恢复同一D。严格内点和正时间均保留。
5. `interval_deficit_profile_of_reflection`：实际路径事件满足`strictInterval=strictUpper∩strictLower`。可测下事件给出`P(U∪L)+P(U∩L)=P(U)+P(L)`，概率性给出`P(U∪L)≤1`。显式单点反射恒等及两项缺陷界推出`1-I≤Pu+Pl`；`I≤1`完成`|I-1|`改写。这里不需要实际区间可微性。
6. `interval_deriv_profile_of_reflection`：全半直线反射恒等在严格内点提供邻域相等，故两个实际半直线概率取得真实导数；显式`DifferentiableAt`给出实际区间导数。已接受signed domination给出`du≤di≤dl`。C8公共因子非负，每个单墙剖面小于剖面和，于是`-B*P≤du≤di≤dl≤B*P`闭合目标。

实际区间结论严格是有条件定理。点反射恒等仅用于值界；导数界使用邻域反射恒等及实际区间可微性。源码没有证明这些反射恒等、Brownian桥律识别或实际正则性。

## 单元31逐项判断

显式标量函数为`f=1-exp(-2uv/T)`，求导始终固定墙、时间以外的参数和末端点。

1. `upperReflection_second_hasDerivAt`：使用已接受的一阶真实导数恒等，逐点把`deriv f`替换为`-(2v/T)exp(-2uv/T)`；再对该函数求导得`-(2v/T)^2 exp(-2uv/T)`。这是实际二阶导数证书。
2. `lowerReflection_second_hasDerivAt`：一阶系数为正，指数的y导数为负，二阶仍为同一负平方系数。逐点函数相等和`HasDerivAt`链式法则覆盖全部实参数。
3. `upperReflection_time_hasDerivAt`：`T>0`排除零分母，商法则及指数链式法则给出`-2uv/T^2 exp(-2uv/T)`，时间导数负号正确。
4. `lowerReflection_time_hasDerivAt`：同样得到下墙时间导数，墙与末端点固定。
5. `upperReflection_heat_equation`：代入三个真实导数证书；`d=z-y=u-v`使`(1/2)f_yy+(d/T)f_y=-2uv/T² exp(-2uv/T)=f_T`。`field_simp`仅在已知`T≠0`下使用。
6. `lowerReflection_heat_equation`：下墙`d=v-u`，代入正一阶和负二阶导数得到相同时间导数。PDE漂移项、半系数和符号均与原文一致。

二阶空间证书适用于总化实标量公式的所有实T；在Lean的实数除零约定下T=0使该标量函数恒为0，因此证书依然正确。这不是原文零能量概率延拓：原文可达、端点一致且在内点时赋值1。时间证书和PDE明确要求T>0。没有把标量PDE宣称成实际区间热核、区间存活概率PDE或反射识别。

## 所属完整性与实际类型/值

单元30共有13个实际所属常量：10个定理（6公开、4生成）和3个定义。完整实际类型42881字节，完整定义值1288字节。特别覆盖两个在`HalfLineReflectionFormula`命名空间内、但模块所有权属于新模块的延迟生成`.eq_1`，及两项profile定义方程。单元31共有20个实际所属定理（6公开、14生成），完整类型37434字节，定义值导出确为空文件。14项生成声明含上/下两组：2、3、4数值非零，非零乘积，约化幂，非零元素整数幂及特征零`n+1`的命题化简；所有完整域、实例、量词和前提均已读。

完整实际类型与所有非定理值使用60项精确原始括号子表达式字典加全部编码上下文直接读取；整个字典已直接读取，逐文件UTF-8字节精确往返验证。没有以结构摘要替代实际类型，没有省略私有/生成声明、依赖let或实例。重复字节按无损字典读一次后复用，不声称逐字重复阅读原始重复字节。原始源证明均完整直接阅读；不展开巨型战术证明项。

已接受的单元26、27及BridgeDomination完整旧证明审查复用。此次消费并完整读取Bridge的12项实际类型（9个透明定义及可测下事件、概率界、signed domination）和全部9个透明值；半直线的5项实际类型（两个定义、正斜率界、两个真实导数）和全部2个透明值；区间的2个真实导数转移接口。旧源码/对象均只读核验为原接受版本，不重复旧完整证明审查。

`OwnedAudit.lean`遍历`env.constants`，通过`env.getModuleIdxFor?`筛选真实模块所有权，完全没有命名空间或public-only过滤。对每一个真实所属常量调用递归`Lean.collectAxioms`并拒绝白名单以外公理。所有33项仅使用`propext`、`Classical.choice`、`Quot.sound`的子集。两份新生产源码中无`sorry/admit/axiom/unsafe/native_decide`。计数从实际所有权行与导出集推导，不照抄描述。

## 服务器证据、失败保留与资源

两份作者成功内核均为attempt002，kernelExit=0，whole-owner auditExit=0。只读观察已验证：当前源码=成功源快照=冻结绑定源哈希，原始成功对象=分线已安装对象；全部18项receipt artifact的SHA256和字节数匹配。完整导出类型/值块与成功审计日志逐块精确相等，仅修剪分隔用前后空白，不规范化任何内部字节。末行分别为`AUDITED_TARGET_CONSTANTS 13 PUBLIC 6 THEOREMS 10 DEFINITIONS 3`和`AUDITED_TARGET_CONSTANTS 20 PUBLIC 6 THEOREMS 20 DEFINITIONS 0`。

单元30失败attempt001仅因`1+x`与`x+1`的加法顺序不匹配；最终只把该证明步骤换成同一除法单调性事实加线性算术。单元31失败attempt001仅缺商法则导入，最终差异只有增加该导入。失败源码/日志精确哈希保留。成功日志只有既有警告，未为整饰警告重放成功检查。

绑定环境：Lean `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，既有共享只读包视图。作者成功资源为CPU14–17、`c12-heavy.lock`、`-M8192 -j4`。只读观察分支`author/c12-uniform-permutation-law-v71`，HEAD `fe32939af989d80cfebfb9c245d456a63b262ce6`。后续纯发布Git元数据变化不会改变本报告绑定的精确源码/对象结论。

作者receipt SHA256：单元30 `05bc10bd54ea58cfff24ba41aaa0803612a4ff8557d4cbbb05a05e6fedcb8104`；单元31 `13954bcbb61cd8f365f787df9d61bc7890257551c960a076d824eb167de6e8e7`。作者release SHA256：单元30 `29185968eb569d617cbf29aa2ba3fe17536ca22c3627cdd86f903b3d47b91e40`；单元31 `3fb517f8340af95ef6c81b158f0b81600c5095db748cff0699b0847c1eb32862`。全部细目见`evidence.json`、`local-checks.json`和`remote-observation.json`。

## 仍未覆盖及释放

本审查只认证两个最终冻结局部目标。实际Brownian桥律/反射恒等、实际区间正则性与PDE、所有阶/混合导数剖面、墙处单侧估计、完整零能量/零墙延拓、补偿Taylor余项以及原始研究根结论均未由本批闭合。没有新颖性结论；这是原文承重分析依赖的形式化。

审查者无生产写权限；审查输出写入完成后writer/execution release，heavyInFlight=false，inFlight=[]。这份普通终审答复结束本审查回合；由父lead继续下一个源绑定依赖，不把答复当作持续运行机制。
