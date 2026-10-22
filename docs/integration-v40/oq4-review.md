# PR162 独立验收：确定性立方根精细余项

STATUS: CORRECT
critical_gaps: []
审查对象：https://github.com/randomcat4/shao-lean/pull/162
精确 head：2db799bf5bb08de3f6ce323a6bcd26790e1f1662
tree：1cd2307bbe8bc1296a30f904b3a5e46e1c72e8ae
新源：Shao/OQ4/RademacherCubeRootRates.lean，9422字节
Source SHA256：6f51957e561b4b693bcff304f797e284d905fc7a5ea3b5457819c3fe5e851247

本验收认证原 Spectrum 第96、97–98行的两条确定性细根率。完整新源码、10项实际所属类型、2个完整透明定义值、全部公开声明的显式展开，以及直接关键 CP 依赖的实际类型和定义值均已审阅；没有把待证余项或概率结论加作前提。原真实弱格概率 S5已在v39接受，本次不扩大原根闭合。

## 精确范围与源码绑定

冻结提交相对其父 eaf3beb6503f702f0f2e692a485728499f311765 的文件集合准确为25项：1份新源和24份文档。该父树是已接受v39树43577d0d66de8325a756c9ac25e43e53809c3525。本审只读获取冻结head的每个blob，25项SHA256全部与发布清单相同；服务器canonical源和本地完整审阅源均与冻结blob相同。唯一原对象SHA256为077c3bf16faa70254cb9f1bfac16ef9add577da6ecf0f762c0198ef421fb5cf8，1145648字节。

原文 C:/game/shao/current/oq4/c01/spectrum01.md 的SHA256是b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b。第96行要求 n=k³−1 时 h=k−1/(3k²)+O(k⁻⁵)；第97–98行要求任意0<α<1的最近整数索引有 h=k+α+O(k⁻²)。当前四个公开定理逐项覆盖这两条展开及其有限版本。

## 公开语义、量词和边界

- below_cube_finite：对每个自然数k≥2，给出同一belowCubeIndex k的实数身份(n:ℝ)=K³−1、n≥1、同一实际root n非负及立方身份、height 1 n=root n，以及|root n−(K−1/(3K²))|≤1/K⁵。
- below_cube_bigO：返回实数常数C=1>0和自然阈值k₀=2，并证明全体k≥k₀的五次幂余项界。
- nearest_cube_finite：对任意实数0<α<1和全部自然数k≥2，同一选择器为Nat.floor((K+α)³+1/2)；输出K+α>0、自然索引正性、实际根/height身份、舍入误差−1/2<e≤1/2和|e|≤1/2、所有半整数平局向上，以及|root n−(K+α)|≤1/(2K²)。
- nearest_cube_bigO：在同一α域内返回C=1/2>0和k₀=2，证明全体k≥k₀的二次幂余项界。常数和阈值在α上相同。

两个透明谓词都准确写成“C>0且对全部自然数k≥k₀的绝对误差界”，没有退化为选定子列。常数、阈值、自然索引正性与舍入误差都是输出。k=2由同一代数证明覆盖，k=0,1不在有限界主张内，既有函数早期值不变。所有分母只在K=(k:ℝ)≥2的尾部使用，因此严格为正。α端点0、1未被擅自加入，c固定为1；同一实际非负Real.rpow根没有替换成自由立方根。

## 独立证明核对

五次幂余项中，置a=K−1/(3K²)、D=a²+ar+r²。K≥2给出a≥2K/3≥0，故D≥K²/3>0。由实际立方身份r³=K³−1，完整多项式展开为a³−r³=1/(3K³)−1/(27K⁶)，介于0与1/(3K³)之间。立方差分解为(a−r)D，正分母推出r≤a，继而(a−r)(K²/3)≤1/(3K³)，约分得到|r−a|≤1/K⁵。源中每个不等式方向、平方下界与除法正性相符，没有把Taylor展开或该余项作为输入。

二次幂余项中，令t=K+α≥K≥2，实际根r≥0。D=r²+rt+t²≥t²≥K²>0，且|r−t|D=|r³−t³|≤1/2，因此|r−t|≤1/(2K²)。最近整数signed error与平局结论由同一已接受nearest_rounding在c=1下取得，全部假设均满足。源中另由t³≥8与signed lower bound推出索引非零，再用自然数非零等价于正性，没有假设正时间。

公开包装精确消费exact_below_cube.2.2.1的实数cast身份、root_spec.1的非负性和root_spec.2.1的实际cube身份。这些是严格更弱的结构事实，未包含任何细根余项；不存在循环调用目标或隐藏概率结论。

## 全所属与关键依赖

实际模块所属集合准确10项：2个定义、8个定理。其中公开定理4项、显式private定理2项、generated定理2项。完整实际类型与定义值均存于配套JSON的owned_actual_types，已与原唯一独立Native所记录audit的逐项UTF-8哈希再次只读比对。

两个generated项为：

- Shao.OQ4.RademacherCubeRootRates.BelowCubeBigO._proof_1：类型为自然数(2+1).AtLeastTwo，仅数码3的实例证明。
- Shao.OQ4.RademacherCriticalPhase.nearestIndex.eq_1：类型为所有c,α,k上nearestIndex c α k=Nat.floor(target c α k+1/2)的定义展开等式。虽然名称在CP命名空间内，实际owner是本新模块，已计入10项而未遗漏。

2个private类型分别是一般非负实数根下的五次幂代数误差引理，以及t≥K、cube误差≤1/2下的二次幂引理，均与已通读完整证明一致。没有新axiom、unsafe、partial、sorry/admit或native_decide。

关键直接依赖root、height、target、nearestIndex、belowCubeIndex的完整定义，以及root_spec、exact_below_cube、nearest_rounding的完整实际接口，已从已接受CP actual-interface及源逐项核对。CP源SHA256为388f17e1c257d9b1fe74914866937bd9dc6ce1fb1398e72761b3f65c8464a96f，与实际消费源相同；其原对象SHA256为2d11da742f05a509d66a7646edf8b97cf64d7f4a9826f092ba0424b32ed278ec，与审计绑定相同。

只读重新遍历既有audit的type/value引用图，16829常量、393912条边记录完整闭合，37个项目依赖全属CP，环境差集/模块owner/stage2/actual owned集合一致。标准公理仅propext、Classical.choice、Quot.sound；owned与项目依赖无新增公理、unsafe或partial。记录trustLevel=1025、skipKernelTC=false、autoImplicit=false。大型raw Expr和8995878字节audit是机器读取，未冒称人工全文阅读。

## 机械证据与保全

本审未运行Lean。历史作者Native、独立完整Native/audit、唯一canonical emit均首轮退出0，实耗分别为5.499742977321148秒、8.692977806553245秒、5.887082051485777秒；原7个linter warning保留。父unit与Full53 import门分别通过，目标重编译/emit为0。历史基线仍为b6573a104d12d0fa333a7645eb1c0e73d67563ea，没有将后续Git-only吸收伪写成新运行证据。

根协调的统一v40 gate已PASS：目标源hash等于冻结源，全部7个命令退出0，公开1882、含生成namespace定理3190、所属5507。基线277份旧源与1054个旧对象按现有证据复用且不变；仅根协调执行整合构建、公理和覆盖门。本审只读取并绑定coordination/integration-v40/gate-result.json，SHA256为e64b378bc563d4fae8a2e1493280624e3c748e25686105426c15c5be11b65542，没有重复成功检查。

25项原始发布文件完全未修改。parent-acceptance.json的68行CRLF、report.json的483行CRLF、semantic-ledger.json的1689行CRLF均保留原字节和哈希。本报告及配套新JSON使用LF，未规范化作者任何证据。

首次只读比较因分线Git库没有main67df1c9对象而退出；随后用已存在且同v39树的精确PR父完成25项比对。该读取失败留账，没有写入或数学影响。

## 结论限度

这只补原第96与97–98行的确定性余项，未新增概率定理。真实弱格S5早已v39通过。严格完美立方候选、一般非整数/ceil严格分类、原116广域O(n/h³)相邻格点对数概率界、任意c定量率、一般分布及uniform-x OQ4、energy9/10、完整Spectrum/OQ4原根均不在本PR认证范围；rawleaf增量0，不推导完成百分比。

Big-O使用明确的正常数全尾部谓词，没有声称新增Mathlib Asymptotics.IsBigO导出接口。原始proof/freeze中的历史pending文字按阶段留档；结论以本精确head实际类型与既有成功机械证据为准。

独立验收为CORRECT，critical_gaps为空。所有服务器读操作固定CPU10–13，未运行Lean、合并、spawn或修改源/对象/缓存；仅写本报告及配套JSON。分线构建及外部CPU0–9/80GiB任务保持不动。
