# PR143 独立验收：CORRECT

STATUS: CORRECT

JUSTIFICATION: 精确提交中的两个完整模块、全部冻结公开合同、全部13个源码私有声明及现有形式证明证据均已独立核对。它们忠实支付原 p53 §2 的确定性慢尺度与同一条稀疏子列；未发现关键缺口。验收范围为18条公开定理、12个定义，Core内部合取不额外计数。完整 p53 / OQ6 / RS2 保持 OPEN。

本审者没有编写或修补两个模块，也没有运行 Lean。只读远端操作通过 tools/server.py，均绑定 CPU22–25；只写本报告与同名 JSON。未修改源文件、缓存、引用或分线，未合并，未触碰受保护 CPU0–9 / 80GiB 外部任务。

## 精确版本与源身份

- PR：[143](https://github.com/randomcat4/shao-lean/pull/143)。
- 冻结 head：`7a346788359701e75fc0d0e94430b74db5fe4f83`；tree：`bd3a0ac9894f2d908044ae9f6ea541c0437c3cca`。
- 唯一 parent 为 v35 main：`b67813c18af01ad1050c947930ee2d93a7889819`；v35 accepted：`f2233eb031b870379cf597a3e9fd0a4d3974eae5`；其树 `7447e8880422c835dc2342c1955b528590e7a305`。
- 变更恰为以下5文件，828行新增、0删除。源码以远端 `git show <精确head>:<path>` 读取，未依赖活动工作树的未提交内容。

| 文件 | 行数/字节 | SHA256 |
|---|---:|---|
| Shao/OQ5/P53/SparseScales.lean |431 /22814|22d4f7f1972a3cbc5fedfc2efa0cadbf91616d4e1d113cbb90ef753a830b7888|
| Shao/OQ5/P53/SparseSelection.lean |186 /8007|17d134c1a8c02b07f5a5e3c3047742048775dbf36c5c1eba47f120a09622d282|
| docs/oq56-p53-selection-frozen.md |180 /8848|a68e155247954cf9a81dd0cda832597f3281ec66f43be9486023cd2292566390|
| docs/oq56-p53-selection-review.md |20 /4468|4faece3955d9cea6ac02f322c87c7b5f76997595b336219d3b1e4d78e5fedc73|
| docs/oq56-p53-selection-scope.md |11 /1946|7bbcd78ee7e4a723795e3da800f419be23bc668ebe471ed61854564e4a4bd179|

两个源码均完整逐行读取，含全部证明；原始 freeze、SOURCE报告、作者报告、完整 FINAL报告及两个完整源码审计附录均已读取。作者报告内重复的完整源码另外逐字比对为同一已全文读取源码，未将截断显示作为完整阅读依据。公理清单、冻结合同与最终证据文件表逐条机器核对，原始编译收据的命令、结果及前后快照另行核验；没有声称人眼逐个阅读千余哈希表。1081/1219物理保护表的完整重建属于原lead记录；本轮核验封存manifest身份及原始before/after相等，没有重演全部物理图。

## 原文、量词与范围

原件 p53 全文 SHA256 `0bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561` /5686B，p45 全文 SHA256 `0b799637356615cfb18a9fef016c11d682aeefde314106e0b56eb46a853c09ca` /10799B，均直接读取。p45 §1 的真实 centered-row 抵消是后续消费者；本包没有将其概率前提当已证明。scope01 与 p54 也已读取，p54 的正向修正没有被移植成本确定性模块的假设。

精确量词为：任意固定实数 α 与整条确定性 x，在0<α<1、x_n/n^δ→+∞、x_n/√n→0之后，存在一条 N。δ=3α/(8−2α)。允许 x 非单调，允许有限前缀为零或负；没有全n正性、额外增长速率、可计算性、矩或概率假设。这里“super”仅是超过这一固定临界幂；作者旧叙述中的“super-polynomial”不能解释为超过所有幂。

N 在任何后续 q、τ 或实际样本之前固定。第97单元的私有 Nat.rec 从正整数1开始，每步将已选正前驱 M 输入下一步的 Nat.find。并非对每个 q、τ 重选 N，也未假设存在一个对所有无界 M 通用的尾阈值。后续共同 q、τ 矩结论尚未在本包断言；消费者必须继续使用这个 N。

## SparseScales 全部证明检查

7个定义与15个完整定理类型逐项对原 freeze 检查；完整定义体与完整头部保留，未在内部 let 截断。freeze SHA256 `1b1fc406c81cafe3839f4aa9bc0bdb15f957441718d087925077d636f459cf92`；合同JSON SHA256 `2e65bd8143fd14eea054a4d1f6d6211f6cd9124e1ae99ec2c9499c288d6684ed`；规范字典 `100b209b78d23d51b53ec0da2533593d0dcd3a2b8d58b791cbb1a10fb94b16bc`。提交内合并冻结文档与这22份合同再次全量匹配。

| 定理与精确源码行 | 已检查的关键推理 |
|---|---|
| sparse_exponent_bounds :116 |0<δ<1/2、β>0及δβ=3α/4，严格正的8−2α才参与消去。|
| sparse_input_tendsto :132 |正幂n^δ→∞与super商最终≥1给x≥n^δ，无单调性论证。|
| sparse_eventually_pos :147 |共同尾段n≥4、x/r/e/s/t/d全正；所有实幂、平方根及实分母条件同时满足。|
| sparseCost_tendsto_zero :168 |在正尾段将e=(n^δ/x)^β换为(x/n^δ)^(-β)，由β>0得到0。|
| sparseSlow_tendsto :180 |e,r→0加最终严格正，先提升到右邻域0+，再取负幂→∞；min在每个阈值的共同尾段趋∞。|
| sparseSlow_eventual_estimates :199 |min两上界分别支付e*s^(α/2)≤√e与s*r≤√r。|
| sparse_cost_slow_tendsto_zero :217 |非负夹逼与sqrt在0连续，没有把0乘∞直接判0。|
| sparse_slow_ratio_tendsto_zero :235 |同样以真实上界√r→0夹逼s*r。|
| sparse_eventual_scale_identities :250 |逐项核e=n^(3α/4)x^(α/2−2)、t²/n²=s*r、t^α/x²=e*s^(α/2)，只在正尾段使用幂规则。|
| sparseAmplitude_cost_tendsto_zero :277 |用第三身份转移实际小费用，未以所需结论为前提。|
| sparseAmplitude_div_nat_tendsto_zero :287 |正性给t/n=√(s*r)，排除仅由平方极限产生符号漏洞。|
| sparseShift_div_nat_tendsto_zero :310 |n≥4时0≤d/n=(t²/n²)n/(n−2)≤2s*r。分母为先cast后实减。|
| sparse_eventual_bounds :348 |s,x最终≥1支付t≥n^(3/4)；已证比值极限支付t≤n与d≤2n。|
| sparse_exp_cost_tendsto_zero :382 |固定c=3α/4>0，t^α≥n^c→∞后使用真实指数极限。|
| sparse_nat_mul_exp_cost_tendsto_zero :405 |独立以0≤n exp(-t^α)≤n exp(-n^c)夹逼；私有引理以u=n^c、u^(1/c)=n支付后者，未错误使用上一零极限乘n。|

完整6个私有引理（:41–115）分别支付正商倒幂、u*u^(-1/2)=√u、slow界、幅度平方身份、幅度实幂身份、n乘指数极限，全部前提充分、没有隐藏源目标。

公式对小n保留总定义；n=2时实除零总化没有被当可消去分母。α端点0/1及统一于α的结论均未声称。

## SparseSelection 全部证明检查

5定义、3完整定理类型逐项匹配原 freeze；freeze SHA256 `7783a7c83948cd38d1f5d40dd1ae590d940d14c85dab464d4f11e3a9d3e6f4b5`；合同JSON `f5b6af994cfc22573cdb543619b208b9615684d861d0d2ec0730e9903e566019`；规范字典 `efc609af9ae36ff885a15a0976a1f9cb7a4d8b217558ae302c34cfed64df0d24`。提交内冻结文档的8份合同全量相同。

:23–49 的literal定义正确：w_j=2^(-j)为实数逆；正层π_j=w_(j+2)exp(-t_j^α)，j+2移位未丢。标签0的t、d、positiveMass各自显式为0；π0是正层质量序列的占位零，绝非未来残余类别0概率，也不把t(N0)、d(N0)误用为零。

:72–112 固定m与正前驱M以后，两个第96单元真实极限分别给n exp(-t(n)^α)≤4和exp(-t(n)^α)≤4/M²。阈值严格为正；与全部共同尾界、n≥2^(m+1)、n≥2M+1有限求交，并用Nat atTop的NeBot取得同一个n。:54 的w_(j+2)=w_j/4与w_j/4≥0同时支付nπ≤w_j和π≤w_j/M²。

:114–145 的nextIndex由Nat.find满足完整SelectionStep，≥4字段保证下一前驱仍正；selectedIndex是真正Nat.rec，基点1，递归不改变x或α。:147–168 的exists_sparseSelectionCore给N0=1、所有j的2^j≤N_j及所有正层同一Core；其中基点1≤1与继承hsteps都实质核对。:170–182 的strictMono与tendsto对任意给定Core作结构蕴含，未无条件省去存在定理的α/x前提。7个私有声明的完整头部/证明均已读，其中3个私有定义的完整体也保留。

## 依赖与现有形式证据

实际项目闭包恰为Selection→Scales；Scales只有两个官方导入，没有旧项目编译依赖。旧73份source/object是发布保护锚点，不能算本数学依赖。全部29个Scales官方接口与Selection的11个Scales接口/8个官方接口，完整已加载类型及必要类前提均已核对；名字列表保存在同名JSON，Lean.collectAxioms是传递查询，覆盖其余证明依赖。

重点前提均满足：负幂0+输入与正底数代数；sqrt在0处连续；指数衰减系数1>0；Nat.find的existential/DecidablePred由真实存在证明和classical提供；Nat.rec内核递归规则；eventually_le_const的严格正间隔；Eventually.exists的NeBot；StrictMono.tendsto_atTop准确限定Nat→Nat。未因ROOT命名位于open Real/Filter文本中而误改作用域。

两个完整审计附录也已读取：初始及后期都遍历env.constants，以getModuleIdxFor?为None发现所有实际所属声明，逐个collectAxioms；并非仅抽查公开名字或只信计数下界。实际SOURCE与LATE结构名集合一致，无新增后期/导入lazy所属项。所有str/num组件与原始输出逐条比对，num按十进制字符串保存，未按点拆名字。

| 已有独立门 | 目标结果 | 首次完整源码前缀 | 实际公理记录 |
|---|---|---|---|
|96|no-o，exit0，stdout/stderr EMPTY，4.058978594839573s|22814B原源前缀精确，exit0无诊断，5.504361484199762s|33 SOURCE +29 DEP +33 LATE =95，62不同结构名|
|97|no-o，exit0，stdout/stderr EMPTY，3.699589656665921s|8007B原源前缀精确，exit0无诊断，5.053493540734053s|25 SOURCE +19 DEP +25 LATE =69，44不同结构名|

本轮直接读取两份原始target.json和prefix-01.json，检查原始命令、实际退出码、无诊断、stdout哈希、before==after、无自身对象导入、无-o、CPU22–25及native8192MiB/j4。两个canonical清单的164条记录逐条与原始stdout重建值相同；全部公理均属于propext/Classical.choice/Quot.sound。96有22公开+6私有+5生成；97有8公开+7私有+10生成；这些不是新增公开定理计数。

96最终JSON SHA `1f155849ed732024e9cbb6f0b8104cfb444e382653d513ff7c65962ad3848a42`，canonical `24fcfad350c0f6595e2027fec8253964bcefe9f642ebba1d9f93ef055c2e588d`；97最终JSON `0a025dfbad1ed83fbbccf3dc361b774844d08647b89550892b46a2ef1ddf1abc`，canonical `e3e26e1cbbeca28cef3cccc4811e2d25a295c870042f49aa7f4332f4d2d7adba`。两份最终表列明的33+40证据文件，当前远端SHA/bytes/精确mtime_ns全部重算相等。完整artifact指纹继续保存在本JSON。

作者失败史未抹除：96四次，前两次证明诊断、第三次输出目录失败、第四次首次EMPTY；97三次，前两次有限代数/归约诊断、第三次首次EMPTY。独立FINAL各只有一次目标和一次前缀，无附录修复。后续报告schema/路径/列表顺序的失败仅影响封装，源与合同未改；本轮没有把作者通过算作独立票。

工具链固定leanprover/lean4:v4.36.0-rc1，Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`；manifest SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。源代码禁用项扫描、UTF8/noBOM/noCR/exact1LF均PASS。

主线另外完成v36整库机械门，本审者读取 `coordination/integration-v36/gate-result.json` 并核对两源码哈希完全相同，所有7门exit0。该收据SHA256 `2cf560661845bcbf2332b4252fc08b359b4a3b8a3ef3b4d0bb0510446fc24ef8`，35246B；记录1800公开定理、2971含生成定理、5075所属常量，复用且保全v35的256源/1033对象。此门由root运行，本审者没有重跑或将其当作语义审查替代。


### 前缀清单与生产计数的口径补充

根据已存完整canonical列表，本包初始SOURCE共58项：96是22公开合同+6源码私有+5源码生成=33；97是8公开合同+7源码私有+10源码生成=25。其中只有18条公开定理、12个定义。初始SOURCE采集在审计附录example/#check/#print之前；全部LATE结构名与SOURCE相同，两个清单的appendix_syntax_new_owned_constants和late_new_owned_constants均为空。58项没有审计器附录常量。

私有名称中的fresh-reviewXX/ExactSourceAudit组件是完整原源在新前缀文件中的模块身份。它们后缀对应已逐行审阅的源码私有helper及其生成proof，不代表附录新增helper。15项源码生成声明为96的4个numeral proof与sparseAmplitude.eq_1，以及97的3个定义equation、3个numeral proof、1个simp lemma和3个private proof。

58是此精确源码前缀环境的库存，不能直接当作正式模块导入后的所属增量，也不与其他分线库存相加来替代全库去重清单。整库5075−4759=316与跨报告原始库存总数320相差4，本OQ56已存列表不支持将差4解释为其附录声明；本报告不对未给出的生产差集作猜测。JSON保存这58个实际名称及分类，供主线按生产清单逐项对应。

## 未声明与最终裁决

本包消除原p53§2的标量慢量及一次递归选择义务，直接消费者为同一N上的真实质量Summable/HasSum、归一化标签法则和背景费用。

仍未支付：残余类别0质量、未来尾质量和背景幂、所有固定q/τ的诚实矩与指数预算、一次固定实iid法则及对称Borel核、独立G/Z与非零方差、真实典范正秩一积分算子、真实条件背景/事件质量/条件矩、每个n≥3的原Studentizer正性、平衡行抵消的实际概率应用、Gaussian尾比较及完整p53结论。全核H并未被声称为PSD，PSD只可能属于未来余项算子。原p52§1–5在v33的闭合独立保留，不归功本包。新颖性、临界常数与完整分类没有认证。

本轮两项非数学读取问题已纠正：初次从错误传入cwd查找AGENTS/SERVER后改读指定workspace；一次只读JSON摘要把mechanical-summary的整数records当列表，类型错误后改为按schema读取。一个远端请求JSON格式失败且明确operation_may_have_started=false，重构合法请求后成功。部分初始过长显示被截断，随后对所有需要的正文完整重读，或将重复源码逐字比对到已全文读取原源。均未启动Lean或产生远端写。

结论：CORRECT，无CRITICAL_GAPS。接受仅限精确head中上述两个确定性模块及其冻结接口；不扩大原根闭合。
