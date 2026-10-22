# RademacherSpectralPairing 独立形式终审 v1

STATUS: CORRECT
LEAN_STATUS: LEAN_FULLY_CHECKED
CONTEXT: 56
S2_STATUS: OPEN
ROOT_STATUS: OPEN

结论仅覆盖冻结的一个有限反射配对义务 P1 及其等价主项抽取形式 P2：全部 m≥1、实弱 cell m≤h<m+1、全部自然数 n（包含 0）、全部 13 个实际定义、归一化合法性和所列时间／小 m 端点。匿名数学证明完整，目标 Lean 陈述忠实，独立实际检查及完整结构／注册表／保全门全部通过。没有未解决的关键缺口。69 个公开辅助 theorem 不计为 69 个原始数学叶。

## 输入与独立性

只在 lead 明确 FINAL RELEASE 后读取以下数学输入及必要的已认证公共接口类型／完整定义值：

| 输入 | SHA256 | 字节数 |
| --- | --- | ---: |
| frozen-rademacher-spectral-pairing-v1.md | 69c5cf5822044e19520e10c4a6de4a31e0e8f43d296e477982a9c5637c85c6fb | 8661 |
| 原 spectrum01.md | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 4306 |
| 完整 Source.lean／canonical | 7cc1e142db3c9e6f2c788ca83f213bb2ea1c4d58d2207b30a43ed5fd471d50ea | 24435 |
| 匿名 proof.md | 06a10a6096d865c0b8964ab1f6d159062c59b752540929054a660cdbb107790f | 18381 |

本上下文未读取作者 receipt、notes、checkpoint、过程或 raw；未读取任何其它 review 推理；未向作者交换数学结论；旧 theorem proof body 暴露 0。反射中的 collectAxioms 只在 Lean 内部遍历依赖，输出公理集合，不把旧 theorem proof value 交给审查者。所有 raw、完整 Expr、注册表、日志和二进制留在服务器，未下载。

原 e44ee586…／9861 B 机制 PREP 的服务器原件及本地 exact archive、原 04041bbc… receipt／a3eaa850… manifest，和 28c9b597… 不可变基线 supplement／72afa138… receipt／c5315b9e… manifest 均保留；此次 FINAL 不覆盖这些服务器原件或本地 archive。标准 formal-review 路径现在交付本 FINAL。

## 数学与 statement 忠实性

实际固定概率对象是 RademacherCosine.law，即两个 ±1 Dirac 测度各乘 1/2；Path n 是 Fin n→ℝ，prefixSum 是前 k 个坐标的有限和，closedStrip 是所有 k≤n 的 |prefixSum|≤h。独立 SemanticAuditV2 已实际展开该 law、halfENNReal 和 closedStrip，检查 P1/P2，另用 rfl 完整展开 remainder。实际概率没有被谱和重新定义，定理没有额外的自由 p、law、谱参数或 U1 条件。

直接引用的已认证 S1 公共 theorem 为 killedMass_finite_s1、closedStrip_probability_finite_s1 和 finite_s1_zero；其实际完整类型与对象定义已反射并读取。它们把同一 m≥1、m≤h<m+1、任意 n 的 Measure.pi closedStrip 概率与真实 killedMass 以及全奇数 S1 和相连，未用新 axiom 或“假定 S1 的任意结构”替代。源码只 import RademacherFiniteS1；ScalarBounds 不在 Source 的实际 closure，是托管项而非证明前提。

逐项审查匿名证明与 Source 后：

1. lowerModes、反射像和 centerModes 对原 range(m+1) 给出互不重叠的完整覆盖。自然数 m−ell 只在 ell≤m 或已证的下半部使用；反射对合和单射实际闭合，不存在漏项或重复项。
2. alpha 反射为 π/2−alpha，beta 反射为 π−beta，故 cot 反射为 tan、余弦反射为负余弦；(-1) 的反射系数与负谱自然数幂合成 epsilon=(-1)^(n+m)。全时间配对没有取绝对值，也没有添加奇偶匹配。
3. 对所有 m≥1，下半部角度在 (0,π/4)，beta 在 (0,π/2)，相应三角分母非零。amplitude>0、0<rho<1、amplitude*rho^n>0 均从原范围推出，包含 n=0，没有以生存概率为分母。
4. P1 的实际 Measure.pi 概率及 killedMass 版本都接原 S1，首对精确抽取为 amplitude*rho^n*(1+epsilon*tan²)。最负模态自身系数为 (-1)^m/H*tan(π/(4H))，其特征值保留 -rho。
5. 13 个实际定义 lowerModes、reflect、centerModes、alpha、beta、epsilon、amplitude、rho、zeroMode、rawTerm、pairedTerm、normalizedTerm、remainder 的全部结构 value 均已比较。remainder 是明确的 erase0 有限和加 zeroMode/(amplitude*rho^n)，不是待选择误差变量。P2 的全部原量词保持不变。
6. 偶数中心零谱在 n=0 保留 0^0=1；只有 n≥1 才消失。零时间完整概率等于 1。m=1 的 remainder 对全部 n 为 0；m=2 仅正时间 remainder 为 0。m=2,n=0 时 zeroMode=-1/3，remainder=-1/(3*amplitude2)<0；后一个严格负号还由独立审计实际验证，未误宣称中心或余项为 0。
7. 正时间余频率来自原反射配对后的奇数 r≥3 且 r<H。整数 h=m 仍是弱闭边界，实际吸收点 H=m+1 未改成 h。全部 n 包含0，没有大时间或 n/H² 前提。

因此冻结 P1 和同一身份的 P2、真实概率连接、分母与全部列明端点均满足。匿名证明对完整 j 中心的解释只用透明 v_j(0) 的含义；本叶交付从已认证奇数 S1 开始，不据此新增 fullSpectrum 认证。

## 完整 Source 与 actual import 结构门

两份 Source 审计均将原 24435 字节作为唯一连续块保存；前缀仅必要 import Lean，后缀是通用反射与作用域采集。实际 -R 模块身份就是 Shao.OQ4.RademacherSpectralPairing；A 的选择是 ALL getModuleIdxFor? none，没有 raw／namespace 名称过滤，没有 self-import 目标 olean，没有在 Source 前置 old43 imports。Aall 另外采集原闭包内全部旧 owner OR raw/user namespace，加全部 current。

反射保留完整 Name／Level／Expr／MData／Syntax 构造、kind、宇宙参数原顺序、完整 types、每个 definition／opaque 全 value、metadata、flags、公理集合与真实 owner。只排除 theorem proof value。比较只把 moduleIndex／sourceCurrent 视为 source→import 传输标记；owner 单独严格按对应 scope 保持。没有依赖 pretty-print、截断 Expr、计数或作者结论判等。

| 独立环境 | 实际 records | definitions | theorem records | closure |
| --- | ---: | ---: | ---: | ---: |
| A0：原 S1 imports、对应 opens | 310 | 27 | 283 | 5510 |
| A：完整 Source 的所有 current | 145 | 13 | 132 | 5510 |
| Aall：原 closure old OR namespace，加 current | 455 | 40 | 415 | 5510 |
| actualDirect，Source opens 对齐 | 455 | 40 | 415 | 5511 |
| 原 own B0：old43 pure imports | 990 | 108 | 882 | 5680 |
| actualFull44：old43+target pure imports | 1135 | 121 | 1014 | 5681 |

A 的 145 条含 69 个公开、2 个私有用户 theorem，61 个自动生成 theorem 以及 13 个实际 definition；私有及生成项全部进入比较。raw Name 与 user Name 的实际 source/old 交集分别计算，均为 0；不是先假定无交集再相加。比较器仍保留交集 old owner 的规则，并已在 PREP 的碰撞夹具验证。Aall 精确等于 A0 与 current 的逐条合并，actualDirect 的 target-owned records 与 A 的 145 条完整语义字段一致；actualFull44 中同一 145 条也与 direct 精确一致。

原 own B0 的 990 条全记录及 108 个定义全部完整 value 逐条保持，含一条 raw/user OQ4 namespace 外而由实际 old owner 选中的辅助项。full 共1135条中1134条在 raw/user namespace；owner OR namespace 覆盖没有漏掉 outside helper。

actualFull44 的实际 OQ4 导入模块恰为44，记录 owner 模块为43。Shao.OQ4.Foundations 已导入但没有自身记录，二者分别核验。没有用 owner 集合大小替代模块导入数，也未预设 target record 数为45。

S1 原闭包与 fullold43 的唯一 owner 差异为 Shao.OQ4.killedAction.congr_simp：原 S1 scope 归 RademacherAllModes，old43 scope 归 KernelRecurrence；其它全部结构字段相同。对应 scope 内均保持实际 owner；本报告不跨 scope 宣称所有 owner 相同，也不将这项旧辅助归属差异当成新 Source 覆盖。

## 完整注册表与作用域门

本次使用完整通用 collector，而非旧四字段 registry。global／scoped／private／inactive／erased／new／default、各 stateStack 层与 scope flags、instance value／priority／synthOrder／attributeKind，以及真实 discrTree root／chain／path／entry／children 原顺序全部保留。source/direct/full 的 registry 比较由真实 closure/order 与 lexical open／section stack sidecar 先行门控：

- A0↔A 和 A0↔Aall：同 closure5510、同原顺序、同 lexical／section。
- A0↔actualDirect-aligned：target 恰出现一次；ordinary 与 default 两 export 域中 target 的实际 entries 都是空数组，才允许去掉这一个空模块过渡；其余 closure/order 与 lexical／section 一致。
- own B0↔actualFull44：同样只允许实际空 target 模块过渡，其余 closure/order、lexical／section 一致。
- 全部注册字段及顺序在各自对应环境中精确一致。Source/current registry 没有新注册项。没有为了判等删除任意模块、scope、路径、优先级、数组重排或其它差异。
- A0 与 B0 是不同环境，不直接声称注册表或全 owner 相等。D-neutral 只用于目标 records 与 full 的对照；两者 closure 不同，不直接宣称整张 registry 相等。目标 records 的全部语义字段仍精确一致。

Source closure 原顺序签名：
64c55c7193fa1b84ebd989109a539d4aa243415b777802844c29211ec2a4e626。
Source header import 原顺序签名：
448c7dbcc8c364683647c7f851c0d5b60bf2039befb0dd5a34bec53b50cf450c。
full44 closure 原顺序签名：
3447c3fc9a83a7eaaf205f50fd6aad4a862c7c4e6c004e59a46f264c70bb3647。
full44 header import 原顺序签名：
d806d362109ed81493ec9b0eccb6a0c3d1f1ff77b15091d69484f67f3446861d。
完整 scope sidecar 哈希、字段比较结论与 raw 哈希／字节数见 curated receipt。

## 实跑、依赖与保全

工具链固定 Lean4.36.0-rc1，commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e；mathlib 807d3836b165983210ee2ecf3cd28f239436949c。全部 Lean 只在指定 server workspaces/lead-oq4，先 activate 再 cd，单进程、taskset0-3、-j1、真实 -R，无任何 -o 或私有 olean 发射。

实际 canonical 命令：
source /root/rivermind-data/shao-lean-20261021/activate.sh && cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4 && taskset -c 0-3 lake env lean -j 1 -R /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/RademacherSpectralPairing.lean

其它各次完整实际命令、-R、退出码、耗时、log SHA／bytes 都逐项保存在 curated receipt；没有用预期命令代替执行收据。

| 检查 | exit | 秒 | log bytes |
| --- | ---: | ---: | ---: |
| canonical | 0 | 7.85 | 0 |
| A0-imports | 0 | 27.42 | 928 |
| A-source | 0 | 23.53 | 968 |
| Aall-source | 0 | 31.93 | 974 |
| D-aligned | 0 | 27.22 | 924 |
| D-neutral | 0 | 27.27 | 940 |
| F-full44 | 0 | 27.92 | 924 |
| B0-scope | 0 | 4.44 | 920 |
| public-interfaces | 0 | 19.79 | 942 |
| semantic-audit | 1 | 3.82 | 2099 |
| semantic-audit-v2 | 0 | 4.00 | 1785 |

共10次最终检查 exit0。canonical 无警告、无输出；反射／scope 审计每次仅2条自己的未使用局部 codec helper（litj、bij）警告，无error；SemanticAuditV2无warning/error。初次独立语义审计因自身未打开 ENNReal 记号域出现2条 parser error，保留原源／log／receipt，只修正自己的 audit 并展开 halfENNReal，v2 的7个独立例子全部通过。目标源码始终未改动。

PREP 的 CoreM lift／Options ForIn API smoke、erasure 作用域测试失败、不可变 metadata guard 中44→真实46项 header 的计数假设修正，以及 FINAL 初次外层字符串构造在派发前被拒绝，均在保留的历史或收据说明；没有隐藏失败、覆写原 raw 或据此改变数学前提。最终数学／结构比较无失败。

145个 source-current records 的传递公理并集恰为 propext、Classical.choice、Quot.sound；新增 axiom0、unsafe0、partial0。源码 sorry、admit、axiom、unsafe、partial、native_decide 标记均0。所有 theorem proof value 仍排除在反射输出之外。

前后完整保全均通过：branch feat/oq4-spectral-pairing，HEAD38648924aa3732ed3653363ad91872d237261fc2；immutable base d90f2f98a763ba0838376985bda0259b489d59d741cc4dc4f30ba78efef75eaa／6751B；完整136源／配置=旧135+唯一PairSource，整个.lake/build完整101文件=旧100+唯一Pairolean，逐项hash和完整路径集合均精确。唯一Pairolean b90ac1f16d32e4ebca0b616e6bada7da37d9e07f4648f8a7bf80c1f812be4df1／1234496B。旧44个canonical均冻结，无Source／Git／shared／cache写入。

关机恢复先核自己的全部 exit receipts、log hashes、Source/full comparison PASS和已落raw；全部已完成，因此恢复后不重跑任何成功Lean或完整结构比较，只做证据身份与最终保全。当前Lean／Lake live0，自己的olean／ilean0。

收尾时收到新资源约束：今后新检查只能taskset18-21，常规单进程8GiB，命令局部限额而非globalcgroup；当前新Lean槽由DA1PREP64独占。本次只作curation，无新增Lean或重型检查，不占该槽，也未终止外部或未识别进程。历史已成功的0-3命令照实保留，不据新约束重跑。

## 通用工具复用与证据交付

仅复用明确白名单的两份纯metadata通用工具：原instrument SHA240bef5756defdc5ab05660a9bb7c4d76d69802ac0d2e24fa4b54f403414f938／11623B，原compare SHA873a090d36630323de898a02694762b62bd2d2061e42f9b5c5746d5d4b1a102a／4772B。compare原字节未改；instrument只作已披露target／manifest／输出参数适配。scope sidecar复用其中结构codec。本上下文独立编写作用域门、夹具、最终wrapper与比较驱动，独立采集所有自身raw；没有复用他人raw，不主张通用工具独立原创或零复用。原299项机制正反例及全部历史保留。

curated receipt：
/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-spectral-pairing-independent-v1/final/independent-final-curated-receipt-v1.json
SHA 3e3dfd5029811994141aa8e206085fa7e9935e42327ea5fd84ad4b5b1effc1f7／47953B。

完整server证据快照manifest：
/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-spectral-pairing-independent-v1/final/independent-server-evidence-manifest-v1.json
SHA39dfc93995a49c0f65b41a6f1374fbb03a8a11aada2f715cd94fee7ad15ee907／18148B。

全部完整Expr／registry／日志／raw仅在：
/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-spectral-pairing-independent-v1/final
本地只交付本报告、curated receipt与精简artifact manifest。三者严格UTF-8、无BOM、无CR、恰一末尾LF。

最终裁决：CORRECT / LEAN_FULLY_CHECKED，仅此冻结有限配对叶。P1/P2视为一个原始义务。U1、统一S2余项界、S3–S5、Brownian、fullSpectrum、一般OQ4root继续OPEN；本终审不认证这些结论，也不单独作研究新颖性或主会价值裁决。
