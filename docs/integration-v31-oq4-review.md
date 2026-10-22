# OQ4 截至 PR104 的集成验收

结论：接受全部15个冻结PR中的20模块、206个显式公开定理，限于各自已冻结作用域。没有阻断本批源码接受的缺口。此票核对已有独立审查与机械证据，没有运行 Lean、重计算或修改数学源/GitHub。root新的整库集成门另行。

只读API观察时间：2026-10-22T02:52:51.835607+00:00；15PR当时均OPEN、未合并、MERGEABLE，完整head/base精确匹配。20源码本地冻结副本、发布Git blob及全部receipt列出证据SHA256均精确相同；52个发布verification JSON已读取。tip104相对v30的114项旧数学源/配置逐字节保持。

顺序：46 → 50 → 53 → 57 → 62 → 65 → 68 → 72 → 75 → 79 → 82 → 86 → 91 → 98 → 104。root已告知在独立集成工作树正常三方汇入PR104；这已经包含前14个OQ4祖先，不能重复合入或重复计数。

| PR | 完整head SHA | base SHA | 新数学模块 / 显式公开定理 |
|---:|---|---|---|
| 46 | `28b459e8d6e30cc06c8402027c1a8ee18a08c5a7` | `48b0ede5cc3b3fc42cee42480c0e5a4e07045a98` | TruncatedEnergy / 18 |
| 50 | `e71b0290c5439457064342e7a63fe11aec7cb0e6` | `28b459e8d6e30cc06c8402027c1a8ee18a08c5a7` | EnergyTiltedLaw, EnergyLogNormalizer, EnergyE1Bounds / 31 |
| 53 | `ae4b9c3865e33e231252693e23ff0338ead29b16` | `2380a8e5798e848f3c9d644ff09e83a90194fd38` | EnergyLinearTiltLaw, EnergyLinearTiltDerivatives / 23 |
| 57 | `1695839731c586cbeb34f157f9aec2246ec00c7a` | `ae4b9c3865e33e231252693e23ff0338ead29b16` | EnergyLinearTiltComparisons, EnergyLinearTiltVarianceWindow / 15 |
| 62 | `69d44c430ba5b2b9a9f3e7c3bf8d4607118465ef` | `1695839731c586cbeb34f157f9aec2246ec00c7a` | EnergyLinearTiltCentering, EnergyPathLaw / 16 |
| 65 | `4388ae02623c03dbf6b707fb3847d8793924d39a` | `69d44c430ba5b2b9a9f3e7c3bf8d4607118465ef` | EnergyE2Bounds / 6 |
| 68 | `c846961bd3dd7a4bac6178b04baa50393ab23cf2` | `4388ae02623c03dbf6b707fb3847d8793924d39a` | EnergyLinearPathLaw / 12 |
| 72 | `d3a16df03abc97e0f6e4af81972eba4b99f5da90` | `c846961bd3dd7a4bac6178b04baa50393ab23cf2` | RademacherCosine / 9 |
| 75 | `51a137af89b4c7060ac4af0baf6410820bc76a4f` | `d3a16df03abc97e0f6e4af81972eba4b99f5da90` | EnergyRelativePathBounds / 6 |
| 79 | `78f9bfd7f028c3b6971ca5e393764ccb241047e6` | `51a137af89b4c7060ac4af0baf6410820bc76a4f` | EnergyJointTransport / 6 |
| 82 | `db692904c6977b2a783184838bb7a4d4acd98c77` | `78f9bfd7f028c3b6971ca5e393764ccb241047e6` | RademacherIteration / 7 |
| 86 | `c8112257ac213cd488ae24ab73100fab36837802` | `db692904c6977b2a783184838bb7a4d4acd98c77` | RademacherFiniteBasis / 9 |
| 91 | `b8bcf3561a20ee91894de23fdb842b4a381b15be` | `c8112257ac213cd488ae24ab73100fab36837802` | RademacherAllModes / 8 |
| 98 | `045f6680004b1b62163b7a4a4c2612f9a42de3d6` | `b8bcf3561a20ee91894de23fdb842b4a381b15be` | RademacherFiniteS1 / 19 |
| 104 | `38648924aa3732ed3653363ad91872d237261fc2` | `045f6680004b1b62163b7a4a4c2612f9a42de3d6` | RademacherScalarBounds / 21 |

允许导入且仅新增以下20个模块（完整hash、原始来源、语义票/数学票/终审票与机械回执见配套JSON）：

| 模块（Shao.OQ4.前缀） | 公开定理 | Source SHA256 | 接受范围 |
|---|---:|---|---|
| TruncatedEnergy | 18 | `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0` | N0：真实闭截断能量权重、可积性、三阶矩支付、精确有限归一化展开。 |
| EnergyTiltedLaw | 22 | `ea13bcf07671ee77a90910807f09f6c1c1deb95e1834f0715bcc042ab5ecbddd` | N1：同一真实withDensity倾斜概率律、支持、积分转换与真实有限矩界。 |
| EnergyLogNormalizer | 6 | `6bbf4093ed296e5fa40cc680f77670c5a3889d95a3679a1cfaf011a84efa6906` | N2：实际log Z；T-only误差系数与M,T共同高度。 |
| EnergyE1Bounds | 3 | `448db6e250307358455e7c8da660ffdb094ddb5a42f0e7e81e9c08c02aa4d39d` | 有限一维E1：N0/N1/N2的同一常数总接口及固定law推论。 |
| EnergyLinearTiltLaw | 14 | `63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78` | 实际能量律上的全部实参数线性倾斜族与真正可积性。 |
| EnergyLinearTiltDerivatives | 9 | `f84467d102660c9abfa09062d1dbe8b3c499058b9960d779aa86fcd653b9a6b2` | 同一积分族的全实参数HasDerivAt、中心平方积分身份及连续性。 |
| EnergyLinearTiltComparisons | 8 | `f1aa93d33998f5365d236b9f96e2e04cab4e6235672a7b634988cd2330497cd4` | 七项raw/normalized有限矩比较，保留两个归一化附加项与D²。 |
| EnergyLinearTiltVarianceWindow | 7 | `a0059db361b524332d85c73eb13577b67de5df1fe4d7f41c3cd2aba9072e5c73` | 固定M,T,K后的共同有限方差窗口，真实方差与导数值。 |
| EnergyLinearTiltCentering | 7 | `82f48c2123d499eed5a7ac8974ff7d51d18e09987539f8323dece141e08bbe16` | 同一实际线性族的中心参数存在、闭窗端点及精确零均值。 |
| EnergyPathLaw | 9 | `3336b977fbe88ae4c27ff7531ffeec6e14c71508587ac2abae99bf475757a177` | E3式(7)实际有限乘积路径密度、真实积分及iid拉回；发布LF补充绑定新SHA。 |
| EnergyE2Bounds | 6 | `41b7343861549f55ae86cddb514a5ed55612448b1ab0efc1e3bb580182746ca8` | 有限一维E2式(5)(6)：实际log支付、同一θ/law与共同C2/H2总入口。 |
| EnergyLinearPathLaw | 12 | `039ad7326ea9a80e476f50bf3f46dd0078c2c61f6786f15a6d72f3ba0c227afb` | E3式(8)全实参数的真实反向路径密度、有限夹界及iid概率。 |
| RademacherCosine | 9 | `c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861` | 固定Rademacher弱闭整数类的一步主余弦对；不等于完整生存概率。 |
| EnergyRelativePathBounds | 6 | `7f9242f4116924f26c9c7b75313e4e37b49c13f7da4f4052e7a7585984a2b654` | 同一θ先于全部n的有限乘法相对路径夹界，保留零质量。 |
| EnergyJointTransport | 6 | `fe6fe757c7fe997cc36727477b4d22f17c2373b7e90657d68f7b5d7ef8d2a39e` | 固定原律h→∞、n/h³→0的联合尺度标量相对传递及真实iid版本。 |
| RademacherIteration | 7 | `dd8986ebe885d4f5cbe9ea021ee6b193ab927e066b9a15f2e5e22e0d030ad360` | 实际有限整数网格保持与主余弦的全部自然时间幂，含n=0。 |
| RademacherFiniteBasis | 9 | `f61cd3f2ea5430c39faa69a96b3ca169d11d5f4585047d7a174491608e5f4f27` | B0–B3完整有限正弦基、显式重建及真实核一步全模态身份。 |
| RademacherAllModes | 8 | `04cd5a52a40398586908a42682724c357daf0e0c8bbf25a049bbd620d27ee8aa` | D1全模态真实有限幂与D2常数一未化简生存谱；source17、distinct-new16。 |
| RademacherFiniteS1 | 19 | `d51b0d0712867e7a078871a49e3ffa7c8c59edf6695e07a306b9fe7bb4c65d13` | C1–C5完整零起点有限S1、cot和及独立低阈值分支，含全部n≥0。 |
| RademacherScalarBounds | 21 | `12670bd33a813849156b245cad28f5efb783a55919f8a0743fcf3fb9fbff329f` | SCA0/1/2及先于全部m≥1的绝对常数标量界；真实Cosine定义桥。 |

语义与公理覆盖：逐模块存在源→冻结票、匿名数学票与最终源形式票；本次核实精确字节、完整结论和实际机械回执，未从零重证。独立完整源通过ALLnone无名称筛选，含private/generated/导入名helper；实际共同import按各票的owner或namespace并集范围审查。公理仅propext、Classical.choice、Quot.sound。早期stdin/类型公理比较不升级成后期完整Expr/定义体/所有者/全实例登记检索树审查。

必须保留的限定：

- INDEPENDENCE_SCOPE：本轮是新上下文集成证据/源码验收。既有source语义审查中的若干译者参与过候选intake，票面明确不是新鲜数学证明审查；匿名数学与最终实现审查的访问边界按原报告保留。不得宣称整条历史全盲、双重独立重证或全部旧proofbody曝光0。
- ALLMODES_OLD_PROOF_EXPOSURE：来源语义票明确意外看到旧 KilledKernel 30–33/38、KilledIteration 74、KilledPathLaw 167–168/250/261–262 行短proof/helper开头；最终形式票接口提取V1又意外露出旧FiniteBasis.theta_one及mu_one两条j=1兼容证明体。lead已允许准确披露后继续；不是新D1/D2证明证据。不能记为零旧证明体访问。
- ALLMODES_OWNER_OVERLAP：source/direct拥有17项，全41 distinct-new16；唯一 killedAction.congr_simp 与旧847重合，非owner字段相同，完整共存owner保持旧KernelRecurrence。必须按实际作用域保留owner，不能把source-owned数量相加当作新distinct数量。
- OUTSIDE_GENERATED_PRIVATE：源码ALLnone无名称筛选；import并集包含module-owner OR namespace及private/generated。Derivatives的energyLinearMean.eq_1、Comparisons旧函数名helper、Joint的energyRelativePathError2.eq_1等均实际覆盖。不能仅按target namespace/public清单验公理。
- SOURCE_IMPORT_AUDIT_EVOLUTION：早期stdin票只明确比较其实际完整类型/公理及对应私有名前缀规范化，不倒推成后期真实-R/raw Expr/定义体/owner/全registry及discrTree逐字段门。后期同范围、同导入顺序/词法作用域比较才按各票承诺范围接受。
- ENERGYPATH_LF：原数学源4feb2d70…/15246B无末LF；发布源3336b977…/15247B恰为old+LF。原终审7b72f6ba…仍绑定旧源；独立源码格式补充16968d36…明确重验新精确字节no-o/ALLnone/全33共存均0，不能覆盖原票归属。匿名proof原字节及proof格式补充另保留。
- RELATIVE_REPORT_CRLF：终审原票1e07ca8f…/11676B保留；发布副本78df65bc…/11674B只删除最后CRLF，前已有LF保留，正文相同。未改数学源、证明或olean，无需因报告排版重复Lean。
- FAILURE_DENOMINATOR：保留所有历史工具错误：Path/LinearPath pp.width、E2首轮namespace引用、Cosine额外旧imports导致完整Expr拒绝及generated universe错断言、Basis/AllModes展开契约错误、S1词法/顺序调整等，均按票面在审计工具内修正，不伪记为全历史exit0。
- SCALAR_CHECKER_FAILURES：8次最终Lean均0；Compare exit1因43imports被错当43owners（实际42owner，Foundations无声明），Compare2 exit1因把前比较器失败错计Lean失败。通过依据是保留的Compare2完整结构检查点及Tail exit0/72证据检查，不伪称两比较器0；lead首次Python路径缺失exit2未执行Lean，随后实际导入检查0。
- SCALAR_FREEZE_METADATA：冻结稿第137行残留候选阶段文字；source语义票以第4/13行明确采纳与第51–93行SCA范围审查。非数学、非阻断；不扩大为C_log/C_tan或概率S2。
- MAIN_DIVERGENCE_AND_BRIDGE：PR46 merge-base为7117acb8，不是v30。base→head树差异含v30其他线删除但GitHub三点增量仅14新增；应正常三方合入，不能覆盖main树。PR53 base2380a8e5实际父为PR50/e71b0290和与v30同树的7f6f5f1e。tip104的114项旧数学源/配置与v30逐字节相同。
- ROOT_GATE：截至本轮API快照15PR全OPEN/unmerged；root随后告知已在独立integration-backlog-v31正常三方合入PR104 tip但尚未发布。本票只放行冻结内容与允许imports；root新的整库编译/公理/清单/发布门仍单独负责。本验收不自行修改GitHub。

原始承重机制采用非加权范围分类：完整形式化2组、部分形式化3组、未完成3组。该8组只按原文具名结构归类，不能当成工作量百分比。外部BE、SP两项仍未在项目中一般性重证，另列，不与K父子重复统计。

| 原机制 | 状态 | 已覆盖与剩余 |
|---|---|---|
| K_Kv | PARTIALLY_FORMALIZED | 有限真实核/路径链、条件BE/SP下S/AC/O0/OC/R3/R4/有限D8及精确有限方差缩放；旧已合入证据不重复计为本批新增。 剩余：实际BE、SP输入本身；固定时长不变性/Brownian块B0–B4/B1、终端块P0–P2与4/π、全部长时间统一极限选择与K总装配。Kv为K派生父结论，不双计。 |
| E1 | FULLY_FORMALIZED_FROZEN_FINITE_SCOPE | 实际截断概率律、真实可积性、log及三个矩误差，同一T-only常数与共同M,T高度；PR46/50。 剩余：本组有限一维范围内无缺口，root集成门另行。 |
| E2 | FULLY_FORMALIZED_FROZEN_FINITE_SCOPE | 全实线性族、真实导数/方差、共同窗口、同一θ精确中心化及共同log/二三阶矩界；PR53/57/62/65。 剩余：本组有限一维范围内无缺口；未要求θ唯一或可测选择。 |
| E3 | PARTIALLY_FORMALIZED | 式(7)(8)实际有限路径密度/积分/iid与同θ乘法相对界；h→∞及n/h³→0下联合标量传递，PR62/68/75/79。 剩余：式(9)(10)实际双变量共同算子及微分共轭的共享形式接口。不能把标量薄叶称完整E3。 |
| E4 | NOT_COMPLETED | E1/E2及有限E3作为前置已形式化。 剩余：真实K/Kv及稀有生存内h²尺度条件能量集中；无条件LLN或自由条件输入不替代。 |
| E5 | NOT_COMPLETED | 有限E1支付可作前置。 剩余：随机分母中心/中等/全部远层相对支付；保留Z(s)^n−Z(0)^n差分与Q=0路径。 |
| E6 | NOT_COMPLETED | 有限精确方差缩放接口是前置。 剩余：固定law原开窗口a_n<x<1的全部序列拼接、正点Donsker/LLN及真实Brownian分母接入。 |
| Rademacher_Spectrum | PARTIALLY_FORMALIZED | 实际弱整数类主一步、自然幂、完整有限正弦基、全模态幂、精确零起点S1与低阈值分支、SCA0–2标量界，PR72/82/86/91/98/104。 剩余：Pair/Tail后继认证、概率S2–S5、实际Brownian、strict与其他coset；临界相位数学/私有源进展不计为本批已认证。 |

OQ4、sharp分类、完整K/Kv、E3/E4/E5/E6、概率S2–S5、实际Brownian、strict/cosets均保持OPEN。Pair/Tail/DA1/DA2/critical phase不在本批允许imports中。206是显式辅助公开目标，含薄汇总与依赖；不存在已冻结的完整剩余细粒度分母，不报告完成百分比。

完整结构化接受名单：[oq4-review.json](oq4-review.json)。只读证据位于同前缀oq4-local-evidence.json、oq4-remote-evidence.json、oq4-remote-receipts.json；原始大日志、Expr及登记仍在服务器，未复制或复算。
