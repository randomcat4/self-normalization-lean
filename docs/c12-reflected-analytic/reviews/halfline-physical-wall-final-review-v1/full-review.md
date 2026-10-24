# 单元39、40独立最终完整审阅

结论：**CORRECT**。两份最终冻结目标均无关键缺口，属于合格的独立完整源文—声明—证明审阅。覆盖8个公开源证明及完整冻结声明、9个实际模块所属完整类型（含1个生成定理），两模块均无定义。全部原根继续为 **OPEN**。

评审者 `/root/halfline_physical_wall_final_review`，与作者 `01a16c4c-25a6-7740-a10e-12635a13edae` 分离；新鲜上下文，明确指定 `gpt-6.1-sol / xhigh`，单一C12子槽，无下派。只写本评审目录。平台未暴露 input、cached input、output、reasoning subset 计数，四项均记为 null。

## 范围与原文

完整阅读只读原文 `C:/game/shao/current/c12/supplement.tex` 第4192–4253行：定义的是固定a>0时严格Brownian桥存活概率、墙上及墙外零延拓，d=z-y、D=1+|d|/sqrtT，监控墙剖面P及P_b；原式要求在T>0、旧端点内部、b²<=T/2、新点闭域下控制补偿余项。原文还提出所有非负混合阶的导数界及墙上一侧估计。

本次验收的是显式标量反射公式的两个精确接口。单元39给实际物理坐标和实际空间导数下的小泰勒界；单元40给闭壁处解析公式的幂剖面、三项真实混合时间导数界及所有正阶空间迭代导数界。两者不把解析公式自动识别为概率，不把墙上解析导数自动解释成零延拓跨壁全域导数。真正零延拓的一侧导数接口留待源单元41。这个限制与冻结声明、源码和作者范围说明一致，不构成本次冻结目标缺口。

## 单元39：物理补偿余项

完整读取 `HalfLineCompensatedBounds.lean` 的两份证明，逐字比较完整导入、命名空间及两个定理头与原freeze，完全相同。

1. `upperReflection_small_taylor_bound`（源码第9行）：以u=a-y、v=a-z、beta=b应用已合格验收的规范化小泰勒界。hy/hz给u,v>0；hnew给u-beta>=0。对任意实数t，距离u-t*beta=a-(y+t*b)，能量T-t*beta²=T-t*b²，故完整路径恒等于物理上半线反射公式。u-v=z-y=d。真实空间导数由完整HasDerivAt证书给出为负slopeTime，故补偿项精确是(b-b²d/T)f_y。剖面严格为exp(-max(a-y-|b|,0)(a-z)/T)，常数8000100、|b|³、T^-3/2和D³全部保留。
2. `lowerReflection_small_taylor_bound`（第31行）：以u=a+y、v=a+z、beta=-b应用同一规范化界。u-v=y-z=-d，beta²=b²，|beta|=|b|；实际路径距离a+y+t*b及时间T-t*b²均正确。物理下半线空间导数为正slopeTime。独立核算(-b-b²(y-z)/T)(-S)=(b-b²(z-y)/T)S，确认两次负号没有抵消错误。|y-z|=|z-y|，下壁剖面为exp(-max(a+y-|b|,0)(a+z)/T)。

保留ha>0，即使标量代数不使用它。T-b²>=T/2>0，所以本定理从未使用零能量约定。新点等于墙面时反射式为1-exp(0)=0；b=0时余项严格为0。旧起点和终点仍严格内部，无隐含的最小墙距条件。

## 单元40：闭壁解析剖面

完整读取 `HalfLineWallProfiles.lean` 的6份证明与全部上下文，六个完整冻结头均未改变。

1. `bound_on_nonneg_of_continuous`（第8行）：由F/G连续，集合{x | F x<=G x}闭；它包含Ioi0，故包含其闭包Ici0。u>=0完整覆盖u=0，弱序关系未改变。
2. `reflection_power_profile_nonneg`（第16行）：对x变量，左右两边均为全实线连续函数。固定v>0、T>0及自然j>0，消费旧严格正u界，再用闭包引理；8j常数与指数半衰减不变。
3. `reflection_power_monomial_profile_nonneg`（第28行）：对含(2*x*v/T)^m的完整函数使用同一论证，任意自然m包括0，无x作分母；16j、4^m*m!与exp(-u*v/T)完整保留。
4. `mixed_time_profiles_nonneg`（第41行）：不是假设一般deriv算子连续。逐点利用此前合格的三个HasDerivAt公式，把真实时间一阶/二阶导数改写成x的多项式乘指数。T>0固定，各表达式对所有实x连续，其绝对值也连续。对三个完整不等式分别闭包延拓；常数80、6144、800及T幂、D幂、剖面指数均吻合。
5. `upperReflection_closed_iterated_profile`（第80行）：旧真实iteratedDeriv恒等式在全部实参数上适用；取绝对值后2(a-z)/T>0、指数>0，使用u=a-y>=0、v=a-z>0的新闭壁幂界。u-v=z-y及upperProfile透明值完全一致，包含y=a。
6. `lowerReflection_closed_iterated_profile`（第90行）：旧真实迭代导数含负系数的j次幂。abs_pow和两次abs_neg正确覆盖奇偶j；2(a+z)/T>0。u=a+y>=0、v=a+z>0，u-v=y-z，通过abs_sub_comm变为|z-y|，lowerProfile吻合，包含y=-a。

闭壁处使用的是全域解析公式的导数值；并未证明零延拓函数跨壁可微。这里允许任意实a是标量解析结论的更强版本，原文a>0的专门化有效；没有改动冻结前提。

## 全部实际类型、公理与工件

逐个完整、无缩略阅读两份 `actual-owned-types.txt`：单元39共13225字节、2个定理；单元40共25506字节、7个定理。八个公开实际类型与冻结头的量词、参数、自然幂、实数类型、导数函数、严格/非严格边界完全一致。生成定理 `bound_on_nonneg_of_continuous._simp_1_1` 的完整类型为任意宇宙及预序上的命题等式“x属于Ici b”等于“b<=x”，包括全部隐式参数与类型类；类型正确，仅依赖propext。全部逐声明覆盖及类型哈希在 `actual-type-coverage.json`。

完整读取两份原 `OwnedAudit.lean`。它按 `env.getModuleIdxFor?` 选择实际模块所有者，覆盖私有和生成常量，不靠命名空间前缀。对每个所属常量递归调用 `Lean.collectAxioms` 并拒绝白名单外公理。原审计映射分别为2/2/0及7/7/0（所属/定理/定义）；八个公开定理依赖仅propext、Classical.choice、Quot.sound，生成定理仅propext。两个定义值导出均为空，SHA256均为e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855。

只读服务器观察核实14个原receipt工件的SHA256及字节数、当前源码/attempt001源码快照、输出对象及安装对象；9个完整类型块逐块精确出现于原审计日志。两次首轮kernel和全所属递归公理审计的退出码均为0，直接复用原证据，没有运行任何Lean、审计或旧依赖producer。

服务器工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`，分支 `author/c12-halfline-taylor-v71`，HEAD `39f0716ef70c0c388f2902a374860451df10ea27`。钉死Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`、只读包视图 `cache-overlays/shared-v34/packages` 均吻合。原资源收据为CPU14–17、c12-heavy.lock、-M8192 -j4；评审未启动重命令，未接触外部CPU0–9/80GiB。

## 旧证据复用与边界

复用7个已合格依赖：小泰勒、空间剖面、混合剖面、反射公式、泰勒路径、泰勒线段、首阶剖面。逐项核实旧完整评审哈希、作者receipt/release、当前源码、输出对象和安装对象。完整读取本次消费的冻结接口及10个透明定义值，局部导出也与原receipt相符。没有重读或重验旧证明。

非阻断元数据问题：单元40原receipt的failedAttemptsPreserved末句机械沿用“2heads”；本次依完整freeze/源码/所属映射核实实际为6公开头、7实际定理，而非相信该描述性文字。原文件字节保持不变。原kernel日志仅有既知mathlib本地变更提示和单元39未引用ha/战术风格警告，无错误；ha在完整冻结和实际类型中保留。

两个局部冻结目标可接受；它们仍是源绑定辅助结果，不是C1/C2根定理闭合或新颖性认证。实际概率反射识别、零延拓一侧接口、实际区间核的完整正则性与其余源依赖继续开放。无关键缺口，无冻结目标内未覆盖项。

## 精确验收绑定

单元39 `Shao.C2.HalfLineCompensatedBounds`：

- sourceSHA256: `bdead915b728011a7f268d490bc5f3a3b21cc50e6ffb0c9f498019e2a79c0754`
- objectSHA256: `ef3b3aa10e6e218b7795b0e889e3f8336f1cec7dc7583e298901d5350c5cf2ac`
- frozenSHA256: `6f8e3be29d3cd88bc81f29b456541b66275544877f0cd635f49295db8e1efb9f`
- authorReceiptSHA256: `5373e21ef8f48dda186e917e451102e90ccb8d4d06c4acdbdc134840a3b1c0a3`
- authorReleaseSHA256: `04c16f7da7226fdced4156f7756c7d51d185c86ccc319f4f42030b36a1e3ac64`

单元40 `Shao.C2.HalfLineWallProfiles`：

- sourceSHA256: `dd0d51b63fbbbb1f67807f66ceb7a92f8f4e5ba883690eceb7dfe01ac9c2c6c7`
- objectSHA256: `95b909b378b541fbb20ae5ba277eac36e6f9ad4fe0a3189c646aaf6ed0447f10`
- frozenSHA256: `139320fcc0720f06949c4acd9868c10f02956d2749311f438b04e998bdb6c9e5`
- authorReceiptSHA256: `c27ce942fd20475ca4822ad255d77a17784675392a9178183925fabeeeff7e93`
- authorReleaseSHA256: `91f720aac653375e6682a48348db1485bb7414064adca0431c58576934e56ba5`

全部写入已完成；本评审者写入权与执行权均释放，无在途任务、无重命令。精确报告哈希由 `writer-release.json` 绑定。
