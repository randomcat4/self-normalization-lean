# CP 最终实现：fresh90 独立有界终审

STATUS: CORRECT

原始数学→冻结 CP0–CP3→完整匿名证明→最终 Source→实际环境接口的独立终审通过；必要的原生 no-o 检查与全部实际所属对象公理审计均 PASS。本独审只认证确定性 CP，不认证实际概率连接、S4/S5、Spectrum 或 OQ4 全根。Brownian 首项已由 root 另行在 PR140/v35 接受（CLOSED_INTEGRATED），不属于本独审裁决。本 CP 工作树未吸收该基线；未执行规范源码发射、产物生成、合入或共享基线更新。

## 输入、完整读取与隔离

| 输入 | 实际字节数 | 完整范围 |
|---|---:|---|
| 原 spectrum01.md | 4306 | 1–119 行 |
| 数学冻结 frozen-rademacher-critical-phase-v1.md | 8147 | 1–117 行 |
| 完整匿名 proof.md | 22593 | 1–379 行 |
| 精确声明冻结 v2 | 10959 | 1–214 行 |
| 最终 Source.lean | 56619 | 1–1152 行 |
| stable-base-v1.json | 45133 | 1–412 行 |

六份输入均完整读取，实际 SHA256／字节数与指定版本一致，完整值记录于 review.json/input-read-receipt.json。最终 Source SHA256 为 `388f17e1c257d9b1fe74914866937bd9dc6ce1fb1398e72761b3f65c8464a96f`；读取前已核对该值，没有读取旧版 Source。匿名证明和最终 Source 为本轮首次曝光。Source 按 1–280、281–570、571–860、861–1152 分段完整读完，证明完整读至 379 行，二者无输出截断。

stable-base 首次展示中间被工具截断；已通过完整 JSON 解析、全部四组键／路径清单恢复及服务器逐项实际哈希比较补全，不以截断内容作验收依据。必要 Lean API 初次展示的中段也已定向重读恢复（ConstantInfo 安全／partial／值、SMap 进口／本地表、module-index、CollectAxioms、run_cmd 无环境污染语义）。未读取作者 progress、receipt、failure logs、他人的数学或完整 Source 审查推理，未读取共享工作树证明体；只使用自己的实际检查输出。没有子代理。

## 数学证明与实现的承重核对

| 范围 | 匿名证明／最终 Source | 裁决 |
|---|---|---|
| CP0 实际根及有限前缀 | 证明 23–101；Source 59–224、860–928 | 根固定为实际 Real.rpow 的实数 1/3 次幂。非负、正时间严格正、立方及唯一性已证。n=0 的高度为 0、delta=1、第三尺度为 0；正时间的 1/c³ 恒等式仅用于 n≥1。Nat.floor 与 Int.floor 对应、弱 H=floor+1、整数高度 delta=1 均覆盖。具体 cutoff=max 1 ceil(1/c³) 的全部合法性、两个发散尺度及任意 StrictMono 采样的同域最终合法性均为输出。 |
| CP1 c=1 端点 | 证明 105–146；Source 598–714、840–858、930–982 | 真实 k³ 和 k³−1，分别有 k≥1／k≥2 的完整有限结论。自然数截断减一在下界核验后转换到整数／实数；k−1 的转换同样保留。真实 (j+1)³、(j+2)³−1 严格递增且每项合法，同一尾函数的 delta/E/F 极限完整；k=0、1 的有限例外未误用。 |
| CP2 舍入、稳定胞元和尾部 | 证明 150–315；Source 230–384、415–596、984–1080 | 统一有界误差引理的分母以 k² 正下界控制，早期 w(k)=0 不导致非法除法。其误差条件对实际 ceil、ceil−1、floor(t+1/2) 分别证明后才应用。ceil 误差 [0,1)、下采样 k≥1 的 ceil≥1／减一转换／误差 [−1,0)、最近整数的 (−1/2,1/2] 与半格向上均已证，k=0 下采样独立为 0。高度误差、方向、稳定 floor 和相位极限全部由这些实际函数推出。相邻目标间隔压过两个舍入误差，产生严格尾部；固定 K 再同时包住合法域与稳定胞元门槛。没有把这些结论加入公开前提。 |
| CP3 全相位与完整极限点集合 | 证明 319–373；Source 716–838、1082–1150 | d=0／1 使用真实 down／up，内部取 α=1−d。公开 phase_realization 经 aux_actual_phase_tail 直接证明固定 phaseIndex(c,d,j+K)，无自由 σ 替代；同一 K、同一实际尾函数同时实现 delta、E、F 三极限并全部合法。三个 Cluster=Icc 都证明两方向；E 区间经除以 q>0 实现，指数区间任一点经 log 的正域与 exp/log 互逆实现。整列不收敛分别由 0≠1、0<q、1<exp(q) 的两端子列和极限唯一性得到。 |

c 始终在外层固定且只有 c>0；α 的内部范围、d 的闭区间范围没有缩小。K 在 c／α／d 固定后存在，位于全部逐 j 条件和极限之外。任意合法采样定理的 StrictMono 输入是其原范围；三个实际舍入构造及 phaseIndex 构造的 StrictMono 与合法性则均是证明输出。弱相位 0 是极限点，任何实际项仍有 delta>0。一般 c 的整数高度未被假设。私有统一引理中的 w、误差或稳定命题没有泄漏为公共前提。

18 个公开透明定义及 23 个完整公开定理头与 v2 逐字一致（定理仅移除证明右端后比较）。实际 checked environment 的 41 个显式公开对象均存在，23 个类型闭合、18 个定义透明值与冻结对象相符；实际类型和值记录于 actual-public-interface.md/json。原始 Expr 只留服务器，正文的显式源声明保留整数／实数转换目标，不以漂亮打印中可能省略的转换类型代替原签名。没有自由相位函数、概率尾函数或未证误差替代实际对象。

## 原生检查、所有权与公理

原生 Lean 为 4.36.0-rc1、commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`。独立私有 -R 根中，最终 Source 的全部连续字节位于 `[0,56619)`；前缀为空，仅附加 7553B 审计后缀，不 import 自身。展开文件 64172B，SHA256 `e0db8df64b1f487ffe704a5ff0e609fb864611fd1156018b3a62ec95b0358955`。实际 main module 为 `Shao.OQ4.RademacherCriticalPhase`。

实际命令使用原生二进制、CPU18–21、`-M8192 -j4 -DautoImplicit=false` 和自己的私有 -R 路径；没有 -o、ulimit-v、RLIMIT_AS 或信任覆盖。首次完整 PASS 的 r02 为 exit 0，11.1880357396 秒。完整命令、前后缀／展开文件哈希、时间、实际路径和日志位置见 check-receipt.json。默认实际 header trustLevel=1025，debug.skipKernelTC=false；导入的已编译 Lean/Mathlib 是本次信任边界，没有声称重新构建或审计整个缓存。

全部实际对象由 module-index ownership 枚举，再与 SMap 导入阶段→源码结束的差集合、stage2 本地表以及审计前后集合交叉核验；没有按公开名单或 namespace 筛选所属对象：

- 导入阶段常量 363102；源码结束和审计结束均为 363295；三种方式所得所属集合完全相同，均为 193 项，后缀未留存额外对象。
- 实际 22 个定义 = 18 公开定义 + 4 私有定义；22 项透明值均实际取得。四个私有定义是 TailResult 与上／下／内部稳定胞元包装，不替换冻结对象。
- 实际 171 个定理；源文本有 23 个显式公开头、83 个私有定理，另有 65 个生成常量。193 项中有 129 项不以公开 namespace 前缀起始，全部纳入审计。
- 每项 kind、unsafe、partial、axiom-kind 及传递公理已记录于 owned-axioms.json。unsafe=0、partial=0、axiom-kind=0；全部 193 项的传递公理并集恰为 `propext`、`Classical.choice`、`Quot.sound`，无白名单外项。未将公共 18 当作实际全部定义数。

r01 的真实失败已保留：exit 1、6.3276504967 秒，源码段无错误，后缀 1181／1185 行因 Lean.Options.setNat 不存在而报错。仅去掉可选打印选项包装后运行 r02，Source 字节始终相同；失败收据、展开文件和完整日志保留于服务器 attempt-r01-suffix-print-option-failure/。首次完整 PASS 后没有重跑成功门，重任务已释放。

## 依赖与保护边界

稳定基线为 `feat/oq4-critical-phase@81fc3d026bcc5480dc23ad20c7cea47b726fef52`；只读 Git 元数据确认身份，没有运行 Git 命令。检查前及后，旧 OQ4 源码 48、受保护源码／配置 92、HEAD 绑定 140、旧构建产物 105 全部逐项哈希匹配；版本 pin、共享缓存与规范目标均未改动。规范目标源码／olean 仍缺席，独立私有目录也未生成 olean／ilean／二进制产物。

实际环境完整枚举 3728 个导入模块，项目模块依赖数实测为 0，非缺失冒充空表。头部有 16 项实际 import 记录（14 项显式 Mathlib／Lean 导入及两项 Init）；这 16 项的实际 resolved Source+olean 路径和 SHA256 均已绑定。实际 Mathlib revision 为钉死的 `807d3836b165983210ee2ecf3cd28f239436949c`；实际搜索路径与原生版本见 actual-dependencies.json。没有借用 DA2 的项目依赖数量，也没有扩大到整个缓存哈希或环境注册框架。

交付的 owned、公理与接口数据是本轮实际环境记录。完整日志、完整 imported module roster、raw Expr（1132989B）及任何运行中二进制只留服务器，没有下载到本地。raw 原始义务叶增量仍为 0；23 个组合公开头及其辅助投影不作 23 个新原始义务计数。
