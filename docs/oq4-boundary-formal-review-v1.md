# 反向分块条件边界占据独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 明确 S/AC 输入下的真实核边界层质量

LEAN_STATUS: 独立服务器无-o目标检查及完整源动态审计均 exit 0，无警告

JUSTIFICATION: 最终源完整实现冻结的未条件化分块概率机制及三个安全常数。实际核行经 KilledPathLaw 绑定到全乘积 law，固定完整末块后首块端点处于长度1的移动闭区间；固定反序保测给正确的上下生存事件。可测性、截面测度、有限性和实概率转换均明确，全部 S/AC 输入保留。实际41个新增常量（包含共同名称下的 helper）全部通过传递公理白名单，禁用项为空。

## 对象与隔离

审查日期：2026-10-21。先只读取冻结声明和匿名数学推导，完成并保留 `boundary-occupation-math-review-v1.md` 的 MATH_ONLY/LEAN_NOT_RUN 范围，再读最终实现。未读取作者 receipt、作者会话或其他审稿票。只写所分配报告，未修改源、冻结声明、共同文件或缓存，未生成目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-boundary-occupation-v1.md` | `678ed57b8bfe84f8282ed5ee80292879c7ddd908c7304ddbc6816fbe58f319af` |
| 所审匿名 `drafts/oq4/boundary/proof.md` 快照 | `a3b3f492849b283e691e863d95d102fdd72ad8f725e60be555f458c381323e62` |
| 本机 `drafts/oq4/boundary/BoundaryOccupation.lean` 与远程 `Shao/OQ4/BoundaryOccupation.lean` | `1568e5514fc4ca8053ccd9b0f123f86e61cc294df0f6de199c8a688b9d7de8a6` |
| 已审直接依赖 `KilledPathLaw.lean`，本机/远程一致 | `1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f` |
| 已审直接依赖 `OccupationPayment.lean`，本机/远程一致 | `3ed77e585a0a687b471d46e004872d35c18d7181388a7828c34e83085bd094d9` |
| 共同 `Shao/Basic/FinitePath.lean`，本机 library/远程一致 | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 共同 `Shao/Basic/ClosedSurvival.lean`，本机 library/远程一致 | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同 `Shao/Probability/FiniteIID.lean`，本机 library/远程一致 | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同 `Shao/Probability/MeasurablePath.lean`，本机 library/远程一致 | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |

以下行号均为最终 `BoundaryOccupation.lean` 的一基行号。

## 完整接口与实际对象

第56行之后 ν 的唯一假设是实数 Borel 概率律；没有新增矩、均值、方差、密度、无原子、非格点或支持限制。`reverseBlock` 第13行仅反序坐标，不取负；`lowerBlockSurvival` 第15–16行是负路径进入共同 `closedUpper` 的事件，准确表示各前缀和≥-d。没有假设 ν 在取负下不变。

第一主结论第172–180行完整保留 l,r≥1、h≥0、|z|≤h、任意自然 j、q,sPlus,sMinus≥0。集中输入对**每个实 x**控制真实 Π_l 下首块最终和进入 Icc(x,x+1)；两种一侧输入分别控制真实 Π_r 下共同闭上事件与闭下事件。输出是实际 `(killedIterKernel ν h (l+r) z).real` 的既有 `boundaryLayer (h-|·|) j` 质量。没有换成抽象测度、条件归一化 law 或假设的层质量。

第二主结论第258–269行固定自然半分 l=m/2、r=m-l，明确 m≥6、β,Cq,Cs≥0，并完整写出 q=Cqβ/sqrt(l)、两种 s=Cs(j+1+β)/sqrt(r) 的真实概率输入。第三主结论第297–311行固定 m=floor(h²)、h≥3、0≤β≤M、M,Cq,Cs≥0，完整保留相应半分长度的三个 S/AC 输入。每个 j 都是明确参数，没有省略取得所有层所需的逐 j 输入。

独立服务器 `#check` 已展开三个完整签名，均与冻结声明一致。β 在本模块只是非负参数，不被偷偷认作已具备某种矩控制的随机量。

## 可测性、拼接与固定反序

- 第18–29行给固定反序可测性、共同闭上事件可测性及闭下事件可测性。闭上事件继续监测 k=0，闭下事件通过可测路径取负的原像定义。
- 第31–54行证明真正共同 prefixSum 的拼接公式，以及在 k≤r 下反序前缀等于末块总和减去前 r-k 项。自然减法始终在 k≤r 下使用，r=0 的辅助公式也无非法端点。
- 第58–65行通过标准有限乘积坐标置换保测定理证明反序保留 Π_r。固定置换是未条件化 law 上的恒等分布结论，不是生存后独立，也没有取负对称性假设。
- 第67–78行用有限指标和的可测保测等价将 Π_l×Π_r 经 `Fin.append` 推送为 Π_(l+r)，并逐坐标核对真正拼接函数。共同路径、前缀、闭事件均被复用；没有复制共同 iid 联合 law。
- 第80–90行定义移动闭区间事件，明确证明尾事件和两侧联合区间不等式的 Borel 性；首块前缀、完整尾块参数和区间起点函数均真正可测。

## 固定完整末块的截面概率

第93–124行的 `movingIntervalEvent_probability_le` 保留任意可测尾事件 T、任意可测实起点函数 x，以及对所有实 x 的首块集中输入。第99–114行固定**完整未条件化尾块 b**，两支分别证明：b∈T 时截面正好是首块终点落入 `[x(b),x(b)+1]`，否则截面为空。

第108–109行由概率 Π_l 的有限测度确保 `ofReal_toReal` 转换合法，再用真实集中界。第115–121行使用实际可测移动事件的 `Measure.prod_apply_symm`，即先积首块截面、再积完整尾块的非负积分；其上界由尾事件常数指示积分精确计算为 `ofReal(q) Π_r(T)`。

第122–124行明确证明该右侧 ENNReal 乘积有限，才使用 `ENNReal.toReal_mono`，最后由 q≥0 化回实概率。所有 Π 都是概率测度，原实测度和右侧都有限；这里使用非负测度积分，不需要依赖任何未证 Bochner 可积性或不可积默认0。相关指示测试在这些有限测度下也确实可积。

## 两层方向、端点和真实核行

第127–169行给逐点的核心集合包含。设总终点 w、较早位置 x，反序末块前缀=w-x。第142–144行调用全程生存于时刻 `l+(r-k)`；由 l≥1、k≤r 保证这是合法正时刻，故 x∈[-h,h]。没有省略靠近块边界的时刻。

- 第149–159行取 w≥0 分支，层条件精确是 `h-j-1<w≤h-j`。使用 x≤h 得反序前缀≥w-h>-(j+1)，所以是闭**下**生存，配 sMinus。首块终点区间起点为 `h-j-1-z-V`，终点为起点+1；只放宽严格下端点。
- 第160–169行取 w<0 分支，层条件为 `-h+j≤w<-h+j+1`。使用 x≥-h 得反序前缀≤w+h<j+1，所以是共同闭**上**生存，配 sPlus。区间起点为 `-h+j-z-V`，终点为起点+1；只放宽严格上端点。

代码把 w=0 分到第一支，不要求两个放宽事件互斥。第224–227行明确使用并集次可加界，允许它们重叠。整个证明没有将边界等号视为零概率；原子保持。

第185–194行证明反序事件、移动区间函数、半开层及完整生存/终点事件 V 均可测。第195–203行实际展开已审 `killedIterKernel_eq_path_law`、可测推送及限制测度，把真实 κ 层质量精确化为 Π_(l+r).real(V)；第204–208行再由真实拼接保测恒等式转为未条件化 Π_l×Π_r。

第209–218行用反序保测把两个尾事件概率分别界为 sMinus 和 sPlus。第219–233行先用逐点包含与并集次可加，再分别应用移动区间截面界和 q≥0，最后得到准确 `q(sPlus+sMinus)`。没有在限制生存后使用独立性，首块生存条件只被丢弃以扩大集合。

## 6/m 与 h² 块常数

第235–255行从 m≥6 的自然除法给 l,r≥1，分别证明 m/3≤l,r，再以非负性和平方根平方恒等式得 `m≤3 sqrt(l)sqrt(r)`。第270–281行确认 l+r=m、两个平方根及 m 的实数转换均严格正。第282–294行代入第一结论、精确合并两种 s，并在正分母上使用前述界，输出 `6 Cq Cs β(j+1+β)/m`。只除以正平方根及 m，不除 β、Cq、Cs，故其零值包含。

第312–320行从 h≥3 得 h²≥9；自然 floor 的严格上邻界给 m≥6 和 h²≤2m，且 m>0。第321–328行用 β≤M、β,M≥0 和 j≥0 证明 `β(j+1+β)≤M(1+M)(j+1)`。第329–340行保留全部真实输入调用第二结论，再乘非负系数和用正分母比较，恰得 `[12 Cq Cs M(1+M)/h²](j+1)`，没有漏掉2或(j+1)。

## 退化情形与任意层

三项结论均量化任意自然 j，没有 j≤h 的隐藏限制；j>h 时原层因 h-|w|≤h<j 为空，上界仍合法。若 h 是非负整数，j=h 层包含 w=0 的顶层点；代码直接使用半开层定义，并未排除此层。

第一接口允许 h=0，闭域起点为0，保留全零路径和零终点原子。上/下放宽事件在这里可重叠，次可加界仍成立。第二、第三接口的长度/半径下限保证其分母合法，β、Cq、Cs 或 M 的零值不被额外排除。

## 独立服务器证据

通过 `tools/server.py` 共享 broker，在指定 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4` 激活固定环境后，顺序运行两个单 Lean 过程，均限 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/BoundaryOccupation.lean
{ 最终完整源码 + #check/#print 与动态审计附录; } | lake env lean --stdin
```

两个过程均不带 `-o`，未生成目标 olean、构建/更新 Lake 或获取缓存。目标与源加附录均无警告；broker exit_code=0、stderr 为空，明确输出 `TARGET_AND_DYNAMIC_AUDIT_EXIT=0`。UTC 为 `2026-10-21T12:08:03Z`。远程最终源前后 SHA256 均为上表值，两个直接依赖及四项共同源码也与本机所读版本逐项一致。

动态遍历实际 `env.constants.toList` 中**全部** `env.getModuleIdxFor? declName = none` 的声明，没有 namespace/root 名称筛选。每项调用 `Lean.collectAxioms`，任何白名单 `{propext, Classical.choice, Quot.sound}` 外的传递公理立即报错。完整最终源码实际经 stdin 重新核验，枚举结果为：

```text
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 41
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
```

其中17个显式声明全部被枚举：

```text
Shao.OQ4.reverseBlock
Shao.OQ4.lowerBlockSurvival
Shao.OQ4.measurable_reverseBlock
Shao.OQ4.measurableSet_closedUpper
Shao.OQ4.measurableSet_lowerBlockSurvival
Shao.OQ4.prefixSum_append
Shao.OQ4.prefixSum_reverseBlock
Shao.OQ4.measurePreserving_reverseBlock
Shao.OQ4.measurePreserving_append
Shao.OQ4.movingIntervalEvent
Shao.OQ4.measurableSet_movingIntervalEvent
Shao.OQ4.movingIntervalEvent_probability_le
Shao.OQ4.surviving_layer_subset
Shao.OQ4.boundary_occupation_block_bound
Shao.OQ4.half_blocks_sqrt_bound
Shao.OQ4.boundary_occupation_half_bound
Shao.OQ4.boundary_occupation_hsq_bound
```

24个实际生成声明也全部审计，包含当前模块生成到共同名称下的 `Shao.closedUpper.eq_1`：

```text
Shao.closedUpper.eq_1
Shao.OQ4.reverseBlock.eq_1
Shao.OQ4.movingIntervalEvent.eq_1
Shao.OQ4.prefixSum_append._proof_1_1
Shao.OQ4.prefixSum_reverseBlock._proof_1_1
Shao.OQ4.surviving_layer_subset._proof_1_1
Shao.OQ4.surviving_layer_subset._proof_1_2
Shao.OQ4.boundary_occupation_block_bound._simp_1_1
Shao.OQ4.half_blocks_sqrt_bound._proof_1_1
Shao.OQ4.half_blocks_sqrt_bound._proof_1_2
Shao.OQ4.half_blocks_sqrt_bound._proof_1_3
Shao.OQ4.half_blocks_sqrt_bound._proof_1_4
Shao.OQ4.boundary_occupation_half_bound._proof_1_1
Shao.OQ4.boundary_occupation_half_bound._proof_1_2
Shao.OQ4.boundary_occupation_half_bound._proof_1_3
Shao.OQ4.boundary_occupation_half_bound._proof_1_4
Shao.OQ4.boundary_occupation_half_bound._simp_1_5
Shao.OQ4.boundary_occupation_half_bound._simp_1_6
Shao.OQ4.boundary_occupation_half_bound._simp_1_7
Shao.OQ4.boundary_occupation_half_bound._simp_1_8
Shao.OQ4.boundary_occupation_half_bound._simp_1_9
Shao.OQ4.boundary_occupation_half_bound._simp_1_10
Shao.OQ4.boundary_occupation_half_bound._simp_1_11
Shao.OQ4.boundary_occupation_hsq_bound._proof_1_1
```

41项的传递公理均为标准白名单子集；全部17项显式声明使用标准三项。三个主概率结论另经逐项 `#print axioms`，均只有标准三项。没有 sorryAx 或新增公理。

最终远程源禁用项正则 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 扫描输出：

```text
PROHIBITED_TOKEN_HITS []
```

## 认证边界

本票认证的是从**明确的真实 S/AC 概率输入**到真实核边界层质量的反向分块机制，及两个安全数值约化。要对所有层使用，须逐 j 供应相应 S/AC 输入，不能从本结论反向声称这些概率输入已证。β 可在后续实例化为第三绝对矩，但本模块没有证明其概率估计。

**S/AC 本身、无条件 O0、能量标记 O1/O2、实际 R3/R4、B1、Brownian 输入、长期结论、4/π、K/Kv、完整 OQ4 与其他全部根组保持 OPEN。**
