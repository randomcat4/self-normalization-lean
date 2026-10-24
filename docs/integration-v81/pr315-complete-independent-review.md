# SourceOriginalZeroWallBudget 独立完整最终审查

STATUS: CORRECT

审查者 `/root/original_zero_wall_budget_final_review` 是新的非作者上下文，未参与候选、冻结或生产证明；使用 math-theorem，未使用 math-ultra，未启子上下文。结论针对 PR315 的精确源版本，Root 资格与合入决定仍由 Root 作出。

## 精确对象与完整覆盖

PR：<https://github.com/randomcat4/shao-lean/pull/315>。head `6e88a5728cc7016a9d6fc09d9d4e645e55f2aa98`，tree `5a15dd3bee26fafdebefb6a812cd1b514cc4a46e`，parent `fa040f83826bcf53fc69dd079ddb97c847a64366`。唯一 changed file 是 `Shao/Probability/SourceOriginalZeroWallBudget.lean`，工作树干净。225 行、11159 字节的完整源 SHA256 为 `95d1c6c2cfa41e2101833c3bec01b81c2d1df061831c8d2046fc023da8208d0d`，UTF-8/LF，无禁止证明占位或绕核构造。

完整读过候选声明47行、数学证明182行、范围117行，以及新源每条证明的全部分支、所有7个 statement let 的值和3个 proof-local let 的值。第一头18–43行，完整证明43–198行；第二头200–203行，完整证明203–223行。全部5个实际所属完整 TYPE 均直接完整阅读，未用摘要替代；导出总 SHA256 `ce301d4e24226b245521596c66baba7f1ad148a18386d641dd68c5cd3b1064c3`，并逐块核为原审计日志中未省略 TYPE 的无损提取。生产源给出的完整 tactic 证明已读；按项目规则不打印巨大 theorem proof-term value。

28个 RELEASE 绑定文件逐项匹配，加 RELEASE 本身共29个不可变生产工件。候选 source-inputs 中14项原只读输入全部精确匹配；连同冻结、激活、候选与旧资格引用，本次本地验证51项绑定引用（含重复引用，并非51个不同文件）。远端原成功证据13项与失败证据15项共28项均逐项匹配。紧凑只读回执为 `drafts/c12-original-zero-wall-budget-final-review/readonly-evidence.json`；最终审查工件不保留完整日志或二进制。

## 声明冻结、原文与依赖

两条实际公共头分别以字面文本独立比较，均与冻结一致；头哈希分别为 `242c9781b337e31caddbada670dc8157d2d83684ef20652e11e908b0d17ba52e`、`e679decc3ca0cdac79447f90857eb8250e1a8348cf74268a8b0f3529f06f30ff`。冻结整体 `bf28cd10acfc5b36e45030451da129063e275c5df476320087d77c7574300abe`，说明 `d946685832c4dfc572389593c8b1d98727d2caef1550e684b082a3d3b9e1d6d4`，激活 `fe1edf1ef5effe45fa6301fc71e20686968fb4b02bc45cc920996a1e5bcd516a`。Root 冻结/激活记录在16:25:51 UTC，作者实际ACK在16:26:57；现存形式证明体及原source01快照均在其后。无新增全局私有 helper、definition 或 instance，未变更数学前提。

完整核对原 main.tex149–179、341–355、395–401、1143–1149，supplement.tex3957–4008，并读到相邻公式/句子的结束以排除断句误解。原 iid、有限正二阶矩、真实平方和、真实归一化律与 R_n(0)、排除空前缀的 M⁺/M⁻ 均保留。main1143的绝对最大值语境没有移用于单侧最大值。本结果给出 main395–398 所需零端点误差，但没有声称完成相邻区间、标量CDF或反射根定理。

直接复用两份已合格旧证明的完整独立审查与原服务器证据，不重审其旧证明：PR303 源 `4b653cba9a9f427cd1086a153e702d7d09f684814919f0a46cfff17da335d190`，原对象 `6b28b4f93b43ac3077989dacf8f52677557db9cae07033def1103a5dc306c2bd`；PR299 源 `9e4380fc2e70a64b6ff7661f5f34cde9c18c1e5537e24b4165faeb46c74aee45`，原对象 `2dbf2e7971700bc33e8fbc80c5146c7ad8ef6c9a5ee2da13dc2f7d082f3d90e5`。两者当前服务器安装源/对象仍精确相同。

完整读了实际消费公共头及定义值：Path、prefixSum、energy、upperMax、maxWithZero、lowerMax、absMax、samplePath、truncationF、truncationBudget、standardNormalDensity/Tail；并核对所消费的 maxWithZero_eq、零能量/非负/标量乘路径、坐标界、可测接口、正态尾全头，以及 Mathlib 的 AE joint-map、IdentDistrib 和有限实测度补集接口。没有以仅支持处处可测的 iid 包装代替 AE 接口。

## 第一头证明与边界

1. C 从已合格 `finite_second_one_sided_compact_budget` 取出，先于 Ω、μ、ρ、n、X、s。`scale = sqrt(n sigmaSq) = sqrt(sigmaSq) * sqrt n` 是原二阶矩预算的精确除数匹配。所有产品事件仍使用真实 energy，而非方差墙或样本替代预算。
2. 固定 `E={energy>0 ∧ upperMax(s•a)≤0}`。对每个正 eps≤1，含空前缀 host 是 `max(0,upperMax)`；E 上它等于0，而 eps·sqrt(energy)>0。因此 E 包含于 host 弱交叉的精确严格补事件。对可测产品空间事件取概率补集，得到 `P(E)≤1−2Psi(eps)+CR`。原最大值=0且能量>0的原子完整保留。
3. 以 eps_j=1/(j+1) 应用同一个固定 E 的上界。实际正态尾在0可导故连续，且 Psi(0)=1/2；实数极限给 `P(E)≤CR`。未交换原路径归一化极限，未假设原律连续、无原子或路径能量几乎处处正。
4. `AEMeasurable.of_eval` 与 `iIndepFun.map_fun_eq_pi_map hX`、每坐标 IdentDistrib 给真实 `map population mu = pi rho`。IdentDistrib 的 `measure_mem_eq` 只要求目标路径事件可测，使用 AE map_apply；因此在产品空间先取补集，再传回原事件，不引入源空间完备性或处处可测前提。
5. energy=0 时原路径逐坐标为0，任何 s 标量作用后 upperMax=0。故严格负生存自动属于 E，不支付 Q0；闭生存被 E 与零能量事件之并覆盖，原 PR299 的 `P(Q=0)≤16R` 给 `(C+16)R`。此16R由同一 mu/rho/n/X 原预算直接消费，未作为新前提。
6. 原弱交叉的补集恰为严格负生存，原严格正交叉的补集恰为闭生存。两个绝对误差分别等于对应补事件概率，完整证明了最后两项。

n=1、大R及所有墙等号照常覆盖；n=0由 hn 明确排除。原单侧弱零墙交叉没有被断言恒真：n=1中心 Rademacher、s=1时概率1/2正说明该区别。Q=0 精确落在 M_s=0；没有删去该原子。没有增加高矩、对称性、密度、无原子或目标预算前提。

## 第二头证明

对任意 n>0 的确定路径，`absMax≤0` 配合已合格 h=0 坐标界给每个 `|a_i|≤0`，故每坐标为0、energy=0。反向由零能量的 absMax=0 得到。再用两个实际统计量非负，将等于0的等价转成严格正的等价。全部方向均成立，无概率、独立性或矩前提。它识别的是绝对最大值零事件；不混淆单侧最大值。

## 全部实际所属声明与递归公理

原审计按 `env.getModuleIdxFor?` 精确选择 target module，不做 namespace 筛选；对每个 owner 调用递归 `Lean.collectAxioms` 并对白名单外公理直接报错。原实际 inventory 是5 theorem=2公共+3生成、0 source-private、0 actual non-theorem；0 VALUE 是由实际 ConstantInfo 全清单确认，非由源码无 def 推断。三个生成定理分别是补集成员、not_le、not_lt 的逻辑重写，相关完整 source simp 分支均已读。

所有 owner 均为 `Shao.Probability.SourceOriginalZeroWallBudget`，kind 均 theorem。下表 fullTypeHash 对原 `ACTUAL_TYPE` 与 `END_ACTUAL_TYPE` 之间的完整 UTF-8 字节计算，不含标签和末尾换行。

| 实际名（上述命名空间内） | fullTypeHash | source proof 覆盖 | 递归 AX |
|---|---|---|---|
| original_absolute_zero_wall_identity | 4112e81d8bf9c34d7f861b5077d9d77e7441a350ef2610106d1a7eb6d2a98e0c | 203–223 全部方向 | propext, Classical.choice, Quot.sound |
| original_iid_one_sided_zero_wall_budget | f9aea2746e3eaaaeb8166459f1016bdac993c866c005b28b176567ee27151441 | 43–198 全证明/全部局部值 | propext, Classical.choice, Quot.sound |
| original_iid_one_sided_zero_wall_budget._simp_1 | 3802b8957e02d6acf6247cf339922b59ec21b90378107e1c467135d235f66cd7 | 105–107、166–168、175–177 补集 simp 分支及原对象 | propext |
| original_iid_one_sided_zero_wall_budget._simp_2 | d7a81e702843530468f48d9160c0f62a6ad0abff0780fe18e82b7a05fa11ccc7 | 105–107、175–177 not_le 分支及原对象 | propext |
| original_iid_one_sided_zero_wall_budget._simp_5 | b961c6905aec15c1dce27300babbc28bc1d7617452a4a7efc3ce9a007af4f91b | 166–168 not_lt 分支及原对象 | propext |

## 原服务器证据与范围裁决

复用唯一最终完整成功 check04：kernel rc0、同次原对象安装/导入的全owner TYPE/递归AX audit rc0。原 source04=当前服务器源=Git blob=本地已审源；原 producer04 SHA256 `bf5fa57f470bea03e1adf125a6d506cb8369981f13e06b48b8112209c322f191` 与当前 audit import 安装对象匹配。原 kernel 日志 SHA `0aff5e6b7eaa301e07491b8d6e157c2dd3e2be6a1f458e9ce24f2fe271256188`，原 audit 日志 SHA `6194a085dc280603d62de071d417c36213526c84f1b3998ced70c3f0ab005919`。原失败01–03的源、日志、rc1及审计输入均仍保留并匹配，未作成功替换。

固定 Lean4.36.0-rc1、mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 与 shared-v34 包视图得到只读确认。作者 final-receipt SHA `b3568d94d8e2ed1f8ab307038081c3607d8f20c401f3096d4c99f5cabd3a1cbe`、RELEASE SHA `398a56eaba1318cbf16aeafe53e668cab85f7e9340ef660f9750633778e09cdd` 匹配，作者0 inflight并释放写/执行权；本次也只读观察到目标 Lean/lake 进程为0。审查新增 Lean/kernel/AX/producer/check=0，旧 producer 重编=0，未合并。

未发现关键缺口。该边界消费正确，不主张新颖性，也不重认证原文已有外部归属。C1/C2、OQ3和OQ56原根仍 OPEN；OQ3保持用户暂停，OQ4仅有其已独立验收的原范围，实际 Brownian 反射仍归C12专线。

要求模型/努力为 gpt-6.1-sol/xhigh；工具不提供本上下文实际模型/努力或 input、cached input、output、reasoning subset 计数，结构化报告均记 null。没有用 token 数估算订阅百分比。审查完成后写权和只读执行权由本目录不可变 RELEASE.json 一并释放，0 inflight。
