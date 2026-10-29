# Unit277 完整实现候选：作者语义与来源报告

状态：**IMPLEMENTATION_CANDIDATE / NOT_INDEPENDENTLY_REVIEWED / NOT_KERNEL_CHECKED / NOT_QUALIFIED**。本件记录同一授权作者对五个冻结声明的完整证明实现及作者自查；不充当独立审阅或机器接受证据。

## 实际交付与精确边界

父级 implementation-ACTIVATION.json（b6810e71fa00cd8cc9834356611a8b3c59a5cfee34be2a13181358492aca246d，9245B）明确重激活同一 /root/oq56_unit277_author。31 个绑定输入在首次写入前全部匹配。声明以 frozen-declarations.json（d6b52da0608637aa14822bcf85258751726f083ce9b7d83cc8ee91775c691a83，4238B）为唯一冻结依据；HEAD/PRE/CLOSE 无数学或空白改写。

完整源码为 FiniteExceptionalBlockOptimization.lean。它严格由 PRE + HEAD01 + PROOF01 + … + HEAD05 + PROOF05 + CLOSE 拼接，无额外分隔字节。另交付五份分别以“:= by + LF”起始的 PROOF、ALL-HEADS/ALL-PROOFS、DECLARATION-ASSEMBLY 与 SOURCE-PROOF-MAP。实际行区间、字节数与 SHA256 以这些机器派生映射为准，不能当作实际内核 owner/TYPE/AX 计数。

唯一写目录 author-01。旧 proposal、冻结区、library、共享区和 C:/game/shao 原来源保持不变。未读 unit276 正文，也未依赖其结果。父级掌管服务器连接及未来唯一检查；本轮没有网络、SSH、工具链探测、Lean、AX、编译、前缀检查、上传或发布。没有子任务、资源选项变化、Goal、自动化或侧栏会话。

## H01：centered_energy_partition

声明的对象为 n>0、任意实向量 b:Fin n→ℝ、非空背景 B。A 是真实补集，M/K 是背景/异常基数的实数转换。μB、μA 按各块总和除以各块基数定义；空 A 的 μA 使用实数除法总定义为0。

证明先用 univ 的 membership filter 与其否定 filter 作真实集合分割。对任意有限实函数 f，建立
    ∑B f + ∑A f = ∑all f.
把 f 取1得到 M+K=n；把 f 取 b 或 b²得到后续总和关系。这不是额外前提。

局部 hweighted 对任意有限 s 建立
    card(s)·[(∑s b)/card(s)] = ∑s b.
其先分 s=∅ 与 s≠∅：空集由空和/除零的定义化简，非空集才证明 card(s)≠0 并消去分母。特别地，未在 A 为空时约去 K。

将全体均值写为 (MμB+KμA)/n。局部 hsquare 是逐点 sub_sq 后有限和的准确展开。三个平方和全部展开后，改写块总和与实基数关系，最后只对非零 M+K=n 清分母并作环代数。结果准确为
    Q = Qb + QA + MK/n·(μA−μB)².
QA 是异常块内部真实平方和，没有丢掉该项。该定理不要求 b 均值为零、任何符号条件或异常块非空。它是后续 Q>0 的实际来源。

## H02：positive_part_block_cauchy

全部量词是实数 N,M,K,q,a,y；仅假设 N>0、M>0、K≥0、q>0。它不假设 N=M+K，不要求 y≥0 或 a≥0。

设 ap=max(a,0)。由 a≤ap 和 N>0，X=Na+Ky≤Z=Nap+Ky。若 Z≥0，用 max 的序性质与非负平方单调性得到 max(X,0)²≤Z²；若 Z<0，则 X<0，原正部为0。此处没有把负分子直接平方后错误地声称同一上界。

实现的精确配方为
    N[N ap²/q+K/M][q+KM/N·y²] − (Nap+Ky)²
      = NK/(Mq)·(q−M ap y)² ≥0.
清分母只使用正的 N/M/q，从不除以 K。右端非负后与上一正部界传递。K=0、a=0、a<0 均沿相同证明闭合；没有增加隐藏排除条件。

## H03：finite_exceptional_block_optimization

声明保持 n≥2、B 非空、任意 c 与实际 Qb>0。q 不是任意自由参数：它是该 B 上实际 b 的去背景均值平方和。Q 是已有 P35.center 对全体 b 的真实平方和。T 使用冻结的 Q=0=>0 约定。

证明中 N/M/K 仍是实际基数转换；通过 H01 获得
    Q=Qb+QA+KM/N·y²,
其中 y=μA−μB。所有附加局部量均为定义，没有增加公开假设。由 QA≥0 与 KM/N·y²≥0，先证明 Q≥Qb>0，再消去 T 的零分支。没有先假设结论所需的 Q 或 s 正性。

定义 a=μB−c、X=∑b−Nc。真实集合分割与各块均值给 X=Na+Ky。H02 得
    max(X,0)² ≤ N C D,
    C=N(max(a,0))²/Qb+K/M,
    D=Qb+KM/N·y²≤Q.
C≥0，故可以把 D 增至 Q。接着严格按 X≤0 与 X>0 分支：前者 T≤0，正部为0；后者 T≥0，使用
    T²=((N−1)/N)X²/Q.
n≥2 保证 N−1>0，sqrt 的平方消去以及除以 Q 都在其非负/正性证明之后执行。所得右端正是 (N−1)C，未改 n−1、n、k/m 或正部。

边界：
- k=0 时内部 hweighted 的空集分支仍有效；H02 没有 K 分母，额外 k/m 为0。
- a≤0 时不删正部，也不假设背景偏移为正。
- Qb=0 明确不在此公开定理的前提范围内，与来源一致。
- 使用 card(univ\B) 而非 Nat n−m；后者的基数关系由分割推出，避免自然数截断减法的语义混淆。
- 任意 c、任意 b；无均值为零、分布、非负性、独立性或概率误差假设。

## H04：original_statistic_eq_offset_form

本私有桥保持任意 Ω:Type u、任意 g/r/x、点态对称 r、n≥4。没有可测空间或概率接口。

b_i 按原 P51.residualU 精确为 g_i+ψ_i/(n−2)，F 是原 originalUpper 的 i<j 去对角残差和，c=F/[(n−1)(n−2)]。通过已接受 residualU_eq_erased_row 与 offDiagonalSum_eq_two_unordered，建立
    ∑ψ=2F,
    ∑b=∑g+2F/(n−2),
    W+D=(∑b−nc)/√n.
这里原 ψ/(n−2)、D=F/[√n(n−1)] 系数完整保留；不修改原 F 的 unordered-pair 计数。

已接受 centeredSq_eq_center_sum 给
    centeredSq=Q/(n−1),
    s=√Q/√(n−1).
Q 是真实中心化平方和，因此 Q≥0。实现显式分 Q=0 与 Q≠0：
- Q=0 时上式推出 s=0，两边的零分母分支均取0；未要求分子也为0。
- Q≠0 时由 Q≥0 推出 Q>0，再得 s>0、各 sqrt 分母正；合法化简后得到冻结的偏移形式。
因此这是全样本恒等式，不只在一个好事件或正能量事件上成立。

按照原 FiniteRows.jackknifeSq 与 P51.centeredSq 的定义，s=√(R_h²/4)，而已接受有限行身份使 R_h²=4Q/(n−1)。故原 R_h=2s=2‖Pb‖/√(n−1)。实现消费相同 centeredSq，没有替换成未中心化行平方或其他 Studentizer。

## H05：original_finite_exceptional_block_optimization

使用的实际 b、F、c、s、T 与 H04 完全相同。card B≥3 明确推出 B.Nonempty；n≥4 推出 H03 所需 n≥2。把实际 Qb>0 送入 H03，得到 Q>0 与抽象优化界。H04 将同一 T 等同于抽象 Tf；已有 centeredSq 恒等式和 Q>0 推出 s>0。

公开结论恰为
    0<s,
    (T⁺)²≤(n−1){n[(μB−F/((n−1)(n−2)))⁺]²/Qb+k/m}.
没有假设该界、CDF、补集相对支付或尾概率结论。没有使用原模型中 g 与 r 可独立改变的前提；H03 是确定性全向量松弛，H05 只代入同一实际向量与同一 F。

实际 wrapper 仍明确限于 n≥4/card B≥3；本次不宣称实际 n=3 端点。p41 的充分大 n 目标未来可以消费该范围，但本单元不因此宣布原始 PE-R 或任何 μ 全尾成立。

## 完整来源忠实性表（MFT）

| 来源锚点 | 冻结对象与实现对应 | 保留范围 |
|---|---|---|
| p41:65–70 | B、A、m/k、μB、Qb、a0；H01/H03/H05 | 补集基数真实，a0 使用同一原 F 与 n−2 |
| p41:73–80，式(3) | H03/H05 的正部优化；H01 能量恒等式、H02 配方 | 系数 n−1、n、k/m；Qb>0；k0/a非正均处理 |
| p41:82 | H03 全有限向量松弛、H05 同一模型代入 | 不假设 g/r 独立，不把虚拟优化当作总体中可自由实现的配置 |
| p51:18–29 | H04/H05 原 ψ、F、W、D、s、T；调用既有行身份 | n≥4；原 centered-row；s=0=>T=0，零分支未被省略 |
| p41:84–120，式(4)–(5) | 不在本源码；保留于既有 proposal 的下一接口 | 未实现背景 numerator/denominator 比较或重标号 |
| p41:25–40、189–344 | 不在本源码；本单元无 α/p/截断/相对支付量词 | 不以任意 α>0 或条件276声称原无条件 PE-R |

源 p41/p51 的输入状态仍是原始候选文稿；其完整概率论证没有由于本有限代数实现而自动取得资格。本次精确来源范围只是 p41 式(3)及原统计量身份的有限实现。完整 μ 尾、NR/PE/DC/OQ56/root、原包络概率提升、异常块条件交互集中与带指数权积分仍未由本单元闭合。

## 静态查验、未运行事项和剩余风险

源码复用已接受有限行供应者，作者只为接口与惯用写法定向查阅其只读文本；没有对既有 proof 作第二次独立资格审查，也没有重放旧 native/AX。实际采用的额外 API 只是有限 filter 分割、有限和分配、平方单调性、实数清分母/环代数、sqrt_div/sq_sqrt 与有序除法。没有新增未冻结顶层声明、定义、axiom、unsafe 路径或默认预算改动。

STATIC-CHECKS 将检查全部31绑定、完整精确拼接、每个冻结 HEAD 的源字节、PROOF起止/映射、UTF-8无BOM/LF/单一末尾LF、顶层声明清单和禁用 token/资源选项。它不是 Lean parser、类型检查、证明成功或 transitive AX 证书。所有源码仍待独立完整 SOURCE/proof 审阅与父级服务器原工具链整体检查；实际 API 实例化、tactic 执行和默认资源预算能否通过尚无机器证据。

没有新增证据证明服务器连接问题已解决，作者也没有连接尝试。未来如实际检查失败，应保留失败收据、精确定位受影响证明并在相同冻结声明内修复，不能静默更改声明或扩大资源。现有原证据不得被当成本源通过。

配置要求为 SAME gpt-6.1-sol/xhigh；实际 backend/model/effort 与 input/cachedInput/output/reasoningSubset 用量未向本角色暴露，全部记 null。

本轮最终 MANIFEST 与唯一 LASTFINALWRITE 将绑定完整源及其所有组件，并释放本次新授予的全部作者/写入/执行/子任务/等待权限。父级冻结与服务器权不会由本记录代为释放；没有 active wait 或后台持续机制。
