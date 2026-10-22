# OQ4 原 S4：实际概率的弱格点位移装配冻结声明 v1

STATUS: FROZEN_DECLARATIONS_PENDING_SOURCE_REVIEW
TASK_MODE: DECLARATION_FREEZE
UNIT_KIND: DERIVED_ASSEMBLY
NEW_RAW_LEAF_INCREMENT: 0
SOURCE_RAW_DENOMINATOR_DELTA: 0
PROOF_STATUS: NONE
LEAN_STATUS: NONE
IMPLEMENTATION_AUTHORIZATION: NONE
ACTUAL_BROWNIAN_INTERFACE_OWNER: ROOT
ACTUAL_BROWNIAN_INTERFACE_STATUS: PENDING
ACTUAL_S3_S4_S5_SPECTRUM_OQ4_ROOT_STATUS: OPEN
FREEZE_OWNER: OQ4_LEAD
FREEZE_SCOPE: FULL_SECTIONS_3_TO_7
CANDIDATE_SHA256: 4440a31adeebfc90529fc2f914a113a6e359ca7c02fdf96f324677a224510ac6
SOURCE_REVIEW_STATUS: PENDING
MATHEMATICAL_REVIEW_STATUS: NONE

lead 全文读入原候选后采纳全部对象、量词、域、输出和尾桥；原候选保持不可变。本冻结只更新元数据、文档自称及下游文件指向，不增删数学前提或输出。原始目标→剩余承重义务→消除项→直接消费者按正文锁定；原 OQ4 根仍 OPEN。

本文件冻结完整待证声明，不给证明。不得增加、删除、弱化或重新解释对象、域、量词、尺度和输出；不得把固定上游结论、最终正性或趋零误差改成可自由实例化的假设。

## 1. 原始目标、剩余承重义务和直接消费者

原始目标是 spectrum01.md 第70–81行：在弱事件实际概率 p(n,h) 与同一真实 Brownian b_U(h/√n) 之间，把原 S3 的确定性表达式转为 π²nδ/(4h³)，再在次临界尺度得到实际倍率趋一。

当前剩余关键义务是实际 S3 与固定 DA1/DA2 的对象等式、同一表达式的装配、真实概率对数的最终合法性，以及仅最终处于弱胞元时的尾序列返回桥。本冻结声明消除的是这条实际概率连接；不再造 Taylor、位移或纯尺度模块。

直接消费者有两项：本文件第6节的实际次临界倍率；配套 frozen-rademacher-s5-probability-phase-v1.md 的固定 c 临界实际相位及完整倍率极限点。本 S4 的完整范围已由 lead 冻结；下游 S5 另行冻结并经过各自来源、数学和形式门，引用不是认证状态。

## 2. 锁定来源与固定依赖

唯一原谱来源 C:/game/shao/current/oq4/c01/spectrum01.md，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b，4306B，commit 35d4580b61e22e7145f47730045a09874ef93259。第11–12行固定弱胞元，第60、65–67行固定实际 S3 的尺度与确定性表达式，第70–77行固定 S4 三项尺度、δ 及误差阶，第80–81行给次临界消费者。

固定数学接口均位于 C:/game/shao lean/drafts/oq4/：

| 接口 | SHA256 / 字节 | 本冻结声明的消费范围 |
| --- | --- | --- |
| frozen-rademacher-s3-brownian-assembly-v1.md | 19f162418e88f7b3ddea57e1c735404f94fd3e50fbd471bfd937eaf93424a71c / 14243 | 第44–79行同一 p/K/a/rho；S3-DOM 142–153行；S3-ALG 155–179行；S3-MAIN 181–195行 |
| frozen-rademacher-lattice-shift-v1.md | 9cf9dba01aa9582ceb8e4d30af06c4778b8b367b61e61562dfc42c7ffb0e2b56 / 6067 | 第31–57行固定定义与合法性；DA1 59–81行的同一个全域绝对常数界 |
| frozen-rademacher-scale-assembly-v1.md | 9e7f840f25038e4ef55ba561eaca112802a6b373849722898f6d6a550ca9e946 / 5248 | 全 k 弱胞元，原三项尺度及 DA2.0–DA2.4；尤其 DA2.1 和 DA2.3/4 |
| frozen-rademacher-s2-assembly-v1.md | c59971859b432bf312d5c1d65ca82d0a02254c06d4d56833322364f87f69146e / 8318 | 只经 actualS3 承接 F0/Q1 的真实对象及输出；不另重计 S2/U1 |

上游只能接其实际认证声明，不在最终目标中重新假设任意谱和、任意 F、任意误差、自由 Brownian 尾等价或自由 DA1/DA2。冻结文本中的状态转述不构成证明。

原 C:/game/shao/current/oq4/frozen01.md，SHA256 ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a，1491B，第3、9行是同一实际 U 及首项等价的原输入。actual B/U/P_B 的公开类型、透明定义、可测版本/事件概率桥和实际首项 tail 仍归 root 且 pending；本冻结声明不选择实现或替代对象。原 spectrum 第61行的更强相对指数 O 率不使用。

## 3. 固定实际对象与有限参数

ν_R:=Shao.OQ4.RademacherCosine.law=(1/2:ℝ≥0∞)•Measure.dirac(1:ℝ)+(1/2:ℝ≥0∞)•Measure.dirac(−1:ℝ)，使用其实际 law_isProbabilityMeasure。对全部 n:ℕ、h:ℝ，固定

Path n:=Fin n→ℝ，
p(n,h):=(Measure.pi(fun _:Fin n=>ν_R)).real(@Shao.closedStrip n h)，
K(n,h):=@Shao.OQ4.killedMass ν_R law_isProbabilityMeasure h n 0。

closedStrip 是从0出发的真实产品路径弱事件：全部 k≤n 的前缀和绝对值≤h。p 不能按谱表达式重定义，K 不能换新杀死过程。对同一原 Brownian 基准，

U=sup_{0≤t≤1}|B_t|，b_U(x):=P_B(U≤x)。

不增加 Rademacher/Brownian 的耦合或独立性前提。

对 m:ℕ、1≤m，按 actualS3 的实际对象固定

H(m):=(m:ℝ)+1，
u(m):=π/(4H(m))，
a(m):=Pair.amplitude m=(1/H(m))*cos(u(m))/sin(u(m))=Scalar.a m，
rho(m):=Pair.rho m=cos(π/(2H(m)))=Scalar.rho m，
λ:=π²/8。

这些等式须实际对接为定义相容输出，不能加成可自由满足的等值前提。对 (m:ℝ)≤h<H(m)，令 δ(m,h):=H(m)−h。固定弱域结论 h≥1、0<δ≤1；h=m 时 δ=1。胞元上端排除，δ 非独立参数；不换成 strict 事件的整数 δ=0。

## 4. S4-ALL：全 k 弱胞元的核心声明

量化任意 m_,n_:ℕ→ℕ 和 h_:ℕ→ℝ，要求每个 k:ℕ 均

1≤m_k，(m_k:ℝ)≤h_k<(m_k:ℝ)+1。

令 N_k:=(n_k:ℝ)，H_k:=H(m_k)，δ_k:=H_k−h_k。唯一尺度前提为

h_k→+∞，
N_k/h_k²→+∞，
∃ M:ℝ, 0<M ∧ ∃ K_M:ℕ, ∀ k≥K_M, N_k/h_k³≤M。

实数趋+∞指对每个实阈值最终超过该阈值；趋零指对每个 ε>0 最终绝对值<ε。M 固定，不能随 k 改变。不得加全部 n_k>0、单调性、奇偶匹配、N_k/h_k⁴→0 或任何待证输出。早期 n_k=0 保留。

以下全部在结论侧：

S4-DOM：H_k→+∞、N_k/H_k²→+∞；存在 K_time，使 k≥K_time 时 n_k≥1、N_k>0、√N_k>0、H_k²≤N_k。原三项尺度同时给出 N_k/h_k⁴→0、H_k⁻²→0。全 k 的弱整数端点和小 m 仍由固定域保留。

在正时间尾段定义普通数学量 x_k:=h_k/Real.sqrt(N_k)。须输出 x_k>0 且从正侧趋0。存在 K_pos≥K_time，使所有 k≥K_pos 有

p_k:=p(n_k,h_k)=K_k:=K(n_k,h_k)>0，
b_k:=b_U(x_k)>0，
Q_k:=p_k/b_k=K_k/b_k>0。

这些是 actualS3 的实际输出消费，不作自由正性前提。若形式上以实数除法及 Real.log 写全 k 总项，必须另交付该项与上述普通正性尾段公式的最终相等；不从 Real.log(0) 或除零形式值取得概率解释。

S4-MAIN：在同一尾段真实概率对数下，

Real.log(p(n_k,h_k)/b_U(h_k/Real.sqrt(N_k)))
  −(π²/4)*(N_k/h_k³)*δ_k →0。

换用 K(n_k,h_k) 是同一个实际概率结论，须由 p_k=K_k 给出精确相等，不另定义一个极限过程。准确量词为：对每个 ε>0，存在 K_ε≥K_pos，使全部 k≥K_ε 显示对数各自合法且其差的绝对值<ε。

## 5. S4-ERR：保留原 O+o 的唯一绑定方式

定义固定、可复核的确定性中心项

Cdet_k:=λ*N_k/h_k²+N_k*Real.log(rho(m_k))+Real.log(π*a(m_k)/4)，
w_k:=(π²/4)*(N_k/h_k³)*δ_k。

η3_k 不是任意趋零函数，而是 actualS3 的同一个实际表达式：

η3_k:=Real.log(p_k/b_U(x_k))−Cdet_k。

同一合法尾段须实际给出

η3_k=Real.log(D_k)−Real.log(T_U(x_k))→0，

其中 D_k:=p_k/(a(m_k)*rho(m_k)^n_k)，
g(x):=(4/π)*exp(−λ/x²)，T_U(x):=b_U(x)/g(x)。

D、T_U 均为 actualS3 原定义，不另选自由函数。D_k、T_U(x_k)>0 也须来自同一实际正性输出。

存在 C_DA>0，在任何 m、h、n 或三序列之前选定，满足固定 DA1 的全部有限域界；本冻结声明必须采用该同一 DA1 见证，不重新给每序列选择常数。对第4节所有序列，同一尾段有精确拆分和界：

Real.log(p_k/b_U(x_k))−w_k=(Cdet_k−w_k)+η3_k，

| (Real.log(p_k/b_U(x_k))−w_k)−η3_k |
  ≤C_DA*(N_k/h_k⁴+1/H_k²)。

对 K 使用同一等式和常数。这里保留的 O 系数正是固定 DA1 的绝对常数；o(1) 正是显示定义的 actualS3 η3。没有任意新增 vanishing e、自由 O 界或 Brownian 强速率前提。

这是原第77行 O(N/h⁴+H⁻²)+o(1) 的派生消费形式，不增加原始叶或独立贡献计数。它并不提供 η3 的收敛速率，也不宣称在所有序列上有统一的尾部门槛。

## 6. S4-SUB：实际次临界直接消费者

在第4节同一对象、弱胞元及两项发散尺度下，若进一步有 N_k/h_k³→0，则须交付

Real.log(p_k/b_U(x_k))→0，
p_k/b_U(x_k)→1，
K_k/b_U(x_k)→1，

并保留第4节的实际最终正性。第三项有界尺度可由次临界趋零实际导出，不要求另给一个 M，也不把它偷偷删除于 S4-ALL 的固定前提中。

这是逐个任意给定序列的实际相对概率结论。原第81行“取整误差统一消失”在本冻结声明仅兑现为全弱相位的 DA1 同一常数和任意序列次临界结论，不借此宣称 x 上的 supremum 收敛或一般分布 OQ4。

## 7. S4-EVENTUAL：最终弱胞元的完整尾桥

另量化任意 m_,n_:ℕ→ℕ、h_:ℕ→ℝ，不要求早期项合法，只要求

∃ K_cell:ℕ, ∀ k≥K_cell,
  1≤m_k ∧ (m_k:ℝ)≤h_k ∧ h_k<(m_k:ℝ)+1，

并保留第4节原三项尺度。p(n_k,h_k)、K(n_k,h_k) 始终按第3节实际定义；不得为了使用上游把原 h 或概率换成其他阈值/事件。

本冻结声明必须交付以下完整待证桥，而非直接把上游前提改成“最终”：

- 对任意固定 K_0≥K_cell，定义 tilde m_j=m_(j+K_0)、tilde n_j=n_(j+K_0)、tilde h_j=h_(j+K_0)。这三条尾序列对全部 j 满足原 fixed actualS3/DA2 的全 j 弱胞元条件。
- 原三项尺度沿同一移位保持；M 仍为固定界，阈值可调整。固定 DA1 的全域绝对 C_DA 不变。
- 同一实际函数逐项满足 tilde p_j=p(n_(j+K_0),h_(j+K_0))、tilde K_j=K(n_(j+K_0),h_(j+K_0))；在正时间尾段 tilde x_j=x_(j+K_0)、tilde b_j=b_U(x_(j+K_0))，并且 H、δ、Cdet、D、T_U、η3、w 全部是同一索引移位。
- 由移位的结论返回原序列，交付 S4-DOM、S4-MAIN、S4-ERR 的相同最终结论；在次临界时也交付 S4-SUB。准确地，对每个 ε>0 存在原索引自然阈值，其后全部真实概率量合法且满足相同 ε 界；不声称非法有限前缀已经合法。

早期 n_k=0、m_k=0、h_k<1 或其他未入胞元项可存在，但均保持各自实际 p/K，不被替换成“合法前缀概率”。其形式全项仅作为极限记号，不用 b_U(0) 或 Real.log 的总函数值补合法性。本尾桥是明确辅助范围，原文未逐字表述；它的唯一用途是让 S5 的最终合法原时间序列忠实消费全 k 上游。这里只列待证输出，不给桥的证明。

## 8. 门、排除与未完成项

本冻结声明消除实际 S3→S4 及实际次临界倍率的装配义务；不重计 S3、DA1、DA2、Scalar、Pair/U1，也不新增原 S4/S5 粗义务总分母。任意自然时间序列、尾桥、最终正性和同常数 O+o 是透明标示的派生辅助范围。

形式接线仍等待实际 U1/S2、actualS3 和 root 的实际 B/U/事件概率/首项 tail 认证。DA1 的完整认证调度信息、DA2 数学状态、actualS3 独审状态都不能替代本冻结声明的来源门、独立数学门或形式门。本轮未读其证明/审查/实现，不给通过判定。

strict、其他 cosets、变化的 c、一般分布、均匀 x 窗口、强 Brownian 指数 O 率、完整 Spectrum/OQ4 根均不在本文件；S4/S5 关键链尚未关闭。lead 已采纳本文件第3–7节的完整范围；下一步另派独立来源声明审查。当前 proofNONE、LeanNONE，无实现授权。
