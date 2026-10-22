# OQ4 原 S4 尺度的确定性序列装配 v1

STATUS: FROZEN_STATEMENT
FREEZE_AUTHORITY: OQ4_LEAD
SCOPE: DA2_DETERMINISTIC_DERIVED_ASSEMBLY
NEW_RAW_LEAF_COUNT: 0
SOURCE_REVIEW_STATUS: PENDING
PROOF_STATUS: NOT_WRITTEN
LEAN_STATUS: NOT_RUN
IMPLEMENTATION_AUTHORIZATION: NONE
ACTUAL_S2_S3_S4_S5_BROWNIAN_SPECTRUM_OQ4_ROOT_STATUS: OPEN

## 1. 来源和本次采纳

唯一原始来源为 C:/game/shao/current/oq4/c01/spectrum01.md，commit 35d4580b61e22e7145f47730045a09874ef93259，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b，4306字节。原11–12行固定弱胞元及 H=m+1，70行给三项尺度，70–81行给位移、确定性余项及其消失。

原只读候选 frozen-rademacher-after-scalar-candidate-v1.md，SHA256 198901adf7de5edfb47603a534378623eb10108d387fdd627bcee0f4c4299a62，7741字节，保持原样。本次单独采纳其 DA2 确定性序列部分。DA1 已另行冻结，本文件不重计 DA1、Scalar 或 Pair/U1 为新的原始叶。

原文的时间索引是 n。本接口允许任意自然数时间序列 n_k，作为明确待证明的辅助推广；原索引由 n_k=k 取回。所有项均位于同一固定弱胞元，是本接口的域；原渐近应用若仅最终进入此域，须在后继装配中合法截去有限前缀，不能把该处理当成本文件已完成的实际概率定理。

## 2. 固定对象和项目上游

量化任意 m_:ℕ→ℕ、n_:ℕ→ℕ、h_:ℕ→ℝ，且每个 k:ℕ 满足

1≤m_k，(m_k:ℝ)≤h_k，h_k<(m_k:ℝ)+1。

令 N_k:=(n_k:ℝ)，并固定

H_k:=(m_k:ℝ)+1，δ_k:=H_k−h_k，
u_k:=π/(4H_k)，a_k:=H_k⁻¹*cos(u_k)/sin(u_k)，
rho_k:=cos(π/(2H_k))，λ:=π²/8。

这些是实际认证 Scalar 模块 Shao.OQ4.RademacherScalarBounds 的同一透明定义，不能改成自由 H、自由 a/rho 或独立 δ。Scalar PR104 的冻结 head 为38648924aa3732ed3653363ad91872d237261fc2；实际上游的定义及合法性必须从认证接口承接，不能另设正性或 Taylor 余项假设。

另一个固定项目上游为 frozen-rademacher-lattice-shift-v1.md，SHA256 9cf9dba01aa9582ceb8e4d30af06c4778b8b367b61e61562dfc42c7ffb0e2b56，6067字节，其 DA1 是同一固定表达式的全有限参数绝对常数界。DA1 已有独立数学门，其 Lean 尚未通过。本文件数学证明可明确相对于这个固定 DA1 结论展开；未来 Lean 必须连接其实际认证声明，不能把任意误差界或逐序列常数加为最终定理的自由前提。DA1 的内部 C_log 不在此成为自由输入。

## 3. 唯一尺度条件

仅加入原 S4 的三个尺度条件，极限均在 k→∞ 下：

1. h_k→+∞；
2. N_k/h_k²→+∞；
3. ∃ M:ℝ, 0<M ∧ ∃ K:ℕ, ∀ k≥K, N_k/h_k³≤M。

M 是一个固定正实界，不能随 k 改变。不得要求序列单调，不得额外要求全部 n_k>0，不得预设 N_k/h_k⁴→0、H_k/h_k→1、H_k²≤N_k 或任意待证输出。最终正时间从这些条件推出。没有 Brownian、真实概率、任意代用尾函数或自由谱余项假设。

## 4. 完整同域输出

在第2节全部序列及第3节条件下，交付以下同一派生装配的完整输出。

DA2.0 合法性：每个 k 均有 h_k≥1、H_k≥2、H_k=h_k+δ_k、0<δ_k≤1，h_k=(m_k:ℝ) 时 δ_k=1。h、H 的所用幂分母非零；a_k、rho_k、πa_k/4 及 sin(u_k) 严格为正，rho_k<1。胞元上端排除；不得把整数弱事件改成 δ_k=0 的 strict 事件。

DA2.1 几何与精确 U1 时间域：

H_k→+∞，H_k/h_k→1，N_k/H_k²→+∞；
∃ K_T:ℕ, ∀ k≥K_T, H_k²≤N_k；
∃ K_+:ℕ, ∀ k≥K_+, 0<n_k。

DA2.2 余项尺度与三次幂替换：

N_k/h_k⁴→0，1/H_k²→0；
∃ M':ℝ, 0<M' ∧ ∃ K':ℕ, ∀ k≥K', 0≤N_k/H_k³≤M'；
N_k/h_k³−N_k/H_k³→0。

DA2.3 原确定性残差消失：

λ*N_k/h_k²+N_k*Real.log(rho_k)+Real.log(π*a_k/4)
−(π²/4)*(N_k/h_k³)*δ_k →0。

DA2.4 次临界确定性特化：若在同一尺度及固定域下进一步有 N_k/h_k³→0，则

λ*N_k/h_k²+N_k*Real.log(rho_k)+Real.log(π*a_k/4) →0。

上述存在界和自然数起点均明确量化。全域合法性不应偷换成仅最终成立；渐近时间域与序列上界不应偷换成全 k 假设。输出中的实对数只消费已证明为正的真实固定表达式。

## 5. 认证边界

本文件只包含固定 Scalar/DA1 后的确定性派生输出，新增原始来源叶为0。任意时间序列及最终正时间是明确辅助扩展，须由新的来源声明审查和数学证明核实；不得把它们归称原文已显式证明的额外结论。

本文件没有真实路径概率、S1/Pair/U1 的断言或归一化余项 R、Brownian B/U、实际概率对数或倍率趋一。DA2.1 只证明后继 U1 时间域最终可用，不认证 U1 本身。原 S3/S4 的概率 o(1)、S5、临界相位与完整极限点集、strict 事件、其他 cosets、全 Spectrum 和 OQ4 root 均保持 OPEN。

精确顺序为：全新来源声明审查→独立作者数学证明→全新独立数学审查→待实际 DA1 形式认证后另行开启 Lean 私有实现、形式终审及规范交付。不得更改本冻结文本的定义、量词、域、尺度或结论；发现问题须报告给 lead，保留原件。
