# OQ4 弱格点位移的有限定量派生接口 v1

STATUS: FROZEN_PENDING_SOURCE_REVIEW
KIND: DERIVED_ASSEMBLY
CANDIDATE_AUTHORITY: ADOPTED_DA1_ONLY
NEW_RAW_LEAF_COUNT: 0
SOURCE_REVIEW: REQUIRED
PROOF_STATUS: NOT_WRITTEN
LEAN_STATUS: NOT_RUN
IMPLEMENTATION_AUTHORIZATION: HOLD
S3_S4_S5_BROWNIAN_SPECTRUM_OQ4_ROOT_STATUS: OPEN

Lead 只采纳候选 DA1 的全部有限参数定量界及同域合法性，固定将来模块 Shao/OQ4/RademacherLatticeShift.lean、namespace Shao.OQ4.RademacherLatticeShift。DA2 的序列特化不在本冻结范围，仍保留在原候选中供后续装配。新增原始来源叶计数为0；这是一个需要完整证明和独立审查的派生接口，不是已获证的代数事实。

原候选 drafts/oq4/frozen-rademacher-after-scalar-candidate-v1.md，SHA256 198901adf7de5edfb47603a534378623eb10108d387fdd627bcee0f4c4299a62、7741字节，保持原字节；本文件是另行明确选择范围的新冻结版本，不改变候选或任何既有冻结接口。

## 1. 来源与范围

唯一新来源为 C:/game/shao/current/oq4/c01/spectrum01.md，commit 35d4580b61e22e7145f47730045a09874ef93259，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b，4306字节。

- 11–12行固定弱事件胞元 m=floor(h)、H=m+1。
- 36行固定 a_H、rho_H。
- 60行固定 λ=π²/8。
- 66–67行给后继 S3 消费的确定性表达式 λn/h²+n log(rho_H)+log(πa_H/4)。
- 70–77行给 H=h+δ、领先位移项 π²nδ/(4h³) 以及误差阶 n/h⁴+H⁻²。

本接口把该确定性部分规范化为全部弱胞元、全部自然时间的统一有限定量界。原文仅在其 S4 尺度下写渐近阶；这里的全 m≥1 定量范围是明确新增的待证辅助义务，不能声称原文逐字给出了该全域界。它由真实固定定义及 Scalar 接口派生，不另立新的原始随机或分析输入。

不消费原 S3 的实际概率余项，不消费 Brownian，不输出实际概率比或 S4 完成状态。原文 n/h³=O(1) 等尺度不是本有限界的假设。

## 2. 固定对象

m:ℕ，1≤m。固定实数

H(m):=(m:ℝ)+1，u(m):=π/(4H(m))，

a(m):=(1/H(m))*(Real.cos(u(m))/Real.sin(u(m)))，

rho(m):=Real.cos(π/(2H(m)))，λ:=π²/8。

所有对象与已冻结 Scalar 的真实表达式相同；a、rho、H 都不是自由参数或自由序列。若未来复用已认证透明定义，必须明确证明定义等式，不以任意满足某界的替代函数充当这些对象。

h:ℝ 满足 (m:ℝ)≤h 且 h<(m:ℝ)+1。定义

δ(m,h):=H(m)−h。

δ 只由 m、h 决定，不能独立量化。n:ℕ，N:=(n:ℝ)，包括 n=0。

## 3. 必需合法性与端点

对全部上述 m、h，须由固定域得出

h≥1，h>0，H(m)≥2，H(m)>0，H(m)=h+δ(m,h)，0<δ(m,h)≤1。

若 h=(m:ℝ)，须保留 δ(m,h)=1。胞元上端仍排除；δ=0 不在域中，不能换成 strict 事件的整数端点。

h²、h³、h⁴、H² 以及 Scalar 定义中显示的分母均须真实非零。a(m)>0、0<rho(m)<1、πa(m)/4>0 必须实际承接同一 Scalar 的合法性结论；不能把它们添加为最终定理的自由前提。所有对数是 Real.log，对正自变量的合法性须核对。

## 4. 冻结核心 DA1

存在绝对实常数 C>0，使对全部 m:ℕ、1≤m，全部 h:ℝ 满足 (m:ℝ)≤h 且 h<(m:ℝ)+1，以及全部 n:ℕ，有

| (π²/8)*(n:ℝ)/h²
    + (n:ℝ)*Real.log(rho(m))
    + Real.log(π*a(m)/4)
    − (π²/4)*((n:ℝ)/h³)*(H(m)−h) |
  ≤ C*((n:ℝ)/h⁴ + 1/H(m)²)。

完整量词固定为

∃ C:ℝ, 0<C ∧
  ∀ m:ℕ, 1≤m →
  ∀ h:ℝ, (m:ℝ)≤h → h<(m:ℝ)+1 →
  ∀ n:ℕ,
    | (π²/8)*(n:ℝ)/h²
        + (n:ℝ)*Real.log(rho(m))
        + Real.log(π*a(m)/4)
        − (π²/4)*((n:ℝ)/h³)*(H(m)−h) |
      ≤ C*((n:ℝ)/h⁴ + 1/H(m)²)。

C 先于 m、h、n、δ、任意序列及任何 S4 有界性常数 M 选定，与之全部无关。m=1、m=2、h=m、δ=1、n=0 必须覆盖。不得只交付充分大 m、H≥H0、正时间、某种奇偶或更强尺度的版本。不得改变 π²/4 的领先位移系数、残差符号或两个余项阶。

## 5. 精确依赖与内部派生义务

唯一项目数学上游为 drafts/oq4/frozen-rademacher-scalar-bounds-v1.md，SHA256 225b63ae8522a126cb5c126f83cb782b024e95f592e9e2da5f36f56e0ce21356、9414字节，固定其 SCA0/SCA1/SCA2。未来实现须实际使用认证后的声明，而非在最终定理假设中重新给出这些待证估计。

为闭合 n=0 等全部有限参数，需要的

∃ C_log>0, ∀m≥1, |Real.log(π*a(m)/4)|≤C_log/H(m)²

是本派生接口内部必须证明的便利义务。它未由 Scalar 冻结为独立输出，不能当作自由输入，也不另计原始叶。公开还是私有 helper 可在形式实现时选择；本冻结核心始终只有 DA1 加第3节合法性，不新增 C_log 的独立贡献计数。C_tan 不被本接口消费。

本文件没有提供上述便利界、位移界或 DA1 的证明。数学作者、全新独立数学审查以及形式门必须分别完成；“派生”不免除任何一门。

## 6. 排除与后续

DA2 的任意序列、H/h→1、n/H²→∞、U1 时间域最终成立、n/h⁴→0、确定性残差趋零等特化均不在本冻结版本。它们留待后续派生装配，不能被新增为 DA1 的前提。

本接口不含真实 p、路径概率、归一化谱余项 R、S1/Pair/U1、Brownian B/U 或自由代用尾函数作为前提或结论。共享真实 B/U 归 root；原 frozen01.md 只有首项等价渐近，不能默用 spectrum61 的更强指数速率。实际 S3/S4 必须另接真实概率、谱和 Brownian 的认证接口及正性/对数合法性。

S2、实际 S3/S4、S5、所有 c>0 的临界极限点、strict 事件、其他 cosets、Spectrum 和 OQ4 根均保持 OPEN。本派生接口的接受不改变这些状态。

本轮只冻结精确声明；来源审查、匿名数学、独立验证、私有形式实现和 canonical 写入均须后续分别释放。不得读取其他审查推理来代替独立证明。
