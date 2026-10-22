# 冻结命题：原 Spectrum 两处立方根精细余项

VERSION: v1
STATUS: FROZEN_MATHEMATICAL_TARGET_NOT_YET_PROVED_OR_FORMALIZED
SOURCE: C:/game/shao/current/oq4/c01/spectrum01.md
SOURCE_SHA256: b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b
SOURCE_LINES: 96,97–98
RAW_LEAF_INCREMENT: 0
ORIGINAL_ROOT_CLOSURE: NONE

本单元补原文明确写出的 O(k⁻⁵) 与 O(k⁻²) 立方根余项。已经接受的 CP/S5 相位及概率极限没有声称这两条定量率；本单元也不重做这些概率极限。直接消费者是原 Spectrum 对这两条展开的逐项覆盖账，不把辅助声明数折算为原始完成百分比。

对象必须采用已经接受的 `Shao.OQ4.RademacherCriticalPhase`（下称 CP）的透明定义：

- `root(n)=Real.rpow (n:ℝ) ((1:ℝ)/3)`，不是自由立方根；
- `height(c,n)=c*root(n)`；
- `belowCubeIndex(k)=k^3-1`，减法在自然数中；
- `target(c,α,k)=(((k:ℝ)+α)/c)^3`；
- `nearestIndex(c,α,k)=Nat.floor(target(c,α,k)+1/2)`，平局向上。

所有 k 的定义域为自然数；K=(k:ℝ)。函数定义不改早期值，以下有限界只对 k≥2 主张，与原文的 k→∞ 展开一致。所有自然数到实数转换必须明确。允许消费 CP 的公开 `root_spec`、`positive_time`、取整与索引公开声明及其透明定义；不得读取 CP 实现证明或其匿名证明/审查推理。两个误差界须在当前单元推导，不可作为新前提。

## R1：完美立方减一

对每个自然 k≥2，令 n⁻(k)=CP.belowCubeIndex(k)，r⁻(k)=CP.root(n⁻(k))。证明自然减法的实数身份 `(n⁻(k):ℝ)=K^3-1`、n⁻(k)≥1，及同一 r⁻≥0、(r⁻)^3=K^3-1、CP.height(1,n⁻)=r⁻。

同时证明明确有限余项界

  |r⁻(k) - (K - 1/(3*K^2))| ≤ 1/K^5。

由此给出原文的实际展开

  r⁻(k)=K-1/(3*K^2)+O(k⁻⁵)，k→∞。

这里 O 的精确含义是：存在输出常数 C>0 和自然阈值 k₀，使全部 k≥k₀ 时上述绝对误差≤C/K⁵。所给有限界可交付 C=1、k₀=2；这些是输出，不能写成假设。不得把源文需要的二阶修正项删成仅 r⁻−K→0。

## R2：同一最近整数规则

对每个固定实 α，0<α<1，并对每个自然 k≥2，令 nᵅ(k)=CP.nearestIndex(1,α,k)、rᵅ(k)=CP.root(nᵅ(k))、tᵅ(k)=K+α。证明 tᵅ>0、nᵅ≥1、(rᵅ)^3=(nᵅ:ℝ)、rᵅ≥0，以及 CP.height(1,nᵅ)=rᵅ。须从同一个 Nat.floor 定义导出实际舍入误差

  |(nᵅ(k):ℝ)-(K+α)^3| ≤ 1/2。

同时证明明确有限余项界

  |rᵅ(k)-(K+α)| ≤ 1/(2*K^2)。

由此给出原文的实际展开 rᵅ(k)=K+α+O(k⁻²)，k→∞，其中精确 O 含义为存在输出 C>0、自然阈值 k₀，使全部 k≥k₀ 的误差≤C/K²。有限界可交付 C=1/2、k₀=2；它可对冻结域内所有 α 使用同一常数，但不得据此主张新的概率一致极限或任意 c 定量结论。

## 成功条件和阶段边界

本冻结不含证明路线。先给一份完整匿名数学证明（或精确反例/断点），再由全新独立实例全文验证。不得增删、弱化或重新解释冻结前提；若显式常数的有限界不成立，立即给反例并 STOP，交父裁决，不自行换常数。没有服务器、Lean、Git、缓存、canonical 或实现授权。精确 Lean 声明须在数学门之后另行冻结并经隔离语义审查。

两个结论仅为同一既有 CP 根/索引的定量确定性细节，不新增一般概率/Brownian假设，不重跑已经通过的 CP/S4/S5 门，不证明一般 strict ceil 分类、原116的一般相邻格点界、一般分布或 uniform-x 的 OQ4，不声称 Spectrum 或任何原研究总根闭合。
