# 反射与条件 BE/SP 到真实 S/AC v1 声明语义核查

STATUS: CORRECT
STATUS_SCOPE: FROZEN_STATEMENT_SEMANTICS_AND_CONSTANTS_ONLY
ROOT_STATUS: OPEN
LEAN_STATUS: NOT_RUN

仅读 frozen-reflected-survival-v1.md，并对照此前已读的数学源 b01/proof01.md §3“同样适用于 −Y”及 AC、既冻 FiniteSurvivalLaplace 和 BoundaryOccupation 的下侧事件契约。未读作者 Finite 实现、证明或独立审查票，未运行 Lean，未修改冻结、数学源、Git 或公共文件。

## 有限产品反射与事件

ν⁻ 是实际映射 x↦−x 推出的概率 law。全部 t（包括零）上的 Π_t(ν⁻)=map(a↦−a)Π_t(ν) 是正确的有限产品 law 目标，不是生存条件化后的 law。

prefixSum 在坐标反射下变号，闭下侧事件对应路径反射的公共 closedUpper 原像；这与此前冻结的 lowerBlockSurvival 定义一致。包含零前缀、t=0 空路径、闭等号和所有原子，均未要求改变公共事件。

冻结没有声称 H(−a)=−H(a) 之类不正确的最大值反射关系；实际使用的是上/下事件的反射原像。

## 仅 ν 的 CDF 输入足以反射同误差

对 ν 的标准化和，显示输入是弱 CDF 事件 ≤x。反射后的弱 CDF 应表达为原 law 严格尾的补集，必须使用原 law 的 < 版本，而不能直接用 ≤ 代替。

实际 Φ 的连续性允许由全实轴弱 CDF 误差取左极限，得到同一误差的严格 < 版本；实际标准高斯的反射恒等式再将比较点 −x 转成 x。这个过程保留相同 β、C_BE，不增加两倍误差，也不需要 ν 无原子。

冻结明确要求实际 Φ 的反射恒等式与连续性，没有把它们当未实例化的抽象比较函数前提。t≥1 保证标准化分母为正，有限产品反射与普通和的负号相容。无需再加入 ν⁻ 的 BE 假设。

## 两份原始 SP 输入

ν 和 ν⁻ 各自的原始 SP 形式都明确列为输入；不能仅凭 ν 的固定 law SP 就省略 ν⁻ 的输入。该范围忠实对应源对 Y 与 −Y 分别使用 S 的需求。

输入没有扩张为已改写的生成式、所需生存界、非增性或可和性。这些实际 law 性质仍由 FiniteSurvivalLaplace 的待证接口供应。无条件 SP 本身没有在此被证明。

## 实际 S 与 AC 谓词

对两个 law 分别应用同一 CDF 参数和其各自 SP，所需闭上/下生存常数为
\[
C_S=\sqrt2\,\exp(6+3C_{\rm BE}).
\]
该数值与 FiniteSurvivalLaplace 的 Markov 后常数一致。通过真实有限产品反射，将 ν⁻ 的上侧结论转为 ν 的下侧，目标正是现有 iidOneSidedSurvival 的双方向概率契约，而非新造抽象事件界。

闭单位间隔集中由同一 ν 的实际 CDF 输入及 β≥1 给出
C_q=1+2C_BE。
当前 β 只是明确 CDF 参数，故必须使用一般 law 的闭 CDF 质量引理及实际高斯 1-Lipschitz 实例，不能调用额外要求 β 为第三矩/单位方差的高层定理而偷偷加强假设。冻结第 15 行已明确禁止该做法。

Cq、Cs 均非负，且只依赖 C_BE，没有遗漏矩或分布依赖。仅当外部 BE 提供数值通用常数时，它们才成为通用数值常数。把这两个实际谓词一同供应给 KilledBlockBounds 的接合方向正确；本票不认证最终实现签名已匹配。

## 退化边界与源作用域

t=1、d=0、原子和全零路径全部保留。ν 不要求对称；反射 law 是单独实际测度，不把“分布对称”当作隐含假设。

不要求 β 额外等于某矩；未来源实例可以取实际第三绝对矩并另供 β≥1。源 BE 的中心、单位方差、有限第三矩，以及两个原始 SP 的证明仍在外部，不因当前条件性接合自动成立。

未发现声明语义或常数缺口，可以进入实现与后续独立形式审查。无条件 BE/SP/S/AC/O0、B1、长时间 K/Kv、能量分母和全部完整根保持 OPEN。

## 版本锁

- 冻结声明：C:/game/shao lean/drafts/oq4/frozen-reflected-survival-v1.md
- SHA256：D70163CB3114DCF35787D6AB1159B80CA67BA6DC2598613AE252E3EC1126F2DC
- 数学源：C:/game/shao/current/oq4/b01/proof01.md
- SHA256：7C51246EB02A0D694A366CE3AB5A3A9CCA03723160C1291BCE29DD817F68BC38
