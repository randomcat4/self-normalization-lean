# 单步杀死核 v2 冻结声明语义盲审

STATUS: CORRECT
STATUS_SCOPE: FROZEN_STATEMENT_SEMANTICS_ONLY
ROOT_STATUS: OPEN
LEAN_STATUS: NOT_RUN

本轮只读取 frozen-killed-kernel-v2.md，依据此前完整读取的数学源 b01/proof01.md §1 K_h 定义及 §6 R1、以及本角色此前的 v1 声明核对重新确认。未读证明或实现，未实施、编译或修改冻结文件；v1 审查票未覆盖。

v2 第 13 行已把行测度明确为 P_h(z)，消除了独立 κ 的潜在记号歧义，澄清充分。输出支持现准确表述为：对每个起点 z，P_h(z)-几乎处处 |w|≤h。

其余量词、前提与接口保持原样：ν 是 Borel 概率测度，h 任意实数；行测度先平移推出、再限制到闭 [-h,h]；源状态域内含义与明示实轴延拓不变；行质量≤1且不归一化；h=0 原子保留；任意有界 Borel 测试的精确积分等式及两侧可积性义务仍明确；余弦测试与同参 Kcos 一致。

没有剩余声明语义缺口，可以按 v2 进入构造实现。本票只审声明，不认证真实 Mathlib Kernel 构造、核幂路径表示、O0/R3 或 K/Kv。根 OQ4 保持 OPEN。

版本锁：

- 冻结声明：C:/game/shao lean/drafts/oq4/frozen-killed-kernel-v2.md
- SHA256：034CBEC4C7E447E9FA27A2C71BC87194924BEA2528BEF0D7FE7DA15667CA3ECF
- 数学源：C:/game/shao/current/oq4/b01/proof01.md
- SHA256：7C51246EB02A0D694A366CE3AB5A3A9CCA03723160C1291BCE29DD817F68BC38
- 保留旧票：translation/killed-kernel-statement-review-v1.md。
