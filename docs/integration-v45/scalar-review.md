# 实际标量 Fourier 导数独立最终审查

**STATUS: CORRECT** — 2026-10-23。审查者 `/root/common_scalar_review`，调度模型 `gpt-6.1-sol` / `xhigh`，与证明作者 `/root/common_scalar_author` 分离。本审查没有修改源码或重跑 Lean；复用下列精确版本已有的成功服务器检查。

## 版本绑定与完整覆盖

- 源码：`drafts/c12-scalar-fourier/SourceScalarFourierDerivatives.lean`，全部 263 行；SHA256 `a265b86455c7f06f38fb4e4758884d59052498933318219d1d4b9bf5cc410072`。
- 服务器分支 `feat/common-scalar-fourier-derivatives`，提交 `33e3336937c4bd2ed6301effc5e6c18b89b575d3`；服务器工作文件、提交内源码和本地副本哈希一致，工作树干净。目标对象 SHA256 `f73e3779d4e6df00bd0fec4ef5898e1db8952a011f96ee99a0236ed2c57e4aa0`。
- 已完整读取两条冻结声明、源契约及根冻结批准；候选 SHA256 `4c27f2af5b99850111ade205aa5c7096240f64a153dceca6e0f8c3bc40d0d95a`，契约 SHA256 `a7f69e1a9c1d67883a71f859cf59b6fcf65aa0668f271349d91166f25ae33f10`。
- 已完整读取全部源码证明、全部 **40 项实际所属类型**及 **3 个定义值**：2 公开定理、21 显式私有声明（3 定义、18 引理）、3 生成定义方程、14 生成算术化简定理。没有未审私有/生成范围；生成项的类型与定义展开或非零算术事实一致，内核及传递公理证据覆盖其证明。

## 数学与来源核对

已读取只读 main.tex 660–678、supplement.tex 3349–3353，以及实际 `SourceScalarNoise.lean` 的完整定义和数据证明。后者源码 SHA256 `d2c8c0aed4fbd8bbc16970a493ddf6658e37fe51b09e0e29fac88a27d0c274dc`，服务器同哈希并使用已接受 v43 对象。目标仍是该固定归一化光滑偶 bump 的真实概率律和正相位特征函数；没有换成自由函数、任意假设的概率律或导数代理。

1. **导数身份（55–123 行）**：相位模恒为 1；一、二阶导数分别为 `i*gamma*r` 和 `-(gamma*r)^2` 乘相位。支配函数 `|gamma|*|r|`、`gamma²*r²` 使用实际律的一、二阶绝对矩可积性，且支配对全部评价点成立。两次积分下微分的可测性、基点可积性、局部共同邻域及逐点可微条件齐全。全局一阶身份把第二次求导的积分函数与标准 `deriv` 逐点识别，故第二身份确为标准嵌套导数。
2. **衰减（125–215 行）**：振幅恰为 `r^k*rho(r)`；光滑性、紧支撑及每阶导数可积性均从固定密度证明。已检查固定 mathlib 的 `fourier_iteratedDeriv`、Fourier 模积分界和正负相位展开的实际条件。频率 `-t/(2*pi)` 将负相位精确化为 `exp(i*t*r)`；导数乘子化为 `-i*t`，取模后恰为 `|t|^n`，没有遗失或多出 `2*pi`。概率律到 Lebesgue 积分的换算使用实际非负密度；一、二阶身份的外部因子为 `gamma*i`、`-gamma²`，符号及次数正确。
3. **统一性与边界（217–263 行）**：`A=∫|(r*rho)'|`、`B=∫|(r²*rho)''|` 有限非负，见证常数 `1+A,1+B` 严格正，并在全部 `gamma,u` 量词之前。证明取得 `|u|*|d1|≤A`、`u²*|d2|≤B`，只除以非零 `u` 的正绝对值或平方，未除以 gamma。故 gamma=0 与负 gamma 均被同一证明覆盖；积分身份含 u=0，逆幂界仅排除 u=0。两条实际公开类型与冻结声明一致，无新增前提。a=0 的界沿用已有实际特征函数模界。

## 服务器与公理证据

复用 `drafts/c12-scalar-fourier/author-receipt.json` 的干净目标检查：退出码 0、无源码警告，`-M8192 -j4 -DautoImplicit=false`，CPU10–13。实际锁定 Lean `leanprover/lean4:v4.36.0-rc1`；manifest 与 mathlib checkout 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。

通过 SERVER.md 的只读 broker 重新核对既有日志原始哈希，完整分段读完实际类型/定义值日志 1–1239 行。类型日志 SHA256 `3ae07a30c3443305246aacbe3d1f94fd889cfca13f24d16c6233e5686686b35e`；审计日志 SHA256 `0f83160cb99f8cf75b689f5ce50f0676c1aef03c4886edaffed72bb5f55a22bc`，均位于服务器 `outputs/common-scalar-fourier-v44/`。

已读取既有 OwnedAudit 检查器：按**所属模块**枚举，使用 `Lean.collectAxioms` 传递收集。确定性解析确认 246 项导入项目声明各不重复，40 项新声明逐名全覆盖、缺失 0，日志成功标记 `AUDITED_PROJECT_CONSTANTS 246`；无白名单外公理，公理并集仅 `propext, Classical.choice, Quot.sound`。源码禁用词扫描无 `sorry/admit/axiom/unsafe/native_decide`。

本模块两条标量结果可接受；它们是经典 Fourier 分析的来源绑定辅助结果，不作新颖性声明。Ξ 乘积消费者、高频 (c,d)、反演、去平滑及 C1/C2 仍 **OPEN**，本票不扩大原根闭合范围。后续只有源码数学变化或实际证据缺口才使对应覆盖失效。
