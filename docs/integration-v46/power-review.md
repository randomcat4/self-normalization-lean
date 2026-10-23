# 真实中心化 signed power / gap 预算独立完整审查

结论：**CORRECT**。本票只认证 `CenteredQuadraticCharacteristicPower.lean` 的完整新模块；公开定理及四个私有引理的证明均通过独立语义审查，全部 35 个模块所属实际声明（含 30 个生成定理）类型完整读毕，与精确对象的服务器内核/传递公理收据相符。没有发现需要修复的缺口。

审查者 `/root/common_power_review`，gpt-6.1-sol / xhigh，新上下文，独立于 `/root/common_highfreq_author`。未编写或修改生产实现，未委派。可用上下文未暴露分项 token 计数，故不估算订阅额度占比。

## 精确版本与覆盖

- 作者提交：`baef8950b5c30ff3fb49b7ebe1cc755b91f7eaca`，记录父基线 `aa16e9180196b59712274a37c2b192811110908e`。
- 源码 SHA256：`026a4057455df3647b139acf3fbcd673b0940007a687b3d1ee6ea13c6d695fc6`，14619 字节。本地完整源码、服务器工作树和提交内源码逐字节哈希相同，结束前再核哈希不变。
- 服务器 `.olean` SHA256：`356c79ce4975dd6c42b7ea45ac5471f9f8df2845b532734fcf460b3336ef9e56`，2326408 字节。
- 冻结完整声明 SHA256：`b0d32a2ade324ec92f2c7183555a5e940fa756ef7cf4a32ed78bde6fa7e2718b`；根冻结记录 SHA256：`5c962dd2e39683fa2eea13b9dd5caff95fb49b4469bfeb8d63f71e3371bac49b`。唯一公开实际声明与完整冻结签名在空白规范化后完全一致。
- 读毕源码全部证明、全部 35 个实际类型及其生成关系。所有所属常量均为 theorem，无定义值需要补读。逐声明覆盖见同名 JSON；未把完整类型日志复制到工作区。

## 数学与源文忠实性

源文 main 704–708 的优化和 supplement 3376–3393 的四个幂导数项在本模块按真实概率律展开；J=8、保留六因子的上下文见 supplement 3369–3374。源文原始文件哈希保持 main `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`、supplement `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。

源码 13–29：`monomial_exp_bound` 从 `(x/k)exp(-x/k)≤exp(-1)≤1` 乘正数 k，再取 k 次幂，得到 `x^k exp(-x)≤k^k`。k>0 支付所有分母，x≥0 支付幂单调性，无极值假设或遗漏端点。

源码 31–81：`gap_budget` 对 0≤z≤1 令 g=1−z²≥0。由 z²≤exp(−g) 得 `z^(m-j)≤exp(−(m-j)g/2)`；m≥16、j≤2 支付自然数减法及 `m-j≥m/2`。故可用 `exp(−mg/4)`。将上一引理应用于 mg/4，严格推出 `(4k)^k/m^k`。没有除以 z 或 g，因此 z=0、z=1 均在证明内。

源码 83–177：`scalar_budgets` 用同一个常数 `C=24^6+28^7+52^13+1`。6、7 次预算分别覆盖未导项与二阶导数的两项。首导令 `X=z^(m−1)√g g^6`，在 m≥16 下严格得到 `X²=z^(2m−2)g^13≤52^13/m^13`。由 `(m X m^6)²≤52^13 m≤C²m` 和两侧非负取根，得到 `mX≤C√m/m^6`；没有把 13/2 当作整数幂，也没有漏掉根号常数。二阶项使用 `m(m−1)≤m²` 后与第一项相加，由同一个 C 覆盖。

源码 179–246：`power_data` 使用已接受真实 centered 生产者的两阶导数接口，逐点构造 `q^m` 及其标准 `deriv` 的可微性。再次对全局一阶导数公式求导，再用全点相等转移到嵌套 `deriv`；得到 `m q^(m−1)q''` 和 `m(m−1)q^(m−2)(q')²` 两项。`m−1−1=m−2` 及自然数 cast 减法在 m≥2 下支付。范数三角不等式、`‖q‖=z`、`‖q'‖²≤Vg` 与 `‖q''‖≤V` 给出两项预算，真实 V 与真实 g 的非负性均已证明。

源码 248–结尾：公开目标是实际 `f(r)=centeredQuadraticChar ν (σ*r) v ^ m`。一阶链式导数带一个 σ 的实标量作用，二阶带两个，使用 |σ|=1 后对应范数恰好不变。导数函数逐点相等被用于二阶可微性，因此输出是标准嵌套 `deriv`，并非自定义导数占位。g 来自实际原始 `quadraticChar` 的范数，0≤z≤1 由真实概率律保证。C 在 ν、m、σ、u、v 的全部量词之外；输入只有真实概率律、有限二阶矩、m≥16、|σ|=1。乘 √V 或 V 后通过 `√(mV)=√m√V` 得到三项结论 `C/m^6`、`C√S/m^6`、`CS/m^6`。无正方差或正谱隙前提，也无 V 或 g 分母，故 V=0 与 g=0 均保留。

30 个生成定理的完整实际类型分别是自然数边界/指数恒等式、正整数非零、乘积/幂非零的简化关系；已核其与对应 `omega`、`field_simp` 证明位置的关系。它们没有向唯一公开类型添加自由导数、自由 gap 或额外数学前提。

## 复用的服务器内核及传递公理证据

本票没有重跑 Lean、重收公理或建立新执行包装。通过 SERVER broker 只读核对已有收据、服务器文件哈希、完整实际类型、审计代码与覆盖。工具链固定 `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。作者目标编译 exit=0；日志只有已有包工作树提示和风格建议，没有证明错误。源码禁用项扫描无匹配。

证据目录为服务器 `/root/rivermind-data/shao-lean-20261021/outputs/common-centered-characteristic-v44/`：

- `power-targeted-04.log`：SHA256 `7ee3d7551f801cdd98d7ffaeed9cda58d4ec3bf3f90120d6ce6d0055339e9cae`。
- `power-owned-audit.json`：SHA256 `f90a48566a3c4072b609418398e34873236b45ae8e2de3fa085643ea918af832`。
- `power-owned-audit.log`：SHA256 `f2892b7065b64b7e162716cc300b51702a85ed2c755dfaf6d15ef45fb4db9ab4`。
- `PowerOwnedAudit.lean`：SHA256 `5187940f61dbcbf76c0e7220d7b5ed7f647404031954f8ffa99b1cf6617fe09e`。按真实 module owner 遍历全部常量，对每项调用传递 `Lean.collectAxioms`，没有盲名前缀筛选。
- `power-actual-owned-types-and-definition-values.log`：SHA256 `278315620419fef7aadc492b1b1ce05c76ce06a0bcf0160fa343c5daadd65c9b`，66254 字节/913 行，分段完整读毕。
- `PowerActualOwnedTypes.lean`：SHA256 `47b85cde4efbd0b35a2f705b0260d1afdaf8c06fa118c24bc2a89b1f312ba7a0`。同样按真实 module owner 导出全部实际类型及任何定义值。

审计 JSON、审计日志和实际类型导出的名字集合完全相同且各有 35 项；处理日志正常的多行公理列表后，各项 kind/axiom 内容也精确一致。35 项全是 theorem，1 个公开定理、4 个源码私有引理、30 个生成定理，0 个定义。每一项的传递公理都只含 `propext`、`Classical.choice`、`Quot.sound` 的子集。机械状态在本模块完整冻结目标范围为 **LEAN_FULLY_CHECKED（复用精确版本成功证据）**。

依赖 `CenteredQuadraticCharacteristic.lean` 源码 `9022df71074e54ffac5352d69dcce0b5867c5a7c019aae264ac3d3105fa7f148`、对象 `e1e4092b75e4b7bcb01afd3fffcf134070c7c3d33fcda63379f2a1717c3756e5` 均与既有独立 CORRECT 票一致。本票消费该结论，不重复审其旧局部证明。新用到的 Mathlib `Deriv/Pow.lean`、`Deriv/Comp.lean`、`SpecialFunctions/Exp.lean` 三份关键源码逐字节等于锁定 Git blob，并核对幂与带实标量作用链式接口。既有 package-view 工作树提示不被解释成整个包干净。

## 范围与交接

该票认证 law 级真实 signed power/g^6 预算，没有证明原始 n/i/T/γ 条件已推出 m=n−i≥16，或 S=mV 与 T、τ 的尺度比较；这些由最终 adapter 支付。噪声因子完整乘积、整个 highfrequency(c)、C1/C2 继续 OPEN。无原始根定理闭合或历史新颖性主张。

根可在精确哈希和接口/交互范围核对后复用本次完整独立审查及配套内核/公理收据；仅在实际数学变化、证据缺口或未覆盖的实质集成风险出现时补审受影响部分。
