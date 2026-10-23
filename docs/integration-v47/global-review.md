# 实际全平面幂及 D/uE 导数：独立完整审查

STATUS: CORRECT

审查者：`/root/common_global_review`，fresh 独立上下文，`gpt-6.1-sol / xhigh`。未参与作者实现，未修改源文件；本次只写此报告及同名 JSON。按 math-theorem 和项目约束审查，未调用 math-ultra、未派生实例、未重跑 Lean/公理审计。复用精确源版本的既有服务器成功证据。

审查对象为服务器树 `/root/rivermind-data/shao-lean-20261021/workspaces/common-cone-derivatives-v44` 的唯一新增文件 `Shao/Probability/QuadraticFullNoiseGlobalOddEven.lean`，完整读取 LF1–308。作者提交 `06bc9ebf05fef8db62d1e74e16b516c1b1fe9c68`；工作树该文件与提交字节相等且无该文件未提交改动。

## 精确证据绑定

| 对象 | SHA256 |
|---|---|
| 最终源，17246 bytes | `7256c6f101d86a76f78f713f06c031cba4ec75c7174bb9d73d0fdb629956008c` |
| 最终 olean，1208784 bytes | `999cf81e1044a178f038875d1902fcc474b93bd2b5c0a17860a0c8a1dfe40dde` |
| `drafts/c12-cone-derivatives/global-odd-even-author-receipt-final.json` | `798dd4c9e909ec98731863d921dd063bb18d2e6728f1146aee742c9a2f4bd4d5` |
| 服务器 `global-odd-even-targeted-03.log` | `e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b` |
| 服务器 `global-odd-even-owned-audit-final.json` | `e097fd59d415838915b92906d37be49c6b3e193113bde5351892fbcc0517f4f5` |
| 服务器 `global-odd-even-actual-owned-types-values-and-axioms-final.log` | `6dd4e15ec48022cb415f50dd53b10dfca0e68a41cd7445e85968390cae4e3f76` |
| 服务器 `GlobalOddEvenOwnedAuditFinal.lean` | `c7cf1cdd584a8cd8cd11ee6d349e32c63d4cd6a64647f61f29e009ff9fbc6a91` |

上述服务器输出位于 `/root/rivermind-data/shao-lean-20261021/outputs/common-cone-derivatives-v44/`。本审查重新读取并核对文件哈希，未重跑其中的检查。最终 receipt 记录 targeted exit 0、全部 owned 传递公理 PASS；实际日志完整输出 8 theorem / 2 public / 0 definition，末尾两个公共公理列表均在白名单内。审计脚本按 `env.getModuleIdxFor?` 遍历目标模块全部常量，包含 private/generated，使用传递的 `Lean.collectAxioms`，没有只按公共名称筛选。唯一诊断为已接受只读 mathlib 的既有 dirty warning。

实际工具链文件为 `leanprover/lean4:v4.36.0-rc1`，实际 mathlib HEAD 为 `807d3836b165983210ee2ecf3cd28f239436949c`。执行收据保留 CPU10–13、`-M8192 -j4 -DautoImplicit=false` 和 root-heavy.lock。

冻结 candidate SHA 为 `f694e32886a09ac120366d985b82ac8c0626364ab684f92a4762ef40781883ba`，contract SHA 为 `f3c53bc75d5e654535145dcbef6a5d65dd1aa56677f40993b011f76c162fcfb7`；已完整读取两者及根冻结文件，两公共声明与冻结文本一致。完整核读 8 个 ACTUAL_TYPE；重复的标准实例项按 24 个唯一展开逐一核读，无数学参数或函数被省略。两公共 `#check` 类型与对应 owned 类型空白归一后逐字相等。

旧提交 `48eb4df6825d49066a91d62030423fecc28e2472` 的旧源 SHA `5dbb7989c84b271f9b960befcf91b1d8cdfdf6e9076ca4558cdae76c6bb87323` 到最终源，仅删除 LF137/200 两空行各一个 `0x0D`；直接读取两 Git blob 验证除此之外逐字节相同。新旧实际类型日志、owned JSON 逐字节相等，旧收据对象哈希等于最终对象哈希。只对最终源进行本次完整数学审查。

## 原文到陈述

原 supplement SHA `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，main SHA `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`，均与既有 source checkpoint 相符。已读取 supplement LF2356–2357、2614–2617、3403–3417、3508–3518、3539–3547 及相关实际符号定义；main LF622–623、675–678 和 supplement LF2343–2344 确认 `gamma=m3/variance`、正号特征函数及 `T=(n-i)m2`。

第一公共声明 LF41–76 从原概率律、二阶归一化、零均值、x/epsilon 及截断预算出发，令 rho 为真实 `cond`。`law_data` 支付 rho 的概率性及二阶可积性；`variance_bounds` 支付 `n*m2 ≥ 3/4`。`paid_moments` 给出 `n*|mean rho| ≤ 2R/(epsilon²(1+x))`；预算实际将其支付到 `epsilon/(4(1+x)) ≤ 1/8 ≤ 1`，代码使用这一上界的较松形式。归一化矩条件及条件均值界均非新增调用者假设。随后真实有限独立同分布导数身份给出两阶可微性，已接受 normalized power 接口给出 `1, 2 sqrt(T), 3T` 三个界。两个符号及全实 u/v 均保留。

第二公共声明 LF201–306 的 D/E 正是原 LF2356–2357 的两个真实 signed power 与真实 Xi 的组合，W(r)=rE(r)。它从相同原始输入内部支付正方差、三阶可积性、支持及 gamma>0；`gamma≤2cutoff≤2h` 在 LF251–257 支付，没有追加给调用者。已有真实 Xi 接口给出 `norm Xi≤1`、`norm Xi'≤67gamma/3`、`norm Xi''≤70hgamma/3`。全局一阶函数先识别，再求其普通二阶导数；没有用默认 deriv=0 或单点身份代替真正二阶可微性。

令 s=sqrt(T)。LF258–263 从 T≥0 和 gamma≤2h 推出 `s*gamma≤T/2+h*gamma`。因此乘积二阶界为
`3T+(268/3)s*gamma+(70/3)h*gamma ≤ (143/3)T+(338/3)h*gamma ≤120(T+h*gamma)`，从未使用 `h*gamma≤T`。一阶界为 `2s+(67/3)gamma≤30(s+gamma)`。奇偶半和/差保留这两个尺度，真实身份 `W''=2E'+uE''` 给出最终 C=120，且 C 的存在量词先于全部原参数。

## 全部声明覆盖

下列 private 名称均带完整前缀 `_private.Shao.Probability.QuadraticFullNoiseGlobalOddEven.0.Shao.Probability.`；public/generated 名称均带 `Shao.Probability.`。每项结论均为 CORRECT。

| 实际声明 | 源行/关系 | 完整审查结论 |
|---|---|---|
| private `signed_power_diffs` | LF18–39 | canonical Fin m product law 真实独立同分布；两次已接受积分导数身份及实标量链式法则。全局 first identity 再支付 nested derivative；任意 sigma，m=0 仍有效。 |
| public `sourceTruncation_quadraticChar_power_global_derivatives` | LF41–76 | 上述真实源矩条件支付及归一化消费者；无条件中心化或对称化 rho。 |
| generated `sourceTruncation_quadraticChar_power_global_derivatives._proof_1_1` | LF76 `omega` | 实际类型为 `∀ n i, i≤n → ¬(n-i≤n) → False`；只支付自然数剩余长度≤n。公理仅 propext、Quot.sound。 |
| private `product_bounds` | LF78–125 | 全局乘积一阶身份后求导，真实 `(pq)''=p''q+2p'q'+pq''`；三角不等式和已有范数界给出 A+G、B+2AG+H。所有前提在主声明内支付。 |
| private `half_add_bound` | LF127–132 | 复数范数三角不等式及除以正实数2，得半和界；不需要额外 c>0。 |
| private `half_sub_bound` | LF134–136 | 以 -w 化归 half_add，范数不变，半差界准确。 |
| private `odd_even_calculus` | LF138–199 | D/E 全局一阶身份产生真实 D''/E''；W=rE 全局一阶身份再给 W''，上界 c2 和 2c1+abs(u)c2。 |
| public `sourceTruncation_odd_even_fullNoise_global_derivatives` | LF201–306 | F=pXi、G=qXi 的真实乘积界；先支付 gamma≤2h，再支付混项；函数等式把内部 D/W 精确还原原式，固定绝对常数120。 |

除上述生成算术项外，其他7个 theorem 的传递公理均为 `propext, Classical.choice, Quot.sound`。源全文无 sorry/admit、新 axiom、unsafe 或 native_decide；模块无 owned definition，因此不存在未读取的定义值。

## 依赖、边界和验收范围

本次只核被消费的旧接口，没有重新审查其证明。服务器直接消费的 `QuadraticCharacteristicPower`、`QuadraticFullNoiseDerivatives`、`SourceFourierScale`、`SourceTruncationBridge`、`QuadraticFullNoise` 源哈希与已接受 v46 receipt 的 source_files_sha256 及本地只读 library 完全一致。该 receipt SHA 为 `2a185ed46b08f4dfef9133654c49575f3523759607c61acf68d445127674cd76`。没有 Region4 依赖，也未重复审查 Region4。

无 L2、cone、高频、正T 或 supplied derivative estimate 前提。i=0、i=n、m=0、T=0 和 u=0 均在陈述域内；证明无除以 m/T/u 的步骤。m=0 时 D≡0、W=rXi，u=0 仍使用同一真实乘法求导身份。

此结论接受的范围：原 highderivatives(d) 的实际条件律专化，以及 Region3/5 使用的实际 D/uE 全平面微分输入。实际 marked-v/u 积分、边界及分部积分、Fourier 反演、Region3/5 概率贡献与 C1/C2 根结论仍 OPEN。本报告无新颖性或根定理完成主张。无待修关键缺口。
