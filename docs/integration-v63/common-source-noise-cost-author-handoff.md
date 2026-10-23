# SourceNoiseCost 作者交接

状态：作者证明完成；源码写权已释放；无在途命令。独立完整复核尚未执行，不作自审验收声明。

- 远程工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/common-scalar-fourier-v44`。
- 分支：`feat/common-source-noise-cost`；头：`bf22cc907e5c494a5c7e81899689e3e83093606d`；树：`4986c07b8491c28a101d6610f647e71007c2fe2e`；父头：`5893148b514a6feaa5f4c36d12485135fae83024`。
- 提交只新增 `Shao/Probability/SourceNoiseCost.lean`。旧的未跟踪 `SourceFourierTestKernel.lean` 保持原样，未纳入本提交。
- 精确源码 SHA256：`531e2ab17798c7ba7db49d19bd08af7cc1c7cf5ae29b0d23af4873fe30dcda20`。
- 同次首检对象 SHA256：`3a083bfb23605cfffc4118ecaeefd5d544b2db18e18defc73ca614d2facd925b`。

## 数学内容和复核重点

冻结的唯一公开结论 `Shao.sourceTruncation_noise_badClock_weighted_cost` 头部及全部 literal lets 未变。没有辅助定理或新定义。实际类型全文见 `actual-owned-types.json`，全证明见 `SourceNoiseCost.lean`；复核者应完整检查源码及所有局部 let 值。

真实完整噪声律下，已验 sandwich 给出 delta 可积且期望至多 400 gamma。已验 gamma 界给出 gamma≤2 n m3，而 paid_moments 给出 n m3≤2 R/(1+x)^3，故期望至多 1600R/(1+x)^3。由 x≥0 可弱化到 1600R/(1+x)，再以高斯密度非负和真实 Mills 界支付 1600R PhiBar(x)。

坏钟部分使用原始乘积律 ν^n、真正坐标 X_i(a)=a_i、乘积独立性及每坐标相同分布。`sourceTruncation_conditioned_sample` 的 map(samplePath) 条件律为 rho^n，坐标 samplePath 在这里定义上等于 id，因此条件测度本身等于 rho^n。把 `sourceTruncation_final_clock_probability_le` 在同一真实能量坏集合上的末项界沿此等式搬移，再相加得到冻结常数。epsilon≤1/800 显式支付旧接口 epsilon≤1/8、1/2、1。没有条件均值为零或原三阶矩有限的假设，也未删除原子或零能量样本。

## 成功凭据

- `check001-exit.json`：第一次完整源码检查 rc0，同一调用使用 -o 保留对象；此后未重编此 producer。
- `audit-exit.json`、`noise-cost-owned-audit.json`：唯一一次实际模块 owner 枚举及传递公理审计 rc0；1 actual-owned theorem、1 public、0 definitions、0 private helpers。公理仅 propext、Classical.choice、Quot.sound。
- `actual-owned-types-scan.json`：1/1 完整类型覆盖；实际 ⋯、…、... 三种省略标记在类型和原审计日志中均为0；源码和对象未变。
- `author-source-scan.json`：冻结头匹配，UTF-8/LF，禁止标记扫描0。
- 原始日志、对象、每次检查 source snapshot 留在服务器 `/root/rivermind-data/shao-lean-20261021/outputs/common-source-noise-cost`；本地只保留紧凑凭据和完整新类型/源码。
- 所有 Lean 命令先 source activate.sh 再 cd，CPU10–13，共用 root-heavy.lock，-M8192 -j4 -DautoImplicit=false。原 SourceNoiseSandwich 已验 source/object 精确复用，0重编。

## 失败与凭据修正

证明首检无失败。已建立审计模板的最初省略扫描按字面反斜线 u 字串计数；发现后仅用确定性脚本重扫同一成功日志/类型，未重跑 Lean。首次重扫因嵌套换行引用报 SyntaxError，完整响应保留在 `actual-character-scan-response.json`；随后 `actual-character-scan002-response.json` 成功。`audit-response.json` 保存最初 Lean 审计响应，`audit-exit.json` 是实际字符扫描后的规范凭据；原日志哈希、源码与对象均不变。

## 下一步及范围

根协调者可以立即分配 fresh gpt-6.1-sol/xhigh 对精确冻结源码/完整实际类型进行独立完整 source-to-statement/proof 复核；可复用已成功的服务器凭据，无需自动重编旧单元。未开 PR、未合并。加权收缩、原始 CDF 回拉、C1/C2 根仍 OPEN。

作者不再拥有本单元写权，且无在途命令。完整机器可读哈希映射及实际模型/用量可见性说明见 `handoff.json`。
