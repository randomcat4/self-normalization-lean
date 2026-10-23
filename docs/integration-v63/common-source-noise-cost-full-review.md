STATUS: CORRECT

JUSTIFICATION: 已完整独立阅读精确新源码、全部局部值、完整冻结声明及唯一实际归属类型，并逐步核对原文到形式陈述和证明。噪声矩支付、真实条件乘积律搬移、真实坏钟事件及常数相加均成立；未发现关键缺口。此结论仅覆盖下列精确版本和本单元范围。

## 版本、独立性与覆盖

- 审查者：`/root/common_source_noise_cost_full_review`，fresh `gpt-6.1-sol` / `xhigh`，使用 math-theorem；未参与该证明的构造或修订，未创建子代理。
- 精确源：`drafts/c12-source-noise-cost/SourceNoiseCost.lean`，108 行，SHA256 `531e2ab17798c7ba7db49d19bd08af7cc1c7cf5ae29b0d23af4873fe30dcda20`。
- 同次首检对象：`3a083bfb23605cfffc4118ecaeefd5d544b2db18e18defc73ca614d2facd925b`。分支 `feat/common-source-noise-cost`；提交 `bf22cc907e5c494a5c7e81899689e3e83093606d`；父提交 `5893148b514a6feaa5f4c36d12485135fae83024`；树 `4986c07b8491c28a101d6610f647e71007c2fe2e`。服务器只读核对 Git 提交内容和工作源的哈希一致，提交只改变新模块。
- 冻结文件 SHA256 `feb3739a9d9427ffffca8b4979066e6c6fc551aaffa2f37716a363dd60646930`；完整候选头 SHA256 `b83255a962bef781a2b36aa8885a376b265d91bc7f0810f4c105a4a7090e9702`。源码 11–29 行完整声明与候选逐字节相符，所有 literal lets、参数顺序、前提及常数未改。
- 实际归属枚举为 1 public / 1 theorem / 0 definitions / 0 private or generated constants。唯一实际类型完整读过，共 11586 字符，UTF-8 内容 SHA256 `aac6ec5cf81cce91f8d5e67e63c66ed45eb603cb7c83873f3ab1386e86e2879a`；与原成功审计日志中 `ACTUAL_TYPE` 到 `END_ACTUAL_TYPE` 的全文逐字相同。没有用打印头或标记匹配代替语义审查。
- 归属覆盖记录见 `coordination/common-source-noise-cost-full-review-coverage.json`。源码 1–108 行全部读过，声明 11–29、证明 31–106、全部局部值均已审查。零定义计数由真正环境 module-owner 枚举和原日志尾记录确认，并非仅按源码关键字推断。

## 原文到声明

完整读取原稿 `C:/game/shao/current/c12/main.tex` 762–850 行及 `supplement.tex` 3882–3908 行，并核对 main 297–322 行的真实权重及预算定义。main SHA256 为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`，supplement SHA256 为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。

本声明精确支付 main 768、777–780 的真实位移与坏钟代价，以及 supplement 3887–3908 的矩/Mills/坏钟组合。`R=truncationBudget ν n x` 是原 `n∫F((1+x)z)dν`，`F(z)=z² min(|z|,1)`；右端 `R*standardNormalTail x` 是 main 306 的 `w_n(x)`。`rho` 是闭截断集合 `|z|≤epsilon/(1+x)` 上真实条件律，`P=rho^n`；噪声是同一 `quadraticFullNoiseLaw rho`，由其实际输入乘积律经 `quadraticFullNoiseMap` 推前所得。该图的 gamma 使用真实条件方差，未把它替换为二阶原矩或零条件均值。

`delta(z)=4(|z.1|+(1+x)|z.2|)` 和 `bad=P.real{energy∉[1/4,2]}` 均为原对象。`energy a=Σ(a_i)²` 没有中心化，也没有除以能量。条件测度/真实噪声/真实 Gaussian 密度与尾均是已有定义的值，没有新增可任意解释的参数。此处给出显式常数 `32768*sqrt(2*pi)+1/standardNormalTail 2+1600`；噪声部分使用已接受的更强真实 Mills 接口，故得到 1600，而原文陈列的较松 6400 并非本声明必须逐字保留的常数。

原始输入仍为真实概率律、原二阶矩可积、`n*Eνz²=1`、原均值零、`x≥0`、`0<epsilon≤1/800` 及原预算上界。没有增加原三阶矩有限、条件均值零、无原子、正能量样本限制或额外噪声假设。此单元是原稿代价估计的形式化组装，不作新的研究原创性主张。

## 完整证明核对

1. **31–47 行：相同对象与可积性。** 局部 `h/rho/P/law/delta/R` 与冻结 lets 逐项定义相同；`gamma=m3/variance id rho`，`m3=∫|z|³dρ`。由 `epsilon≤1/800` 明确推出供旧接口使用的 `≤1/2`、`≤1/8`、`≤1`；`x≥0` 给 `1+x>0`，真实预算非负给 `R≥0`。`sourceTruncation_actual_noise_cdf_sandwich` 收到完全相同的全部原始前提。其第三合取项正是本 delta 的可积性，第五合取项正是 `∫delta≤400gamma`，投影次序正确。
2. **48–61 行：三阶矩支付。** `sourceTruncation_gamma_bounds` 的第七合取项为 `gamma≤2*n*m3`；`sourceTruncation_paid_moments` 的第二项为 `n*m3≤2R/(1+x)^3`，两者的 rho 和真实方差均与本地定义相同。因 400、800 非负，得到 `∫delta≤400gamma≤800(n*m3)≤1600R/(1+x)^3`。最后的 `ring` 只整理乘除法，没有删除任何概率或矩条件。
3. **62–75 行：真实 Gaussian 权重。** 对 `x≥0`，`1+x≤(1+x)^3`；分母 `1+x>0`、分子 `1600R≥0`，故可将上界放松到 `1600R/(1+x)`。`standardNormalDensity` 是 `gaussianPDFReal 0 1`，因而非负。再用 `standardNormal_mills_bounds` 的第一项 `phi(x)/(1+x)≤standardNormalTail x`，乘以非负的 `1600R`，得到 `phi(x)*∫delta≤1600R*standardNormalTail x`。没有把尾与密度方向颠倒，也没有把 `R_n(0)` 当作 `R_n(x)`。
4. **76–91 行：真实条件测度等式。** 新局部 `μ=ν^n`、`X_i(a)=a_i`、`A=⋂_i X_i^{-1}{|z|≤h}`、`μx=cond μ A` 都完整读过。坐标可测由 `measurable_pi_apply`，乘积独立由 `iIndepFun_pi`；每个坐标与原 ν 同分布由真正的 `measurePreserving_eval.map_eq` 给出。`sourceTruncation_conditioned_sample` 在这些实际 iid 输入上给 `map(samplePath X) μx=P`。`samplePath X a=(i↦a_i)` 定义上是恒等映射，故 `map id μx=μx` 给出整个测度的等式 `μx=P`，不是仅某个事件概率相等，也不是把原 ν 直接误写成 rho。
5. **92–106 行：坏钟和总常数。** `sourceTruncation_final_clock_probability_le` 收到相同 `hX/hIndep/hLaw`、原矩/均值/规范化和预算，并用已支付的 `epsilon≤1/8`。其第三合取项是同一 μx 下真实 `energy(samplePath X)` 的坏钟上界，常数恰为 `32768*sqrt(2*pi)+1/standardNormalTail 2`。坐标恒等化及 `μx=P` 把同一个坏事件搬移到 P；`add_le_add` 加上第 3 步噪声支付，最后 `ring` 恰得到冻结常数再加 1600。可积性 `hd` 原样保留到最终合取中。

边界已核对：`x=0` 仍有正分母且所用接口均允许；`n=0` 与原规范化 `0=1` 不相容，并未通过删掉该量词缩小陈述。坏事件是闭区间的真实补集，零能量落在其中；能量等于 1/4 或 2 的样本留在好区间。原子及零坐标没有被去除。条件三阶矩与正方差由既有已接受接口从相同原输入支付，不是新增原始前提。

## 依赖与机械凭据

只复核实际消费接口、字面定义和本单元相互作用，复用旧证明证据，没有重审旧证明或遍历 native dependency DAG。已完整读取消费头：`sourceTruncation_actual_noise_cdf_sandwich`、`sourceTruncation_gamma_bounds`、`sourceTruncation_paid_moments`、`sourceTruncation_conditioned_sample`、`sourceTruncation_final_clock_probability_le`、`standardNormal_mills_bounds`；另读取真实 noise map/law、budget/F、energy、samplePath、Gaussian 密度/尾定义。九个既有库源的本地/服务器哈希逐一一致，具体值保存在审查目录的 `receipt-verification-final.json`。

SourceNoiseSandwich 的根资格记录 SHA256 `6ce709cc673ba87a857f6f4b3297b6bd19febf2e8bbca26d2eb6a759c2a6c67e` 未变；原源 `f972d6271477f37751d8b5b1bfcf74ef55348d00426e8a83b21942f3fd332d79`、对象 `71cc730b05fbd4582076af890a4405ab48cabaa98b05e9d41f34a1116fc7ca91` 均在服务器只读核对相符。该旧源已有完整独审，未再读其旧证明、未重跑其 Lean/公理检查。

- 首次整源 `check001` 实际 rc0，同一调用 `-o` 生成保留对象；原检查源 snapshot 哈希与本次精确源相同。原 log SHA256 `638db0d02ef8f9882dc5b59320453a6882df5b941dca663f5bfe4d6730c9e414`；服务器只有 `check001.log`。日志仅含既有 mathlib 工作目录本地变更提示，无证明错误。
- 唯一实际 module-owner 审计 rc0。完整读过审计程序：遍历实际环境归属而非名字前缀，对每个归属常量调用传递 `Lean.collectAxioms`，打印完整实际类型和所有定义值，并拒绝白名单外公理。原日志完整 AX 头是 `[propext, Classical.choice, Quot.sound]`，尾为 `AUDITED_TARGET_CONSTANTS 1 PUBLIC 1 THEOREMS 1 DEFINITIONS 0`；无定义值记录。原 log SHA256 `d40b336f72e51bf1f23be1d9bd733e54bc80e8ff01b2b81daf8e357f35972001`。
- 完整实际类型 JSON SHA256 `b9e835b5932eed572b6008944f767ec5e52db3dd47305bb65c4f7538cea15ff1`；原 owner JSON SHA256 `b2a9e45de2b86ef26a663132d40924de08d3a173cc7b9d413117eb915a2679be`。
- 原命令均先激活，再进入工作树，CPU10–13、同一 `root-heavy.lock`、`-M8192 -j4 -DautoImplicit=false`。核对固定 Lean `v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。本审查新增 Lean 命令 0、producer 重编 0、旧公理重放 0。
- 源是 UTF-8、LF、无 BOM；禁止的 `sorry/admit/axiom/unsafe/native_decide` 均无。真实 `⋯`、`…`、`...` 在完整类型和原始审计日志中都为 0。

## 扫描修正的来历

作者原审计模板的日志省略扫描曾统计字面反斜线 u 字串。原成功 Lean 响应 `audit-response.json` 和原日志保留，作者首次修正因 Python 引用 SyntaxError 失败也保留；第二次只确定性扫描同一日志和同一类型，正确统计真实字符。最终 `audit-exit.json` SHA256 `2816fe6b263e5dd813446aa213492732438e35dade252f7d7b92d2efedaa76e0`、`actual-owned-types-scan.json` SHA256 `b71a3b331911d23d25692ec7e5fdd929c04ed4ae845370a375fcf3ba77ea3cef` 均与本地及服务器原件一致。检查前后源码、对象、原成功日志均未变。这是凭据扫描修复，不是新 Lean 成功或新证明。

本审查自己的首次日志目标提取正则因过度转义返回空列表；立即以实际行前缀纠正，并完整读取折行的 AX 头及总数尾。两次只读响应保留在审查目录；第一次已经通过的原类型逐字比较及全部哈希不受影响，同样没有触发任何 Lean 或证明变更。

## 裁决边界和释放

本精确版本的唯一冻结定理和完整证明 **CORRECT**；结合已实际成功的整源内核与全部归属传递公理凭据，可供根协调者按精确哈希验收本单元。没有关键缺口或待补声明。

本单元只完成真实噪声/坏钟的 Gaussian 加权代价。weighted contraction、原始 CDF pullback、main 798–850 的后续整体论证及 C1/C2 根仍 OPEN；不据此关闭其他原根组，也不将有限/局部单元计数换算为完成率。

审查者已完成并释放上述报告及 `drafts/c12-source-noise-cost-review/` 的写权；无在途命令，无 PR、合并或 Lean/source/freeze/library 更改。实际 input、cached input、output、reasoning-subset 用量未由平台提供，均记为未知，不估造订阅比例。
