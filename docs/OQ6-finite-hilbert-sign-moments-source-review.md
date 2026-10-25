# 单元185独立完整源码审阅

状态：`SOURCE_REVIEW_COMPLETE_MACHINE_PENDING`。对下述精确候选，我的数学判断为 `CORRECT`：完整源码证明了冻结的有限 Hilbert 符号矩接口，未发现需要修改前提或证明的实质数学缺口。此判断不等于 Lean 已接受源码；当前没有我收到的内核、模块全部所有者 TYPE/FULLVALUE 或递归公理资格。

唯一审阅目标为 `author-01/FiniteHilbertSignMoments.lean`，SHA256 `f5a30c5f0466413355b5deaacf5075d9f73bba9b2dff1d0b81905cbdf3a33fd6`，39654字节、796行。已完整读1–796行、34个源码声明、15个定义值与19个证明体（5公开、14私有），并核对 v1 冻结和修订01–04。34是源码声明数，绝不是实际生成所有者数。全部公开目标仍任取 `n,d : ℕ`、真正 `EuclideanSpace ℝ (Fin d)` 向量族及实数 `q ≥ 2`；常数的完整值先固定为2。

完整阅读的原文 p44、p51、p54 已独立核对，SHA256分别为：

- p44：`3d6a674252a81b7ca051fd54aa0a621511ebce94af2f0bdf9b4eca8715bc5239`；
- p51：`96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`；
- p54：`e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`。

完整原文与形式陈述之间的对应范围只到 p44 §1(3) 的固定向量有限符号矩，以及同一个真实 `BrownianSup.radMeasure` 的积分版本。向量族可直接取矩阵的列；能量是列欧氏范数平方和，因而是 Hilbert–Schmidt 能量。本件不闭合 p44(2) 的鬼样本交换、标量二阶混沌、随机矩阵条件化或后续 Fubini。p51 S18 的原非线性基核集中仍归 Shao–Zhou Lemma6.1；p54 对过强条件p矩变化速率的反例、仅收敛/统一有界的修正，以及严格好事件余量均保留。无183/184数学依赖、根闭合或新颖性主张；C2/C12/OQ56仍OPEN，OQ3仍PAUSED_BY_USER。

## 源码到证明的完整覆盖

| 实际源码行 | 声明与核查结果 |
| --- | --- |
| 18–32 | 8个公开定义：true/false为±1；signPath落在真实实路径；cubeMean为全部 `2^n` 路径的质量1平均；signSum/pathSum保持整向量和；energy、moment和常数2的值忠实。 |
| 34–46 | 7个私有定义：标量和、坐标出现次数、全偶条件、配对符号、真实内积乘积、有限allocation、阶乘比。pairCount的两个端点都在同一个 `r` 求和体内；没有漏重数。 |
| 48–62 | `cubeMean_product`：有限乘积的和公式与每坐标除2严格一致，包括空指标。 |
| 64–95 | `sign_power_mean`：偶见证与除2余数分别证明±1偶/奇幂；非全偶时选择一个奇坐标使乘积为0。 |
| 97–112 | `pair_sign_mean`：先按每个坐标聚合两个端点的全部出现，再用上项。 |
| 114–213 | `hilbert_even_domination`：真实内积完全展开整个范数平方，再取k次幂的所有配对词；同样展开标量平方。平均后全偶指标恰为0或1，剩下的可能负内积乘积先取绝对值，再逐因子用Cauchy–Schwarz。没有逐行绝对值替换或维数损失。 |
| 215–337 | `scalar_even_multinomial`：标准多项式展开、全偶筛选、与allocation的精确双逆。`m_j ≤ Σm_j = 2k`和偶性保证 `m_j/2 < k+1`，取模在实际支持上不回绕；两个逆与系数阶乘恒等式均已支付。 |
| 339–361 | `even_factorial_lower`：0基例与两步阶乘递推；归纳乘子非负，第二个奇数因子至少1。 |
| 363–410 | `squared_multinomial`：同一allocation上平方和的多项式展开；`m_j ≤ k`给普通取模双逆；系数分母由阶乘正性非零。 |
| 412–437 | `evenFactor_bound`：0基例为1≤1；阶乘比递推为 `(2k+1)γ_k`，再与 `(2(k+1))^(k+1)`比较。 |
| 439–491 | `scalar_even_bound`：逐allocation相乘阶乘下界，严格正分母使倒数比较方向正确；所有待乘的偶次幂积非负，a无需非负假设。 |
| 493–504 | `hilbert_even_bound`：依次组合整向量支配、标量偶矩及阶乘比界；能量幂非负。 |
| 506–527 | `rpow_tangent`：0<r≤1上凹性，只在1处求导；x<1用右端点导数、x>1用左端点导数，分母严格正。x=0和r=1合法。两次dot调用的独立完整接口补充见scope-api-supplement.md。 |
| 529–600 | `cubeMean_rpow_le`：B=0时由正权及逐项非负推出每项0；B>0才定义并除以B。cardinality给平均1，切线界与非负实幂乘法恢复尺度。 |
| 602–638 | `cubeMean_Lp_mono`：q>0、q≤p给p>0与0<q/p≤1；非负底数实幂复合及正指数保序，包含零底数。 |
| 640–641 | `hilbertConstant_pos`：由完整值2。 |
| 643–714 | `finite_hilbert_sign_moment_bound`：k=ceil(q/2)、p=2k，q≤p≤2q；有限Lp单调接偶矩界。平方根底数非负、p>0，实幂反射/复合给p次根上界；仅需能量非负，再用√p≤2√q。 |
| 716–747 | `radMeasure_atomic`：真实乘积测度与有限Dirac和在每个可测乘积矩形完全相同。公开边缘概率实例给SigmaFinite；矩形可测性及每个Dirac应用的条件逐项存在。 |
| 749–774 | `rad_integrable_and_integral`：任意实函数在Dirac下有限范数与路径可测单点给可积；有限和及非∞缩放保持可积，`toReal`精确变为 `2^(-n)`，积分等式正确。未添加全局可测性前提。 |
| 776–777 | `pathSum_signPath`：两个完整定义逐字归约相同。 |
| 779–791 | `rademacher_hilbert_moment_bound`：把真实积分桥用于冻结的范数实幂函数，恢复moment并调用全实q界；确实同时返回可积性。 |

## 边界与接口条件

n=0时Bool函数空间有唯一空函数，平均质量1；k=0的辅助恒等式保留自然数0次幂为1。n=0且k>0时配对词类型为空；d=0时欧氏向量全为0。公开目标q≥2保证正实幂，因此空和与零能量的矩为0。最终取根使用的是允许非负底数的 `Real.rpow_mul`、正指数保序和平方根恒等式，没有暗用能量正性。所有重索引分母都是正阶乘或正2次幂，不需要n>0或k>0。

已读全份作者 source-to-statement、handoff、source-spans、actual-source-map、library-calls、frozen-plan-dispositions 的实质字段，并由完整源码解析其无损前缀/分支。已读62个非平凡显式接口的完整主源声明及环境、生成接口的原声明/属性/环境，另核对88个基础接口的预期契约在实际使用处的实例与义务。它们都不是实际展开TYPE；实际TYPE仍待服务器。主源中额外核对 `ConcaveOn.le_slope_of_hasDerivAt`、`ConcaveOn.slope_le_of_hasDerivAt` 和 `Integrable.smul_measure`。全部使用条件均在实际作用域中成立。

静态映射有局部词法解析不精确：hfilter受限求和被误拆成若干伪binder，同名家族的actualSites有宽泛候选集，两次割线dot接口未进显式records表。它们没有改变源码或数学陈述。本审阅以实际源码为依据，在scope-api-supplement.md中消歧和补齐；不能把490个map条目当作490个真实binder，也不能把 `unresolvedExpectedTypes=[]` 当作类型正确凭证。基础 `two_mul` 的元数据只写ℝ特化，但其实际第74行使用是ℕ上的 `l+l=2*l`；已按实际自然数实例核对，不伪称该元数据是actualTYPE。

复用父级 `parent-source-intake.json`（SHA256 `6924941a58e1fb644bdbf55d4e73fc68338748fc65feb1e86eaa9f72dc3b8f8f`）的工件/源码区间完整性检查，不重跑7140个已绑定引用检查；其结果仅是静态输入证据。本次独立数学结论来自完整实际源码和原文阅读。

## 后续资格边界

待同一上下文收到精确source的实际server kernel receipt，以及模块索引的全部所有者清单：逐owner完整TYPE、每个非定理FULLVALUE、每owner递归AX。实际owner数目前UNKNOWN；只允许propext、Classical.choice、Quot.sound。届时复用本次完整证明审阅，核对实际生成类型/值、覆盖集合、源哈希与公理；不需要因获得机器元数据而自动重读全部不变证明。任何源码数学变更只使受影响部分证据失效。

本审阅者不是作者；只写final-review-01目录，未改任何源码、旧证据或共享文件；Lean/server/network/Git/upload/cache/children/locks均为0。
