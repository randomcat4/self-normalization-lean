# Unit 183：repair-01 与实际对象证据的最终独立审查

结论：**CORRECT_AND_QUALIFIED_FOR_EXACT_UNIT183_SCOPE，qualified = true**。该资格只绑定源码 SHA256 `9ffdbe105b2cbdc5552acdc11d8942dd08372e8d55574bd65dcad8c186344470`（67573 字节，1262 LF）和对象 SHA256 `65cf3bd6489e09be794ffa6b8686b0ab15df5cf56d27baf192691dfff0b7d6d3`（1607696 字节）。原完整独立源码审查、五个受影响声明的完整新证明与作用域审查、62 个实际 owner 的全部类型、3 个非定理的完整值及逐名递归公理审查已闭合；未发现未覆盖的数学、声明、数据、类型、作用域或公理缺口。

这是同一位独立审查者的续审。审查者不是作者，没有写入或修改作者 Lean 源码，没有运行 Lean、服务器命令、网络、Git、上传或子代理。新增产物只写入 `drafts/oq56/unit183/final-review-01/repair01-and-server-evidence/`；原审查及原 RELEASE0 保留原字节。请求的模型与推理档为 `gpt-6.1-sol / xhigh`；实际模型、实际推理档以及 input/cached-input/output/reasoning-subset 数量没有由运行时暴露，均记为 null。

**完整旧证据的精确复用。** 原完整报告 `final-review-01/review.md` 的 SHA256 是 `679c8b7901b57515c5491e05c391eca0d4c38602c1e4d15d35825865ce620b5b`，15507 字节；六个遗漏普通 Prop 的完整补覆盖 `supplemental-six-props.json` 的 SHA256 是 `14d9d78e886b01551b8030e75b96ad53b54192ec2a0e7b34cf7a9a36fe1ef88d`，39068 字节；原完整独立源码绑定 `independent-static-bindings.json` 的 SHA256 是 `e56eaa8e314d049068a372e648376b65b5dcd3a82cbab6caddeb5ecfc65dded1`。这些记录绑定原源码 `ef6c5a9366fa38256aab911d38bc59fae8145247b00d59d48764376db8bc9260` 的全部 1258 行、19 个完整声明头、3 个完整定义值、全部证明、数学推导和源文范围、实际 API 主源码、54 个正文 let、逐绑定与分支作用域。它们当时明确是尚待服务器证据的源码语义审查，没有声称 elaborated/kernel TYPE 或编译通过。本次只对实际改变的五段证明重新完整审查；其余 14 个声明的头、定义值和证明字节相同，复用原完整审查。

原作者的 165 个命名 Prop 映射原件和计数保留。独立补充的六条是 P03/hExponentNonzero、P04/hTailPositive、P05/hWeakCard、P05/hEmpty、P10/hRange、P11/hCoordinates；原实际命名 have 数为 171。原审查已给出它们的完整源码词法类型、完整证明、字节/行范围、完整 chronological prefix 和适用分支。T03 的 `Ω : Type u` 及旧计划名称的实际消费边界也按精确源码纠正，未以旧计划中同名项冒充新函数或接口的冻结。

**本次精确输入与变化。** 修复作者的 manifest SHA256 为 `78900d883aa3632dc6e4a4093345704d23d39ee043c70e4041a731e8d637fc24`，5027 字节；其中 17 项全部重新按实际字节核对。作者 RELEASE0 SHA256 为 `f06593bbb6603b498c318944fcaef6d6067c669337f28ab10e49b144eb85c307`，683 字节，writer/execution/inflight/children/heldlocks 均为零。本次完整阅读 README、source.delta.patch、diagnostic-delta.json、五个完整新源码块及全部受影响绑定和分支；父级接收记录仅作为来源绑定，未代替独立语义审查。

19 个完整声明头及 3 个全局定义值逐字不变。正文仅 P04、P05、P08、P09、P10 改变。新增数据、函数、实例、公共假设和全局声明均为零；新增普通已证明 Prop 是 P04/hHeadPositive 与 P09/hNaturalCoefficientIdentity，删除的是 P05/hCardEq。故新源码实际命名 have 数为 `171 + 2 - 1 = 172`。受影响范围中独立逐项核对了 98 个命名 Prop、15 个类型和值均未改变的数据绑定、72 个控制语句及其 121 个有类型绑定者、74 行内联函数。12 个改变的 active-scope spine 用无损共享文本视图完整重建；78 个去重绑定公式及其原始完整证明/数据值在精确源码中核对。没有使用摘要代替完整作用域，没有把正在证明的 hInd/hCard/hSupport/hFiberCard/hMap 当作可用前提，也没有把兄弟分支的局部假设带入当前分支。`independent-delta-bindings.json`、`independent-active-scopes-lossless-view.json` 和 `delta-static-check.json` 保存逐项范围与完整 prefix 绑定。这些局部类型称为源码词法类型，不冒称独立导出的 kernel 局部上下文。

| 声明 | 修复稿完整证明范围 | 完整复核与数学结论 |
|---|---|---|
| P04 positive_factorial_prod_le | 159–219 | 重读合并阶乘不等式、零长度归纳矛盾、空尾、正尾及尾部总和。最终自然减法等式前新增 `hHeadPositive : 1 ≤ ℓ 0 := hℓ 0`，由已有逐项正性推出；与 hSplit、hTailTotal 一起保证截断减法消去合法。没有新增假设。 |
| P05 positive_composition_count_eq | 221–317 | 重读正组合减一到真实 piAntidiag 的映射、两个 Fin 界、逐坐标注入、加一逆向覆盖和全部分支。hCard 改为自然 cardinality 等式，实际 Finset.card_bij 直接证明；先 funext 后 Fin.ext。j≤k 分支的总和、j=1、k=j 均适用，j>k 的正组合为空且 choose 为零。真实 Sym/card 主源码继续适用。空集接口使用完整新主源码中的 `Finset.eq_empty_iff_forall_notMem`，大小写正确。 |
| P08 factorial_tail_le_pow | 344–353 | 完整复核 hTail、自然 hBase 与实数幂单调。gcongr 已闭合后移除多余命令；`1≤j≤k` 和自然减法边界保持不变。 |
| P09 finite_sum_pow_eq_multinomial | 355–424 | 完整复核实际 sum_pow_eq_sum_piAntidiag、指数转换的双向覆盖、Fin 范围、注入与系数。新增精确自然数 `∏m_i! * Nat.multinomial = k!` 普通等式，直接应用完整 Nat.multinomial_spec 后再 exact_mod_cast；实数除阶乘前分母严格正。n=0/k=0 使用真实空和、空积与 piAntidiag，不补加正性假设。 |
| P10 factorial_weighted_multinomial_le | 426–892 | 重新完整阅读全部长证明。supportSet、supportCard、supportOrder 在 exponents 前固定；外支集坐标为零、空支集矛盾和 card≤k 的来源正确。supportSum 先证明等于全和再使用全和=k，避免改写 k 后破坏 Fin(k+1) 依赖；sum_map 后的 rfl 只闭合定义相等。完整审查 fiber→正组合注入及 card≤、权重界、支集按 card 重组、choose≤n^j/j!、k!/j! 代价、自然阶乘尾界、几何和归纳、choose≤2^k 及最终乘幂。移除 sum_filter 后多余 rfl 不改数学。n=0、空 fiber、card>k 的零分支均保留；常数 2 和最终幂未丢失。 |

新 Finset.Empty 全主源码包 SHA256 为 `e4d9a4b86411075d77afa4ebbad2d6882675967ea28dfba1cb6f18abbf15344c`，8116 字节，完整读取。它绑定项目固定 mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，真实接口为大写 `notMem`。旧无 v2 choose 头中混入半段 proof 的提取、旧 Markov 局部包的不可消费部分及 factorialBasic 末尾半条 lemma 均未被重新消费；原完整审查使用的修复主源码/API 包继续按原精确绑定复用。

**实际机器结果与历史失败的区别。** 原始 ef6c… 源码的 author-kernel-01 是 native RC 1 / 16 errors；原失败收据保留，未被包装为成功。author-kernel-02 是配置缺 mode、在 snapshot/Lean 前中止，Lean 调用为零，不是第二次证明失败。repair-01 的 author-kernel-03 才是本次精确源码的实际 native RC 0，耗时 7.049260888248682 秒，零 errors，无 timeout，进程组结束，4984 项保护指纹前后相同；产生上述 65cf… 对象。该次有 41 个 warnings：40 个源码建议、弃用或未使用提示，加 134 字节 Lake mathlib dirty warning。严格包装器 success=false 的事实保留，**没有声称 clean 或 wrapper success=true**。

全 owner 审计直接导入同一个既有对象，没有重新编译 producer。owned-object-audit-01 是 native RC 0，耗时 5.460864732041955 秒，无 timeout，进程组结束，4993 项保护指纹相同；唯一 warning 是同一 134 字节 Lake dirty warning，严格包装器同样 false。AUTHOR-STOP SHA256 `e82f93b5a02c100ec60fb15f85f12739b0c5db9043ae6bf3a21979845aedacc7`，1949 字节，绑定停止 producer 自动重编。这里采用 native kernel/实际对象审计及其保护条件，保留包装器对 warnings 的更严格失败状态，没有把 warning 等同于证明错误，也没有删除警告来伪造 clean。

服务器 kernel 收据 SHA256 `1ff093805d4702176e860f7240737c27f550dcec0866d0059efbedc7bf08bc9f`，4712349 字节；审计收据 SHA256 `cbd9ee6513e2fad5ba7ade8d6cce89ca22a4c5e50a7add988b221ee6a9d11701`，4713573 字节。完整原始收据、对象及日志保留在已记录服务器 physical path，没有复制到本地。本审查完整阅读并核对本地双端 hash 绑定的规范 metadata、compact summary 和 dispatch/diagnostics 投影，并明确以这些服务器证据为机器执行来源；没有声称审查者亲自发出服务器命令或逐行读取多 MB 保护日志。完整路径、SHA256、bytes、mtime_ns 保存在 `input-bindings.json`。

**全部实际 owner 的完整类型、值和公理。** 完整阅读审计源码，确认其使用 T01 anchor 的实际 imported-module index，遍历整个 env.constants，按相同 module index 选 owner；没有 namespace、public 或人工声明计数过滤。每项均调用递归 Lean.collectAxioms，并完整打印 TYPE；每个非定理完整打印 VALUE。实际 metadata 文件 SHA256 `23e43c4e053a4904255984975db031abb82421ae575bb52b2b97ce70daa11ff9`，206314 字节；compact summary SHA256 `5cfe79e6361daf6770ffa467872130d97ebe6bec01b882c823c6d56c24b00843`，5317 字节。每一项 rawOwnedJSON 与解码字段、完整 name components（包括 private numeric component 0）、kind、bodyExpressionPresent、levelParams 和逐名 AX 均独立核对。

实际清单为 **62 owners = 59 thmInfo + 3 defnInfo**。其中 19 项与源码一一对应（16 源码定理和 3 源码定义）；其余 **43 项**均由完整实际名称与类型映射确认是生成证明辅助项：D02 1、P02 7、P03 1、P04 7、P05 7、P08 2、P09 1、P10 16、T01 1。并非从源码声明计数推断实际 owner 数。43 项全部是 theorem，包含 omega 产生的具体自然算术证明、simp 的泛型命题重写以及 D02 字面量 2 的 Nat.AtLeastTwo 实例证明；没有隐藏新增数据或公理。泛型 field_simp 类型绑定到 P02 两个完整调用作用域，不捏造环境名称能唯一定位某次 tactic 调用的额外信息。

62 个完整 TYPE 共 1488 行、3 个非定理完整 VALUE 共 24 行，全部实际阅读并逐项解释；`all-actual-owners-independent-map.json` 保存全部完整文本、精确名称组件、逐项 SHA256、源码声明/操作/分支范围与语义映射。三定义的实际 VALUE 分别精确表达 M0*(τβ)^(-1/β)、2*2^(1/β)*scalarMomentScale、ΣY_i(x_i)，没有额外自由数据或隐含选择函数。T01/P03/P11/P12 等实际类型保持任意 Ω:Type u、真实 measure/probability 与 integrability 条件；T02 真实 Real rpow 与 T01 自然 NPow 区别已逐处核对。T03 的 C 存在量词在 Ω/n/μ/Y/q 前，且有 C=sumMomentScale 的明确等式，实际类型没有加入 standardBorel、atomless、同分布、默认 Ω、高矩或自由 factorization 假设。

所有 62 项 bodyExpressionPresent=true，没有 axiomInfo、opaqueInfo、unsafe 声明或未映射 owner。每一项完整递归 AX 都是白名单子集；逐名累积为 propext 62、Classical.choice 42、Quot.sound 53。不同项的 AX 子集差异按真实记录保留，不把全局三项集合复制给每个对象。没有 sorryAx、admit、新 axiom、native_decide 或非白名单依赖。

独立仅用每项原始 JSON、完整 TYPE、完整 VALUE 和 COUNT 记录，在内存中重建原审计 stdout，得到精确 **133500 字节 / SHA256 `e0b5afc0406efd49a62ea72632f300127a65835f616a13fdf2ca6ea9e6f665d9`**，与实际收据完全相同；没有省略标记、截断类型或多余未审查 owner。未在本地落地原日志副本。该检验同时闭合规范 metadata 与服务器原输出的内容关系。

**数学结论与源文范围。** 仍只支付原始 p44 §2(6) 的非负独立坐标和伸长指数矩结论。对固定 0<β≤1、τ>0、M0≥1，定义 C=sumMomentScale>0；对任意可测空间、所有自然 n（含零）、互异也允许的各坐标概率 μ_i、可测且分别 μ_i-AE 非负的 Y_i，只需真实 exp(τY_i^β) 可积且积分≤M0。对每个真实 q≥1，真实 Measure.pi μ 上 S^q 可积，且 `(∫S^q)^(1/q) ≤ C*(n+q^(1/β))`。原 P02 的 Taylor 升 1/β、y=0/ℓ=0；P03 的概率零次矩及 M0≤M0^ℓ；T01 的真实 monomial 可积、有限乘积 Fubini、有限和可积及 integral_mono 前资格；T02 的 ceil q≤2q、真实概率 Lq 单调与完整 Integrable 结论；T03 的常数先固定，均由原完整审查精确复用，并与本次全部实际类型核对相容。

不支付 Hilbert 双对称化、Khintchine、rowtail、DC/SZ engine、root closure 或 p54 被反例否定的 p-rate，不声称 novelty，不声称 OQ56 或任何 root group 完成。无尚待修复的数学或证据缺口。旧阶段的 qualified=false/pending 记录保持历史真实性；本份最终资格以完整复用证据加本次 affected delta 与实际机器证据为合取，仅适用于上述精确 source/object/范围。

本地辅助脚本首次写最终输入清单时，把 amendment-01 的文件名误写成带 multinomial 后缀，发生 FileNotFoundError；这是本地只读文件定位错误，发生在实际 62 项验证之后，没有 Lean/服务器行为。按真实文件名修正并重跑后全部独立静态断言通过；失败事实单独保留在 `local-helper-failure-preservation.json`，不计作证明失败。
