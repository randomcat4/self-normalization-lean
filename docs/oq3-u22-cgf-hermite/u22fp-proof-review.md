# FP253 独立完整最终数学、语义与精确证据审查

STATUS: CORRECT

JUSTIFICATION: 最终 47LF 源码证明了全部实数 c、a、x 与全部自然数 n 上，实际复值实变量函数 c·exp(−(a·y)²/2) 的第 n 阶导数公式。证明内部先建立真实光滑实函数，再用有可微性保证的归纳证明逐阶求导与实到复嵌入相容，随后应用缩放链式法则和已合格 FN251V2 的全阶 Rodrigues 恒等式。完整冻结声明、最终源码、全部实际 TYPE、唯一实际 owner 及同首次原始对象的传递公理收据相互一致；未发现未声明前提、量词缩小、导数总化取巧或关键证明缺口。本裁决仅覆盖 FP253 的缩放与嵌入导数桥，不关闭 Gaussian Fourier/Hermite 积分识别或 OQ3 根目标。

## 审查身份、权限与执行边界

本上下文是唯一 fresh 独立最终审查者 /root/oq3_fp253_final_review，任务指定 gpt-6.1-sol/xhigh，非证明作者。唯一写权限是本报告；没有编辑证明、冻结文件、收据、旧证据、共享实现或协调状态，没有撤销他人编辑。已完整读取并应用 math-theorem 的 SKILL.md、prompt-library.md、openai-workflow.md、lean-verification.md，以及 chinese-output-style/SKILL.md；未使用 math-ultra。

已只读读取 AGENTS.md 中相关恢复/所有权规则、SERVER.md、library/lean-toolchain 和 TEAM 中作者/审查者及服务器执行规则。当前 OQ3 明确恢复条款覆盖历史单独暂停文字。本轮只进行本地文本、字节与证据审查，未联网、连接服务器、运行 Lean/AX、修改缓存、使用 Git/API、创建子代理或联系其他聊天。下面机器结果属于已保存服务器收据的精确复用，不表述为审查者重新执行，也不认证记录时间之后的实时服务器状态。

## 完整阅读与精确字节绑定

下表 FP 文件全部 ENTIRE 阅读；最终源码、首次失败源码的所有证明行及全部实际类型均完整覆盖。严格 UTF-8 解码及本地字节检查确认所有表列文本均无 BOM、CR=0。文件名相对于 C:/game/shao lean/drafts/oq3/。

| 文件 | SHA256 | B / LF |
| --- | --- | --- |
| u22fp-source.lean | 97a170e158d792f49b43c06cb3211389a0713dffaf92b934538a0e609a9b6d14 | 2011 / 47 |
| u22fp-frozen-declaration.lean.txt | 17cb168cdc81c151131f6d0d3cce6b6cf59f1ea6dd383197f1f46fd31d8e4302 | 354 / 7 |
| two-hundred-fifty-third-unit-scope.md | a96dc5ea88b940ecebec079e6bc7073f3645b788a260e0b0ffc503053617e809 | 1315 / 21 |
| u22fp-actual-types.txt | 16da56d59325e7720a2550b49216f3d99040dc07b74b7fb009d35c3d8887d94c | 377 / 7 |
| u22fp-primary-api.txt | 19cfa32f6202b5a8f44742a6c30c45ce695198aface682147e7d98a2bb340cc4 | 3473 / 54 |
| u22fp-Audit.lean | 2c6b08805c7199fc725dbfacc087861e2e603bd3e9c2602d3f621cf1cdb79d93 | 2125 / 49 |
| u22fp-attempt01-source.lean | 2eb90fd99bf7288662fa623cd113e276a6b341df5fe148a3f08b9f0a7a6fd05b | 1995 / 47 |
| u22fp-receipt.json | 4b1246123ef55232266d5ece5950d63205976b14c2023d032615a13ce826cd76 | 7910 / 267 |
| u22fp-audit-record.json | 91b3319370be6d4f055ecf1571ffe00db3355432c28aa9d67368d0771d4929d6 | 3031 / 103 |
| u22fp-build-history.json | b1eb13cda8dd98c218b8bf1300204d3cd6cf83412c265f30b5fa44e2845597f0 | 4533 / 164 |
| u22fp-own-firstO-view-binding.json | d69220542206a69598273d588704c3e3f113726249362ec45800224bc297ab0a | 569 / 10 |
| u22fp-bearing-dependency-binding.json | cdb9936dd6018db6bdbb56c373648ddc32c5ce205231a6cd7fd811ae129dc309 | 1943 / 40 |
| u22fp-server-dependency-binding.json | 52e8e75d9f43e2cdbfd8866ac7e74a64a68228f7bb44938730f56983043b531f | 358 / 11 |

承重 FN251V2 的冻结、全部实际类型/定义值、资格记录、服务器收据和完整最终独立报告均已 ENTIRE 阅读；没有无故重审其已接受的旧 74LF 完整证明，也没有重跑旧 native/AX。对应复用绑定如下：

| 文件 | SHA256 | B / LF |
| --- | --- | --- |
| u22fn-v2-frozen-declaration.lean.txt | 317906269c813616abe1add17f1061347e3d37c76cd2bce77133aadec20cf3c3 | 889 / 20 |
| u22fn-v2-actual-types.txt | 60cfa931d04ccf6806c1a4cbb2c82abae08c5948bbfe8d3659002e51f7ab3d75 | 1477 / 30 |
| u22fn-v2-qualification.json | 159661c5644c9a57cbf590e70dcc4ad430d414ffa492678d7c8cbf8396bd7c26 | 1259 / 25 |
| u22fn-v2-receipt.json | f5a4f057ab49055c347dc8d18c8913cd786846e322ae34d3447592027f6b2117 | 5673 / 190 |
| u22fn-v2-proof-review.md | c4e695b07c106575f1757aa90c8fd892161f976ee876adba93aa6efc0ae26e5c | 20776 / 152 |

另外仅重新计算已合格 FN251V2 源码的字节绑定：46b2178c0dfe2f2bde41e22cf96f1eba1ab4b10977f5d9b60add28563f8aa575，3086B/74LF，匹配资格记录。FP 的承重绑定和服务器依赖绑定同时指向这一源与首原始对象 abb107c3a4f882e04ac92711c619e2ec8d5f5eb02f409d3fb388c9a30c08ef1e；viewSameOriginal=true、sharedCacheWrites=0、noOldSuccessReplay=true。资格记录明确 COMPLETE_QUALIFIED、父已全文读报告、独立审查者已 COMPLETED_STOPPED。原始 FN receipt 中 pending-review 的历史状态没有被改写，后续资格记录与精确报告完成了它原本等待的审查环节。

原始只读材料按指定范围完整阅读：C:/game/shao/current/oq3/proofs/r2/report.md 第 1–158、220–235、493–523 行，整文件 SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55，20102B/523LF；同目录 repair01.md 全 226LF，9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd，5846B；C:/game/shao/current/oq3/verdict.md 全 58LF，fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5，3041B。三者严格 UTF-8、CR=0；没有声称阅读 report 未分配的其他行，也没有编辑 C:/game/shao 的材料。

## 冻结、全部实际类型与承重定义值

本地逐字符检查确认：完整 7LF 冻结声明去掉记录用最后一个 LF 后，恰好在最终源码第 8–14 行出现一次，后面直接接“ := by”。不是只比名称、局部目标或简写签名。冻结包含且只包含 c a : ℝ、n : ℕ、x : ℝ 四个参数，无额外假设、声明内 let、自由 coherence/error 或导数恒等式前提。冻结时间记录 2026-10-27T19:43:04.887665Z 早于两次 native 记录；首次失败与最终成功版的公开声明也逐字相同。

全部 u22fp-actual-types.txt 7LF 为：

    DECL Shao.OQ3.gaussian_hermite_scaled_complex_iterated_derivative
    TYPE ∀ (c a : ℝ) (n : ℕ) (x : ℝ),
      iteratedDeriv n (fun y => ↑c * Complex.exp ↑(-(a * y) ^ 2 / 2)) x =
        ↑(c * a ^ n *
            ((-1) ^ n * Polynomial.eval (a * x) (Shao.OQ3.gaussianHermitePolynomial n) * Real.exp (-(a * x) ^ 2 / 2)))
    AXIOMS [propext, Classical.choice, Quot.sound]
    KIND theorem

打印器的 ↑ 是实到复嵌入，Polynomial.eval 的参数顺序是点记法展开；完整函数、量词、幂、负号、分母 2、a*x 的所有出现均与冻结相同。实际计数为 1DECL/1TYPE/1theorem/0VALUE，statement let=0；没有额外私有或生成 owner 被类型摘录省略。这里只有复值实变量的迭代导数，不是对复变量的全纯求导。

FN251V2 的全部 30LF 实际文件中，5TYPE 分别覆盖 gaussian_hermite_iterated_derivative、gaussianHermitePolynomial.eq_1、gaussianHermitePolynomial、gaussian_hermite_polynomial_recursion、gaussian_hermite_polynomial_first_four。四项为定理；唯一非定理值完整为 fun n => Nat.rec 1 (fun x P => Polynomial.X * P - Polynomial.derivative P) n，类型 ℕ → Polynomial ℝ，SAFETY 为 Lean.DefinitionSafety.safe。这里步骤参数 x 未使用，正是冻结的显式 Nat.rec；H0=1、H(n+1)=XHn−Hn′，H0..H3 为 1、X、X²−1、X³−3X。全 n、全实数 x 的 Rodrigues 实际 TYPE 为 iteratedDeriv n (fun y => Real.exp (−y²/2)) x = (−1)^n Hn(x) Real.exp (−x²/2)，没有点集、阶数或正性限制。

FP 只导入合格 GaussianHermitePolynomialRecursor 与两个 Mathlib 模块，不导入被隔离的 FN V1，也不导入或依赖 FO。V1 的 QUARANTINED_UNQUALIFIED 及旧 unsafe helper 不因本审查而改变；相同全局常量名没有被用来混合 V1 的对象或证据。

## 完整源码的逐段数学审查

第 1–14 行给出的公开函数正是 y ↦ (c:ℂ)·Complex.exp(↑(−(a·y)²/2))，指数先在实数中计算再嵌入复数；右边整个真实实数乘积最后嵌入复数。符号 −(a·y)²/2 没有被误读成 (+a²y²)/2，a 的幂是 a^n，不是 |a|^n 或 a^(2n)。声明没有复参数推广，也没有偷偷把任意 x 改为零点。

第 15–18 行定义实际实函数 f(y)=exp(−y²/2) 与 q(y)=c·f(a·y)。f 是多项式经实指数复合，q 再作线性预复合和常数相乘；fun_prop 在这两个明确表达式上建立 ContDiff ℝ ⊤。这为每个有限阶的真实导数提供平滑性，c、a 可以任意为零或负数。f、q、hf、hq 都是证明内部局部对象，不出现在 theorem 的前提，也不替代原函数。

第 19–28 行的 hembed 是对所有 m∈ℕ、t∈ℝ 的真实导数桥：D^m(↑∘q)(t)=↑(D^m q(t))。m=0 时 iteratedDeriv 的零阶定义使 rfl 成立。继承步 induction m generalizing t 将归纳假设保留为所有点的等式；第 25–26 行 funext ih 因而给出整个第 m 阶导函数相等，绝非对固定 t 的点值等式直接求导。

第 27 行两次 iteratedDeriv_succ 把两边第 m+1 阶导数写成第 m 阶导函数的真实 deriv，并用上述函数等式替换复值导函数。第 28 行从 hq.differentiable_iteratedDeriv m (by simp) 得到实函数 D^m q 在所有实数点可微；所需 m<⊤ 对每个自然数成立。其在 t 的 hasDerivAt 给出真实实导数，再由 HasDerivAt.ofReal_comp 得到实到复连续线性嵌入后相同导数的嵌入，最后 .deriv 正好闭合目标。这一步没有依赖不可微处 deriv 的默认零值：每个用到的实导函数都有显式可微性证据，并由 ofReal_comp 同时得到相应复值函数的真实 HasDerivAt。

第 29–33 行另一个局部 hfun 证明原公开复值函数与 ↑∘q 在每个实数 y 上相同。Complex.ofReal_mul 和 Complex.ofReal_exp 分别把实乘法和实指数的嵌入与复乘法、复指数对齐；没有把复指数替换成实部、模长或别的函数。此处逐点等式只是明确相同函数，不是一条未证明的导数规则。继承分支内的 hfun 与这里的 hfun 属于不同局部作用域，没有覆盖数学条件。

第 34–43 行计算真实实导数 D^n q(x)。第 39 行 iteratedDeriv_const_mul_field 提取 c；该钉死库接口在实数域中不要求 c 非零，c=0 也在接口范围内。第 40 行 iteratedDeriv_comp_const_mul 使用 hf.of_le le_top 提供 ContDiff ℝ n f，因此缩放链式法则给出 a^n·D^n f(a·x)。这里所需平滑性已实际证明，未将函数形式的符号恒等式当作导数规则；接口本身对任意 a 成立。

第 41–42 行将 f 展开为同一 exp(−y²/2)，恰在 a·x 处调用合格 FN251V2 的全阶真实 Rodrigues 定理。第 43 行 ring 只把 c·(a^n·((−1)^n·Hn(a·x)·exp(−(a·x)²/2))) 重新结合为冻结右边 c·a^n·((−1)^n·Hn(a·x)·exp(−(a·x)²/2))；没有除法消去、非零假设或分析步骤藏在 ring 中。

第 44 行依次以公开函数相等、所有阶嵌入桥、真实实导数计算重写最初目标，得到冻结的最终实到复嵌入。第 46–47 行仅结束 section/namespace。全部证明行均在本次完整审查范围内，没有待信任的本单元局部 helper 或省略的定义值。

完整阅读的钉死 primary-api 为：ContDiff.differentiable_iteratedDeriv 和 iteratedDeriv_succ 所在 Defs.lean SHA256 95e6b06e0b5094f2404bef7f871317a22065cf3f4eea2775011be4fff7bdd491；const_mul_field 与 comp_const_mul 所在 Lemmas.lean SHA256 c7104925a2be874d83ce24a5bb02452ff2d6269e768754635f8188fd461989dc；HasDerivAt.ofReal_comp 所在 RealDeriv.lean SHA256 01728182a2668a08c78d03c10aa9487d893247a9be09920bd179eb9921385baa。相应已供全文摘录确认：有限阶导函数可微的严格阶数条件、真实 iteratedDeriv_succ、无非零 c 前提的常数因子规则、带 ContDiff 的 a^n 链式规则，以及实导数嵌入的 HasDerivAt，均按原条件使用。

## 全量词与退化边界攻击

n=0 时 iteratedDeriv 0 是原函数，a^0=(−1)^0=1，合格 H0=1；包括 a=0 时的 0^0=1 约定，右边确为 c·exp(−(a·x)²/2) 的嵌入。证明没有因使用继承步而漏掉零阶。c=0 时 q 恒零，所有阶真实导数均零，n=0 的原函数也零；常数因子接口没有排除这一情形。

a=0 且 n>0 时 q 恒为 c，实际正阶导数零；右边 a^n=0。这里没有除以 a，hf/hq 和缩放接口都对 a=0 有效。a<0 时每次链式求导保留一个有符号因子 a，故确为 a^n；不引入绝对值。c<0 仍只是线性常数因子。x 为任意实数，包含零和负点；所有平滑性与归纳等式都全域成立。全 n 由自然数归纳和合格全阶 Rodrigues 保证，不是只验证前四阶。H0..H3 只辅助解释接口，不作为有限样本代替全阶证明。

## 首次失败、成功原对象与全 owner 公理证据

完整读取失败版和最终版后，本地精确字符串差异验证为：仅第 21、26 行的 (iteratedDeriv m q t/y : ℂ) 分别改为 ((iteratedDeriv m q t/y : ℝ) : ℂ)，其余字节逐一相同。总计增加 16B，LF 仍为 47，公开声明与冻结未改。这明确要求 iteratedDeriv m q 的结果先取实数类型再嵌入复数，修复类型推断形状；没有改变 q、求导阶数、归纳内容或数学前提。

首次 native001 源 2eb90f…d05b、1995B/47LF，记录自然 RC1、4.352911777794361 秒，日志 SHA256 167e01d46ad03200a11c31827e8bb91d5ca6f6122c8b411c14a6ce83e45b3bf0、342B；它是保留失败，不能列为证明通过。最终 native002 源 97a170…6d14、2011B/47LF，记录自然 RC0、4.472578454762697 秒，日志 fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626、133B。交付说明记有零 warnings，本审查未读取远端原始日志，不把该 warning 数表述成新的独立实测结果。

成功版首原始对象为 58a239ad91461e511d623efc44f2ae17247ca96a1f2c6aa87c875110d73a9622、93936B。同一原对象全 owner 审计自然 RC0、5.369777822867036 秒，日志 5cb8e7d56b3be5508e2b6f68be11ad4d1f27b1afb810dc01f68660c5cd5536a8、629B。receipt、audit-record、build-history、actual-types、own-firstO-view-binding 的源码/对象/类型散列和数量相符；本地结构比较还确认完整 build-history 与 receipt.build_history 相同，成功尝试恰为 attempt2。

view 记录链接 /runs/oq3/accepted-source-view/Shao/OQ3/GaussianHermiteScaledDerivative.olean 指向 workspaces/lead-oq3/.lake/build/lib/lean/Shao/OQ3/GaussianHermiteScaledDerivative.olean，精确源/对象散列一致；new_own_firstO_links=1、old_entry_changes=0、shared_cache_writes=0、binary_copies=0，没有以复制二进制或替换旧入口冒充原对象。

完整 49LF Audit.lean 先检查唯一冻结目标确为 theorem，再以 env.getModuleIdxFor? 和 env.header.moduleNames 识别真实所属模块 Shao.OQ3.GaussianHermiteScaledDerivative，遍历全部 env.constants；并非仅审一个名称前缀。每个所属声明均拒绝 axiom，Lean.collectAxioms 递归收集传递公理并强制白名单，打印完整 TYPE；若出现任何 defnInfo 则强制 d.safety==.safe 并打印完整 VALUE。实际模块只有已读唯一 theorem，故 0VALUE 不是漏审定义。全部实际公理恰为 propext、Classical.choice、Quot.sound。最终源码的静态标识符扫描也没有 sorry、admit、axiom、unsafe、native_decide。

钉死环境为 leanprover/lean4:v4.36.0-rc1 和 mathlib 807d3836b165983210ee2ecf3cd28f239436949c。收据的当前阶段 ROOT_OQ56_OQ3_40、CPU36–39/44–47、native -M8192 -j4 与当前 OQ3 恢复授权一致；保留的 memory.phase=ROOT_OQ56_OQ4_39 是沿用的 phase39_memory.py 公式标签，不改变该新执行的 resourcePhase 与 OQ3 CPU 绑定。cacheMutation=false、activeFileOrSlabDiscounted=false，memoryEvents 的 max/oom/oom_kill 均零。本审查不取得新的资源权限，也不把这些历史记录冒充当前实际进程观测。

## 原始来源忠实性与结论边界

report220–235 的三阶 Hermite 修正和 P1(0)=0 是该方向背景；FP253 只把同一合格一元 Hermite 族的全阶 Gaussian Rodrigues 公式推广到任意实尺度/振幅，并严格连接到复值实变量的真实迭代导数。这一新桥可供后续精确 Gaussian Fourier/Hermite 恒等式消费，但本源码没有积分、积分下求导、Fourier 变换、实际累积量组合或二维 Edgeworth 符号测度识别，不能据此宣布最终 Hermite 积分识别完成。

report1–158 的倾斜族、固定 x∈(0,1)、严格 0<β<2/5、矩/非退化/率间隙条件，以及 report493–523 的小胞计数、误差账和远区边界均未被 FP 改写。repair01 全文明确以 Song 2020 Theorem2.1 的 uniform-in-law weak-Cramér Edgeworth 定理提供 s=8 的一致输入；不恢复早期从 Angst–Poly 三角阵列对角化推一致性的已修复论证。外部结果归属仍保留。

repair01 的精确 Laplace 常数为 v_corr=−hat_t0·sqrt(det Delta)·sqrt(Lambda1)，而非错误的倒数因子；FP 没有更改 p54 修复。verdict 保留真正联合非格点仍不足的已接受固定律反例、远频近共振障碍，以及当前正面修复只是充分条件而非最弱刻画。没有重新认证历史优先性或声称首次。

实际概率律密度、全局特征函数可积性、Fourier 反演、完整 Gaussian/Hermite 积分识别、平滑/去平滑、远区、B–D 和 OQ3 正面根目标在本报告中均不关闭。本单元的正确性属于基础导数桥，不是新的研究优先性或根定理完成裁决。

## 最终裁决、完整回读要求与释放

STATUS: CORRECT。没有需要作者修复的关键数学、声明忠实性、承重接口或精确证据缺口。此结论精确绑定 FP253 源 97a170e158d792f49b43c06cb3211389a0713dffaf92b934538a0e609a9b6d14、2011B/47LF，覆盖唯一公开 theorem、全部 1TYPE/0VALUE 和所有局部证明行；冻结 17cb168c…4302、实际类型 16da56d5…7d94c 与首原对象 58a239ad…a9622 不得与其他版本互换。父上下文仍须 ENTIRE 阅读本报告并核对绑定后，才做其自身 qualification；本报告未修改 pending 收据，也未发布、整合或替父上下文接受新根范围。

报告写入后由本审查者 ENTIRE 回读，并在完成回执提供最终 SHA256/B/LF，避免自引用散列。本审查已完成并停止：COMPLETED_STOPPED。唯一报告 writer 权限释放；不释放或变更父作者/分线的所有权。children=0，heavy=0，inflight=0，pending=0，uncertain=0；没有后台调用、检查或后续写入排队。

usage: {"model":"gpt-6.1-sol","effort":"xhigh","source":"本上下文任务配置；无独立平台用量遥测","input_tokens":null,"cached_input_tokens":null,"output_tokens":null,"reasoning_subset_tokens":null,"purchased_credit_estimate":null,"subscription_percentage_allocation":null}。没有把原始 token 数或信用额估计当作订阅百分比的精确分摊。
