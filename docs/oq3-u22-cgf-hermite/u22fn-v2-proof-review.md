# FN251V2 独立完整最终数学、定义值与证据审查

STATUS: CORRECT

JUSTIFICATION: 最终 74LF 源码严格实现冻结的显式 Nat.rec 多项式族，并完整证明同一族的零项/继承项递推、所有自然阶与所有实数点的 Gaussian Rodrigues 恒等式，以及 H0 至 H3 的精确多项式等式。全部 5 个实际所属声明、4 个定理、1 个完整定义值和该定义的 safe 字段均已完整阅读；精确源码的首原始对象及同对象递归公理收据相互绑定，没有发现未声明数学前提、量词缩小或关键证明缺口。本结论只认证 FN251V2 的有限范围，不认证旧 FN251V1，也不关闭 OQ3 正面根目标。

## 审查身份与边界

- 本上下文为独立最终审查者，父上下文为作者；任务配置为 fresh gpt-6.1-sol/xhigh。仅对本报告具有写权限，未编辑证明、冻结、旧证据或协调文件。
- 已完整读取并应用 math-theorem 的 SKILL.md、prompt-library.md、openai-workflow.md、lean-verification.md，以及 chinese-output-style/SKILL.md。未使用 math-ultra。
- 已读取 SERVER.md、项目钉死的 library/lean-toolchain，以及 AGENTS.md 当前 OQ3 明确恢复条款；TEAM 的相关规则作只读参考。当前明确恢复及阶段 40 覆盖历史暂停文字。本任务自身 children/heavy 均为 0，不取得任何服务器执行权。
- 本轮未运行 Lean/AX、未接触远端对象、未上传、未使用 Git/API、未创建子实例或联系其他聊天。机器结果来自下列本地精确散列绑定的服务器记录；不把“读取收据”表述成“审查者重跑命令”。

## 完整阅读与字节绑定

下表所有新版本文件均已 ENTIRE 阅读，随后以严格 UTF-8 解码重新核验 SHA256、字节数及 LF 数；全部无 BOM、CR=0。名称均相对于 drafts/oq3/。

| 文件 | SHA256 | B / LF |
| --- | --- | --- |
| u22fn-v2-frozen-declaration.lean.txt | 317906269c813616abe1add17f1061347e3d37c76cd2bce77133aadec20cf3c3 | 889 / 20 |
| u22fn-v2-source.lean | 46b2178c0dfe2f2bde41e22cf96f1eba1ab4b10977f5d9b60add28563f8aa575 | 3086 / 74 |
| u22fn-v2-actual-types.txt | 60cfa931d04ccf6806c1a4cbb2c82abae08c5948bbfe8d3659002e51f7ab3d75 | 1477 / 30 |
| two-hundred-fifty-first-unit-scope-v2.md | be74bdfcb818fcd45824b73bc5d7fb793ac0a1903096b339d192e6307ff9e8d9 | 2299 / 34 |
| u22fn-v2-bearing-dependency-binding.json | 8ff2a675683da1ab56a7a61e4daa8c1060e45576d1f71d78530029b234025519 | 1272 / 24 |
| u22fn-v2-primary-api.txt | e19f8513c908c4265ccab23c28e04fd7e44d363863f6128301500721f56e24f1 | 1972 / 32 |
| u22fn-v2-receipt.json | f5a4f057ab49055c347dc8d18c8913cd786846e322ae34d3447592027f6b2117 | 5673 / 190 |
| u22fn-v2-audit-record.json | 2af956241855f3ea19b689bf6c3e2a6695fe702a622dd487ea3d57f95edbad52 | 3221 / 107 |
| u22fn-v2-build-history.json | 9f04faed03ac662f29ac029a5de21c7d506f6f717c873195c04355d76e0e3aea | 2268 / 83 |
| u22fn-v2-Audit.lean | 6514a8cdee1a8bfb3c2f5d229bb51a010606e2a56c8644d99b75843edbdbbcd4 | 2273 / 49 |
| u22fn-v2-server-dependency-binding.json | 990fcb8285bb1c4ae2295aab8ceaf6d35d4e780f78ccfb7dd2794d5a1af0237f | 526 / 14 |
| u22fn-v2-own-firstO-view-binding.json | d7ade4cd57bb7ab2ce27dfae298637805fe3b25ee6db1569877e0892aad85cf0 | 573 / 10 |

另完整阅读旧冻结 15LF、旧最终源码 64LF、旧实际类型及全部 5VALUE 共 56LF、旧 scope、receipt、build-history、Audit、server-dependency-binding、own-firstO-view-binding、bearing-dependency-binding，以及旧失败 attempt01 源码 59LF。对旧最终源码与新源码生成并完整阅读了包含全部共同/增删行的本地差异；未使用 Git。主要旧字节绑定为：

| 旧文件 | SHA256 | B / LF |
| --- | --- | --- |
| u22fn-frozen-declaration.lean.txt | a0304e0a164d86b690152d0305542599196bcff48c1c947fbdd21af344728eca | 670 / 15 |
| u22fn-source.lean | 6b8941c7af6c27b1041c9b170950011cc4e270007a933abaf5a9f19db9c39c9a | 2706 / 64 |
| u22fn-actual-types.txt | 77cee9cc4612fc91b973ffe80258c028bc03946295b862035bd15cd3bdcd3cc4 | 2488 / 56 |
| u22fn-attempt01-source.lean | bbb10bb2a580ea40013386cd0e1725bc9ecf601fd51efc4cec82f27af5ce2db1 | 2436 / 59 |
| two-hundred-fifty-first-unit-scope.md | f870f3340c467e8c463a4a6b37b9863a0418f5bd8eb67b6119727a6c5d3eb8ca | 1833 / 28 |
| u22fn-receipt.json | 8e798a34f7d71761742bc07d7b0292cfdebc222258685708391190d1455d10c6 | 8279 / 275 |
| u22fn-build-history.json | df3861267ff35701b4499b7e52e4294a2aaaa21cd08ca23cb45dd8871d57ae76 | 4528 / 164 |
| u22fn-Audit.lean | 2328cf0854df116b067e2d28ca9c8b82dfd5075ed430145404a77504db5ccd9f | 2075 / 47 |
| u22fn-server-dependency-binding.json | 8d22b11e6f6898ab094464f670c79acd77a1ebf5fb865087a2aad952668d7a1b | 817 / 25 |
| u22fn-own-firstO-view-binding.json | 7ded8719c7f7c3b81f1e4a3fd42ff151df6b79b9e9e8652bfaa02b19449bcf0e | 557 / 10 |

原始只读语义材料已按要求阅读：C:/game/shao/current/oq3/proofs/r2/report.md 第 220–235、493–523 行（整文件散列 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55，20102B/523LF）；同目录 repair01.md 全 226LF（9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd，5846B）；C:/game/shao/current/oq3/verdict.md 全 58LF（fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5，3041B）。未声称完整阅读 report.md 未分配的其他行。这三文件也均为 UTF-8、无 BOM、CR=0。

## 冻结声明与完整定义值的比较

严格按“完整冻结 → 完整最终源码 → 全部实际类型/值”顺序阅读。冻结中的完整定义是：

    def gaussianHermitePolynomial (n : ℕ) : Polynomial ℝ :=
      Nat.rec (1 : Polynomial ℝ)
        (fun _ P => Polynomial.X * P - P.derivative) n

逐字符比较确认：上述定义连同完整实现值与源码第 10–12 行相同。三个冻结 theorem 的完整声明（去除冻结文件记录分隔用末尾 LF，保留内部空白、全部量词与结论）分别与源码声明前缀逐字相同，之后恰接“ := by”。这覆盖 recursion、iterated_derivative、first_four 全部三条，不是只比名称或返回类型。没有声明内 let、自由 H 族、自由系数、导数公式假设、隐藏区间或额外可微性前提。

冻结绑定时间为 2026-10-27T19:25:54.077573Z；新模块前置绑定在 19:27:56.720769Z，首检查收据在 19:28:13.240206Z，记录顺序与“完整定义值及三声明先冻结，再实现/检查”相容。与旧冻结逐字比较，Rodrigues 和 H0..H3 两个公开目标保持完全相同；新冻结明确新增公开递推等式并改变定义实现值，未静默修改数学前提。

实际完整 VALUE 为：

    fun n => Nat.rec 1 (fun x P => Polynomial.X * P - Polynomial.derivative P) n

这里打印器将冻结中的未使用占位参数“_”打印为 x，P.derivative 打印为 Polynomial.derivative P；x 未用于步骤值，1 的类型由 Polynomial ℝ 确定。该 elaborated term 正是上述冻结显式 recursor，没有额外系数或递归 helper。定义实际类型为 ℕ → Polynomial ℝ。SAFETY 完整打印为 Lean.DefinitionSafety.safe；noncomputable section 不等于 unsafe。

## 全部实际所属声明的完整覆盖

已完整阅读 actual-types 文件的全部 30LF，无省略、无类型缩写字典。独立计数得到 DECL=TYPE=5、KIND theorem=4、VALUE=1、safe 字段=1、statement let=0、_unsafe owner=0。以下为所审查的全部实际 TYPE 与 VALUE（公理列表对每项均为 [propext, Classical.choice, Quot.sound]）：

    DECL Shao.OQ3.gaussian_hermite_iterated_derivative
    TYPE ∀ (n : ℕ) (x : ℝ),
      iteratedDeriv n (fun y => Real.exp (-y ^ 2 / 2)) x =
        (-1) ^ n * Polynomial.eval x (Shao.OQ3.gaussianHermitePolynomial n) * Real.exp (-x ^ 2 / 2)
    KIND theorem
    DECL Shao.OQ3.gaussianHermitePolynomial.eq_1
    TYPE ∀ (n : ℕ),
      Shao.OQ3.gaussianHermitePolynomial n = Nat.rec 1 (fun x P => Polynomial.X * P - Polynomial.derivative P) n
    KIND theorem
    DECL Shao.OQ3.gaussianHermitePolynomial
    TYPE ℕ → Polynomial ℝ
    SAFETY Lean.DefinitionSafety.safe
    VALUE fun n => Nat.rec 1 (fun x P => Polynomial.X * P - Polynomial.derivative P) n
    DECL Shao.OQ3.gaussian_hermite_polynomial_recursion
    TYPE Shao.OQ3.gaussianHermitePolynomial 0 = 1 ∧
      ∀ (n : ℕ),
        Shao.OQ3.gaussianHermitePolynomial (n + 1) =
          Polynomial.X * Shao.OQ3.gaussianHermitePolynomial n - Polynomial.derivative (Shao.OQ3.gaussianHermitePolynomial n)
    KIND theorem
    DECL Shao.OQ3.gaussian_hermite_polynomial_first_four
    TYPE Shao.OQ3.gaussianHermitePolynomial 0 = 1 ∧
      Shao.OQ3.gaussianHermitePolynomial 1 = Polynomial.X ∧
        Shao.OQ3.gaussianHermitePolynomial 2 = Polynomial.X ^ 2 - 1 ∧
          Shao.OQ3.gaussianHermitePolynomial 3 = Polynomial.X ^ 3 - 3 * Polynomial.X
    KIND theorem

eq_1 不是另一个待假设的递推族：其完整类型只是对每个 n 展开同一常量为 Nat.rec。三个 public theorem 的实际全量类型与冻结量词/目标一致，eval 的参数打印顺序变化只是点记法展开。除唯一 safe 定义外，其余四项全部是 theorem；不存在未审查的额外非定理 VALUE 或 unsafe helper。

## 逐段数学审查

第 1–12 行只导入固定 Mathlib 的多项式导数、迭代导数、指数导数及代数化简工具，随后在 Shao.OQ3 中定义实际实系数多项式族。没有项目 producer 导入。Nat.rec 初值是 1，步骤是 P ↦ XP−P′；n 没有被限制在有限范围。

第 14–22 行的 recursion 命题同时给出 H0=1 和每个 n 的 H(n+1)=XHn−Hn′。两个分支分别由 Nat.rec 零项与继承项计算规则 rfl 证明，确实来自同一实际定义，没有把所需递推公式当成自由输入。由相同初值与步骤的逐阶唯一性，新旧数学族相同；本报告不声称两个同名模块之间存在一个已另行编译的跨模块等式。

第 24–35 行 Rodrigues 目标覆盖全部 n∈ℕ 和 x∈ℝ。归纳显式 generalizing x，因此继承步的 ih 对所有实数 y 成立，funext ih 合法地提供整个函数等式 hfun。n=0 时 iteratedDeriv 0 是原函数，H0=1、(-1)^0=1，simp 闭合真实零阶恒等式。继承步使用实际 iteratedDeriv_succ，将第 n+1 阶导数化为第 n 阶导数函数的 deriv；没有将固定 x 的点值等式错误地用于求导。

第 36–43 行分别建立 q(y)=−y²/2 在任意 x 的真实 HasDerivAt，导数为 −x，以及 g(y)=exp(−y²/2) 的导数 −x g(x)。前者从恒等函数导数依次 pow 2、neg、div_const 2 获得，显式 change 固定函数/标量形状，ring 只证明 −(2·x^(2−1)·1)/2=−x；除数是非零常数 2，没有对 x 作除法。后者使用 exp 链式法则，乘积交换由 ring 完成。这不假设 Gaussian 可微，也不依赖任何积分结论。

第 44–51 行，固定 c=(-1)^n。实际 Polynomial.hasDerivAt 给出 Hn.eval 的解析导数 Hn′.eval；const_mul c 再与 hgaussian 相乘，提供产品 c Hn(x) g(x) 的完整 HasDerivAt。change 将目标的函数乘法明确为逐点 Pi.mul，hd.deriv 因而恰好重写所求 deriv，未将多项式乘法、标量乘法或函数乘法混淆。产品求导的标量式为 c Hn′(x)g(x)+c Hn(x)(−xg(x))，等于 −c(xHn(x)−Hn′(x))g(x)。公开递推经 eval_sub、eval_mul、eval_X 给出 H(n+1)(x)=xHn(x)−Hn′(x)，pow_succ 给出 (-1)^(n+1)=(-1)^n·(-1)，最后 ring 精确匹配符号与因子。该推导对负 x、x=0 及全部 n 均成立，不需要除以 Gaussian 值或引入非零点假设。

第 53–71 行计算的是 Polynomial ℝ 中的精确等式，覆盖全部系数：H0=1；H1=X·1−0=X；H2=X·X−1=X²−1；H3=X(X²−1)−(X²−1)′=X³−X−2X=X³−3X。h0 使用递推第一分量，h1/h2/h3 依次使用同一公开继承方程。h3 的 derivative_sub/derivative_pow/derivative_X/derivative_one 展开真实形式导数，norm_num [map_ofNat] 将 Polynomial.C 上的自然数映射规范化为多项式数值常量，尤其正确处理系数 2；没有自由 coefficient 或新的数学前提。最后 conjunction 恰按冻结顺序收集 h0、h1、h2、h3。第 73–74 行只结束 section/namespace。

本次使用的承重接口均已阅读所供钉死原始摘录：Polynomial.hasDerivAt 为 (fun x => p.eval x) 的导数 p.derivative.eval x；iteratedDeriv_zero、iteratedDeriv_succ 使用真实解析导数。对应源文件 SHA256 分别为 5131dceeeab71a2f61f2b570ebab47e6131e55cbf9a070724226aacf2b35e845 和 95e6b06e0b5094f2404bef7f871317a22065cf3f4eea2775011be4fff7bdd491。DefinitionSafety 的三种构造 unsafe/safe/partial 及 DefinitionVal.safety 字段摘录也完整阅读，其钉死源 SHA 为 3c0a5641cdd36fede77a3a2fd07a151968b78a8cf235fd0e9fe70e82603fff3d。

## 同一首原始对象的内核、公理和安全字段证据

钉死环境为 leanprover/lean4:v4.36.0-rc1、mathlib 807d3836b165983210ee2ecf3cd28f239436949c。新 native001 记录对应最终 source 46b2178…a575，RC0、4.6072957664728165 秒；首原始对象为 abb107c3a4f882e04ac92711c619e2ec8d5f5eb02f409d3fb388c9a30c08ef1e，206752B。build-history 仅有这一新版本尝试，native 日志绑定为 1bb01ce37c5a8ef3d5a372a0991533ef1db40a81dede7cb05f4d9afd9d1bcf9b、973B。交付说明记有 4 个 warnings；本轮未读取远端原始日志，不将该警告数冒称为本审查独立实测的结论。

同一首原始对象的全 owner TYPE/VALUE/safety/递归 AX 审计自然 RC0、5.272824659943581 秒，审计日志 SHA256 为 6927372e8ba0a6b5023071a1682ceea7934c1e6e03cfba564987b451fa40100e、1744B。receipt、audit-record、actual-types 与 firstO-view-binding 的源码、对象、实际类型文件散列/数量完全一致。绑定指向 workspaces/lead-oq3/.lake/build/lib/lean/Shao/OQ3/GaussianHermitePolynomialRecursor.olean；accepted-source-view 中对应新链接指向这一对象，new_own_firstO_links=1、old_entry_changes=0、shared_cache_writes=0、binary_copies=0。没有用另一对象的审计代替首成功对象。

Audit.lean 全 49LF 不是按名称前缀猜所属：它使用 env.getModuleIdxFor? 和 header.moduleNames 对比真实模块 Shao.OQ3.GaussianHermitePolynomialRecursor，遍历全部 env.constants。它先检查三个冻结目标均为 theorem、冻结定义为 defnInfo；对每个实际 owner 拒绝 axiom，调用 Lean.collectAxioms 并拒绝标准三公理之外的任何传递依赖，打印完整 TYPE；对每个 defnInfo 强制 d.safety==.safe 并打印完整 VALUE。故 eq_1 及任何生成 owner 均在相同遍历中，不会因不在三个公开名称数组内漏审。所有实际公理恰为 propext、Classical.choice、Quot.sound；没有 sorryAx、新 axiom 或越过白名单的依赖。源码静态扫描也未命中 sorry/admit/axiom/unsafe/native_decide。

服务器记录使用阶段 ROOT_OQ56_OQ3_40、CPU36–39/44–47、native -M8192 -j4，与当前 OQ3 明确恢复条款相符。内嵌 memory.phase 的 ROOT_OQ56_OQ4_39 属于继续沿用的 phase39_memory.py 准入公式，当前 AGENTS 明确保留该公式；不据此误认为新执行被放回旧 OQ4 所属。记录没有 cacheMutation、OOM 或 max 事件。本审查未开展新资源操作，也不认证记录时间以后的实时服务器状态。

## V1 → V2 连续性与旧证据保留

旧 native001 是 source bbb10b…2db1、2436B/59LF、RC1；旧 native002 是 6b8941…9c9a、2706B/64LF、RC0，并产生旧首对象 1b297a2f01500dd7b123c8973111f4f3d6c8565d254df1ef520eb6fcbabaa985、211208B；旧同对象 AX 收据也为 RC0。这些机器结果保留其原义，不能抹去失败，也不能把两个版本的 source/O/TYPE 文件互换。旧 receipt 仍记 pending fresh full review；新 scope/binding 明确 oldVersionQualified=false，且本轮只读检查未发现旧 u22fn-proof-review.md。旧 V1 不进入未来 qualified publication。

旧实际文件的全部 9TYPE/5VALUE 已完整读过。除两个公开定理和 eq_1/eq_2 四定理外，五个值分别是：自递归 _unsafe_rec、使用 Nat.below 的 _f、以 Nat.brecOn 调用 _f 的公开定义、以 Nat.casesOn 实现的 match_1，以及展开一层公开定义的 _sunfold。具体 _unsafe_rec 的 VALUE 在继承分支再次引用 _unsafe_rec n，确实是实际 owner，而不是注释中的字符串。旧 Audit 没有读取/强制 safety 字段，因此本报告不声称旧 helper 的 safety flag 已被实测；仅据实际 owner/完整 VALUE 与用户 no-unsafe 约束，将未接受 V1 保守隔离为 QUARANTINE_UNQUALIFIED 是准确的版本处理。

新版本选用显式 Nat.rec，并公开零项/继承项计算规则；数学上是相同初值和相同步骤的唯一多项式序列。完整差异只改变定义实现、加入公开递推声明，并将后续原有展开调用改为这一递推接口；Rodrigues 和 H0..H3 目标逐字不变。新代码不导入 V1，不将 V1 的成功重放成 V2 的证明，也不将本报告追认为 V1 的最终接受报告。

新 preflight 记录新 module/source 对象尚不存在、ownHeavyActual=[]、ownLockFree=true，旧 sourceSHA 和旧 firstO SHA 分别保持上述值，oldViewStillTargetsOriginal=true、oldEntryChanges=0、cacheMutation=false。新 view 绑定再次记录 old_entry_changes=0。因二者使用相同 Shao.OQ3 全局常量名，未来合格导入链应只采用 V2，不同时 import 两模块；这在当前 V2 源码仅有 Mathlib imports 的事实下没有形成当前冲突。旧服务器源码、原对象与旧 view 的保留由这些前置/新 view 记录支持；本审查只在本地重新验证记录及本地原始文件散列，未擅自声称进行新的远端不变性观测。

V2 新模块、新 run、新 firstO 与新增 safety 审计针对不同且新冻结的源字节，是必要的新 gate；并非对旧成功 producer/leaf AX 的重复检查。V1 从未 qualified，故不存在改写已接受证明的行为。没有数学前提变化、旧失败丢弃或隐含的跨版本证据拼接。

## 原始来源与可接受范围

report220–235 的对象是二维 Edgeworth 修正多项式及三阶 Hermite 成分；FN251V2 给出的只是实际一元 Hermite 多项式侧的 Gaussian Rodrigues 基础，尤其精确 H3=X³−3X。它既没有引入一个“假设具有所需 Fourier 性质”的自由 H 族，也没有凭这个一元公式建立完整二维修正 P1、实际 homogeneous κ 的组合、Fourier/Hermite 积分识别、实际概率律的密度或反演。FM250 的显式 Gaussian 积分另有资格记录；FN 不导入 FM250，也不依赖仍有 compiled-import 缺口的 FJ247 来完成本证明。

repair01 全文将倾斜族一致性输入明确归于 Song 的 uniform-in-law weak-Cramér Edgeworth 定理，s=8，严格 0<beta<2/5；原报告早期 Angst–Poly 对角一致性不能被本单元复活。report493–523 的每格误差、远区率间隙与严格阈值，以及 repair01 的 small-cell 振荡/边界 Laplace 常数和 p54/v_corr 修正均未由 FN 修改。verdict 中固定律接受反例、定量修复的充分条件性质及未认证历史优先性也保持。

因此实际全 R² 特征函数可积、密度、Fourier 反演、完整 Hermite 识别、平滑/去平滑、远区、B–D 与原始 root 正面目标仍 OPEN。该单元是基础恒等式及前三阶所需多项式，不能由 5actual/3public 等清单计数推出根完成度；没有新颖性声明。

## 最终裁决与释放

STATUS: CORRECT。没有需要作者修复的关键数学、定义值或冻结一致性缺陷。精确 FN251V2 source 46b2178c0dfe2f2bde41e22cf96f1eba1ab4b10977f5d9b60add28563f8aa575 的 3public+eq_1 四定理、唯一完整 safe 定义值及标准三公理证据均在上述范围获得本独立审查通过。此裁决与 V1 未接受历史完全分离。父上下文须 ENTIRE 阅读本报告并核对精确绑定后，才进行其自身 qualification；本报告未改任何 pending receipt，也未进行发布或整合验收。

本审查已完成并停止：COMPLETED_STOPPED。唯一允许写入的 u22fn-v2-proof-review.md 审核 writer 权限释放；不释放也不更改父作者或分线所有权。children=0，heavy=0，inflight=0，pending=0，uncertain=0，没有后台工具调用或后续检查排队。

usage: {"model":"gpt-6.1-sol","effort":"xhigh","source":"本上下文任务配置，未取得独立平台用量遥测","input_tokens":null,"cached_input_tokens":null,"output_tokens":null,"reasoning_subset_tokens":null,"purchased_credit_estimate":null,"subscription_percentage_allocation":null}。未用原始 token 数或信用额推算订阅百分比。报告本身的最终 SHA256/B/LF 随完成回执提供，避免自引用散列。
