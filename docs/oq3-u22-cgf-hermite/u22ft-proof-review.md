STATUS: CORRECT

JUSTIFICATION: 本次 fresh 独立完整最终审查覆盖 FT257 全部 70LF 新源码、完整 17LF 冻结声明、全部 19LF 实际类型、49LF 审计源码及完整本地机器证据。唯一公开声明逐字等于冻结版本。证明以 Fin 2 两坐标完整恢复任意实际指数，保证支撑映像不塌缩；真实 MvPolynomial.eval₂ 展开与 Hermite 系数和均在同一 P.support、P.coeff 上精确重索引，再消费已合格 FR255 的真实可积性和积分合取。未发现关键数学、语义或精确证据缺口。结论只覆盖任意实际实二元多项式的显式高斯/Hermite 积分；实际六阶累积量词的多项式组装、实际 law 密度/全局 CF/反演/平滑/exterior/B–D 与 OQ3 正面根目标仍 OPEN。

审查者为唯一 fresh 独立最终上下文 `/root/oq3_ft257_final_review`，任务明确配置 `gpt-6.1-sol` / `xhigh`，未参与 FT 作者实现或修复。唯一写权限为本报告；不修改源、冻结、证据、状态或共享实现，不撤回其他所有者编辑。已完整读取并应用 math-theorem 的 SKILL.md、prompt-library、openai-workflow、lean-verification 与 chinese-output-style；未使用 math-ultra。已读当前 AGENTS 恢复条款、SERVER.md、TEAM 相关角色/完整审查规则和 library/lean-toolchain。旧 OQ3 暂停已由最新明确恢复条款取代。本轮未联网、连接服务器、执行 Lean/AX、改缓存、使用 Git/API、创建子代理或跨聊天消息；服务器检查只复用保存的精确新源及同首次原对象证据。

1. 完整新源、冻结与字节身份

以下 FT 文件均 ENTIRE 阅读，并从本地原始字节重新计算 SHA256。严格 UTF-8 解码成功，全部 CR=0、无 BOM；B 是字节数，LF 是实际换行字节数。表内文件相对于 `C:/game/shao lean/drafts/oq3/`。

| 文件 | B / LF | SHA256 |
| --- | --- | --- |
| u22ft-source.lean | 2909 / 70 | 6e06b59e0d1dddfef1120a00376c937324748d3d8dea41e38c5c979595a6e95d |
| u22ft-frozen-declaration.lean.txt | 941 / 17 | 2691557efe490f4e0487829c1700c7253fec76d3797d0a3b529a8ade2b2fd7b3 |
| two-hundred-fifty-seventh-unit-scope.md | 1557 / 24 | 0a7da375f930a6012dae95d2a0d004299af29785c0216ad1179ab3d96651f2ae |
| u22ft-actual-types.txt | 984 / 19 | 8ec03dbd037d320662d1ac949e6844f539d48bdfacbe8e7953121cd221408a4f |
| u22ft-Audit.lean | 2126 / 49 | b4f7307b468a5e412d7ba7ad31fd41694692db4de30f84fffab4e85cc9af9bd6 |
| u22ft-receipt.json | 5482 / 186 | ba818fc4f640fc834cedc45234ed0b22e5b5868bceb46957428354c15c832051 |
| u22ft-audit-record.json | 3031 / 103 | 566bf256f6cd0f0b67c6ac69cc70d460f52381bb9de2da9141953f7cbe3e0dec |
| u22ft-build-history.json | 2267 / 83 | fc30441814869bb45092d31763859252b339643b0dedcd9c61492981ef9c116f |
| u22ft-own-firstO-view-binding.json | 577 / 10 | 7e9e23cc227df9644abc786f907c994587aa8a344fb12aad7c753b7ae68ca4bf |
| u22ft-bearing-dependency-binding.json | 827 / 19 | 1675b2393ffacfb6165d412e746879fd8201561c5f1d3f8b3ea7a99bdb9ef8b6 |
| u22ft-qualified-dependency-binding.json | 1758 / 34 | a9b10a7ea49de42f72d6680162f6f97bfee2e01a68650681c58fef6a87a5c9b6 |
| u22ft-server-dependency-binding.json | 393 / 13 | 6a0248580ef25421f27418d478f59f0fca6ed5dc6cf7a2131af783de6d540aa7 |
| u22ft-primary-api.txt | 1907 / 32 | 9db834044fa1ed5ab76264b190902c157009c6b04dfd2fa9cdf12992449727c3 |

从完整源第 9 行 theorem 起至第 25 行精确 ` := by` 前提取声明，只移除证明分隔符并保留末 LF，所得 941B/17LF 与冻结文件逐字符相等；没有空白规范化或对象替换。唯一公开 theorem 是 `Shao.OQ3.pair_mv_polynomial_gaussian_hermite_integral`；实际统计为 1public、0statementlet、0topdef。局部 e/back/s/a 均在证明内具体赋值，不是自由接口、额外前提或结论性假设。

完整实际 TYPE 量化所有 `P : MvPolynomial (Fin 2) ℝ` 和所有 `x : ℝ × ℝ`，无任何假设。两分量都涉及同一函数：负相位 `exp(−I(x1z1+x2z2))`、真实 `MvPolynomial.eval₂ Complex.ofRealHom ![I*z1,I*z2] P` 和标准高斯；测度明确是二维 Lebesgue volume。答案同为实际 P.support 与 P.coeff d、同一 Hermite 家族在 d 0/d 1 阶的值、完整 2π 和空间高斯。`Polynomial.eval` 的实际打印仅展开点记法；没有用定制函数或“所需表示”等式替代实际多项式求值，没有 degree、同质性、局部 x 窗口、density/coherence/desired-error 前提。

2. 承重接口、安全定义与旧合格证据精确复用

FR255 完整冻结 16LF、全部实际类型 19LF、qualification、receipt 和完整独立最终报告 119LF 均 ENTIRE 阅读。其已合格旧 72LF proof 本轮只核字节身份，复用完整报告及精确旧源/首次原对象证据，没有无故重新审查或重跑。以下依赖文件均重新核算原始字节，严格 UTF-8、CR=0、无 BOM。

| 文件 | B / LF | SHA256 |
| --- | --- | --- |
| u22fr-source.lean（仅核身份） | 3175 / 72 | b42dda2bb45128b6beabd03e960722e1224089bdb07995196ea1265529ec3331 |
| u22fr-frozen-declaration.lean.txt | 935 / 16 | bc125639c811fab61a9aa305b46ca0614268eddb497646ab1d3c67cb946b3557 |
| u22fr-actual-types.txt | 986 / 19 | 8398cb95071a8f32045bec66b4565f0a29be3ec05ee61ab7868506593286d947 |
| u22fr-qualification.json | 1230 / 24 | 3b0761719d95e79aa4f6dc84ff6853293a7736d9c37006e73f2aadfb95619606 |
| u22fr-receipt.json | 7907 / 267 | ee29e8e57d964617fbf59630ad4d3eea5d2f0f027e00bf2a5d152435074aa6de |
| u22fr-proof-review.md | 21283 / 119 | 9af83e313a931277ffe8abe4e637a8182caf09b2f99f1fbea34f21a37df4bc28 |

FR 实际唯一 TYPE 对任意有限自然指数对集合 s、任意实系数函数 a 和全部实 x，给真实 Integrable 与同一复有限多项式高斯积分的合取。被积函数逐项是 `(a d : ℂ)*(I*z1)^d.1*(I*z2)^d.2`，答案是同一 s/a 的 `2π∑ a d*H_d.1(x1)*H_d.2(x2)` 乘空间高斯。无表示前提，无次数上界，无额外积分存在性假设。本次第 66 行消费的实参 s/a/x 与该接口逐项匹配。

FR qualification 为 COMPLETE_QUALIFIED，parentFullReportRead=true，独立 `/root/oq3_fr255_final_review` 已 COMPLETED_STOPPED，指定模型/努力同为 gpt-6.1-sol/xhigh。首原 O 为 faffd7f59be43bf03c9b578c4d51dc06d4464b09c84a45db6be1e0b1e147c39e、141376B。原 native002 RC0/5.024525877088308s 和同 O 全所属递归 AX RC0/5.8364792708307505s 精确复用；首 native001 的失败和原作者 receipt 的 pending-review 历史状态均保留。完整 FR 报告覆盖其所有 72LF 最终证明、有限项真实可积、有限和换积分、FQ254 真实二维全阶积分、2π 常数和全部实际 owner；本轮没有把它误作未完成的根结论。

FN251V2 的完整冻结 20LF、全部实际类型 30LF（5TYPE/1safeVALUE）及 qualification 均 ENTIRE 阅读；其旧全 proof、receipt 和完整独立报告只核精确身份并按已全文读取的 FR 报告中 FQ/FP/FN 合格覆盖复用。身份如下。

| 文件 | B / LF | SHA256 |
| --- | --- | --- |
| u22fn-v2-source.lean（仅核身份） | 3086 / 74 | 46b2178c0dfe2f2bde41e22cf96f1eba1ab4b10977f5d9b60add28563f8aa575 |
| u22fn-v2-frozen-declaration.lean.txt | 889 / 20 | 317906269c813616abe1add17f1061347e3d37c76cd2bce77133aadec20cf3c3 |
| u22fn-v2-actual-types.txt | 1477 / 30 | 60cfa931d04ccf6806c1a4cbb2c82abae08c5948bbfe8d3659002e51f7ab3d75 |
| u22fn-v2-qualification.json | 1259 / 25 | 159661c5644c9a57cbf590e70dcc4ad430d414ffa492678d7c8cbf8396bd7c26 |
| u22fn-v2-proof-review.md（仅核身份） | 20776 / 152 | c4e695b07c106575f1757aa90c8fd892161f976ee876adba93aa6efc0ae26e5c |
| u22fn-v2-receipt.json（仅核身份） | 5673 / 190 | f5a4f057ab49055c347dc8d18c8913cd786846e322ae34d3447592027f6b2117 |

唯一非定理值全文为 `fun n => Nat.rec 1 (fun x P => Polynomial.X * P - Polynomial.derivative P) n`，实际 SAFETY 是 Lean.DefinitionSafety.safe。完整 5TYPE 还包括生成展开等式、递推、全部自然 n/实 x 的 Rodrigues 迭代导数式和 H0..H3；H0=1、H1=X、H2=X²−1、H3=X³−3X。本单元引用同名常量沿已合格 FR/FQ/FP 导入链抵达该同一安全 Nat.rec 家族；没有另设 Hermite 族或导入已隔离 FN V1。FN qualification 的全部身份与本地实际哈希相符，首 O 为 abb107c3a4f882e04ac92711c619e2ec8d5f5eb02f409d3fb388c9a30c08ef1e。

时间和版本绑定一致：FT bearing-binding 在 20:02:22.409257Z 诚实记录 FR 当时等待独立最终审查，冻结在实现前，未倒写旧 pending bytes。FR qualification/FT qualified-binding 在 20:10:17.697297Z 完成；FT server-binding 在 20:11:09.659046Z 核同一 FR 源和首 O、viewSameOriginal=true、ownLean=[]、lockFree=true、sharedCacheWrites=0，之后才是 FT 首 gate 的 20:11:16.055732Z 完成记录。qualified-binding 绑定本次最终 FT 源/冻结，完整 FR 合格证据与实际接口、安全 VALUE 阅读范围；没有未合格依赖先行 gate 或旧成功 producer 重放。

3. 全部新源证明与数学语义核查

第 1–8、69–70 行只含两个明确 import、命名空间、作用域、noncomputable section 和闭合。非计算性不等于 unsafe 绕过；新模块只拥有一个 theorem。第 9–25 行就是逐字冻结声明，全部 P/x 的量词不变。

第 27–32 行：`e d=(d 0,d 1)`，`back k=single 0 k.1+single 1 k.2`。hback 对任意 `d : Fin 2 →₀ ℕ` 使用 Finsupp 外延性，并以 fin_cases 枚举 Fin 2 的全部两个元素。i=0 时 single0 取 d0、single1 为零；i=1 时 single1 取 d1、single0 为零。0≠1 由有限类型化简正确处理。因此 back(e d)=d 是整个指数函数的等式，不只是总次数相同、已知支撑上相等或某个有限测试。

第 33–38 行：对 e d=e d′ 用 congrArg back，再用 hback 恢复 d=d′，得全域 Function.Injective e。s 精确定义为 P.support.image e，a k 精确定义为 P.coeff(back k)。任意 k∈s 来自唯一 d∈P.support，且 a(e d)=P.coeff d；对 s 外系数怎样赋值不影响 FR 的有限和。这里没有把不同坐标指数对按总次数合并，也没有把重复映像任取一个系数。

第 39–46 行：heval 对任意实际 z 证明真实多项式求值等于该 s/a 有限和。展开 s/a 后，Finset.sum_image 所需 Set.InjOn 前提由 `(fun d _ d′ _ h => hinj h)` 提供；忽略两个成员证明是因为 hinj 全域成立，前提没有被省略。完整 primary-api 已读：固定 Mathlib Algebra/MvPolynomial/Eval.lean（SHAfb0dd2f7f249f9234abcf7cba2deca0cbdcc6cbf05e07adc18714579ba3a3e72）76–79 的 eval₂_eq′ 明确给 `f.eval₂ g X=∑d∈f.support,g(f.coeff d)*∏i,X i^d i`；Fin 2 具有所需 Fintype，g 恰是实到复环同态 Complex.ofRealHom。

同一 primary-api 的 Finset/Basic.lean（SHA45b548e8d8491da4820c71eb29b0a2c92786f98e300d947e677f6fbe16e6f78a）92–97 通过 to_additive 给出的 sum_image 语义要求索引映射在原 finset 上单射，恰由上述 hinj 提供。没有使用允许合并零项的弱条件版本，也没有在重索引时漏计不同指数的系数。

第 47–55 行：sum_congr rfl 保持同一个 P.support；hback 把 P.coeff(back(e d)) 改回真正 P.coeff d。Fin.prod_univ_two 完整展开 Fin 2 全坐标乘积，Matrix.cons_val_zero/one 恢复替入的 I*z1/I*z2，因此两个自然幂恰是 `(I*z1)^(d 0)` 与 `(I*z2)^(d 1)`。最后 ring 仅把 `coeff*(pow0*pow1)` 重新结合为 `(coeff*pow0)*pow1`；未丢 I 因子、未把 `(I*z)^n` 换成 `I*z^n`，未更换实系数的复嵌入或原多项式 P。

第 56–65 行：hsum 用完全相同的 s/a 展开、同一个 sum_image 单射证明和同一 P.support 的 sum_congr，把每项系数还原为 P.coeff d，并把 Hermite 阶数 e(d).1/e(d).2 还原为 d0/d1。逐项同一性包含两个 Hermite 因子、各自原空间坐标和乘积次序；不存在只核左右总和度数、重定义目标系数或把 Hermite 和当成假设。

第 66–67 行：FR255 同时给所构造有限和的真实 Integrable 和其真实积分值。反向 heval 在任意 z 上改写两个分量的同一有限和，hsum 改写答案中的实系数和；simpa only 不改变测度、相位、Gaussian、2π、x 或 P。结果因而是冻结的真实可积性与积分合取。不是先使用不可积函数的总化积分零，再借零等式冒充可积；真实 Integrable 直接由合格 FR 的第一分量逐点等同移交。

独立符号核对：FR 给任意有限 `∑ a_(m,n)(I*z1)^m(I*z2)^n` 的负相位高斯积分为 `2π∑ a_(m,n)H_m(x1)H_n(x2)exp(−‖x‖²/2)`。两坐标指数编码使其有限和逐字代表实际 P(I*z1,I*z2)，并使答案逐字是 P 的支撑/系数 Hermite 转换。负相位配 I*z 导出正 probabilists-Hermite 符号；例如一次项给 x 而非 −x，二次项给 x²−1。2π 是未归一化二维积分常数，没有添入 Fourier 反演的归一化因子。此符号核对不替代上述全域证明及源绑定机器证据。

边界逐项覆盖：P=0 时 P.support 和 s 都为空，两和零，真实零函数可积；常数 P 的唯一可能非零指数是零指数，back(e0)=0、两个零次幂和 H0=1 保留；单变量项在另一坐标仍用零指数。系数可零、负或互相抵消，无除以系数；不同指数可有同一总次数，由 e 全域单射保留各项。任意高自然次数均覆盖，没有六阶截断或同质性前提。x 的零坐标、原点和负坐标均允许，无除以 x、开方或非零消去。实到复嵌入使所有实系数诚实保留；没有从有限多项式推断无穷级数或一般函数展开。

4. 全部真实所属类型、递归公理与保存检查

actual-types 全文实测有 1DECL/1TYPE/1KIND theorem/0VALUE，名字集合确定性等于 receipt.all_owned_names，唯一就是上述公开 theorem。没有被省略的私有/生成 owner、模块级 def 或非定理值；0VALUE 来自实际枚举，不是只打印公开名的结果。其 TYPE 的完整量词、测度和两分量已逐项与冻结/自然语言范围核对。最终源码 sorry/admit/axiom/unsafe/native_decide 的完整标识符扫描为零。

Audit 全 49LF 已读：先确认冻结目标存在且 isTheorem，之后遍历 env.constants 并通过 getModuleIdxFor?/header.moduleNames 判定实际模块所有权，不按名称前缀筛选。每个实际 owner 拒绝新 axiom，Lean.collectAxioms 递归依赖仅允许 propext、Classical.choice、Quot.sound，完整打印 TYPE；任何 defnInfo 必须 safety==safe 且完整打印 VALUE。强制所属集合非空、唯一 frozen target 恰为 1。实际审计输出只有该一项 theorem，AX 恰为标准三项，无新增或不允许的传递公理。

确定性比对显示 build-history 的唯一一条记录与 receipt.build_history 逐字段相同；audit-record 全部字段与 receipt 对应字段逐字段相同，没有偏差。首 native001 绑定本次 6e06…e95d 源、2909B/70LF，自然 RC0/4.983537191525102s，时间 20:11:16.055732Z；日志 133B、SHAfe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626。交付说明为 0warnings；本地所读 JSON 未单列 warning 数，原服务器日志正文不在本轮阅读范围，故不将其冒称为本审查者独立日志实测。

首次原始 O 为 4d847b2372840750165d8372026e435c155ba6986702e717e1b8653e9fc36133、145096B。随后同一原 O 的全部真实 owner/递归 AX 审计自然 RC0/5.771003734320402s，时间 20:11:37.242201Z，日志 1236B、SHA170567789f987f293757c575369fc8b9c52cd4ce91b9b8526284a6e2bb06e145。Audit 源和实际类型原始 SHA 与 receipt/audit-record 完全匹配；没有 FT 失败稿、旧成功重放或把未知在途请求当通过。

own-firstO-view-binding 将 GaussianMvPolynomialHermiteIntegral.olean 的同一首次原对象链接入 accepted-source-view 的同模块路径，source/firstO 与 receipt 一致；new_own_firstO_links=1、old_entry_changes=0、shared_cache_writes=0、binary_copies=0。server-binding 的依赖同原 O 与 qualified-binding 一致；no_success_producer_replay=true。作者保存 receipt 的 pending fresh review 是当时的诚实历史状态，本报告不改写；父全文读取本报告后才可另写 qualification。

环境钉死 leanprover/lean4:v4.36.0-rc1，mathlib807d3836b165983210ee2ecf3cd28f239436949c。外层 resourcePhase=ROOT_OQ56_OQ3_40、CPU36–39/44–47、native-M8192/j4 符合最新 OQ3 恢复；memory 内 phase39 是共用 phase39_memory.py 公式历史标签，不改变外层实际阶段。native/audit projected_admission_used 分别169352658944/169352339456B，均小于180GiB guard；过程预算140GiB、系统/其他reserve60GiB、hard200GiB，cacheMutation=false、activeFileOrSlabDiscounted=false、max/oom/oom_kill=0。原始 raw 使用量诚实保留，只扣 bounded clean inactive_file。本轮没有独立重观测服务器进程/锁，也没有运行本地或服务器 Lean；复用对象身份与保存的源绑定机器证据。

5. 原始来源忠实性与未覆盖范围

只读原始 report.md 的指定 1–158、220–235、493–523 行已按范围完整阅读；repair01.md 全 226LF、verdict.md 全 58LF ENTIRE 阅读。原始文件身份重新核算：`C:/game/shao/current/oq3/proofs/r2/report.md` 20102B/523LF，SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55；同目录 repair01.md 5846B/226LF，SHA9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd；`C:/game/shao/current/oq3/verdict.md` 3041B/58LF，SHAfd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5。全部 CR=0，原始内容未改动。

本结果为 report220–235 的有限 Hermite/高斯修正提供真实实际 MvPolynomial 转换桥，比显式 s/a 接口多闭合实际 P 的求值、真实支撑/系数和两坐标指数的精确识别。它没有定义或证明实际六阶累积量词组装的 P，也没有把实际 Edgeworth 系数、P1(0)=0 或统一系数界自动识别到这些多项式。后者属于下一个源绑定消费者；这里不能把“任意 P 都能积分”误作“实际所需 P 已构造并识别”。

实际随机律的密度、全局特征函数可积性、Fourier 反演、平滑/去平滑、exterior、B–D 与正面 OQ3 root 均保持 OPEN；显式高斯多项式的真实可积性不能代替实际随机律的全局 CF 或误差估计。原始固定 x∈(0,1)、严格 beta<2/5、倾斜矩/协方差非退化/正则鞍点/全局唯一性和独立率间隙/远区义务均不变。本定理对全部空间 x 的恒等式不提供这些原随机模型条件、统一误差常数或原参数序列。

已接受真实联合非格点反例与远频近共振障碍、p54 修补和 `v_corr=−hat_t0·sqrt(detDelta)·sqrt(Lambda1)` 保留。repair01 指定的 Song2020 Theorem2.1 uniform-in-law weak-Cramér、s=8 外部结果归属保留，不恢复 report 原始 Angst–Poly 对角统一性推断。此处是经典有限多项式表示与已有高斯/Hermite 积分的形式化桥，不认证历史首次、最优前提或研究核心新颖性。

6. 最终裁决、全文回读与释放

STATUS: CORRECT。无关键缺口；本裁决绑定本报告列明的精确 FT 源/冻结/范围/全部实际类型、FR 精确合格接口和完整旧报告、FN 同一安全 VALUE，以及首 native001/同首次原 O 全 owner 递归 AX 证据。后续数学或证明字节改变必须按实际影响范围重评；不能自动沿用本报告到实际六阶组装或更强根目标。

本报告定稿后由审查者 ENTIRE 回读；最终 SHA256/B/LF 随完成回执返回以避免自引用散列。父实例必须 ENTIRE 读取并核精确绑定后才可 qualification，本审查者不写 qualification 或其他状态。

COMPLETED_STOPPED：全文回读并返回完成回执时，释放本报告唯一 writer/审查权限，之后不再写任何文件；不改变父作者、分线或共享所有权。children=0，heavy=0，inflight=0，pending=0，uncertain=0；无服务器、上传、Git/API、子代理、跨聊天消息或排队写入遗留。

usage: {"model":"gpt-6.1-sol","effort":"xhigh","context":"fresh","source":"本上下文明确任务配置；无独立平台用量遥测","input_tokens":null,"cached_input_tokens":null,"output_tokens":null,"reasoning_subset_tokens":null,"purchased_credit_estimate":null,"subscription_percentage_allocation":null,"actual_usage_available":false}。未编造用量或将 token/信用额估计当作订阅百分比精确分摊。
