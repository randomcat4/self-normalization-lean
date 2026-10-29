# Unit277 repair01：实际八条 native 错误的同作者修订

状态：REPAIR_CANDIDATE / PENDING_AFFECTED_SOURCE_REVIEW / NOT_KERNEL_CHECKED / NOT_QUALIFIED。本报告是作者对已冻结五声明内实现修复的说明，不是独立审阅或服务器通过证明。

## 精确输入与实际失败

本轮由 repair01-ACTIVATION.json 明确重激活同一作者；授权 SHA256 为 c3da0fdafd4c7723e77796558040c3038cd5b668cd05bd3d22e4f6b123af4288，16770B。首次写入前，全部68个绑定输入的 SHA256 与字节数一致；最终封包前再次检查。唯一写目录为 author-repair-01。旧 author-01、所有冻结文件和既有独立审阅/失败收据保持原字节。

修复依据是 native01-terminal-inspection.json 的八条完整诊断，不是另一单元的计数或描述。其实际源为 d183e84abbb1d37364b3272f465150e1018a5a60349a5b7eb2afd56783265939，15280B/359LF。原 native01 RC1，5.408928487449884s，派生8 errors、6 warnings，无对象；allOwnedEnded=true、protectedDerived=35812、preservation_equal=true。它没有超时、heartbeat 或错误数量上限失败。原始大收据/日志留在服务器，未复制到本地。

旧源具有完整独立 SOURCE/proof 审阅的 SOURCE_ACCEPTED_PENDING_KERNEL 结论；这没有把失败的 native01 变成通过，也不自动覆盖新改动。本次由父级安排同一独立审阅者对受影响证明、完整上下文与精确新哈希作复核，然后才可运行新整体服务器检查。

## 修订产物与未变边界

完整修订源为 FiniteExceptionalBlockOptimization.lean：
- SHA256：0073a6b41714f383603bd0b332da818a6862527d688cc9afd788c703844ecc42；
- 15694B、371LF；
- 精确冻结 HEAD 83LF、PROOF 280LF、PRE/CLOSE 共8LF。

完整五份 PROOF、ALL-HEADS/ALL-PROOFS、DECLARATION-ASSEMBLY、SOURCE-PROOF-MAP 和 CHANGED-PROOF-COVERAGE 均随包交付。计数、范围与哈希由这些实际组件派生，源码声明数量不是内核实际 owner/TYPE/AX 数量。

冻结的 PRE、CLOSE 和五个 HEAD 均逐字节复用。仅 H02、H03、H04 的实现有变，合计七处实际行差异；相邻的 H03 M/K 数值转换修复形成同一差异块。H01 与 H05 的完整 PROOF 字节保持一致：
- H01：9f64b094035bd02b525b729e0344c5aa90ccb1dac264ac375e5119b05abbb4b4；
- H05：612ce9c9d1992c1874f4c3965f80ffadf4a6588f34a4732672a144b80c1f73b1。

没有新增顶层 helper、定义、公开假设、常数、guard 或预算选项。仍仅有冻结的 autoImplicit=false。未修饰六个 warning，也没有把 warning 当作新增 error。所有引用供应者保持原证据，不重跑或重审旧 proof/AX。

## 八条实际诊断与精确修复

下表的旧行号来自实际 native01；新行号来自修订源和精确 marker。完整原诊断 SHA256、正文、组件哈希、旧/新差异行与相互作用范围在 CHANGED-PROOF-COVERAGE.json。

| 序号 | 实际旧源行 / 所属证明 | 实际错误 | 修复的新源行与内容 |
|---|---|---|---|
| 1 | 76 / H02 | add_le_add_right 产生“待定项+Na≤待定项+Nmax(a,0)”形式，与目标“Na+Ky≤Nap+Ky”不匹配 | 76–78：先展开 ap，显式获得 Na≤Nmax(a,0)，再只用该不等式线性推导两侧加同一 Ky |
| 2 | 133 / H03 | exact_mod_cast 没有将局部 N 展开为 n 的实数转换 | 136–137：先 change 为 (2:ℝ)≤(n:ℝ)，再使用原 hn |
| 3 | 136 / H03 | exact_mod_cast 没有将局部 M 展开为背景基数的实数转换 | 141–142：先 change 为 0<(B.card:ℝ)，再转换原 hB 的 card_pos |
| 4 | 137 / H03 | exact_mod_cast 没有将局部 K 展开为异常基数的实数转换 | 144–145：先 change 为 0≤(A.card:ℝ)，再转换 Nat.zero_le |
| 5 | 193 / H03 | T 已去零分支，但 n 的显式转换和局部 N/X 未在两侧同步展开，残留一个定义等式 | 202：simp only 中显式加入 N、X，只展开原局部定义，不添加数学事实 |
| 6 | 207 / H03 | zero_pow 的指定化简没有把目标中的 0²化为0，期望目标与已有非负乘积类型不一致 | 215：使用 pow_two 与 zero_mul，把 0²直接展开为0·0再化简 |
| 7 | 247 / H04 | exact_mod_cast 在局部 N 别名下未得到目标实数不等式 | 256–257：先 change 为 (4:ℝ)≤(n:ℝ)，再转换原 hn |
| 8 | 270 / H04 | 展开 c 后原 n 的显式转换与其他局部 N 共存，field_simp 后保留混合表示的倒数项，ring 无法闭合 | 286–288：以 change 把完整分子目标统一写成同一个 N，包括原 F/((N−1)(N−2)) 偏移，再执行原 field_simp/ring |

第1条不依赖新的加法序 API：线性推导只使用 N>0 与 a≤max(a,0) 导出的已知乘法不等式，数学内容与旧证明相同。

第2、3、4、7条只把局部定义在转换 tactic 前显式暴露；所用自然数/集合假设没有变化。

第5条精确规范 T 的两侧表达式：T 原定义、Q>0 后的 if_neg、N=n 的实数转换、X=∑b−Nc。它不展开/替换背景能量，不改变零约定。

第6条只是目标零平方的无条件恒等化简。右端非负性仍来自 N−1>0 与 C≥0，没有增加前提。

第8条保留完整原 c=F/[(n−1)(n−2)]。新 change 的左右两边与旧目标定义相等；所有分母统一使用同一 N 的语法形式，清分母仍只用 √N≠0、N−1≠0、N−2≠0。没有消去 F、删除原偏移或更改 Studentizer。

这些修复没有发现需要修改冻结接口的数学反例；它们是实际实现/规范化错误的修复候选。作者没有运行新 Lean 来判定这些候选是否已通过。

## 修复后的完整证明语义与相互作用

H01 未改。它用真实 B/A 分割和精确有限平方展开给 Q=Qb+QA+MK/n·(μA−μB)²。其局部有限集均值身份先分空集与非空集，空 A 不会触发对 K 的非法约去。旧独立 SOURCE 对该精确证明体的覆盖可按相同哈希复用；不把它称为已有成功对象。

H02 的数学配方未改。对任意实 a/y、N>0、M>0、K≥0、q>0，先令 ap=max(a,0)，由 X≤Z 得 max(X,0)²≤Z²，然后用
    N[N ap²/q+K/M][q+KM/N·y²]−(Nap+Ky)²
      =NK/(Mq)(q−M ap y)²≥0.
没有 N=M+K 前提，没有 y≥0/a≥0 前提，也没有 K 分母。第1条修复只完成原本需要的加同量序推导。独立复核应完整阅读改后的 H02 及其供给 H03 的同一冻结结论。

H03 仍从实际 Qb>0 与 H01 推出 Q>0，不能倒置为假设。真实集合基数关系与原块均值给 X=Na+Ky，H02 与 QA≥0 给分子平方界。X≤0 分支 T≤0；X>0 分支合法除以 Q 和根号。修复的三处转换、T 定义正规化及零平方化简均沿这条原路线。n≥2、B.Nonempty、任意 b/c、actualQb>0 不变；k=0、a≤0 不受排除。

H04 仍以原残差双计数建立 ∑ψ=2F、∑b=∑g+2F/(n−2) 与 W+D=(∑b−nc)/√n。原 centeredSq=Q/(n−1) 身份推出 s=√Q/√(n−1)。Q=0 时 s=0，两边约定为0，即使分子非零；Q>0 时只作正分母代数。第8条统一目标语法没有改变任何系数或零分支。完整 changed H04 应由同一独立审阅者在原供应接口上下文中复核。

H05 未改。它仍只用 n≥4、card B≥3、点态对称 r、实际 Qb>0，消费 H03/H04 的完全相同冻结结论，得到实际 s>0 及 p41(3)的正部界。其原证明体字节可复用，但需检查 changed H03/H04 的接口与 H05 的相互作用；不因新上下文自动重做 H05 的完整旧证明审阅。

## 来源忠实性表（MFT）

| 原始来源 | 修订后保留对象 | 当前范围 |
|---|---|---|
| p41:65–70 | 实际 B/A、m/k、μB、Qb、原 F/[(n−1)(n−2)] | 补集基数和原偏移不变；无额外符号或独立性条件 |
| p41:73–80，式(3) | (T⁺)²≤(n−1){n(a0⁺)²/Qb+k/m} | 正部与所有系数完整；Qb>0 实际能量前提，Q/s正性由证明推出 |
| p41:82 | 任意确定向量的松弛及同一实际 b/F 代入 | 不假设实际 g/r 可以独立变化 |
| p51:18–29 | 原 ψ/(n−2)、W、D、centered s、T、零分母定义 | 实际 wrapper n≥4/card B≥3；没有实际 n=3 扩张 |
| p41:84–120，式(4)–(5)与后续概率论证 | 仍不在本单元源码 | 背景身份、异常块条件集中/积分、CDF和原 μ PE-R 全尾仍未闭合 |

没有把源 a.e. 包络改为点态全称事实；本五声明本来就是不需要包络/概率接口的有限代数。没有使用 unit276 或 unit278 的实现结论；也没有 NR/PE/DC/OQ56/root 完成或新颖性主张。

## 待复核和执行限制

本轮只在新目录建立候选，未使用 SSH、网络、Lean、AX、工具链、编译、prefix、上传、Git/API、资源变更、子实例、Goal、自动化或侧栏会话。独立 SOURCE/affected-proof 审阅和新整体服务器 gate 均由父级决定；本次作者未派发任何请求。原失败源与收据保留，不能把源修订描述成机器通过。

STATIC-CHECKS 只确认68个旧输入、精确冻结拼接、差异/映射与输出编码等文本事实。新的实际 owner/TYPE/VALUE/AX 数量未知，不能借用旧单元或 source declaration 数量。sourceCount 与 LF/字节数均为库存，不是完成率。

配置仍为 SAME gpt-6.1-sol/xhigh；实际 backend/model/effort 与四类 usage 未暴露，保持 null。MANIFEST 和唯一 LASTFINALWRITE 在最终封包时绑定本源及全部组件；该最终记录释放所有本次受派作者/写入/执行/子任务/等待权限。父级所有权不由本作者代为释放，ordinary turn 在封包后结束，没有 active wait 或持久续跑。
