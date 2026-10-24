# EndpointRelativeError 独立完整终审

STATUS: CORRECT

三个冻结公开头均有完整正确证明：条件律全零能量的高斯费用、真实二次倾斜及线性半轴相对误差、固定于 x 的条件律 END。结论仅绑定以下精确源与已核对依赖；C1/C2/OQ3/OQ4/OQ56 原根继续 OPEN，最终范围接受和集成由 root 决定。

审查者 `/root/common_endpoint_relative_error_full_review`，fresh `gpt-6.1-sol / xhigh`，使用 math-theorem，未使用 math-ultra 或子代理；作者为另一上下文 `/root/common_endpoint_actual_author`。已读 AGENTS.md、SERVER.md、TEAM 当前机械审计边界和 streamlined-acceptance-current.md。作者在 relative-error-handoff.md 明确释放 END 源写权和 producer 执行权；审查没有改生产源、冻结文件、旧凭据、缓存、library 或原论文，没有 Lean/lake/公理审计调用、push、PR 或 merge。全部服务器操作仅为只读核对；没有本地 Lean 或重计算。

## 精确版本与覆盖

工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/common-endpoint-v66`，分支 `feat/common-endpoint-relative-error`。源提交 `cff0b897ecd9ef43fe0240128f65333c97d96e76`，tree `1911b791392221b8a278c230ef6ea139330786b5`，Git blob `aa4deeb67bc99554abcad835a7583cf28485524f`；该提交只改 `Shao/Probability/EndpointRelativeError.lean`。最后完整只读核对为 `2026-10-24T03:33:25.934203+00:00`，HEAD/树一致、工作树 clean，未见目标模块在途 Lean。

源码 2395 行、126150 字节，UTF-8、2395 LF、0 CR；SHA256 `e9624ff50b79c8e41b749e4b6851870129797a38c692b809a90e81cda8699223`。本地生产副本、远程当前文件、提交 blob、relative-attempt020 保存源四者同哈希。完整读取第 1–2395 行，包含 42 个显式定理的完整声明和全部证明（3 public、39 private）、233 个 let、12 个 letI、6 个 haveI 的完整值和嵌套证明。没有用头部扫描替代证明阅读。

当前公开冻结文件 SHA256 `c1a2ecd01de9c3d1ed87c6dfe447e25b4ff02819a86b811f60efa95271936598`；私有释放冻结快照 SHA256 `33cc4e35e29ecd4623f2dab1413e1029d56546bf9d1ba71d47f387f19f7335bd`。本审查独立机械提取完整源码头，3 个公开头和 39 个私有头分别与实施前冻结文本逐字结构一致，仅忽略空白；全部 let、量词、假设和墙方向均在比较中。新增 Layercake 导入使用既有精确缓存，没有改变数学前提。

直接逐项完整读取服务器审计日志的 56 个 ACTUAL_TYPE 块：42 个源码定理加 14 个生成定理。pp.all、pp.deepTerms、pp.proofs 保持 true，完整实例参数、依赖 let 和实例值没有省略；日志无省略标记。生成项是有限求和分配、零幂/非零数值、有限索引正性、能量零等价、正态 CDF 和逆像成员等事实，逐个与所属源码证明核对。实际 owner 枚举发现 0 非 theorem，故全局非定理完整值应读数和已读数均为 0；没有新增全局定义或全局 instance。定理机器证明值未展开，逐项绑定实际 owner 索引、完整类型块 SHA、对应源码证明块 SHA 和同一原始内核对象。

逐声明源码行段、头/证明哈希、局部值覆盖、全部 56 类型块原日志行号/哈希、生成项来源和逐条传递公理见 `common-endpoint-relative-error-full-review-coverage.json`，SHA256 `9da3847bddd5b8f23314dfd54b33eccc399a6b54a42ad2e960e2e04f6e81539b`。覆盖数由实际 owner 和源码映射导出。

## 原文、量词与依赖范围

完整读数学候选 `drafts/c12-endpoint-relative-error-candidate/proof-candidate.md`，并对照原只读 main.tex 140–245、301–349、424–558 及 supplement.tex 216–239、1023–1071。候选中历史 OPEN 的随机窄带由已经独审合格的 EndpointRandomWindow 解决；本审查只消费其精确接口和合格证据，没有重审或改写 W。原文的真实 iid 路径、未中心化能量 ΣAᵢ²、弱 crossing、严格 survival、全零样本、固定于 x 的 cutoff 和可能非零的条件均值均保留。

已核对 Path/prefixSum/energy、truncationF/truncationBudget、retainedCutoffLaw 和标准正态尾的实际定义；完整读所消费的条件律/样本量/尾预算/付费矩/方差、BoundedQuadraticTilt 和 iid_centered_berryEsseen 声明接口。所读接口源码均与 root-activation 的合格依赖哈希一致。原律只需概率、可积二阶矩、nEνA²=1、EνA=0；概率律的二阶可积保证一阶可积，均值条件没有借总化积分弱化。三、四阶矩仅在实际有界条件律内获得。没有加入条件均值零、对称性、无原子、非格点或 Q>0 几乎处处。

END 的量词严格为每个固定 `0<epsilon≤1/800` 先选 Ce，再对 ν、n、x 和所有 `|t−x|≤1/(1+x)` 一致。Ce 可依赖 epsilon；报告不声称 epsilon 趋零时一致。原根后续选定数值 epsilon 的使用与此兼容，但本模块不单独证明原根。Shao–Zhou (2016) 的原端点中偏差结果归属保留；证明实际使用本地已验收有限 iid Berry–Esseen，而非引入外部端点结果、浓集公理或把 END 塞入假设。未主张研究新颖性，也未改变 p54 修复或其他分线范围。

## 全部承重证明核对

1. 第 25–233 行真实计算 `P(Q=0)=(rho.real {0})^n`。在非零集合上以 `(C|a|−1)²(2C|a|+1)≥0` 积分，得到 m2³≤m3²·rho(A≠0)；m3=0 时反推 m2=0，与 n m2≥3/4 矛盾。有限乘积和 `1−p≤exp(−p)` 给指数费用 `exp(−(1+x)^6/(16r²))`，再由显式指数不等式及 Mills 下界支付 `sqrt(2π) r Φbar(x)`。n=0 由原归一化排除，未删掉实际全零路径。

2. 第 234–779 行完整证明三项二次指数 Taylor 余项、可积性、真实有限乘积倾斜和换测度。`f(a)=ta−t²a²/2`、`W=S−tQ/2−t/2`、`D=t(√Q−1)²/2` 满足 `W+D=S−t√Q`。H 采用 W≥0，J 采用 −D≤W<0，两项不交且精确分割弱尾；`F=tW+t²/2` 和真实 normalizer Zⁿ 给公开恒等式。H≤1；J 由真实支撑盒上的有限能量界支配而可积。Q=0 时 W=−t/2、D=t/2，路径保留在 J 闭左墙；W=0 原子只入 H。

3. 第 780–1278 行 Lyapunov 给 q³≤nβ²，小预算使 n 的倒数有真实费用。`Z≥1/2`、`Z^n≤2`、`|Z^n−1|≤8z`，并对实际倾斜 g=a−ta²/2 证明均值偏移≤16z/(1+t)、总方差误差≤32z/(1+t)²、总方差≥9/10。方差明确扣除真实 `M²/n`，没有把倾斜或条件均值归零。中心三阶矩先付原有界律的 64m3，再用倾斜密度≤2，得 128β。所有除法正性在使用前建立；松 h 只通过 th≤1/800 支付，没有偷换成本质支撑半径。

4. 第 1279–1524 行实际正态 CDF 的导数与尺度比较给均值/方差扰动误差≤2|A|+2|V−1|。任意概率 μ 的闭区间误差≤2B：下界用 Ioc，闭左墙上界从 a−δ 逼近并用正态 CDF 连续控制，完全允许 μ 的原子。随后对 H_t(y)=exp(−ty)1{y≥0} 用真实层蛋糕，0<s≤1 的精确超水平集为闭区间 `[0,−log(s)/t]`，故半轴积分误差≤2B。已读固定 Mathlib 的 Layercake 第 545–547 行完整接口，确为 `t≤f(a)` 和 Ioc(0,M)。完成平方和 Lebesgue 平移精确给标准正态半轴积分 `exp(t²/2) Φbar(t)`，没有把闭墙原子忽略。

5. 第 1525–1886 行以实际可测 g 的 pushforward、真实有限 iid 乘积和方差映射应用已验收 BE。标准化事件与 W≤y 逐点相等，分母变换为总方差的 3/2 次幂。128β 与 V≥9/10 给合法 BE 常数 196608；加入正态参数误差后，经层蛋糕得到半轴费用 393408z/(1+t)。最后 `Z^n≤2`、normalizer 误差和 Mills 给费用 `786816 sqrt(2π)+8`，严格被公开 `2^20 sqrt(2π)` 覆盖。生产证明使用比候选更松但合法的中间常数，未改公开常数。

6. 第 1887–2084 行消费精确已合格 W 的 `Cw=2^17`，结合线性半轴及 `Z^n≤2`，得到实际弱单尾常数 `Cs=(2^20+2^18)sqrt(2π)`。反射律由 map(−id) 实际构造，均值变号、二/绝对三阶矩不变，预算保留，不假定原律对称。t>0 时两弱尾交集严格等于 Q=0，严格正能量端点事件严格等于两尾并集的补集，给精确 `1−P(U)−P(L)+P(Q=0)`。

7. 第 2085–2282 行始终使用 cutoff `epsilon/(1+x)`。令 qB=ν(B)、m=ν(Bᶜ)、T2=nEν[A²1(Bᶜ)]，证明条件二阶矩 `nEρA²=(1−T2)/qB`、qB≥3/4；尾质量和尾二阶矩分别支付误差，得 `|q−1|≤3r/(epsilon(1+x)²)`。样本量来自同一 cutoff 的已验收下界。结合实际均值漂移、β 和邻域 `1+t≤2(1+x)`，得 `z≤Kepsilon r`，其中 `Kepsilon=4/epsilon²+12/epsilon+16`，且 `z≤epsilon/2+3epsilon²/2+2epsilon³≤1/1000`；同时 th≤epsilon≤1/800。没有混用 t 的条件律或换 cutoff。

8. 第 2283–2395 行先选合法 `Ce=2 Cs Kepsilon exp(2)+sqrt(2π)`，再引入所有原律参数。真实双弱尾误差与 Q0 费用相加，邻域正态尾比较支付 exp(2)，准确闭合全部 t 的冻结 END。t≤0 时严格正能量绝对端点事件直接为空，G(t)=0；包括 t=0，没有从弱尾补集错误外推。

## 原始内核、公理与失败证据

首次三头完整整源成功是 `relative-attempt020/kernel.rc=0`，同次原始 `-o` 对象 SHA256 `d151025f575332bba21c3fe1dbf50bc30fca5715dce069692c515d2f32398804`；build 路径仅解析至这个原对象。原 kernel.log SHA256 `12544f890e3a1bf4918d08fd973423ceb72239aa9925ddc4dc407cb8537ec057`，81 条 warning、无 error。原生一次全 owner 审计 `relative-owned-audit.rc=0`；审计代码 SHA256 `9e186986be9d819e1712e15aa10a4356d8bae18ac13a988a7c04d5c7ec046435`，日志 302020 字节、SHA256 `a02c6ce701c2382f7f30022902d477ea224d4ae3bcd82d1b6b1895522d3439e6`，原生 JSON SHA256 `d67024da44a2a637c76ac061ba867cd741024bb26fb84fca13c539ed52746112`。本地 JSON、原生 owner 索引和 56 个类型块一一对应。

审计按 `env.getModuleIdxFor?` 的实际模块归属枚举，无 namespace 过滤；拒绝任何非 theorem，对每个实际所属声明逐项调用 recursive `Lean.collectAxioms`。本审查逐项核对全部 56 行 AX 集，均仅为 propext、Classical.choice、Quot.sound 的子集。去注释源码禁止 token 扫描为空。传递公理闭包检查涵盖所有公私有/生成项，不是只抽查三个公开目标。

只读逐项核对全部 20 个 relative-attempt 目录的原生 rc、当次源哈希、日志哈希和成功原对象哈希；20 份源均不同，5 次 rc0 分别为 002、009、011、017、020。前四次是较早部分源码，不视为完整三头通过；15 次失败及 018/019 最终 adapter 修复前的记录全部保留。第一次完整成功后 0 同源 producer 重编。作者管理脚本的多余右括号失败未影响 Lean 或源/对象。审查中一次过大显示响应被截断，仅重新读取受影响类型块；一次接口定位误按 theorem 搜索实际 lemma，随后按标识读取。两者均仅是只读展示恢复，没有 Lean、AX 或写入重放。

固定 toolchain 文件仍为 `leanprover/lean4:v4.36.0-rc1`，mathlib manifest 和实际 HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。root-activation 的全部 22 个合格依赖逐项当前源码、原始对象和执行别名哈希匹配。W 的源码 `3821ff66b25ea3c98bf4753b062fc95139454cf6450e527c2206df46b98bf18d`、原对象 `bbfd78ed01932ccb8f744512e5667ea5996a664e8b96d0a7470d876ec2360191` 及已合格完整独审报告复用；既有 Layercake 对象 `38b9101df65ca9ba1a4c94528c011db0157a7b77a83aa43f809554d04a82e0a1` 同样匹配。未重编已绑定 producer、重审 W 或机械重跑 AX。原资源记录为 root-heavy.lock、CPU10–13、-M8192 -j4、activate 先于 cd；本审查没有再启动内核来重复这些证据，也没有触碰外部 CPU0–9/80GiB 工作负载。大日志和对象仍只在服务器。

## 判定与释放

未发现数学关键缺口、隐藏目标假设、冻结漂移、原子/零能量漏项、全类型/非定理值覆盖缺口、非白名单传递公理或源对象错配。CORRECT 足以供 root 对本精确 END 生产单元作接受判断；后续生产改动只使受影响证据失效，无变化时可复用本报告与原生收据。原根不因此闭合。

本次独审完成，明确释放两份审查输出的写权和本任务执行权；没有生产源权利、在途工具或未完成写入，没有启动后续长模块。实际 input/cached-input/output/reasoning-subset token 数不可见，均记录 null，不估计订阅百分比。
