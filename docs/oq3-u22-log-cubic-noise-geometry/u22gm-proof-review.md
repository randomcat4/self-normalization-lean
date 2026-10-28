# GM276 独立完整最终数学审查

STATUS: CORRECT

JUSTIFICATION: 最终 131LF 源码完整证明冻结的条件性紧参数谱族高斯振荡命题。证明从已合格 BP149 的同一次存在量词解包中取得同一个真实白化族 E、参数界 M 及由同一 M 定义的正 Cstar，再把已合格 GJ273 的真实 log(n)/n³ 曲边胞结果作用于这个 E，并逐项证明完整系数不超过该 Cstar。所有量词、16 个声明内 let、所有证明局部值、全部两个实际拥有类型及零 VALUE 均已覆盖。既有最终源 native001 和同一首对象全拥有递归公理回执一致，没有发现本限定辅助范围的关键数学、题意转换或证据缺口。

本结论只认证 GM276 的统一显示系数。它保留真实协方差谱界 hspec 为前提；不声称在本单元已从典范开放 MGF 域推出谱界，也不关闭真实样本误差、加权去平滑、外区、B–D 或 OQ3 正面根。

## 独立性、权限与实际用量边界

审查上下文为 /root/oq3_gm276_final_review，fresh、NON-AUTHOR；父 /root 负责实现。本次唯一写权为 C:/game/shao lean/drafts/oq3/u22gm-proof-review.md。其余源码、冻结、历史、来源、旧报告和机器回执全部只读；没有修改共享实现，没有重写旧合格材料，没有创建子代理，没有服务器访问、Lean/lake/AX、上传、网络/API、Git、缓存或跨聊天操作。

已完整读取 math-theorem 及其 prompt-library.md、openai-workflow.md、lean-verification.md，应用 chinese-output-style，并读取 Windows 本地文件操作的 windows-shell7 指引。现行 AGENTS.md 的末段、SERVER.md、TEAM.md 必要规则、streamlined-acceptance-current.md 和 REGISTRY 的 rootThread/currentAuthoritativeState.OQ3current 均已核对。没有启用 math-ultra。当前 Root 为 01a17d3c-6dfd-7cc0-94ed-35d758a423a5，OQ3 同一所有者为 01a16c48-80ee-7520-a9d9-faeeb6d05c78；2026-10-27 显式恢复已覆盖历史暂停。TEAM 的旧协调者、旧暂停和旧 CPU 段落没有被当作现行权限。

配置单独记录为 prescribedModel=gpt-6.1-sol、prescribedEffort=xhigh、freshContext=true。实际运行签名和精确 token 遥测未暴露：actualModel=null、actualEffort=null、inputTokens=null、cachedInputTokens=null、outputTokens=null、reasoningSubsetTokens=null。未把 null 当作零，未把原始 token 数或购入额度估算换算为订阅百分比。

当前 OQ3 phase40/CPU36–39,44–47/c12-heavy.lock/native -M8192 -j4、项目140GiB/32CPU、系统与其他60GiB/8CPU、180GiB守卫/200GiB硬限均由现行记录控制。本审查 heavy=0；下述机器内容全部是保存证据，不声称本审查实时观察远端进程、二进制或锁。library/lean-toolchain 为 leanprover/lean4:v4.36.0-rc1，library/lake-manifest.json 的 mathlib rev 为 807d3836b165983210ee2ecf3cd28f239436949c；没有探测或安装本地 Lean。

## 完整覆盖与精确字节

最终源、冻结、scope、全部 GM 的 Audit/actual-types/receipt/audit-record/build-history 和六份依赖/首对象/格式/最终绑定均已全文读取；首次门前旧稿也全文读取。BP149 的91LF完整独立报告和59LF完整实际类型、GJ273 的202LF完整独立报告和69LF全部12实际类型均 ENTIRE 阅读，连同消费接口全部 let、原始源码及 receipt/资格映射核对。为识别接口读取旧源码，不重新进行已合格旧证明的完整认证，也不重放旧检查。

以下统计从实际本地字节计算。表内文本均严格 UTF-8、CR=0、BOM=false、EOF-LF=true；LF 是真实换行数，未混用逻辑行和无末尾换行统计。

| 输入（drafts/oq3/ 下，另注除外） | SHA256 | B / LF |
|---|---|---:|
| u22gm-source.lean | b320a7530a3d732cd16e93e0a49a4d8c3e89c94fefe1b395c873234adf5d8e18 | 7190 / 131 |
| u22gm-frozen-declaration.lean.txt | 058c24d9b9edf3f542d7dca2e429c6714466a9847e686ce4a7945751553c9a43 | 3163 / 51 |
| two-hundred-seventy-sixth-unit-scope.md | b3f0afa7a40c90847a6568cf9764b028ffea240c97ada2d564fc40b73c7d7e72 | 2166 / 13 |
| u22gm-actual-types.txt | 0d222ce37f2574a95bb749f1af7279b04dc79ce7748c81f61d790bdd95c0bdb7 | 4041 / 63 |
| u22gm-receipt.json | 78e4d13e2676762b343804c8348345b334cac75a561e2438bf4bfecad86ce7ea | 5571 / 187 |
| u22gm-audit-record.json | 7a343e3716f3d56c390809cd91036d07e2afa3ba82a9d057b63612bad7692ab9 | 3119 / 104 |
| u22gm-build-history.json | e538a6a9191c7d2bd8e3e3e940369fcc3b74e153ea05d4fa4abff395e0e6f13e | 2268 / 83 |
| u22gm-Audit.lean | 40e9b4bd680f31014e926eba4c12f7ac40764a6132edadf7f3b43911b5dd9363 | 2132 / 49 |
| u22gm-bearing-dependency-binding.json | 137e018225496c90717e6f4b1dcf5680680d0184d24dadf79f89462a7032bd87 | 3327 / 63 |
| u22gm-qualified-dependency-binding.json | 3fc5c22fdbdc9c2afefe8ed724966032cf5e3c7a93373f669bb9153a49d611f9 | 393 / 9 |
| u22gm-server-dependency-binding.json | 22283370acdfde6880bf5f4c305bfeba1ac372687327c3fd6c13306c9aa3d0b4 | 633 / 19 |
| u22gm-own-firstO-view-binding.json | e650785b934cc551960c7935ab68b19e84a6a315d77bcbbfca6a5515d25e62dc | 575 / 10 |
| u22gm-pre-firstgate-source.lean | 8c2d06e9af4f317f95d19c99dd3e5b876acb399af5df022b7372667e414acf29 | 7174 / 131 |
| u22gm-pre-firstgate-format-binding.json | 9a85dbaf9aa5465e71bfb9f619b4de0e3c0dc5f08fd3b6434e1cc51c570fe2bc | 726 / 11 |
| u22gm-final-source-binding.json | 1692b9d01dca8cbbec954954da4a484a3a4de0e5cfd5be5f7aab9b97c5fea220 | 821 / 14 |
| u22bp-source.lean | dcd06857e360cab10992139afe5a68b335f66eeeb47f9c4db6f004a42e653472 | 7505 / 137 |
| u22bp-proof-review.md | 18485d507e8cf9f36b2be5f5d2e0ddaa93144bc937ba7dec72bc24f63b6bcf79 | 20050 / 91 |
| u22bp-actual-types.txt | 37696fafa2ce3490b3598c1bf11541fce15a353885b7913c6ded4567011350ca | 3837 / 59 |
| u22bp-receipt.json | 2ab1aac7a0ff13db8b5c1e9d9c095251c550590a94eacdfec44a195d33c1eebc | 4765 / 112 |
| publication-u22-bn-bv/docs/oq3-u22-compact-physical-whitening/manifest.json | 6b172b2276958a6d47c629c1c7fc8b81712bd29beb65d249a510999a7e42b1e0 | 24438 / 397 |
| u22gj-source.lean | 41dd914fc7c593127273317aff9d4a8c8465748d077a93c810933cdf75d41a03 | 4086 / 80 |
| u22gj-proof-review.md | ffa19ddee4935a304eba00c361615e4eb3adc4279644cd10923f2c9ca9dde3ce | 25529 / 202 |
| u22gj-actual-types.txt | a721d150c65f6a9c95cda6b6a881a023a767c19c4f8d32d908678819add4716b | 3794 / 69 |
| u22gj-receipt.json | c2b1bf7f390c148c9215a10f0cfadfa14b0f66fed49186307434b8be527ebb66 | 8755 / 278 |
| u22gj-qualification.json | 6f7610d904dac59028a958dc858d545e4771dd5ee704499f17e930fb98b14fbf | 1502 / 28 |
| u22gj-review-metadata-correction-binding.json | 417ad6c04d8e69ed0ab012fc32c7fddce269187123a56b051ed73d3de529e856 | 976 / 17 |
| u22gj-proof-review-pre-metadata-correction.md | 8838228191afe3e6fb07dea97746747dbf4ffa8b39a0a24f7c7a6436a61bdf07 | 25533 / 202 |

源码从 theorem 开始至其 := by 前的全部声明，加一个末尾 LF，与真实 .lean.txt 冻结文件逐字节相等；声明内 let 恰为16。旧稿与最终源去空白后完全相等，逐行只在63/68/69/71/72/87/124/125行缩进改变，增加16字节；首次 upload/Lean gate 前已修复，冻结字节未变。这里不声称缩进对 Lean 语法完全无关，而是明确该旧稿未执行、最终稿才是门与审查对象。

bearing 在实现前记录 sourceImplemented=false、冻结/范围和已合格依赖。qualified-dependency-binding 历史 sourceSHA256 是8c2d06…，不能冒写成最终源；pre-firstgate-format-binding 显式连接8c2d06…与b320a753…，final-source-binding 精确绑定最终源、同一冻结、旧资格绑定、格式绑定、最终 receipt 和 actual-types。父方曾猜冻结扩展名 .lean 而收到 FileNotFound，未写入、未上传、无外部作用；真实 .lean.txt 已全文核对，这不构成数学失败。

## 冻结语义与全部16个声明内值

前提是实际实概率测度 mu、实际紧集 Theta、lo>0、hi>0、rho≥0，以及对每个 p∈Theta、每个实 xi/eta 的真实两侧二次型谱界。hspec 内的 D 是 parabolaCovariance(mu.tilted(x↦p.1*x+p.2*x²))。没有改成任意输入矩阵，没有新增目标振荡、可积性、系数或边界管质量假设，没有把 canonical-open-MGF 的后续接口当作本证明已经实现的步骤。

16个声明内值全部覆盖如下。第1个是 hspec 内 D。第2–6个依次为 tilt、D、s、t、A：tilt 是原二次指数倾斜；D 是其实际抛物线协方差；s=sqrt(D00*D11−D01²)，t=sqrt(D00+D11+2s)；A 的两条对角线分别为(D11+s)/(s*t)、(D00+s)/(s*t)，两条非对角线都为−D01/(s*t)。第7–11个是 U=1/sqrt(lo)、R0=2U、kappa0=(2M)*(4hiU)、G0=R0*(1+2(|a0|+rho)/level²)、Cstar=exp(kappa0*R0)*(8kappa0(R0+1)²+768(G0+1))。第12–16个是 h、cellA、stdCell、g、Φ，完整内容如下。

h=log(n)/n³。cellA 为真正的 Ioc(aL,aR)×Ioc(qL,qR)，与闭物理窗 |w.1−a0|≤rho、0≤w.1²/level²−w.2≤rho 相交；三个弱不等式及两条抛物线均保留。stdCell 是 w↦sqrt(n)•E(p)(w−y) 的实际像。g(v)=exp(−sqrt(n)*(p.1*((E p).symm v).1+p.2*((E p).symm v).2))，使用同一 E 的真实逆映射。Φ 是 gaussianReal 0 1 与自身的积。

输出 E:Theta→((ℝ×ℝ)≃L[ℝ](ℝ×ℝ)) 是真实连续线性等价族，逐 p 保留 A*D*A=1、对所有 w 的实际两行矩阵作用、正向算子范数≤2/sqrt(lo)和逆算子范数≤4hi/sqrt(lo)。未声称 p↦E 连续或可测。M>0 及 forall p:Theta, ‖p‖≤M 在所有 p/n/y/端点之前；由该同一 M 定义的同一 Cstar>0 也在这些量词之前，不是每胞另选系数。

全称结论覆盖每个 p:Theta、每个 n≥2、每个闭网格矩形内的 y 和每组两边长≤1/n的端点。y 仅须属于原闭矩形，不要求它属于 cellA、是鞍点或率极小点。没有偷偷假设 level>0；level=0 使用 Lean 实数全定义除法，level²≥0 和分母为0时商为0使本纯几何命题仍有定义。正物理尾事件识别另有义务，不能由此取消正 level。Theta为空、rho=0、退化或空胞都被原量词覆盖，无非空或边界零质量假设。

ℝ×ℝ 的球、连续算子范数和参数界全部使用项目已有的乘积最大范数。hspec 的 xi²+eta² 没有被误认作该乘积范数的平方；谱白化转换由合格 BP 承担。已阅读实际 openBallOscillation 完整值：sSup(insert 0 {r | ∃u∈ball(z,h),∃v∈ball(z,h),r=|f(u)−f(v)|})；它是全点对开球振荡，不是本质上确界。Set.indicator 在 stdCell 上为 g、外部为0。已读 parabolaCovariance 完整值：对角元分别是 x 与 x² 的 variance，两个非对角元为它们的 covariance。

这两项定义来源为 library/Shao/OQ3/OpenBallOscillation.lean（SHA f1e693a8b9b2db416dd730bcdfb596030d768b911015bcfdfc50a16e97e62e2d，4403B/97LF）及 library/Shao/OQ3/RegularCovariance.lean（SHA 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853，15931B/305LF）；消费完整定义值，未重新认证其全部旧证明。

## 直接承重依赖的精确资格复用

BP149 的完整独立报告状态 CORRECT，fresh NON-AUTHOR /root/oq3_u22bp_full_review，覆盖原137LF完整源码/证明、完整59LF唯一实际类型、声明和证明局部值及原服务器全拥有递归AX。没有单独 qualification.json；实际接受资格由上表 publication manifest 的 state=COMPLETE_QUALIFIED_MILESTONE_NO_ROOT_CLOSURE、qualified_reviews、bp row、source_map 和 evidence_files_sha256 提供。发表包的 BP 源、报告、receipt 和 actual-types 本地字节 SHA 分别与上表四项完全相同，不能因 author receipt 的历史 pending 标签否定后来的完整合格报告。

BP 的唯一实际类型已全文读取，含 hspec 的实际 D、全部 tilt/D/s/t/A、E 真实行作用与正逆算子界、M>0/全参数范数界、共同 U/R0/kappa0/G0/Cstar，以及 n≥1 的原 ncube 胞积分结论。GM 使用这个存在量词的前半部和正性，不依靠旧半径1/n³的积分界去推出新半径的结论。BP 原首对象为1060c56b7a44079f5b34488124f9a6b851b976a3b709ce78764dcad110b28ccc/379696B；旧 native02/全拥有AX 分别6.908112024888396s/6.225595226511359s、自然RC0，旧首失败仍在原回执内。

GJ273 的 qualification state=COMPLETE_QUALIFIED，精确源41dd914…、完整202LF报告ffa19dde…、receipt c2b1bf7…、全部12实际类型a721d150…和首对象69b7efd11dcaebe186f8993296e9a3fb238419776a76ac85da67ca18096c7c0c/238264B相互绑定。独立审查者 /root/oq3_gj273_final_review 已停止并释放。native002/同首对象全12拥有AX分别4.989622315391898s/5.931582955643535s、自然RC0；初次失败未抹去。

本次逐项阅读 GJ 全12实际类型：三公开项为半径0<log(n)/n³≤1/sqrt(n)、实际胞积分界、n³倍标量系数趋0；两生成项均为 forall n,2≤n→¬1≤n→False；七个 simp 项依次覆盖2/3/4非零、NoZeroDivisors下两非零因子的乘积非零、MonoidWithZero/IsReduced下非零元自然幂非零、GroupWithZero下非零元整数幂非零、AddMonoidWithOne/CharZero下自然后继强制转换非零，全部类型类/宇宙/非零前提均已读。GJ的9个声明let h/A/B/g/kappa/R/C/G/Φ均完整消费；GM用到实际胞界，其余类型检查资格覆盖而未越权声称GM已新增标量极限定理。

GJ 的实际胞接口要求 n≥2、任意 theta、真实 E、y、七个实数、rho≥0、闭锚点和两条边宽界；输出真 Integrable 与 K*log(n)/(n³sqrt(n))，其中 K=exp(kappa R)*(8kappa(R+1)²+768(G+1))，kappa=(|theta.1|+|theta.2|)‖E.symm‖、R=‖E‖、G=R*(1+2(|a0|+rho)/level²)。它没有以所需积分为假设，GM也没有添加此类前提。GJ宽度证明由n≥2得到n≥1、n>0、sqrt(n)>0、log(n)>0，再用log(n)≤n、sqrt(n)≤n及n²≤n³完成；全部生成项均包含在原合格报告和类型清单，未以名称过滤遗漏。

GJ报告旧归档与最终报告逐行比较只改第21行：冻结“38逻辑行/末尾无换行”更正为“37逻辑行/37LF/末尾有LF”。correction binding保留旧报告883822…，最终资格只指向更正后的ffa19dde…；数学、源码、冻结、receipt和成功门都未改变。本次没有改写旧报告。GM server-dependency-binding 保存的BP/GJ精确source/firstO/viewSameOriginal均与上述资格一致，cacheWrites=0、noOldGateReplay=true；这只是复用保存观察，不冒称现在访问服务器。

## 最终源码全部证明的独立推导

1–7行只导入两个合格项目模块、打开标准测度/概率/矩阵/拓扑范围并进入noncomputable section；130–131行关闭节及命名空间。9–59行完整声明与冻结逐字节相等。没有降低证明设置，没有添加公理。

60–69行 classical/dsimp only 展开声明let，proof-local tilt/D/s/t/A逐个复现实际值。70–73行唯一一次调用 BP，参数逐个为同一mu/Theta/hcompact/lo/hi/hlo/hhi/hspec/level/a0/rho/hrho。obtain 同时解包 E、hE、M、hM、hMbound、hCstar、_hold，随后 refine 原样返回 E/hE/M/hM/hMbound。没有换族、重新选M或从另一次存在量词取系数；_hold是旧ncube结论，后续未使用，因此不存在对更大半径的不合法单调反推。

74–84行 proof-local U/R0/kappa0/G0/Cstar与声明逐个定义相等。hCstar来自同一BP见证的同一表达式。hU由正lo给出1/sqrt(lo)≥0，hR0=2U≥0，hkappa0=(2M)(4hiU)≥0。hfactor的非负性来自 |a0|+rho≥0 和 level²≥0，包含level=0的总除法；因此所需物理因子≥0。所有这些量都在引入p/n/y/胞之前定义，系数保持共同。

85–92行任取目标全称量词，hb调用GJ，theta精确为(p:ℝ×ℝ)、E精确为(E p)，所有n/hn/y/端点/level/a0/rho/三个几何前提依次原样传入。GJ的A/B分别与GM的cellA/stdCell定义相等，g/Φ/h也相同。proof-local kappa/R/C/G逐项与GJ系数值相同；hb.1因此是真正同一被积函数的Integrable，不是上界函数可积性或Lean不可积积分的默认零。

93–98行 hR=(hE p).2.2.1 取得正向算子范数R≤R0，hInv=(hE p).2.2.2取得逆算子界，投影准确，未误取矩阵作用合取。hMbound p是同一M的真实参数范数界；产品范数定义上等于max(|p.1|,|p.2|)，所以两坐标绝对值各≤M。这里没有把欧氏范数或坐标平方和替换进来。

99–107行坐标界相加得|p.1|+|p.2|≤2M，乘以非负真实逆范数，再使用hInv与2M≥0，得kappa≤kappa0。kappa≥0、R≥0直接由绝对值/范数；乘以共同非负因子得G≤G0且G≥0。mul_le_mul hkappa hR hR_nonneg hkappa0严格提供kappa*R≤kappa0*R0所需两项符号，exp单调给C≤exp(kappa0*R0)。没有遗漏“两个不等式相乘”时的符号条件。

108–117行R+1和R0+1均非负，故sq_le_sq只需比较R≤R0。用非负平方与kappa0证明8kappa(R+1)²≤8kappa0(R0+1)²。add_le_add hG le_rfl精确给出G+1≤G0+1，乘非负768得第二项比较。没有把1+G和G+1在不匹配的API中混用。

118–121行实际括号8kappa(R+1)²+768(G+1)≥0，由两项比较及上界指数非负得到完整K≤Cstar，包括全部乘积项。122行原样携带hb.1，并将hb.2接到目标。123–128行change只展开相同let；div_le_div_of_nonneg_right使用同一分母n³sqrt(n)≥0，mul_le_mul_of_nonneg_right还要求log(n)≥0，最后由n≥2⇒n≥1及实数强制转换、Real.log_nonneg明确给出。实际n≥2还保证分母和log(n)严格正；证明只需非负，所以不存在除负数或漏掉n=2的分支。

所有证明局部值及产生它们的分支都已覆盖，包括局部hp、hU/hR0/hkappa0/hfactor、hb、hR/hInv、hpcoords、hkappa/hkappa_nonneg/hR_nonneg/hG/hG_nonneg/hC/hsquare/hfirst/hsecond/hinner0/hcoefficient；没有未审查的用户辅助定理或全局定义。

## 全部实际拥有类型与逐项判定

actual-types共63LF/4041B，恰有2 DECL、2 TYPE、2 KIND theorem、0 VALUE；名称集合与receipt.all_owned_names完全相同。唯一公开类型完整保留如下，打印的have均是声明let，不是新增前提。

~~~lean
DECL Shao.OQ3.compact_parabola_pair_log_cubic_gaussian_oscillation
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ)),
  IsCompact Theta →
    ∀ (lo hi : ℝ),
      0 < lo →
        0 < hi →
          (∀ p ∈ Theta,
              have D := Shao.OQ3.parabolaCovariance (mu.tilted fun x => p.1 * x + p.2 * x ^ 2);
              ∀ (xi eta : ℝ),
                lo * (xi ^ 2 + eta ^ 2) ≤ xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
                  xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤ hi * (xi ^ 2 + eta ^ 2)) →
            ∀ (level a0 rho : ℝ),
              0 ≤ rho →
                have tilt := fun p => mu.tilted fun x => p.1 * x + p.2 * x ^ 2;
                have D := fun p => Shao.OQ3.parabolaCovariance (tilt p);
                have s := fun p => √(D p 0 0 * D p 1 1 - D p 0 1 ^ 2);
                have t := fun p => √(D p 0 0 + D p 1 1 + 2 * s p);
                have A := fun p =>
                  ![![(D p 1 1 + s p) / (s p * t p), -D p 0 1 / (s p * t p)],
                    ![-D p 0 1 / (s p * t p), (D p 0 0 + s p) / (s p * t p)]];
                ∃ E,
                  (∀ (p : ↑Theta),
                      A ↑p * D ↑p * A ↑p = 1 ∧
                        (∀ (w : ℝ × ℝ),
                            (E p) w = (A (↑p) 0 0 * w.1 + A (↑p) 0 1 * w.2, A (↑p) 1 0 * w.1 + A (↑p) 1 1 * w.2)) ∧
                          ‖↑(E p)‖ ≤ 2 * (1 / √lo) ∧ ‖↑(E p).symm‖ ≤ 4 * hi * (1 / √lo)) ∧
                    ∃ M,
                      0 < M ∧
                        (∀ (p : ↑Theta), ‖↑p‖ ≤ M) ∧
                          have U := 1 / √lo;
                          have R0 := 2 * U;
                          have kappa0 := 2 * M * (4 * hi * U);
                          have G0 := R0 * (1 + 2 * (|a0| + rho) / level ^ 2);
                          have Cstar := Real.exp (kappa0 * R0) * (8 * kappa0 * (R0 + 1) ^ 2 + 768 * (G0 + 1));
                          0 < Cstar ∧
                            ∀ (p : ↑Theta) (n : ℕ),
                              2 ≤ n →
                                ∀ (y : ℝ × ℝ) (aL aR qL qR : ℝ),
                                  y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR →
                                    aR - aL ≤ 1 / ↑n →
                                      qR - qL ≤ 1 / ↑n →
                                        have h := Real.log ↑n / ↑n ^ 3;
                                        have cellA :=
                                          Set.Ioc aL aR ×ˢ Set.Ioc qL qR ∩
                                            {w |
                                              |w.1 - a0| ≤ rho ∧
                                                0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho};
                                        have stdCell := (fun w => √↑n • (E p) (w - y)) '' cellA;
                                        have g := fun v =>
                                          Real.exp (-√↑n * ((↑p).1 * ((E p).symm v).1 + (↑p).2 * ((E p).symm v).2));
                                        have Φ :=
                                          (ProbabilityTheory.gaussianReal 0 1).prod
                                            (ProbabilityTheory.gaussianReal 0 1);
                                        MeasureTheory.Integrable (Shao.OQ3.openBallOscillation (stdCell.indicator g) h)
                                            Φ ∧
                                          ∫ (z : ℝ × ℝ), Shao.OQ3.openBallOscillation (stdCell.indicator g) h z ∂Φ ≤
                                            Cstar * Real.log ↑n / (↑n ^ 3 * √↑n)
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
DECL Shao.OQ3.compact_parabola_pair_log_cubic_gaussian_oscillation._proof_1_1
TYPE ∀ (n : ℕ), 2 ≤ n → ¬1 ≤ n → False
AXIOMS [propext, Quot.sound]
KIND theorem
~~~

逐项裁决：公开类型 CORRECT，完整量词/所有let/Integrable/积分和冻结相同，证明如上覆盖。唯一生成 _proof_1_1 也 CORRECT，其类型只是由n≥2推出n≥1后与¬1≤n矛盾，准确对应末行omega的生成子项；不是新增假设或漏掉的主结论。公开项transitiveAX为propext/Classical.choice/Quot.sound，生成项为propext/Quot.sound，没有全局定义、VALUE、安全性或其他私有生成项余部。

## 保存的首成功机器证据与全拥有公理门

唯一 GM native001 对最终 b320a753…/7190B/131LF 自然RC0，耗时6.671724101528525s；成功日志133B，SHA fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626。同一首对象全拥有AX自然RC0，耗时5.92673596739769s；日志4293B，SHA f1e229295304dba4d4245b31e6ce5316b97759a968d3731327b258dbe7bcebc7。第一原始olean为c52020de4b1b4d0d2957cbbbe93e377368e076f6028833d70540bc39b16d2a0c/366520B。没有机器证明修复或不明在途重试。

receipt.build_history 与单独build-history结构完全相等；audit-record每个键和值与receipt中相应非build_history部分一致。最终源、冻结、scope、Audit、actual-types和原首对象的哈希均被同一回执连接。own-firstO-view-binding把原工作区对象链接到accepted-source-view，new_own_firstO_links=1、old_entry_changes=0、shared_cache_writes=0、binary_copies=0，没有重编译对象替换首对象。

Audit49LF程序全文已读：先验证冻结公开名为theorem；再遍历env.constants，按getModuleIdxFor?的真实拥有模块等于Shao.OQ3.CompactParabolaLogCubicOscillation选择全部拥有常量，拒绝axiom；对每个常量Lean.collectAxioms递归检查白名单；打印完整TYPE/AXIOMS/KIND及实际存在时的安全性/VALUE；要求拥有集非空且冻结目标数为1。没有只按公开名或命名空间审计。pp.deepTerms/pp.maxSteps只控制打印，不降低内核验证。

保存结果的五行尾部为U22GM_FROZEN_DEFINITIONS 0、U22GM_FROZEN_THEOREMS 1、U22GM_ALL_THEOREMS 2、U22GM_ALL_DECLARATIONS 2、U22GM_AXIOM_GATE PASS。与完整63LF导出、receipt的全部拥有名/计数精确相符。最终源扫描无sorry/admit/new axiom/unsafe/native_decide/implemented_by，递归公理只有标准三项且无sorryAx。

本次从本地已保存u22gj-repair-primary-api.txt的前两行读取相同的mathlib local-changes警告；这两行含LF精确为133B且SHA等于GM成功日志。再在内存中连接该133B警告、完整GM63LF actual-types、上述五行LF尾部，恰得4293B/SHA f1e22929…，精确等于GM全AX日志回执。这是对保存日志全部字节的本地重构及哈希比较，没有运行日志中的任何命令。成功native只有已知thin-overlay两行警告，没有隐藏Lean error；全AX导出没有省略生成项。

回执外层resourcePhase为ROOT_OQ56_OQ3_40；复用内存辅助器的内部phase仍为ROOT_OQ56_OQ4_39，是phase39内存公式的历史标签，不能据此误说OQ4获得本次执行。已记录两门CPU36–39,44–47、native_MiB8192、j4，raw cgroup约199.765GB、admission_used约161.520GB、加8GiB后约170.110GB，均保留真实raw和有界clean inactive_file折扣字段；没有缓存清除、外部进程变更或旧门重放。本审查只核对保存记录的内部一致性，不新增实时资源断言。

## 原始来源、宽度修复和未闭合范围

完整按要求读取 C:/game/shao/current/oq3/proofs/r2/report.md 的1–158、165–215、220–235、493–523行（SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55，20102B/523LF），全文读取同目录repair01.md（SHA9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd，5846B/226LF）及 C:/game/shao/current/oq3/verdict.md（SHAfd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5，3041B/58LF）。最初按旧报告路径尝试proofs/r2/verdict.md只产生本地FileNotFound；随后定位并全文读取真实顶层verdict.md，无任何写入或外部作用。

原report取h=n^-3/log(n)，repair01的Song路径取h=n^-3，而本单元明确证明eps=log(n)/n³。新eps与原report宽度之比为(log n)²，渐近加宽；n=2时log n<1，不声称逐n都更大。不能把原式(9)的O(n^-7/2/log n)原样写成本单元的新界，也不能把原Fourier窗口n³log(n)换成新eps倒数而不另证。GM真正给出的是Cstar*log(n)/(n³sqrt(n))，来自新GJ界而非旧式(9)的复述。

对固定mu/Theta/lo/hi/level/a0/rho，所得同一E/M/Cstar控制所有p/n/y/合法胞。结合已合格GJ的纯标量log(n)/sqrt(n)→0，可在数学上读出这一统一高斯胞上界是o(n^-3)；GM自身实际导出只新增上述一个统一界定理及其生成项，没有把该解释伪称为另一个已编译声明。Cstar不要求对变化的level、lo、hi等继续统一，也没有推出参数族的连续可测选择。

hspec是原来源保留的真实二次倾斜协方差上下谱条件。本单元消除的是在该条件下逐参数高斯系数缺乏共同显示界的义务。典范开放MGF域/正协方差推出谱界的旧生产者若要用于原模型，后续消费者仍须保持同一真实A/E及其概率对象，不能另添coherence前提或换成无关白化族。

真正半开胞与闭抛物窗、两条窗口曲线、完整指标函数及全部边界均保留；不凭高斯边界零测删除真实分布原子。原始严格0<beta<2/5不变，GM不含beta所以没有放宽端点或证明最优性。修正后的Song uniform-in-law/s=8输入属于外部Song定理，不算GM独立证明，也不恢复原report已被修正的Angst–Poly对角统一性论证。p54首项保持v_corr=−hat_t0*sqrt(detDelta)*sqrt(Lambda1)。真正联合非格点不足的已接受反例不被本高斯局部正面引理冲销。

真实Gaussian噪声概率、canonical all-frequency Fourier/Hermite统一误差、实际weighted de-smoothing、同一原概率模型的逐胞比较/重倾斜与权重重建/精确求和、外区率间隙应用、B–D及OQ3正面根均保持OPEN。来源verdict的历史PROVED是其原研究审查范围，不升级为本次Lean根闭合。新颖性未重新检索或认证；GM是现有合格接口的实质性统一系数消费者，不宣称历史首次、最弱假设或整篇研究完成。

## 交还与释放

最终裁决为 CORRECT：精确最终GM276的完整source-to-statement/全部proof/16声明let/全部2TYPE/0VALUE与同首对象服务器kernel/全拥有递归三项白名单证据一致。可在该限定范围复用本独立最终报告及既有成功机器回执，无需因为此报告新增而重放BP、GJ或GM已完成的成功门。

COMPLETED_STOPPED。仅此报告在保存后从磁盘 ENTIRE 回读，并计算真实SHA/B/LF/CR/BOM/EOF-LF；结果随交还消息提供，避免自指哈希。报告写权在整篇回读和字节核对完成后交还并释放，此后不再写。children=0、heavy=0、inflight=0、pending=0、uncertain=0，没有远端请求或后台写入遗留。
