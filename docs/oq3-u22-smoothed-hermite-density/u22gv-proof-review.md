# GV285 独立完整最终审查

STATUS: CORRECT

JUSTIFICATION: 最终精确源码完整实现原冻结声明；26 个声明内 let、全部新证明及证明局部值、全部 13 个实际所属完整 TYPE（含 12 个生成定理）和 0 个非定理 VALUE 均已审查。新增拼接在同一实际倾斜律及显式协方差白化上证明 E2=E，取得实际六阶累积量多项式的统一二阶频率加权积分界，消除参考函数的高斯阻尼，并由实际 CGF 的实多项式/Hermite 接口精确识别未阻尼逆变换。阈值在全部 n/p/x 之前选择，最终得到所述一致 n³ 乘密度误差趋零。保存的最终精确源服务器原生编译与同一首次对象全实际所有者递归公理收据一致，可按现行规则复用。没有发现隐藏数学前提、量词削弱、见证错接、符号或归一化错误，以及本单元的关键证据缺口。裁决仅限本冻结平滑密度结论，原 OQ3 正面根仍 OPEN。

## 独立性与权限

审查者为 fresh、NON-AUTHOR 上下文 `/root/oq3_gv285_final_review`；作者为父 `/root`。任务规定配置为 `gpt-6.1-sol / xhigh`。我未参与作者实现或修复，唯一写权限为 `C:/game/shao lean/drafts/oq3/u22gv-proof-review.md`，其他数学源、冻结、资格、历史、状态、协调和旧审查均只读。没有修改其他文件、撤回其他作者编辑、开子实例、连接服务器、执行 Lean/lake/AX、联网、上传、Git/API 发布、缓存操作或其他聊天操作。

已完整阅读 math-theorem 的 SKILL.md、prompt-library.md、openai-workflow.md、lean-verification.md，以及 chinese-output-style 的 SKILL.md；未使用 math-ultra。已读 SERVER.md、TEAM 的机械审查边界、streamlined-acceptance-current.md、AGENTS 最新 OQ3 恢复条款及 REGISTRY 当前权威所需字段。当前 Root5 为 `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`；OQ3 唯一 owner 为 `01a16c48-80ee-7520-a9d9-faeeb6d05c78`。phase40 激活文件本地实测 SHA256 为 `2b69e1eb2251724f2236bd8176623e7445a794dbb12a4f17a346885469fba480`，与任务一致；旧暂停不恢复为当前禁令。

当前 phase 为 ROOT_OQ56_OQ3_40，Root/OQ56/OQ3 各 heavy1、总上限3；OQ3 CPU36–39、44–47及原 c12-heavy.lock、native -M8192 -j4、项目140GiB/系统其他60GiB、180GiB警戒/200GiB硬限按原约束保留。本角色 heavy0，不占执行槽。`library/lean-toolchain` 实际文本为 `leanprover/lean4:v4.36.0-rc1`；固定 mathlib807d3836b165983210ee2ecf3cd28f239436949c/shared-v34 沿用保存证据，项目服务器专属规则优先于通用技能的本地探测建议。

## 完整新阅读与字节身份

本轮完整读取最终 source 1–278、freeze 1–86、scope 全9LF、actual-types 1–163、Audit.lean 全49LF，以及全部 bearing/qualified/server-dependency/own-firstO-view/preupload-import/repair01/final-source 绑定、receipt、audit-record 和 build-history。没有跳过或截断任何新数学声明、证明行、类型或局部值。逐行比较 prototype→attempt01→final 的全部源；对最终 theorem 头移除末尾 `:= by` 后，与 freeze 去末尾空白作精确字符串比较，结果相等，非仅语义近似。

下表均为本地原始字节独立 SHA256 重算。所有所列文本严格 UTF-8 解码成功，CR=0、无 BOM、EOF 有 LF；B/LF 也独立导出。路径均相对于 `C:/game/shao lean/drafts/oq3/`。

| 文件 | B / LF | SHA256 |
|---|---:|---|
| u22gv-source.lean | 15856 / 278 | `8fa3e6b674c24916ec4daab92a64637c10f336488e69f536e48928bb2aeab425` |
| u22gv-frozen-declaration.lean.txt | 5656 / 86 | `4e99b6dd7707bf0efd78cd88e3547a7deeab26659567f23398f1a7ca19f4234b` |
| two-hundred-eighty-fifth-unit-scope.md | 2564 / 9 | `c521b47fbcd05787971383f56ca1c78c52ffa625d7660830d80c0e2dac1c9ad3` |
| u22gv-actual-types.txt | 11387 / 163 | `bd68c77e6e74d6777f0f945f40457e8d9b3e19619d7661e9a455d4f79f247926` |
| u22gv-Audit.lean | 2154 / 49 | `5aae872a960189025b241d8cf15a80ccc51b9381a6a992c30012208c898de4e7` |
| u22gv-bearing-dependency-binding.json | 918 / 20 | `40f7e77ceacd4caa22de587924895ef8453193cacbce96815848f322171f11f5` |
| u22gv-qualified-dependency-binding.json | 1133 / 21 | `2a339c2c48d34d6c18b728dccccb9037d15e612e0499a03e1106e93004a9cfe1` |
| u22gv-server-dependency-binding.json | 1800 / 56 | `46a463a0fc9ba2f25f4d1f5740b7fe2e63c47ac412314fd891093a1a41be7f25` |
| u22gv-own-firstO-view-binding.json | 585 / 10 | `4670f498b9c9952b705e0bbf62c4fc5125b562e467f82e08a7fa3013e4fbf078` |
| u22gv-preupload-import-binding.json | 628 / 10 | `27c89afa781e8a7d46876a38ef7f62366ce8be7f0110f0386309a49dc838e857` |
| u22gv-repair01-binding.json | 1013 / 20 | `c04366d1068408e0866f5a458b1f0d44df7e6f5fbdacd4edac0fb7bb7b048fa0` |
| u22gv-final-source-binding.json | 1056 / 18 | `8f30e78aa33e1c7cb876f7d1a60e73426fcaa1788897da55d1b8ffdb161b04a6` |
| u22gv-receipt.json | 9049 / 279 | `5ea63a87c61108058708d44aeba040b4631841d8bbcfe3dd75a19d65ee4f52c6` |
| u22gv-audit-record.json | 4162 / 115 | `f11508ae624cca3b98762918d5d63e440b7df3542b4c868c9d141ed8ae81f594` |
| u22gv-build-history.json | 4541 / 164 | `b7bfc0911fadbb0d34c99f092106ef2a06b55284906436ab28c0ed4e24743050` |
| u22gv-preupload-prototype-source.lean | 15802 / 278 | `3e02f2a11dc1f039c61bfeae8697b195f879f60c905e5fd955cc1aa2dca505fb` |
| u22gv-attempt01-source.lean | 15805 / 278 | `3296e67e4649575cb651e48a2c73c102a26286e0bd4566c049f8f0fcf3b4bb42` |

bearing 中 sourceImplemented=false、GTGUFinalReviewsPending=true 是冻结时历史事实。qualified-dependency 绑定的是首次上传的3296e67e…源，随后 repair01 与 final-source 绑定把精确最终8fa3e6b6…源接上；依赖、冻结头和全部26个 let 未改变。这些历史字段不被误作当前数学状态，也不改写旧字节。

## 已合格依赖的复用及接口覆盖

完整消费接口已重新阅读：GT source 1–96及完整154LF/12TYPE；GU 全72LF source及完整16LF/1TYPE；FL 完整源码声明1–465及完整1149LF/3TYPE（分1–390、391–780、781–1149逐行显示，仅去显示前导缩进，无数学内容省略）；FU 全104LF source及完整57LF/8TYPE；CY 全86LF source及完整21LF/4TYPE。FL 已合格证明466–522与GT已合格证明97–255不因新上下文重做。旧完整审查不重新签发：核对其资格、来源、覆盖、裁决、边界与停止状态所需段落，并独立重算完整报告散列；不声称本轮从头重读这些旧完整报告。

GT/GU/FL/FU 四份 qualification 均为 COMPLETE_QUALIFIED，各自所指 source、review、receipt、actual-types 的本地散列全部逐项匹配。GT/GU 共同164LF完整报告 SHA256为 `ad14393ed7bd94aba3c817aa801e25fad0fc4fb4b8a5be83da78c1d15a4f0875`；FL142LF报告为 `7830c6cf74065f43a1b539d34c29a91fdea2309f8d461bed1eb11cc05634dc66`；FU138LF报告为 `ece9e5f5626e3291f2021faec85c18a60f42ab7d199dc6740c3de2e3799ec32e`。本轮使用这些已接受完整证明/机器证据，审查新增互动。

| 依赖 | 精确 source SHA256 | qualification SHA256 | 保存首次对象 SHA256 |
|---|---|---|---|
| GT283 | `da5234af6dac618c4bb2fca58a4f81a7db3572f6dcec9b3a9f3e3fe062f27802` | `74f006360e3e6fbaa57f02717aeb6166c95540dcae825ee4ed509450d6406029` | `f09469e788535d58912abbfc01f22f4f6aeb68413f95823d01c2528f758573ba` |
| GU284 | `77815c07b8768c0cd16eace8547ae9e2f1e6663f54b73484c12f7fb09a2155a4` | `5d4634719d6633d5af5909ddb1bccfc65f839f518935a24277a241b1c8fc6dec` | `79365cc3133e7496eeb3b2ac6d7645daf5c0f92ca5beb478046c88b24a913780` |
| FL249 | `d7f92e2bc3345af07d24422830928c6d5e334b11f99eac4a8909bdcef35ca920` | `19c30f44cbf511ec9c230b258193f35ac161ab0b407b37224a85c24bbccdf38f` | `cd0a47b8628be1bacbaa8a2030b4792a739c16096b5216ed35e974baada93ae3` |
| FU258 | `964ec9f0ced82946f8a328908067cae4c39e5ebbe5467d3c5f94a972b58ec1df` | `80bbddbecb3838e792eb30eabb142f45970f8c705c7f2019c25013d13f9f6052` | `4d5fc3c227622a008be83a77d108032bcd8e0ffae4b96304f62f15666fb7a687` |

CY184 source 为 `95aa9d280eb607c46768688ae6adcd758205f9cbf00d8891277e98d50145bbeb`，actual-types 为 `1c9ab44cd8b155bd4ac3d9aa1b1cee392486041bcfb643ecdc1db357b681046e`，旧完整135LF CORRECT报告为 `c6e2b660894524e59bd5526b4aefe98b95c854bad14ca16ba66e6838a469ad12`，完整旧receipt为 `074cd2b02b835b11067741febff705cbe527ed49d1b248afa57399ed8af8a38e`。CY历史没有独立qualification文件，historicalFirstO=null；当前受资格约束的观察对象为 `36c2389b115b169053ff1062ff3382405677eac5a34060bff352650b4ee6ac5e`。server binding 的 CY viewSameOriginal 仅指视图等于这一当前观察对象，不能倒造历史首次对象记录。CY旧receipt的 pending fresh review 是旧签发时状态，由其已接受完整CORRECT报告补足审查，不改写旧receipt。

保留继承 DF/BV/DB/CY 的历史 own-firstO 归档限制。没有补造历史、重跑旧原生/AX或用新视图散列充作不存在的历史首O。GV对CY只使用全部自然径向幂、任意a>0的真实全平面Lebesgue可积接口，参数实际为2、20及a=1/2。

为确认参考符号约定，另读取 curated library 中 GaussianHermitePolynomialRecursor 的定义/递推与导数式，以及 GaussianMvPolynomialHermiteIntegral 的完整所用声明1–25：H0=1、H(n+1)=XHn−Hn'，高斯n阶导数为(−1)^n Hn e^(−x²/2)。这是消费旧定义的语义核对，没有创建新的旧证明接纳或扩大依赖审查范围。

## 完整声明与新证明的数学核对

1. source11–23保留真正概率mu、紧Theta、Theta处于实际二次MGF域内部、实际倾斜协方差det>0、实际jointCharacteristic的一致弱Cramér条件。辅助范围为0≤beta<2/5、c>0、R≥0，没有把误差结论、CGF多项式性、白化一致性、密度或自由Hermite系数塞入前提。原严格0<beta<2/5的根范围仍单独保留；辅助边界beta=0不被用来更改原题。

2. 26个声明let逐值核对：外层 tilt/D/s/t/A/means/Y/laws/Phi 共9个；样本及频率/平滑部分 Qsample/M/T/nu/X/kappa/a/Sn/Pn/b/v/gamma/rho/k/damping/kernel 共16个；存在H后的reference共1个。tilt是真实指数倾斜，D为其协方差，A是所列二维逆平方根公式，Y=A([x,x²]−means)，laws=map Y tilt。Qsample是真实有限乘积律；M=(样本平均、能量平均)，T=√n E(M−means)，nu=其推前，不是自由选择的替代律。

3. a使用实际方向CGF在0的3至8阶导数，j∈Fin6，系数I^(j+3)/(j+3)!及√n^(j+1)分母不变。Sn保留q∈Fin7、全部sigma词、权重sum(sigma_i+1)≤6、1/q!及空词项。Pn精确为exp(−Q/2)Sn。b=1/(2n^6)，gamma两个独立一维高斯的方差v=toNNReal(2b)，rho为nu与gamma独立相加推前。k是方差2b的二维高斯卷积实密度，因子1/(4πb)及指数分母4b相符，非事后定义的近似输出。

4. source99–113两次调用GT和FL使用完全相同的mu/Theta/hTheta/实际hdet/hWC。各自E和E2都逐点由同一A的两行作用给出。hEE先对p函数外延，再用ContinuousLinearEquiv.ext及对w函数外延，以两条实际A行作用等式传递，确实证明E2=E后subst。没有假定两个存在见证自然一致，也没有混合另一倾斜律、样本状态或自由E。输出lo/hi及E估计保留GT选择，FL的包在E替换后使用。

5. source115–129所有新增命名局部let Xf/kf/af/Sf/Pf/envelope逐值与目标X/kappa/a/Sn/Pn及FL hgaussian展开比较相同；Fin6/Fin7、实际3至8阶CGF、有限词权重和高斯乘子均保持。hPenv为同一实际Pn对所有n≥1、p及全频率的包络CP(1+r^18)e^(−Q/2)，CP>0在n、p之前存在；不是截断窗口的可积性被误用为全局可积性。

6. source130–178以CY两条真实全平面接口取得r²e^(−Q/2)、r^20e^(−Q/2)可积，常数乘加后与envelope逐点环恒等。hEnv0由CP正、自然幂非负和exp正得出。K=∫envelope+1为新局部值；显式MeasureTheory.integral_nonneg保证K>0。对Q≥0，Q(1+r^18)=r²+r^20，故Q‖Pf‖≤envelope。hQbound使用实际Pn连续性给出可测性和非负范数支配，产生真实Integrable(Q‖Pn‖)及积分≤K。Q始终为坐标平方和，未换成Prod最大范数；K独立于n和p。

7. source179–188的hprobLaw恰取hpoint第六个合取（.2五次再.1）取得laws p的真实概率实例；h0取hcgf的第一项，是对每个实际方向的integrableExpSet内部含0；hM从hmom对每个自然j的统一矩包取真实可积性。匿名局部letI使用hprobLaw，并非额外公理。FU所有概率/指数矩邻域/全自然径向矩条件都由原MGF族的FL结论导出，无裸加矩假设。

8. source190–210先以epsilon/2取得GT的统一N0，再定义c0=(2π)^−2>0，取自然J>c0K/epsilon，统一选择N=max(N0,J+1)。n≥N≥2，故n>J、n≥1且n³≥n。乘epsilon>0得c0K<epsilon·n≤epsilon·n³，因此c0K/(2n³)<epsilon/2。N只依赖epsilon和已固定族常数，不依赖p、x；没有先看p/x再选N。证明中hcube、hJn、hKsmall各不等式的正分母及乘法方向均满足。

9. source211–232从同一GT结果投影nu概率、Pn连续和全局可积、rho概率/withDensity k/k可积/质量1。FU在实际laws p、实际n≥1上选出一个实MvPolynomial H，位于全部z和x之前；其在(i z1,i z2)求值恒等于同一实际Sn。FU的hHermite给真实未阻尼kernel·Pn积分可积且等于2π乘Hermite系数和乘exp(−Qx/2)。局部乘法交换只重排标量乘积，没有改变kernel的−I相位或累积量I^(j+3)。

10. source233–238的hInv将c0乘2π化为1/(2π)，π非零，所得恰为声明实reference的复嵌入；完整系数和、两个Hermite阶数与高斯因子保留。reference不被解释为非负概率密度。H可在epsilon、n、p之后选择，这是实际量词；没有额外声称epsilon无关选择、统一系数界、按n^(−r/2)分组或P1(0)=0。

11. source239–262的dampedReference是同一个GT参考。GU施于实际Pn、真实全局L1及Q‖Pn‖可积、b≥0，给两条真实振荡积分差≤b∫Q‖Pn‖。由K界和c0>0得归一化参考差≤c0 bK；乘n³后恰为c0K/(2n³)<epsilon/2，分母消去使用n>0。没有从有限窗口尾界推断未阻尼积分，也没有漏乘c0。

12. source263–275从GT相同n/p/x结果取得n³‖k−dampedReference‖<epsilon/2，用复三角不等式与上一半误差合成严格<epsilon，最后Complex.ofReal_sub/Complex.norm_real/Real.norm_eq_abs得到实数绝对值。每个x同时返回hiH.1的真正未阻尼积分可积性。最终所需合取投影和存在H的位置均与目标一致；未把复积分实部等式误写为整个复等式。

以上覆盖全部声明内let、九个新增命名证明let（Xf/kf/af/Sf/Pf/envelope/K/c0/dampedReference）、匿名概率letI、各have/obtain/choose来源和所有局部函数值；不存在未审查的新模块级定义值。

## 全实际所有者与机器证据

独立解析完整actual-types导出：DECL=13、TYPE=13、KIND theorem=13、唯一名称=13、VALUE=0；名称集合与receipt.all_owned_names精确相同，无省略号。主公开定理1个；生成定理12个，包括9个_simp_1_4至_simp_1_12和3个_proof_1_1至_proof_1_3。已逐个读全TYPE，非只看主名称或公理行。

生成TYPE内容分别为：将π=0化为False的命题等式；类型2/3/4的非零化简；一般无零因子的乘积非零、约化幺半群自然幂非零、带零群整数幂非零；CharZero中自然数加1非零；实到复嵌入的减法恒等式；以及n≥2推出n>0、n≥1和J+1≤n推出J<n的三个反证算术辅助。它们与完整新源的field_simp/push_cast/omega实际使用一致，不增补数学假设。

完整Audit.lean按env.getModuleIdxFor?的模块所有权遍历所有常量，未按名称前缀过滤；每个owner调用Lean.collectAxioms递归审计，拒绝新增axiom及白名单之外公理；若有defnInfo还检查safe并打印完整VALUE。这里所有13项均为theorem，故没有漏掉的非定理/opaque定义值。源禁止词扫描 sorry/admit/axiom/unsafe/native_decide 为0。所有13项AXIOMS并集恰为propext、Classical.choice、Quot.sound，没有新增项目公理。

保存证据中native002：最终source8fa3e6b6…、RC0、21.513025850057602秒；成功日志2439B，SHA256 `7e5d3139b00be3b1851c0a068a3bc93541d5032b21ed2c3123594963890650f5`。首次成功原对象2653800B，SHA256 `51aa972179e7d0d0b46e373a4a829e9484ea271b8bd19e0d4460d60868e701b4`。

保存同一首次对象的all-owner递归AX：RC0、5.8527711015194654秒；完整日志11641B，SHA256 `c612ae5d04e84ec9287ad90babfdda0fbaf53863efb26871c98868ccd16e25c8`，actual-types散列与最终receipt一致。own-firstO-view绑定同一source/firstO及其精确target/link，新增自有首O链接1、旧条目改动0、shared-cache写0、binary copies0。audit-record所有字段与receipt同名字段精确匹配，独立build-history与receipt.build_history完整结构相同。

本轮未连接远端，故没有独立重观察远端当前进程/对象或重读服务器原始日志；机器结论是保存的精确作者native/同首O审计收据、完整本地实际类型和审计程序的复用，不冒充本审查现场执行。final-source-binding记载父已完整阅读成功原始日志；已知overlay、9处unused Phi/damping/letIstyle/unused或unreachable ring等警告不构成证明错误，不进行PASS后美化或重跑。内存记录中的phase39字符串是沿用内存公式helper标签，外层resourcePhase为实际phase40；没有据此恢复旧CPU或旧资源限制。

## 失败、修复与归档真实性

prototype源3e02f2a1…只在本地，初猜FU模块名DirectionalCGFSixOrderHermiteIntegral错误；上传前仅第3行改为实际已资格receipt.module GaussianSixOrderActualCGFHermiteIntegral，得到attempt01源3296e67e…。逐行独立比较确认其余字节内容保持，没有把未上传prototype称为服务器失败或通过。

native001：3296e67e…源、RC1、24.625241989269853秒、无对象；原始失败日志1150067B、SHA256 `49eabb6b381e8995be0a6916db8ff57443eb8fa1e7a089049f7f5ed449a3117a`。本审查未读取该远端原始日志；repair绑定如实记载父读取全部3个完整诊断及精确终局目标，rawFullLogParentRead=false，省略了1149213B重复FL上下文，未声称全日志读完。

attempt01→final只有三行改变，已完整独立比较：111行 `intro w` 改为 `funext w`以处理函数相等；146行把有歧义的bare integral_nonneg改为有显式积分目标的MeasureTheory.integral_nonneg；164行删除rw已经闭合目标后的冗余rfl。冻结声明和所有26let完全不动。三个变化不增加或重解释数学前提，最终完整源码与成功native002/全ownerAX均绑定到8fa3e6b6…版本。两个native尝试均保留，没有未知inflight请求重放或旧成功producer/leafAX重跑。

## 原始题意、可声称结论与剩余边界

本轮实际阅读只读原report 1–31、81–158、217–235、493–523；repair01 1–69、188–226；原verdict全部58LF。正确路径为 `C:/game/shao/current/OQ3/verdict.md`，不是r2目录内不存在的verdict.md。完整文件SHA256依次为 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`、`9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`、`fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5`。未声称完整重读其余原始证明或重新认证引用文献。

原报告的真实白化Yθ、实际六阶Edgeworth有符号密度、n³log n频率窗口与严格beta<2/5范围相符。repair01与verdict把uniform-in-law、s=8外部Edgeworth输入归于Song Theorem2.1；不恢复原report的Angst–Poly对角统一性论证，也不把GV说成整个外部Song定理的形式化。p54修正保留 `v_corr=-hat_t0*sqrt(detDelta)*sqrt(Lambda1)`，两个平方根未反置或删除。真正联合非格点不足的已接受反例与显式远区局部化/率间隙义务继续保留。

GV新闭合的是：同一实际白化IID样本律nu，经方差n^−6的独立二维高斯平滑后所得真实概率rho的实密度k，相对同一实际κ3…κ8有限词所确定的未阻尼归一化Hermite有符号reference，具有全p/x一致o(n^−3)误差；并同时给出实际Pn及每个未阻尼振荡积分的真实全局可积性、rho的withDensity表达和k质量1。

“移除参考阻尼”不等于原始概率律去平滑。本单元不证明nu已有密度、不证明reference非负或质量1、不输出统一Hermite系数/导数界或分阶P1(0)=0，也没有把平滑密度sup误差自动积分成任意不连续加权测试函数误差。已合格GM276的物理小胞高斯平均振荡结果可继续精确复用；GV不重复其几何，也尚未提供其所需实际耦合/密度比较消费者。原律加权去平滑、物理小胞重建、胞求和、外区、B–D和OQ3正面根保持OPEN。没有新颖性、历史首次、最弱前提或最优阈值认证。

## 使用记录与释放

prescribedModel=gpt-6.1-sol；prescribedEffort=xhigh；freshContext=true；actualModel=null；actualEffort=null；inputTokens=null；cachedInputTokens=null；outputTokens=null；reasoningSubsetTokens=null。实际模型/努力与分项token遥测没有暴露给本审查，未知写null，不从提示配置推算实际使用量，不把原始token或购入信用估值写成订阅百分比的精确分配。

最终裁决 CORRECT，覆盖上述精确最终冻结声明、完整新source-to-statement/proof、全部26个声明let及证明局部值、13个完整实际TYPE/0VALUE、所消费旧精确接口的新增互动及保存同一首O的完整owner递归标准三公理证据。没有待作者修补的关键缺口。父须ENTIRE读取本报告并核精确字节后自行接纳；本角色不写qualification，也不提前代替父的接收动作。证明/声明改变时仅按实际受影响范围更新证据。

RUN_STATE: COMPLETED_STOPPED

RELEASE: 在完成本报告全文回读与SHA256/B/LF/CR/BOM/EOF-LF验证并返回完成回执时，唯一报告writer权限释放。交付后writer=0、heavy=0、inflight=0、pending=0、uncertain=0、children=0；无服务器操作、未决外部请求或后台持续任务。STOP。
