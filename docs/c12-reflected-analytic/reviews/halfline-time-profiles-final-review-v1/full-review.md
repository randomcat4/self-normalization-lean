# unit33：半直线标量时间剖面独立终审

STATUS: CORRECT

最终冻结目标内没有发现关键缺口。`Shao.C2.HalfLineTimeProfiles` 的七份源证明、七个公开完整声明、十五个实际归属声明的完整类型，以及唯一透明定义的完整值，已在独立新上下文中完整审查。复用精确源码绑定的服务器 attempt003 内核和全归属传递公理成功回执；本审查没有运行 Lean、重放审计或重编译旧生产模块。

## 范围与题意

只读原文为 `C:/game/shao/current/c12/supplement.tex` 第4192–4253行，完整文件 SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。保留原始换行的这62行共2624字节，SHA256 `7c114b02812a59089a18904d502318e4ac65a8574c7a80f735aa16dc3a8283f2`。

受审对象为实标量函数 F(C,T)=1−exp(−C/T)。一至三阶真实时间导数证书要求 T>0，C可为任意实数；时间剖面界额外要求 C≥0。精确上、下墙标量恒等分别代入 C=2(a−y)(a−z) 与 C=2(a+y)(a+z)。在相应半直线内部距离非负时，exp(−C/(2T)) 正好是原文单墙剖面 exp(−uv/T)。对 l≥1，f−1 与 f 的时间导数相同，所以这是原文 (j,l)=(0,1),(0,2),(0,3) 的标量半直线部分。

本模块没有识别实际布朗桥生存概率与反射公式，没有证明实际区间的正则性/PDE、空间与时间混合导数、任意高阶时间导数、墙处的一侧空间估计、零能量概率延拓或补偿泰勒余项。任意m的指数单项式界不等于任意阶实际导数已获证明。C=0被覆盖；T=0不在导数剖面目标中，虽然定义和两个纯代数恒等在总化实数除法下仍有值。所有原始 C12/OQ3/OQ4/OQ56 根组保持 OPEN；无新颖性认证。

## 冻结与精确工件

原冻结 `frozen.lean.txt` SHA256 `34cbaa9c054180b94658e4171c5864fc295c59eb8b72d21ef804ebe05e329b74` 保留。最终冻结 `frozen-v2.lean.txt` SHA256 `7afb638c53f37812e1c7ebc4eac1ba38c1b5a3aa69feb846ecd35d5641c53d6a` 只新增 `Mathlib.Analysis.Calculus.Deriv.Pow` 导入。脚本逐字核对七个完整声明头及完整透明定义，原冻结、最终冻结、最终源码中的数学接口完全一致。

- 最终源码：6313字节，SHA256 `7a9bbd4c2abd2b675911324f6451b36af4d611039bf7612dc763a92c0ff3bc89`；本地审查包、服务器工作树与 attempt003/source.lean 一致。UTF-8、无BOM、CR数量0。
- 目标对象及当前安装对象：937680字节，均为 SHA256 `6a0dd951f96306239195e4cd7717dc32b8bfba96d26a78dc0c4b0571c7bbed37`。
- 作者回执：SHA256 `fac6dcd6471679d5d2bb6720a7e0f1bd911ffe8af5f8886dffa7b81ba7958fdb`；作者释放：SHA256 `a2dc29139c969c4c20f3d473e25a42fd7fa62e8b8fce479d45c374374f00d746`。
- 审计实现：3188字节，SHA256 `9f67f419395c503e18ce1c93fc18612467b6e6f6ee62187caccd11fec73a9f4b`；审计JSON：3305字节，SHA256 `1ae65c4a39679e81115a9f2279f96f09538c877ec490ac369274db9d36de3d56`。
- 全实际类型：32497字节，SHA256 `fd5ff367f01b1f01949a20f15d58b2e5b9c6d250c38046b4573a1d77795991d3`；完整定义值：415字节，SHA256 `dc18f0962a1fecda398445bbe0d76f028ae4fc29f66b850b5e88cf52908fe9c8`。
- 原始审计日志：33125字节，SHA256 `2883cd53e377b2fbc0cd1dea6280ada0bb119e6e9d2be9a49a435879393458ec`。十五个完整原始类型块和完整值块，连末尾LF在内，都逐字节出现于这份日志中。

回执列出的十一项服务器工件全部重新做了只读哈希核对，包括失败 attempt001/002 的源码与日志以及成功 attempt003 的源码与日志；全部一致。失败历史保留，修复涉及缺失幂导入、固定库显式参数、Pi.pow_apply 和邻域集合成员的暴露，没有改变声明。成功内核日志只出现既有包提示与战术风格提示；未据此改源码或重跑成功检查。

服务器分支为 `author/c12-halfline-spacetime-v71`，观察 HEAD 为 `b677029b26987a90d0dbfa50a3500d19b062208d`；目标文件仍为待提交文件。受审结论绑定上述源码/对象哈希，不把同分支其他工作或后续单元纳入审查。

## 七份完整证明

1. `nonneg_exp_monomial_profile`：固定库 `Real.pow_div_factorial_le_exp` 的实数接口为 x≥0、任意自然n时 x^n/n!≤exp(x)。以 x=q/2 使用，实数阶乘严格正；乘非负 2^m 和严格正 exp(−q) 后，用 exp(q/2)exp(−q)=exp(−q/2) 得完整全称结论 q^m exp(−q)≤2^m m! exp(−q/2)。含 m=0、q=0，不依赖数值试验。
2. `timeCompletion_hasDerivAt`：商法则给 ((−C)/t)'=C/T²；指数链式法则和常数1减函数规则给 −(C/T²)exp(−C/T)。T>0保证分母非零，实际函数是完整透明定义 F(C,·)。
3. `timeCompletion_second_hasDerivAt`：先对显式 (−C/t²)exp(−C/t) 用商、幂、乘积法则，归一化为 (2C/T³−C²/T⁴)exp(−C/T)。再以 Ioi 0 为 T>0 的邻域，在每个正t用一阶证书的 `.deriv` 建立真实 `deriv (F C)` 与显式函数的邻域相等。`HasDerivAt.congr_of_eventuallyEq` 的方向和全部前提吻合。
4. `timeCompletion_third_hasDerivAt`：同理对显式二阶公式求导。系数导数为 −6C/T⁴+4C²/T⁵，乘指数的链式项补入 2C²/T⁵−C³/T⁶，合成 −6C/T⁴+6C²/T⁵−C³/T⁶。在整个正时间邻域使用二阶证书的 `.deriv` 后，才向真实二阶导函数传递可微性。两份高阶证书都没有仅从单点等式推导可微性。
5. `timeCompletion_time_profiles`：令 q=C/T≥0、E=exp(−q)>0、P=exp(−q/2)>0。任意m界在 m=1,2,3 给出 qE≤2P、q²E≤8P、q³E≤48P。绝对值三角界由 `abs_le` 和有完整非负单项式信息的 `nlinarith` 实现，得到常数12=2·2+8、108=6·2+6·8+48。三份真实导数证书给精确 −qE/T、(2q−q²)E/T²、(−6q+6q²−q³)E/T³，再除正的 T、T²、T³。P 精确变形为 exp(−C/(2T))，保持原文的半指数衰减。
6. `upperReflection_eq_timeCompletion`：完整展开两个透明标量定义，分子以环恒等规范化为相同表达式。对所有实参数成立，未加入几何前提。
7. `lowerReflection_eq_timeCompletion`：同理使用 C=2(a+y)(a+z)。其结论是标量公式之间的等式，不能替代实际概率反射定理。

## 全归属与完整类型覆盖

审计按 `env.getModuleIdxFor?` 遍历每个环境常量，以实际所属模块等于本模块选择；没有以命名空间筛选，也没有只选公开定理。实际归属共15：14个定理（7公开+7生成）和1个定义，没有其他种类。对每个归属常量都运行作者已成功的递归 `Lean.collectAxioms`，所有传递公理都在 `{propext, Classical.choice, Quot.sound}` 白名单内。

七个生成声明均属于 `timeCompletion_time_profiles`：`_simp_1_1`、`_simp_1_2`、`_simp_1_3` 分别是在完整 Zero/OfNat/NeZero 实例下的2、3、4非零命题等于False；`_simp_1_4` 是有 NoZeroDivisors 和两个非零前提的乘积非零；`_simp_1_5` 是 MonoidWithZero/IsReduced 和底数非零下任意自然幂非零；`_simp_1_6` 是 GroupWithZero 和底数非零下任意整数幂非零；`_simp_1_7` 是 AddMonoidWithOne/CharZero 下自然数像加1非零。其完整量词、宇宙、实例和前提都已读取，与所属源证明中的合法简化用途一致。各声明完整类型的独立哈希与逐项审查结论保存在 JSON 中。

32497字节实际类型以22项精确重复子表达式字典进行无损阅读。全部字典项和全部编码上下文都已直接读取，未删类型字段、实例、前提、量词、空白或名字；反向替换逐字节回到原文件哈希。唯一完整定义值另行直接读取。字典、完整编码与往返清单一并交付。

## 已接受依赖与固定库

复用单元31与26的独立完整审查，审查JSON分别为 `1fcc2466a834a04850bc45b0287058b02dd89443edbaa2dc6209b5a04d13a81f`、`7f994541cb9e7999a0007570f92314086c9f5db9e999c171716c0d5a4e7a3240`。当前服务器源和安装对象均与这两份审查的绑定一致。没有再审旧证明。当前模块不使用单元31的热方程定理；直接消费的项目透明值是单元26的 upperReflection/lowerReflection，二者的完整实际类型和完整值已读，并核对旧回执绑定。

固定 mathlib 的 factorial指数下界、HasDerivAt 的商/幂/指数/乘法/减法接口、`.deriv`、邻域相等传递及 Ioi_mem_nhds 的完整使用接口与所需上下文已读。承重接口源文件均与固定 mathlib HEAD 的对应字节一致；日志的“repository has local changes”提示没有掩盖这些接口的变更。

## 机械证据和释放

工具链固定 `leanprover/lean4:v4.36.0-rc1`；mathlib固定 `807d3836b165983210ee2ecf3cd28f239436949c`，只读包视图 `cache-overlays/shared-v34/packages`。作者 attempt003 内核退出0，全实际归属传递公理审计退出0。回执资源为 CPU14–17、c12-heavy.lock、−M8192、−j4。审查者仅运行文件读取、哈希、文本比较和只读Git观察，Lean调用0、审计重放0、旧模块编译0、成功门重复0、缓存写0、生产/冻结/共享/Git修改0、子代理0。

审查角色与作者分离；按明确配置记录模型 gpt-6.1-sol / xhigh，独立运行计数不可见，input/cachedInput/output/reasoningSubset分别为null，不推测订阅百分比。最终释放由 `writer-release.json` 记录：本审查的报告写入与执行均释放，heavyInFlight=false，inFlight=[]。父实例可据精确哈希接受本局部单元并继续下一个来源依赖。
