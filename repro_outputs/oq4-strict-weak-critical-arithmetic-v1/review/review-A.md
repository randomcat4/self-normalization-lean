# A 严格／闭临界商算术分类：独立完整终审

STATUS: CORRECT

审稿者 context225，fresh gpt-6.1-sol / xhigh，未参与本批数学推导、声明冻结或实现。完整阅读最终383行生产源码及全部新证明，六个冻结头和唯一透明值，29个实际所属声明的全部原始未省略显式类型，以及唯一非定理常量的完整值。另完整阅读实际消费的38个项目旧接口类型及所有非定理值；旧证明资格按已合格精确版本复用。本审稿无 Lean/parser/build/nativewalk，无旧对象内容读取或哈希，无作者源码、共享文件、Git或缓存写入。

## 精确版本与范围

- 模块 `Shao.OQ4.RademacherStrictWeakCriticalArithmetic`，声明位于既有 `Shao.OQ4.RademacherStrictWeakBoundary` 命名空间；所属统计不以命名空间过滤。
- 最终 `rademacher-strict-weak-critical-arithmetic-v1/attempt003/Source.lean`：`dbbbb11f0472ca7d61640752fa08d67a3280d762657d4c4eccc9b9ac000a1ba4`，19588字节、383 LF、UTF-8无BOM且无CR。
- 冻结接口 `001b2f3e0bd784a217639dfce94f65d8c69c184c476b6902837c4d56722333c6`；lead冻结 `1c3f65d8f4361eabb14486c337a6da83531dd09eb2a07375b31f55002f4f9d22`。独立纯文本切片比较六头完整类型及定义值逐字相同，无额外顶层头、前提或定义变化。
- Combined `be5605b0a0d049fe06919f4f0ad75f9587b3dec3c1ed9ab358e5cb5e238816a1`；服务器实际编译源码逐字等于它，且等于 Source 加原审计后缀。审计后缀与已合格核心使用的工具相比，仅目标模块、冻结公开库存、输出路径及日志标识变化。
- 完整数学稿 `strict-weak-boundary-math-v1/proof.md`：`15f676f2fbe43e24c28bbdbae6333a5929d0515389244309a32eff3e7b0c9c47`；完整原来源 `C:/game/shao/current/oq4/c01/spectrum01.md`：`b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`。本单元锚定§3临界格点几何、§4严格／闭边界差。

本批认证固定 canonical Rademacher 实际闭／严格概率商的临界主公式、两类实际严格递增子列，以及按 c³ 有理／无理分类的完整聚点集和收敛性。算术二分是来源上的明确新增推论，不是原文逐字声明；没有新颖性判断，不外推到一般增量律、原空间搬运或一般 OQ4。所有原研究根组仍 OPEN。原空间临界算术搬运 B 不在本报告范围。

## 来源到陈述和完整证明

`criticalRatio c n` 的完整值就是 `ratio n (height c n)`；旧 `ratio` 的分子为 `RademacherS5Assembly.p`，经 S5→S4→S3→S2透明别名是有限乘积 Rademacher 律的 `closedStrip` 实概率，监测零前缀。分母 `strictP` 是同一 `pathLaw` 上监测1至n的 `strictEvent` 实概率。`pathLaw` 是 ±1各半的独立有限乘积律，`prefixSum` 是实际有限前缀和。已读这些实际类型和值及别名链；没有把谱主项或任意正函数当作概率。商使用全定义实数除法，通常商的解释只用于共同正尾。

1. **critical_main，17–62行。** `height c n = c·root n`，`root n = (n:ℝ)^(1/3)`，`q c = π²/(4c³)`。`scales hc` 精确给出高度趋∞和 n/h²趋∞；`positive_time hc hn` 只在 n≥1提供 n/h³=1/c³。故第三尺度的最终上界取正数1/c³、起点1合法；未在n=0约消n。消费旧 `boundary_main` 的完整类型与正尾／三种极限均吻合，最终系数与q的等式只在n≥1使用，得到全部冻结结论。n=0时高度0、J=1、实际商1而因子exp(q)>1，只是被排除的有限前缀；主头没有错误声称它们逐项相等。
2. **noninteger_subsequence，66–176行。** 局部完整证明令 T=(k/c)³、U=ceil T、y=h(U+1)。旧 `up_rounding` 给0≤U−T<1，因而0<(U+1)−T<2；c>0和高度立方恒等式给0<y³−k³<2c³。高度非负和k≥1给y>k。立方差因式分解的第二因子至少k²>0，于是0<y−k<2c³/k²。这里+1确实防止ceil恰命中整数。旧 `up_subsequence` 的真实StrictMono尾给U+1的StrictMono；拉回 `critical_main` 正尾，再选D>max(1,2c³)、K=K0+T+D+2，统一保证k≥2、2c³/k²<1、cutoff和两概率正性。K的增大保留StrictMono，移位索引归一化逐项正确。由k<y<k+1排除任何整数高度；在同一AE整数前缀路径上直接证明closedStrip与strictEvent相等，包括零前缀，再用measure_congr得到实际两概率相等。仅在已获正性处除以strictP推出商1。没有调用要求h≥1的Bridge来代替全正阈值论证。
3. **rational_integer_subsequence，180–233行。** p,d为正自然数，c³=p/d。对所有k，((pk)/c)³=d p²k³且(pk)/c≥0，`root_spec` 的非负立方根唯一性给高度恰等于pk，包括k=0。系数d p²>0，Nat立方严格单调，所以k↦d p²k³是实际StrictMono自然数映射，移位K=max(2,T)仍StrictMono并落入共同正尾及cutoff。每个移位高度都是整数，J=1；由critical_main加法误差的StrictMono拉回得到实际商趋exp(q)。没有错误使用仅适于c=1的完美立方索引，也没有增加互素条件。
4. **critical_rational，237–315行。** 从(r:ℝ)=c³及c>0先证明r>0，再用Rat.num_pos得正整数分子，随后才用Int.toNat_of_nonneg保持原值，得到p=r.num.toNat≥1、d=r.den≥1和精确正有理表示。Rat.cast_def的目标除环条件满足。两个已证实际StrictMono子列分别给1和E=exp(q)的内包含。外包含任取真实 `Cluster` 见证σ、StrictMonoσ和商子列趋L；误差拉回趋0，使二值因子Fσ=exp(qJ)也趋L。boundary_gap只用于已证高度非负处，其二值结论给每个Fσ∈{1,E}。若L不在该集合，ε=min(|1−L|,|E−L|)/2>0；趋值要求尾上距离<ε，而任一二值距离至少2ε，矛盾。故证明了任意聚点的外包含，并非只展示两个端点。q>0使E>1，若整列收敛，则两个严格递增子列的唯一极限相等，矛盾。
5. **critical_irrational，319–380行。** 对每个n≥1，`positive_time` 给h>0和h³=c³n；若h=z∈ℤ，n≠0允许将c³写成有理数z³/n，直接违反无理前提，未在n=0除n。对这些每个正时间，使用同一个AE前缀整数支持证明闭事件与严格事件逐路径等价；closed→strict时等号会使h=|z|成为整数，strict→closed时零前缀由h>0处理。该论证没有h≥1门槛，因此确实覆盖0<h<1的低阈值以及两概率同时为零的情形。概率相等不是无条件商1；只有与critical_main的strictP正尾相交后才用div_self。最终商1给整列趋1；任意StrictMono子列的极限由唯一性等于1，恒等索引给反向包含，故真实Cluster恰为{1}。

完整 `Cluster` 值确实是“存在 ℕ→ℕ 的StrictMono子列及沿该子列的Tendsto”，没有替换成另一种filtercluster。全部公共量词、前提、let索引、目标类型及criticalRatio值与冻结逐字一致。既有核心的完整证明资格复用独立context223报告／收据 `ab4f87264c30120fbf7baccffd71c5252369a92e63b0e5cc0d2306270affb474` 和lead接受 `b427b660a935149308e9b22d07eb983455de025ae2807f349bf9986f4fda76ae`；本审稿没有重审旧核心证明。

## 实际所属、展开接口与传递公理

独立验证同次成功saved native JSON的 `environmentDifference = moduleOwnership = stage2 = owned.names`，无重名、不按命名空间过滤。实际29 = 6公开 + 23生成 + 0显式private；种类为1 definition + 28 theorem，全部确属目标模块，无foreign-namespace owner。本计数由实际owner表导出。

已完整读29个原始未省略展开类型（含所有binder/let/实例），以及criticalRatio的完整定义值；没有采用类型摘要或字典压缩。23个生成头为criticalRatio方程、irrational的自然数正性证书、有理分子的toNat证书、noninteger索引／cutoff／相邻整数矛盾证书，以及rational子列的正性、移位和数码／乘积／幂非零simp证书。每个确切名字和覆盖均列入收据。全部新证明通过生产源码阅读覆盖；生成定理的巨型proof-term不再打印，其type/value依赖绑定原native JSON。

服务器只读同次 `audit-native.json`，独立检查compact投影逐项一致，从每个owner分别递归遍历typeRefs和valueRefs并与原collectAxioms及per-root-axioms逐项相等。62515个closure节点全部可达、边无缺失；810个项目依赖声明、33个项目模块。所有节点无unsafe/partial，opaque有可用值，项目无新增axiom。每个owner传递公理均只在 `propext, Classical.choice, Quot.sound` 内。

实际消费的38个旧项目完整类型／非定理值覆盖8个模块；其中7个旧库模块源码与v74 PASS源映射匹配，第8个是精确已合格的StrictWeakBoundary。重要Rat.num_pos／Rat.cast_def／Int.toNat_of_nonneg、StrictMono趋∞、Nat幂严格单调及measure_congr的实际类型也已读并核对使用条件。旧proof均复用，不重编或重审。

冻结导入的 `RademacherRealThresholdBridge` 仅被导入，38个实际消费旧项目接口中没有它的声明。仍绑定其旧源码 `644f10f118e2765a346cf64e47e6637ce97f23b292a377c43ec06620318a0df2`、general116既有接受、独审收据 `11357a1c3c37b18da187087050458b36099b51dc59ea333f7958a4d6ff78dcff`、native证据 `52290e5673953e3d4b181abb8e2be7f262515d310ed5bb4a0d046f55fb0402fd` 及sole对象记录。本批全正时间等式来自新源码的直接AE论证，不依赖该旧桥的h≥1结论。

## 成功内核与对象绑定

复用作者attempt003首成功kernel：PID887081，退出0、reaped、未超时，24.212013486772776秒；Lean v4.36.0-rc1、固定mathlib `807d3836b165983210ee2ecf3cd28f239436949c`、-M8192/-j4、trust1025、autoImplicit=false、skipKernelTC=false。执行收据 `daba0abb4432110ea8f9cb88a661fe473721469a00bbfcd98b818b10d52c7ff2`。attempt001缺旧导入对象、attempt002普通证明API/归一化错误均保留在作者failure-ledger，均已reaped且没有成功对象；只认证最终attempt003字节。

首成功对象原已单次记录SHA256 `2f8b40f8cc499c03d57b75fe1879ac20c5e4705a453e9c9db1967a576336455f`。本审稿只stat：dev64947/inode5125382/size974672/mtime_ns1792831223172324371完全吻合。旧核心首对象dev64947/inode5112450/size605688/mtime_ns1792829561372923682及Bridge sole对象dev64947/inode3539971/size341208/mtime_ns1792741872471617276也只stat复用。

全部111 runtime-view对象与103实际项目导入绑定当前路径／stat：旧110项复用此前已合格B的保存stat JSON `9412d24ef30ff42d342874cd9556745223a6a73467db29d30fc138e5d93c63f0`，新增1项为既有合格Bridge的保存stat。没有把当前新观察冒充过去快照。mtime_ns全过程是Python整数，未经JavaScript Number。

18项compact的服务器和本地字节／哈希均独立核验，manifest `2ed5c26f2edda0e3d4d5943e82a96bf066d2e823247cc50cd067b1ac150f1e9e`；原saved native JSON `eeabd97d1382e03ad504886f0ca9968a6a0f9fd6b5de6636d46fd26dffedb276`。详见本目录local/server只读核验及qualified-old-inputs。初次适配既有只读核验脚本时，111路径view中旧110项不内嵌stat造成KeyError；保留failed001响应，改为读取已合格旧stat快照后全部通过。它没有运行Lean、修改输入或产生数学失败。

JUSTIFICATION: 六个冻结声明忠实表达固定Rademacher严格／闭边界临界商及明确新增算术推论。全部新证明、边界/零概率前缀、实际StrictMono与完整聚点外包含、实际所属展开接口和全传递公理均正确，并精确绑定同次首成功内核与对象。A报告及收据固化后只等待另行交付的B，不重写或重审A。所有原研究根组OPEN。
