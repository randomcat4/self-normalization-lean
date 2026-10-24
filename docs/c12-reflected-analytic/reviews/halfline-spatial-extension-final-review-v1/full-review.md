# 单元41、42独立最终完整审阅

结论：**CORRECT**。两个最终冻结目标均无关键缺口。完整覆盖12个公开源码证明及全部冻结头、导入和上下文，18个实际模块所属完整类型（16定理、2定义，含4个生成定理），以及两个完整透明空间截断值。原始 C1/C2 等研究根继续 **OPEN**。

评审者 `/root/halfline_spatial_extension_final_review` 与作者 `01a16c4c-25a6-7740-a10e-12635a13edae` 分离。此为明确配置 `gpt-6.1-sol / xhigh` 的新鲜独立终审上下文，使用一个C12子槽，无下派。使用 math-theorem 和中文输出规范；仅写本评审目录。平台未暴露 input、cached input、output、reasoning subset 使用数，四项均为 null，不以估计值代替。

## 原文与冻结目标

完整阅读只读原文 `C:/game/shao/current/c12/supplement.tex` 第4192–4253行。源对象是在 a>0、T>0、两端点内部时的严格 Brownian 桥存活概率；墙上和墙外为零延拓。原文定义 d=z-y、D=1+|d|/sqrt(T)、监控墙剖面 P 和 P_b，提出墙上一侧导数界，以及 b²<=T/2、新空间点在闭域内时的补偿余项界。

单元41、42的冻结对象是**显式半直线反射标量公式在空间变量 y 上的零延拓**，固定 a、T、z。上半线是 `if y<a then upperReflection a y T z else 0`；下半线是 `if -a<y then lowerReflection a y T z else 0`。这完整实现固定内部终点、正时间及正壁参数下的空间截断语义。它们未把任意 z 的公式宣称为对两个端点同时截断的源概率函数；源的零能量及 a=0 约定也没有被这些全实参数标量定义识别或证明。

对源码去除每份定理证明后，与对应 freeze 的完整字节投影完全相同，包括2个定义的完整值、12个完整声明、导入、命名空间、参数顺序与前提。当前源均为 UTF-8、无BOM、LF。冻结目标没有改变或隐藏前提。

## 单元41：闭半直线上的实际零延拓

完整阅读 `HalfLineSpatialExtension.lean` 的8份源码证明及两个完整定义。

1. `upperSpatialExtension_eq_closed`：将 y<=a 分成严格内部和墙点。内部由分支条件直接相等；y=a 时空间截断值是0，解析公式为1-exp(0)=0。该恒等式对任意实 T 成立，因为分母为固定参数且 Lean 实数除法是全定义的；它只是标量恒等式，没有引入源的T=0物理律。
2. `lowerSpatialExtension_eq_closed`：对 -a<=y 同样分解。墙点 y=-a 使 a+y=0；下壁方向正确，没有将 y<=a 的条件误用到下半线。
3. `upperSpatialExtension_iteratedWithin_eq`：先在整个 `Iic a` 上证明截断函数减1与解析函数减1的精确 `Set.EqOn`。`iteratedDerivWithin_congr` 因此转移任意自然阶 j 的域内导数。随后使用 `uniqueDiffOn_Iic a` 和解析函数的真实 `ContDiffAt ℝ j`，在 y∈Iic a 处识别为实际全域解析迭代导数。解析式只是仿射函数、固定常数除法和指数的复合，对全部实空间点光滑；`fun_prop` 没有被要求证明截断函数跨墙光滑。
4. `lowerSpatialExtension_iteratedWithin_eq`：同一完整论证作用于 `Ici (-a)`，实际点条件 -a<=y 完整保留。`uniqueDiffOn_Ici (-a)` 包括墙点。本定理也包含 j=0：两边是各函数减1的值，墙点均为-1。
5. `upperSpatialExtension_iteratedWithin_profile`：用前述精确导数恒等式改写后，直接消费已合格单元40的闭域解析剖面。自然阶要求 j>0；T>0、y<=a、z<a 与旧接口完全一致，常数 `(8*j/sqrt(T)*D)^j` 和 `upperProfile` 保持不变。墙点 y=a 明确属于范围。
6. `lowerSpatialExtension_iteratedWithin_profile`：消费下半线闭域剖面，条件 -a<=y、-a<z 保持；D中的差仍为 |z-y|。全部正自然阶及墙点 y=-a 均受覆盖。
7. `upperSpatialExtension_wall_hasDerivWithinAt`：消费已合格单元26的全域解析 `HasDerivAt`，在 y=a 简化指数为1，得到真实系数 `-2*(a-z)/T`。限制到 `Iic a` 后，通过整个闭集上的相等关系及墙点自身的成员证明转移到实际空间截断函数。结论确为 `HasDerivWithinAt`，不是形式上的默认导数值。
8. `lowerSpatialExtension_wall_hasDerivWithinAt`：在 y=-a 简化下壁公式，系数为 `+2*(a+z)/T`，闭域为 `Ici (-a)`。正负号、墙点和值传递均独立核算正确。

墙点一阶证书保留 a>0、T>0 和终点严格内部三个源前提，即使相应纯标量恒等式可更强。一般闭域恒等式和剖面没有虚构跨壁全域可微性；在物理非退化情形中，外部常零函数的斜率与上述内侧非零斜率不同，不能推导跨壁可微。

## 单元42：实际空间截断的导数与补偿小泰勒界

完整阅读 `HalfLineExtensionTaylor.lean` 的4份源码证明及全部冻结上下文。

1. `upperSpatialExtension_hasDerivAt_interior`：hy:y<a 给 `Iio a` 是 y 的整个开邻域；对其中每个 x，截断分支与解析公式相等。以 `HasDerivAt.congr_of_eventuallyEq` 转移完整解析导数证书，得到实际截断函数的全域局部导数。没有用单点相等替代邻域相等。
2. `lowerSpatialExtension_hasDerivAt_interior`：`Ioi (-a)` 是 y 的开邻域，处理方向与下壁一致。实际导数系数为正 `2*(a+z)/T` 乘指数。两个辅助证书允许全实参数，因为它们只证明固定时间下的标量局部解析性质；物理解释仍限制在正时间、正a、内部终点。
3. `upperSpatialExtension_small_taylor_bound`：使用单元41的闭域恒等式，将未来 `upperSpatialExtension a (T-b²) z (y+b)` 精确改为解析反射值；hnew允许未来点恰好在墙上。旧点的严格内部条件 hy 给旧值恒等式及实际截断函数的真实 `HasDerivAt`。其 `.deriv` 将实际 `deriv (upperSpatialExtension a T z) y` 改写为已验证的解析导数，然后与已合格单元39的导数证书作相同改写，完整余项与原不等式逐项相同。
4. `lowerSpatialExtension_small_taylor_bound`：对下壁使用 -a<=y+b，旧点、终点仍严格大于-a。补偿因子仍精确为 `b-b²*(z-y)/T`，没有因下壁坐标反射而改变源中的 d。右侧剖面为 `exp(-max(a+y-|b|,0)*(a+z)/T)`，正确对应墙符号-1。

两个定量定理都保留 a>0、T>0、旧端点和终点严格内部、b²<=T/2、新点闭域条件。hsmall 给 T-b²>=T/2>0，未来值不调用任何零能量约定。常数8000100、|b|³、(1/sqrt(T))³、D³与相应 P_b 全部保持。b=0时余项为0；未来点恰好等于墙时反射值和截断值均为0。未添加最小墙距或额外正则性前提。

## 实际所属完整类型与透明值

逐个完整、无缩略读取两份原始 `actual-owned-types.txt`，分别23970字节、26961字节；未使用结构摘要替代类型。14+4个实际所属声明全部与 owner 映射精确一致。12个公开实际类型与冻结声明中的实数类型、自然数阶、严格/非严格边界、导数函数、时间参数顺序和所有常数一致。

单元41另外4个生成定理也完整覆盖：两个 `.eq_1` 的完整类型是截断定义与对应 `ite` 值相等，包括真实 `Real.decidableLT`；两个 `*_eq_closed._simp_1_2` 的完整类型是任意宇宙、任意预序上 `x<x` 这个命题等于 `False`，不含额外数学前提，仅依赖 propext。不存在未覆盖的其他命名空间所属常量。

两个实际定义的完整 `VALUE` 块共704字节，逐项核对了参数顺序 a,T,z,y、严格不等式方向、分支中的反射参数顺序 a,y,T,z 与常零分支。单元42的非定理所属数为0，值导出确为空，SHA256为 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。逐声明类型/值哈希见 `actual-type-coverage.json`。

## 内核、公理及当前字节绑定

完整读取两份原 `OwnedAudit.lean`：通过 `env.getModuleIdxFor?` 选择实际模块所有者，不以命名空间前缀过滤；遍历每个所属常量，并对每项调用递归 `Lean.collectAxioms`。原结果是单元41共14所属=12定理+2定义、8公开源定理；单元42共4所属=4定理+0定义、4公开源定理。所有传递公理只在 propext、Classical.choice、Quot.sound 白名单中，两个生成简化定理只使用propext。源码无 sorry/admit/新axiom/unsafe/native_decide。

只读服务器观察核实18个原receipt工件的SHA256和字节数，包含保留的失败尝试。两份当前生产源与原成功快照、输出对象与安装对象分别完全一致；18个完整类型块及两个完整值块均逐块精确出现于原审计日志。复用41的attempt003和42的attempt001成功内核/全所属公理回执，退出码均为0。41的attempt001/002保持归档，修复只涉及证明中的beta展开和集合成员推断，完整冻结头/值未变。42首轮即通过。

原kernel日志仅含已知mathlib本地变更提示、弃用的if_pos/if_false名称和41墙点证书未使用的源物理前提警告，无error。只读观察首轮因服务器没有rg可执行文件而在定位mathlib接口时失败，记录在 `inspection-first-failure.json`；使用grep完成相同只读查找，不涉及任何Lean/audit重跑或生产变更。

观察时工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`，分支 `author/c12-halfline-taylor-v71`，HEAD `39f0716ef70c0c388f2902a374860451df10ea27`。Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 和只读包视图 `cache-overlays/shared-v34/packages` 均与原回执相同。原资源回执为CPU14–17、c12-heavy.lock、-M8192 -j4；评审未执行重命令，未触及外部CPU0–9/80GiB任务。

只读读取了实际mathlib接口及完整变量上下文：`iteratedDerivWithin_congr`、`iteratedDerivWithin_eq_iteratedDeriv`、`uniqueDiffOn_Iic/Ici`、`HasDerivWithinAt.congr_of_mem`、`HasDerivAt.congr_of_eventuallyEq`。相应假设正是完整集合上的相等、集合唯一微分性质、解析 `ContDiffAt`、点成员或完整邻域相等；源码逐一满足。文件哈希和所读完整接口保存在 `mathlib-interfaces.json`、`mathlib-deriv-context.json`。

## 依赖复用与范围裁决

精确复用单元39/40联合终审（JSON SHA256 `815a92d347798b380ece64ee317caa3d121654a527a8a48e42f6c9db162b8964`）、反射公式26、空间剖面32和首阶剖面30的合格独立完整评审。核实五项依赖的原评审、作者receipt/release、评审释放、当前源、输出及安装对象的精确绑定。完整读取本次消费的完整冻结接口及透明反射/剖面值，不重新审查或编译旧证明。

两个局部冻结目标可接受，无关键缺口，无冻结范围内未覆盖项。该结论仅接受源绑定辅助标量接口；并未证明实际Brownian概率反射识别、实际区间核完整正则性/混合界、源零能量或a=0约定，亦未声称C1/C2原根闭合或研究新颖性。

## 精确验收绑定

单元41 `Shao.C2.HalfLineSpatialExtension`：

- sourceSHA256：`24ea5b54cd351d4bf92feb25fee1ac8360122525edee3ed97737b40c3c4866b7`
- objectSHA256：`7d9878ba6bd77c0a4b93a99f82531f4cb66c8f7682d00cb09d81e5fb1a7c10da`
- frozenSHA256：`18dce7801a24ed9644b91b6a4ae2df8d00a3c2c335090cac90e04bab8e1736bd`
- authorReceiptSHA256：`7d9db3e3d753199403e1bfd5a7b0dd15b01932f662f48e2c4aaedeb58994d079`
- authorReleaseSHA256：`1f7e063f11fc2f4b2520e7267d0c1e6245b11e3de5f438cf2aafd0fe7b41d022`

单元42 `Shao.C2.HalfLineExtensionTaylor`：

- sourceSHA256：`8f5dd1220bad6e15a108386b0814a0dc1dabb7cc088ee2374392d42b304b63be`
- objectSHA256：`deadea923ae90d8398156806d103e03d606bae372716b58515683b261704dd47`
- frozenSHA256：`856d14a39161cce4189d997f69c2e66162ab490f78ba6724ce6e8338c3b65568`
- authorReceiptSHA256：`6034ebf36b9c616c2972d4705fdf05e4b51a5a5c53bc37864a023970f62f39f0`
- authorReleaseSHA256：`0a72e43e5a1fe24790f2cd2153806747651c0b670c6d84b851b32064a0641518`

全部写入完成后，由 `writer-release.json` 绑定最终报告及证据哈希。评审写入权、执行权均释放，无在途任务、无重命令。
