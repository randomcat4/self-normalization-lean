# 第 43、44 单元独立完整最终审阅

STATUS: CORRECT

两个冻结单元在其精确陈述与已说明的源范围内正确，未发现关键缺口。第 43 单元的六个证明、第 44 单元的四个证明、十个完整声明及全部上下文与头部 `F₁/F₂` 值已逐项完整阅读；34 个实际所属类型均按原始未删节导出完整阅读。两个完整定义值导出均为空，所属映射确认没有非定理常量。本文是完整最终审阅，不是仅语义、接口或机械检查摘要。

审阅者为新鲜独立上下文 `/root/halfline_extension_calculus_final_review`，作者为 `01a16c4c-25a6-7740-a10e-12635a13edae`，协调者为 `01a16be2-3e35-7e13-97d3-7b11b603dead`。模型/推理配置为显式任务指定的 `gpt-6.1-sol/xhigh`；没有启动子上下文。实际分项用量未由平台暴露，输入、缓存输入、输出、推理子集均记为 `null`，不估算订阅占用比例。

## 精确绑定与检查覆盖

| 单元 | 公开源证明 | 实际所属定理 | 其中生成定理 | 非定理定义 | 完整类型字节数 |
|---|---:|---:|---:|---:|---:|
| 43 `Shao.C2.HalfLineExtensionTimeProfiles` | 6 | 21 | 15 | 0 | 52615 |
| 44 `Shao.C2.HalfLineExtensionPDE` | 4 | 13 | 9 | 0 | 14517 |
| 合计 | 10 | 34 | 24 | 0 | 67132 |

43 的全部 117 行源文件与 44 的全部 63 行源文件已读完。移去证明正文所得的投影逐字节等于各自冻结文件，包括导入、命名空间、全部变量/假设、结论及完整头部 `let` 值；两源文件均为 UTF-8 无 BOM、LF，禁止标记扫描无 `sorry/admit/axiom/unsafe/native_decide`。

| 绑定 | 单元 43 SHA256 | 单元 44 SHA256 |
|---|---|---|
| 当前源码及成功快照 | `8112034038cb606e5b07f768bfb7e716ba2aead5a9de4d8954a3ec38098cd70b` | `9c62e604d941e5bb831ef6cdf2589e919563be1a5c977c9b8b19214e3235f918` |
| 原成功输出及当前安装对象 | `b5e2f82dab63f39666d3973490260c5a4968f614cf421716e08b82bef04fefdd` | `70789b18c6499251b8ac2c3edac03ebfc79c9643aa3111bf8588dc270cb8caf5` |
| 冻结文件 | `6111bd4dc3212d10a8441fd84bd81474b0483bd2aade3cd5087f9c6ee47cc8db` | `9b4cc43fb3863c28a5828d5b9575c76818828d71b167ca60b11376109eb2e544` |
| 作者检查收据 | `e70182b935bcaad374a9fd42378ad47a3f249c73a920cbb800aba5a5d6fa28c5` | `4c17f0426dfe167d6cf08bd827a3f531ea575155efe4efe8d1b75f116dfc9410` |
| 作者释放文件 | `8199e00ef49727812e4d16a9660392001e120ac074c042d752517bbc7113fcaf` | `be553e6f6a7f6d583a9e2bfac7cace6954dd6c44da678ce2ffda5a8a526df335` |
| 完整实际类型导出 | `8d5854392091d5f37759394eb2922eef01c97a1adeadaea515e36bcd095bad6f` | `166544a410cca1bcbf39848405ccbdd0778373251c99893bd323469dddd56270` |

两个空值导出的 SHA256 均为 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`，字节数均为 0。全部实际类型名称、类型块散列、完整类型散列与分类见 `actual-type-coverage.json`；不存在通过名称前缀筛选而漏掉的所属常量。特别地，名称位于旧命名空间的 `Shao.C2.HalfLineMixedProfiles.curvatureTime.eq_1` 实际归属于单元 43，已连同其完整类型审阅并计入 21，而未归回旧模块。

服务器当前分支为 `author/c12-halfline-extension-v71`，观察到的 HEAD 为 `467e398d5468d0614ba0ae97406cd3a5df6c4a69`，工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`。源码可能尚未提交，资格依据是上述实际文件与对象散列，不以 HEAD 代替文件版本。完整本地、服务器及原审计日志绑定见 `local-bindings.json`、`remote-observation.json`、`verified-bindings.json`。

## 原文与解释范围

已完整阅读只读 `C:/game/shao/current/c12/supplement.tex` 第 4192–4253 行以及 4302–4315 行，包括生存核商定义、零扩展/零能量约定、原始 `D/P/P_b`、偏导方向与墙面说明、PDE、补偿余项和 Taylor 使用上下文。没有读取或宣称验证未分配的区间级数展开。

正时间、正墙参数且固定终端严格内点时，所用显式半直线公式为 `f=1-exp(-2uv/T)`，上侧 `u=a-y,v=a-z`，下侧 `u=a+y,v=a+z`；`D=1+|z-y|/sqrt(T)`，单墙 `P=exp(-uv/T)`。本单元中的空间切断只针对起点空间坐标，终端始终固定且在物理解读中严格位于内部。没有把它当作对任意终端的完整双端点概率延拓。

整个实时间轴上的辅助恒等式以及任意实数 `a,z` 的墙时间函数定理，只谈 Lean 中已明确总定义的标量切断公式。它们不宣称原文 `T=0` 或 `a=0` 概率约定。第 43 单元的轮廓界无需 `a>0` 的纯解析强化是有效的；物理解释仍限制为原文 `a>0,T>0`。第 44 单元 PDE 保留 `ha : 0<a`、固定终端严格内点、正时间条件，允许旧起点在墙上。

## 单元 43：六个证明的完整核对

1. **`upperSpatialExtension_spatial_time_functions`**：对所有实数时间，先调用已独审的 `upperSpatialExtension_iteratedWithin_eq`，把闭集合 `Iic a` 内真实 `iteratedDerivWithin` 的 1、2 阶导数转为显式解析反射函数的全局迭代导数；再用已独审的全实时间 `upperReflection_iteratedDeriv`。一阶结果为 `-slopeTime(a-y,a-z,t)`，二阶结果为 `curvatureTime(a-y,a-z,t)`。负号正确，第二项定义正是负平方乘指数。`funext t` 给出整个时间函数相等，未对单点等式直接求导。

2. **`lowerSpatialExtension_spatial_time_functions`**：同样使用 `Ici(-a)` 的已认证集合内导数。下侧解析系数为 `-(2(a+z)/t)` 的幂，再有最外层负号；在 1 阶产生正斜率，2 阶由 `neg_sq` 消去内层符号，得到相同负曲率。上下方向和闭墙条件完全对应，未用跨墙可微性。

3. **`upperSpatialExtension_mixed_time_profiles`**：已完整核对头部 `F₁/F₂` 是切断函数减 1 的真实集合内 1、2 阶空间导数随时间组成的函数，并非抽象代理函数。先按前述整个时间函数相等重写，再以 `u=a-y>=0`、`v=a-z>0`、`T>0` 调用 `mixed_time_profiles_nonneg`。证明中的 `hn1` 是全函数等式 `deriv(-slopeTime)=fun t => -deriv(slopeTime)t`，`hn2` 再对该函数恒等式使用 `deriv.neg`，得到二阶时间导数整体负号；取绝对值后消除。读取并核对了钉死 mathlib `Deriv/Add.lean` 260–290 行：这里使用的确为无额外可微前提的 `deriv.neg` 及对应函数版本，源码与钉死 Git blob 散列相同。没有错误地只重写在 `T` 点的值。

4. **`lowerSpatialExtension_mixed_time_profiles`**：`u=a+y>=0,v=a+z>0`，一阶空间导数为正斜率，直接复用相同非负距离混合轮廓。`u-v=y-z`，用绝对值对称性转为原文 `|z-y|`；上侧 `u-v=z-y`。所有符号、平方和参数位置均正确。

两混合定理中三项按顺序是 `(j,l)=(1,1),(2,1),(1,2)`，常数和尺度分别为 `80 T^(-3/2) D P`、`6144 T^(-2) D^2 P`、`800 T^(-5/2) D P`。旧起点允许在墙上；使用的是 `u>=0` 已认证接口，没有把严格内部版本误用于 `u=0`。正时间处 `slopeTime/curvatureTime` 的已有 `HasDerivAt` 接口也保证这些是实际导数，不借助不可微时总导数的缺省值获得空洞估计。

5. **`upperSpatialExtension_pure_time_profiles`**：用闭域值等式建立整个时间函数与 `timeCompletion(C)` 相等，其中 `C=2(a-y)(a-z)>=0`。调用已独审的三阶纯时间轮廓后，严格以 `T!=0` 化简 `-C/(2T)=-(a-y)(a-z)/T`。于是常数 `2,12,108` 依次对应 `T^(-1),T^(-2),T^(-3)` 乘 `P`。`C=0` 包含墙面，整个时间函数此时为零，证明仍成立。

6. **`lowerSpatialExtension_pure_time_profiles`**：整个时间函数改用 `C=2(a+y)(a+z)>=0`，其余调用条件与指数恒等式相同。没有引入端点距离的正下界。公开陈述的纯时间导数作用于 `f`；它与源式中 `f-1` 的正阶时间导数由常数平移求导律一致，不能把本项误读为新定义了另一种概率核。

## 单元 44：四个证明的完整核对

1. **`upperSpatialExtension_wall_time_function`**：在起点 `y=a`，严格内部条件 `a<a` 为假，逐时间展开明确的切断定义即得常零函数。结论是完整函数相等，不只是某个时间的迹值。

2. **`lowerSpatialExtension_wall_time_function`**：在 `y=-a` 同理，严格条件 `-a<-a` 为假。两辅助引理适用于所有实数 `a,z,t` 的显式标量定义；没有附加原文零能量概率含义。

3. **`upperSpatialExtension_heat_equation`**：先将整个切断时间函数识别为 `timeCompletion(2uv)`，再用正时间 `timeCompletion_hasDerivAt` 获得实际时间导数 `-2uv/T^2*exp(-2uv/T)`。单元 43 的两个完整函数等式在 `T` 处求值，得到真实闭域 1、2 阶空间导数 `-2v/T*exp(-2uv/T)` 和 `-4v^2/T^2*exp(-2uv/T)`；这一步只评价已证明的函数等式，不对单点等式求导。`T>0` 保证清分母有效。PDE 右边为 `[-2v^2-2v(z-y)]/T^2*exp(-2uv/T)`，因 `v+z-y=u`，精确等于时间导数。

4. **`lowerSpatialExtension_heat_equation`**：时间导数相同，空间一阶改为 `+2v/T*exp(-2uv/T)`，二阶仍为负曲率。PDE 右边为 `[-2v^2+2v(z-y)]/T^2*exp(-2uv/T)`，因 `v-(z-y)=u`，再次等于 `-2uv/T^2*exp(-2uv/T)`。`ha/hz` 即使在部分代数步骤未被引用，仍完整保留在冻结及实际类型中，没有弱化物理陈述。

PDE 中集合内空间导数作用于切断函数减 1，正阶常数平移不改变其导数，与原文 `f_y/f_yy` 一致。墙上 `u=0` 时，真实时间导数为 0；上侧 `d=-v`、下侧 `d=v`，右边两项分别为 `-2v^2/T^2` 与 `+2v^2/T^2`，精确抵消。没有把切断函数在墙外的常零性与墙内空间导数混在一起，也没有宣称跨墙全局光滑。

## 依赖复用与服务器机械证据

完整阅读了实际消费的冻结接口及上下文：41 的闭域值/集合内导数接口，32 的两侧全实时间迭代导数，33 的 `timeCompletion_hasDerivAt`、三阶轮廓与两侧整个公式识别，40 的闭距离混合轮廓；以及有关的 34 斜率/曲率可微接口。完整阅读了 `upper/lowerSpatialExtension`、`upper/lowerReflection`、`slopeTime`、`curvatureTime`、`timeCompletion`、`upper/lowerProfile` 的实际透明定义值；顺带完整读了同一值导出中的 `intervalProfile`，但未将区间结论纳入本次结果。

复用的完整最终独审为：41/42 联审 `805384db49164aa800d40233bd99e0687b3d8eb042b26b3b2e253e48db2ea48b`；39/40 联审 `815a92d347798b380ece64ee317caa3d121654a527a8a48e42f6c9db162b8964`（本次消费 40）；32 审阅 `207cdaed8fd92e51545abfdc8cbebb5e31e83392f457a40f2b18fcb788a95b81`；33 审阅 `92378ff6a2bf4a732a27927ccc9989ea1f8d4fd94e3885c8a7f5af1bff521c14`；34 审阅 `08f1a0c45b250d3763b38dec80a1b5e834af6e55a474f0fbfa5f41d5646d90a3`；30 所在联审 `1fcc2466a834a04850bc45b0287058b02dd89443edbaa2dc6209b5a04d13a81f`；透明反射定义所在旧审阅 `7f994541cb9e7999a0007570f92314086c9f5db9e999c171716c0d5a4e7a3240`。均核对既有 `CORRECT`、作者和审阅者释放、作者收据，以及本次消费的当前源码/原输出/当前安装对象的精确散列，没有重审旧证明或重新编译旧生产者。42 作为直接导入也已绑定，虽本次十个证明未消费其 Taylor 结论。

复用 43 `attempt002`、44 `attempt001` 的作者内核与全所属传递公理检查；所有 16 项原检查工件（含 43 的保留失败版本）按收据逐一绑定。原成功日志已完整读取且无错误，全部未删节类型块与原审计日志精确对应。审计程序依据 `env.getModuleIdxFor?` 选择全部实际所属常量，并对每项运行传递的 `Lean.collectAxioms`；34 项全部只依赖 `propext, Classical.choice, Quot.sound`。两个原检查的退出码及审计退出码均为 0。

版本为 `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，包视图为共享只读 `cache-overlays/shared-v34/packages`。作者资源收据记录 CPU14–17、`c12-heavy.lock`、`-M8192 -j4`。审阅者没有执行 Lean、审计、旧生产者构建、成功门重放或缓存写入。

43 保留的失败 `attempt001` 仅为上侧负号导数自动化匹配失败；其完整冻结投影与最终冻结散列相同。最终证明以显式整个函数负号求导恒等式修正，失败源码和日志继续保存在服务器。44 无失败检查。原成功日志的弃用名称、未使用变量/策略和既存 mathlib 工作树提示均未构成数学缺口；所实际核对的 `deriv.neg` 源文件散列与钉死版本完全一致，未为消除提示改动已冻结字节。

本次只读补充观察有一次审阅脚本路径选择错误：误取旧反射生产者的 `attempt001`，而其原收据明确成功快照为 `attempt004`。错误观察及纠正说明保留于证据；仅补读受影响的正确快照散列并验证匹配，没有重复任何 Lean/审计或成功证明检查。这不是生产证明失败。

## 裁决及剩余范围

两个单元分别为 `CORRECT`，冻结目标内无遗漏或关键缺口；结合精确复用的内核/公理证据，二者均可按本项目的 `LEAN_FULLY_CHECKED` 口径接受其局部冻结范围。正确性、原文范围与机械验证分别核对，没有用编译成功替代源语义审阅。

这批结果是显式半直线切断公式的集合内空间/时间微积分辅助层，不是新的概率反射原理，也未证明实际 Brownian 路径生存概率与该显式公式的识别、区间核的完整导数/PDE、原文的 `T=0/a=0` 概率约定或整个补偿 Taylor/原始根结论。C12/OQ3/OQ4/OQ56 原始根组仍为 `OPEN`。新颖性不在本次资格内，不能将这些解析推导宣传为原问题全部解决。

审阅工件只写入本目录，生产源码、冻结、共享协调文件、Git、缓存均未修改。完成后的精确报告绑定与无在途释放见 `writer-release.json`。
