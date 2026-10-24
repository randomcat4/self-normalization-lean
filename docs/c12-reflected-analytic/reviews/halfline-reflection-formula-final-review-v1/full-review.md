# 单元 26：半直线显式反射公式独立完整终审

STATUS: CORRECT

本结论严格绑定 `Shao.C2.HalfLineReflectionFormula` 的最终 4863 字节源码，SHA256 `e852b2878fe686464158ce509b45de20c5cc8c478e65316e25d39bf6543dbf8c`。六个公开定理、两个透明定义、八个实际生成辅助定理的全部完整类型，以及两个定义的完整实际值已独立读完；源码全部证明已逐步审阅。没有发现关键数学缺口、冻结前提变化或覆盖遗漏。

审稿人是新上下文 `/root/halfline_reflection_formula_final_review`，与作者 C12 lead `01a16c4c-25a6-7740-a10e-12635a13edae` 分离。按分派使用 gpt-6.1-sol / xhigh、math-theorem、中文优先；没有使用 math-ultra、子代理或其他证明者。审稿人只写本报告目录，没有编辑生产源码、冻结文件、作者收据、共享文件或 Git，没有执行 Lean、lake、缓存写入或重放成功检查。输入、缓存输入、输出及推理子集用量不可获取，均记录为 null。

## 精确冻结与来源范围

冻结文件 `frozen.lean.txt` 的 SHA256 是 `86c2293d120cad59f4b6dd6cf205207771ceb6f1be9baef80da09d64cea28f7f`，1580 字节。独立脚本仅删除各公开定理的证明体；余下完整导入、命名空间、两个定义值、六个完整定理头与冻结文件逐字相同。服务器 attempt001–004 的同一投影均产生该冻结哈希；前三次失败保留，修订没有改变冻结假设、定义或结论。最终源码及冻结字节均为 UTF-8、无 BOM、LF、CR 数为零；没有重新格式化冻结字节。

原始只读来源 `C:/game/shao/current/c12/supplement.tex` 第 4192–4253 行已完整阅读。4194–4206 行定义的是正时间、内点上的严格布朗桥生存概率及另行规定的边界、零时间延拓；4212–4222 行固定墙和终点，定义位移与剖面；4224–4244 行要求含剖面的高阶混合导数、墙处单侧估计、PDE 及补偿 Taylor 余项；4247–4253 行给出半直线的显式反射表达及指数吸收思路。

本单元形式化的是显式实标量函数的分析依赖：高斯一次因子吸收、正距离斜率界、固定墙/终点/时间时关于起点的真实一阶导数，以及常数 4、不含剖面因子的导数界。它没有把任何布朗桥概率或热核商识别为这两个函数。没有证明原文带 P 的一阶界或任意高阶混合导数，也没有证明区间正则性、墙处单侧估计、PDE、Taylor 余项。所有 C12/OQ3/OQ4/OQ56 原根组保持 OPEN。

## 逐个源码证明及语义审阅

**两个定义（源码 11–15 行）。** `upperReflection a y T z = 1-exp(-2(a-y)(a-z)/T)`；下半直线把两个减号改为加号。参数次序都是 `a y T z : ℝ`。实际值导出中的全部运算实例确实是标准实数减法、乘法、除法、指数函数；数值 2 的生成证明 `upperReflection._proof_1` 仅用于 `Nat.AtLeastTwo (1+1)`。两个完整实际值与源码定义相符。这里是总实函数，并未实现来源的“墙外置零”或“零能量内点置一”延拓。`a` 不受正性限制是一条合法的标量平移推广，不能据此把 `a=0` 时的函数解释为来源的完成概率。

**`gaussian_linear_absorption`（17–25 行）。** 对任意实数 r，`(r-1/2)^2≥0` 推出 `r≤r^2+1`；`Real.add_one_le_exp` 给出 `r^2+1≤exp(r^2)`。乘以严格正的 `exp(-r^2)` 保持不等式，指数加法给乘积 1。证明覆盖负 r 与 r=0，没有额外正性假设或有限数值检验代替一般证明。实际完整类型恰为 `∀ r : ℝ, r*exp(-(r^2))≤1`。

**`positive_reflection_slope_bound`（27–70 行）。** 冻结及实际类型均量化 `u,v,T : ℝ`，保留三个严格正性条件。置 `s=√T`，由 `T>0` 得到 `s>0`、`s^2=T`，所有倒数变形均有非零分母。若 `v≤2|u-v|`，指数非正，故指数函数不超过 1，再依次界为 `2v/T≤4|u-v|/T=(4/s)(|u-v|/s)≤(4/s)(1+|u-v|/s)`。在补情形，`-abs(u-v)≤u-v` 和 `v>2abs(u-v)` 蕴含 `v≤2u`，乘以正 v 得 `v^2≤2uv`。除以正 T 并取负号，得到 `-2uv/T≤-(v/s)^2`；指数单调性与 `v/s>0` 保持方向。抽出 `2/s` 后应用上一条吸收界，最后 `2/s≤(4/s)(1+|u-v|/s)`。两个分支穷尽，非负乘子均有证明；等号边界进入第一分支。

**`upperReflection_hasDerivAt`（72–81 行）。** 固定 a、T、z，先对 `a-y` 求导为 -1，再乘 -2、乘 `a-z`、除以常数 T，指数的导数为 `2(a-z)/T`。对 `1-exp(...)` 求导，得到负号的冻结公式。`convert` 中的函数等式由定义展开，系数等式仅为环化简，没有改变被求导变量或终点。实际完整类型是对全部实 a、y、T、z 的 `HasDerivAt`，没有隐藏条件。

**`lowerReflection_hasDerivAt`（83–92 行）。** 对 `a+y` 求导为 +1，指数导数为 `-2(a+z)/T`，再由外层 `1-exp` 的负号得到正的 `2(a+z)/T` 因子。证明、实际类型、冻结正负号与参数次序全部一致。常数除法的求导允许 T=0：按实数总除法，两个函数在 T=0 时均恒为 `1-exp(0)=0`，显示的导数也为 0。因此无正时间假设的两个可导性定理正确，但它们没有表达来源的零时间完成概率约定。负时间同样只是良定义标量函数，不被解释为概率。

**`upperReflection_deriv_bound`（94–102 行）。** 先消费前述 `HasDerivAt` 的 `.deriv`，真实地获得导数值，随后取绝对值。`T>0`、`z<a` 保证斜率前因子正，指数永远为正。代入斜率界 `u=a-y>0`、`v=a-z>0`；距离差精确化为 `u-v=z-y`。结论确为 `|deriv (...) y|≤(4/√T)(1+|z-y|/√T)`，没有用不可导时总化导数为零的漏洞。

**`lowerReflection_deriv_bound`（104–114 行）。** 使用下半直线真实可导性与 `.deriv`，由 `-a<y,z` 得 `a+y,a+z>0`，代入 `u=a+y,v=a+z`，距离差为 `y-z`，再用绝对值对称性变为 `|z-y|`。时间、两端点和全部正性条件在实际完整类型中均保留。无端点距墙的正下界，且 a 不受限制。两个界都只宣称严格内点、T>0；墙端点或 T=0 未被悄悄纳入这些界。

## 实际所有权与全部类型覆盖

完整读取的 `actual-owned-types.txt` 有 21657 字节，SHA256 `6ef92e70392b3a6eaa62691e2985407a531acbf6624565b21a3ed5e11f08dab1`；两个完整定义值在 1950 字节文件中，SHA256 `b5e0d800379629be837f9b009e797e8dba59fc0b7b574e31e38319d834f9faff`。所有公开类型与以上冻结接口逐项吻合；额外生成定理也已完整阅读，未仅按名字或数量接受。

实际所属声明为 16 个：6 个公开定理、8 个生成辅助定理、2 个透明定义。辅助类型逐项如下，均为合法通用代数/数值实例命题，不携带概率、微分或原根结论：

| 完整命名空间 `Shao.C2.HalfLineReflectionFormula.` 下的辅助名 | 完整类型的语义（所有类型类前提保留阅读） |
| --- | --- |
| `upperReflection._proof_1` | `Nat.AtLeastTwo (1+1)` |
| `positive_reflection_slope_bound._simp_1_1` | 对有 Zero、数值 2 和相应 NeZero 实例的任意类型，`(2=0)=False` |
| `positive_reflection_slope_bound._simp_1_2` | 上一条的数值 3 版本 |
| `positive_reflection_slope_bound._simp_1_3` | 上一条的数值 4 版本 |
| `positive_reflection_slope_bound._simp_1_4` | 在 Mul、Zero、NoZeroDivisors 下，a、b 均非零蕴含 `(a*b=0)=False` |
| `positive_reflection_slope_bound._simp_1_5` | 在 MonoidWithZero、IsReduced 下，任意自然数 n，a 非零蕴含 `(a^n=0)=False` |
| `positive_reflection_slope_bound._simp_1_6` | 在 GroupWithZero 下，任意整数 n，a 非零蕴含 `(a^n=0)=False` |
| `positive_reflection_slope_bound._simp_1_7` | 在 AddMonoidWithOne、CharZero 下，任意自然数 n，`((n: R)+1=0)=False` |

每个实际类型的独立内容哈希与条目都记录于 `local-checks.json` 和 `evidence.json`。16 个类型条目的名字集合与实际所有权审计集合完全相同，无遗漏、重复或错误分母。两个完整定义值已单独阅读，不以类型或摘要代替。

## 机械证据复用及绑定

作者服务器收据 `receipt.json` SHA256 `bc317d24523edb05615fd3f98dd89dc12d6a70457c41d099ecb513181fb65e77` 报告 attempt004 内核退出码 0、实际全所属审计退出码 0。本次只读观测时间为 `2026-10-24T08:07:42.993207+00:00`。独立验证服务器生产源码和 attempt004 快照均为最终源码哈希；成功输出对象与 `.lake/build/lib/lean/Shao/C2/HalfLineReflectionFormula.olean` 导入对象均为 `479ce890330887f671e1b0f2a9142514230830bd9d5416db24dabd142eaecbe3`，593768 字节，且源码→对象→审计时间顺序一致。没有源旁另一份对象。服务器原收据与本地收据逐字哈希一致。

收据中的 13 项原始审计/类型/值/尝试快照及日志的 SHA256、字节数逐项与服务器实物一致，包含前三次失败证据。完整实际类型导出与完整定义值导出由原审计日志独立提取后，分别与本地已读文件逐字相等；原日志末尾是 `AUDITED_TARGET_CONSTANTS 16 PUBLIC 6 THEOREMS 14 DEFINITIONS 2`。无需复制完整日志到本工作区或重复运行审计。

`OwnedAudit.lean` 全文已审阅：遍历 `env.constants.toList`，以 `env.getModuleIdxFor? name` 解析 `env.header.moduleNames` 的真实所属模块，选取所有目标所属常量，未用名称前缀过滤。对每一个被选声明调用传递闭包意义的 `Lean.collectAxioms name`，仅准许 `propext`、`Classical.choice`、`Quot.sound`；对全部实际完整类型和两个非定理值输出证据。所得 16 行逐个为该模块所有，种类总数为 14 定理、2 定义，6 个公开定理齐全，公理集合全部在白名单内。源码无 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。没有转储定理证明项，生成辅助类型覆盖没有省略。

只读核对 `lean-toolchain=leanprover/lean4:v4.36.0-rc1`、mathlib Git HEAD `807d3836b165983210ee2ecf3cd28f239436949c`、既定 `cache-overlays/shared-v34/packages` 链接、分支 `author/c12-uniform-permutation-law-v71`、当时 HEAD `fe32939af989d80cfebfb9c245d456a63b262ce6`。收据规定 CPU14–17、`c12-heavy.lock`、`-M8192 -j4`。日志只有既有 mathlib 本地变化提醒，无本单元错误；没有修改缓存、工具链或包。作者发布前的 `RELEASE.json` SHA256 `b33e315b4a7a1fa3e34a527d4cafd44d536913c4aa257f86e602a3c14a02be9d` 绑定相同源码、对象及收据，并释放写作/执行，无在途任务。只读进程观测没有本模块 Lean/lake 命令；其他所有者命令保持原样。

## 裁决与保留义务

数学正确性：CORRECT。精确冻结目标有完整证明；完整实际类型和定义值均已独立覆盖；绑定既有服务器内核及全所属传递公理收据的证据链通过。可以复用本终审与该精确源码的原成功机械证据，不应因换上下文再运行一次。

来源忠实性：本单元作为半直线显式公式的一阶、无剖面分析依赖忠实，不能把这个较弱辅助结果当作原文整个导数/Taylor 引理或概率反射原理。布朗桥概率识别、区间正则性、含剖面及高阶混合导数、墙处单侧估计、PDE、Taylor、所有根结论继续 OPEN。该单元不提出新颖性或论文级贡献认证；常数 4 是此辅助界的显式常数。

本报告发出后，审稿人释放本单元报告写作权与执行权；无在途工具/Lean/重命令。后续单元 27 的其他文件及父实例 Git 元数据不属于本次数学改动或证据失效条件。
