# U16c v2 独立声明、来源与静态环境审查

STATUS: CORRECT

唯一审查 lease 1，仅拥有本报告和服务器 statement-review-v2.md；不修改任何 v1/v2 scope、旧报告、实现、共享文件或缓存，不 spawn，不运行 Lean/probe/构建。并非独占代码库，保留他人编辑。承认既有 v1 声明上下文存在，本次仍先只提取冻结 v2 fence 的完整定义体和定理类型，独立重新盲译并保存，尚未读本次 scope 说明或两版差异。

## 第一阶段：v2 完整体与完整类型盲译

输入 thirty-ninth-unit-scope-v2.md，实际 SHA256 `8623fcad91638c2ba30b59612a2d57e0c785948e75d815c653a7a1b8d16e129e`。

`gaussianRateProfile` 对任意实数 S,T,b,y,z 定义 y²/(2S)+(z−by)²/(2T)。定义自身使用总化实除法，并未要求分母非零；定理的 S,T>0 门负责给出真正二次代价解释。b 可正负，不是预先定义的实际协方差参数。

`exists_cubic_rate_weight_margin`：固定实参数 q,ell,S,T,b,D,radius，分别要求 q>0、ell≥0、S>0、T>0、D≥0、radius>0，并有严格 ell<q/(32T)。再输入任意实二元函数 I，假设所有满足 |y|+|z|≤radius 的点上，profile(S,T,b,y,z)−D(|y|+|z|)³≤I(y,z)。在这些条件之后同时存在三个严格正实数 delta/gamma/c；对全部自然 n≥1、全部实 k≥0 和任意有符号实 r，只要 k/(n:ℝ)≤delta、|r|/(n:ℝ)≤delta、(n:ℝ)qk/16≤r²，就有 gamma*k+c*r²/(n:ℝ)≤(n:ℝ)I(−k/(n:ℝ),r/(n:ℝ))−ell*k。

delta/gamma/c 在全部 n/k/r 之前选定；n≥1 是实际除法门，k 不限为整数，r 不能当作非负。D0、ell0、有符号 b、k/r 零边界都在完整类型内。真正 hI 的原点 l1 半径条件必须先由两个比值门共同建立。实际 I/Legendre/Hessian/Taylor 生产者没有在这里输出；结论只是给定局部三次下界之后的确定性权重余量。

独立类型初判仍需核严格 gap 1/(2T)−16ell/q>0、二次交叉项的有符号控制、三次误差对同一正小邻域的吸收与所有量词；不能沿用任意未核对的 v1 文本或将规范导入更名当作内核验收。本段先落盘，再比对 v1/v2 冻结 fence、真实来源和实际静态库环境。根 A/B/C/D、实际率 Taylor/Hessian、负层概率、完整 LLT 与 hW 均保持 OPEN。

## 第二阶段：v1/v2 逐字节比较与真实来源

本次盲译先落盘后，才读取完整 v2scope、对照 v1scope 和 v1完整报告。实际 v1scope SHA256 `9f660ea048c1b2a89ea4ce7f983ef60d8f631561fd52e7c3612bb538979f4133`，实际 v2scope SHA256 `8623fcad91638c2ba30b59612a2d57e0c785948e75d815c653a7a1b8d16e129e`。本地和真实远端对应值一致；远端保留 scope.md v1 为4213字节、scope-v2.md 为4961字节。

两份完整 Lean fence 的原始 UTF-8 字节完全相同，不只是去空白相同；其共同 SHA256 是 `7fd5a5da0c6a82d2fb966392ed911864ea73b058ff2ce932917e95e8e3e38829`。完整公开定义体和完整目标签名，包括所有参数、假设、三次余项、n/k/r量词、因子16/32及结论，均未改变。全文差异只涉及冻结版本标记、说明中的导入路径 Data.Real.Basic→Basic.Real.Basic、相应缓存名称和新增透明环境修订记录；无数学假设或结论变化。旧 v1报告实际 SHA256 仍为 `e75a5553346aea1a2e272a2cad0af8f94b05e14d0ef52b84f79b85233f97672a`，本地与远端旧 statement-review.md 同为13014字节；没有覆盖或更正历史。

经上述实际一致性核查，可以承接已核 v1 数学，但本票在下文完整重新呈现论证和源对应，独立自包含并绑定 v2，不要求读者另读旧票才理解裁决。此次没有任何实现、内核检查、API probe 或机械通过可用，不能以导入更名充当证明。

真实来源 R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，本次再直接核243–250和368–384行，沿用此前完整核对的238–258、348–392行语义。第370–371行真实率的 inverse-covariance 二次项加三次 O 余项，第378–383行负层曲边约束 r²≥nqk/16 后给 nI−ell k≥gamma k+c r²/n。概率 Chernoff(16)、真实 Legendre 定义/展开生产者、全局正尾率唯一性和远区严格率间隙属于另行义务，不是本定理的输出。

真实绑定需要 S=Var(Y)>0、C=Cov(Y,X)、T=Var(X)−C²/S=实际 tau²>0、b=C/S。此时 detCov(Y,X)=S T，直接展开真实矩阵逆二次项等于 y²/(2S)+(z−by)²/(2T)。T 是方差而不是标准差 tau；来源 kappa²/2=q/(32tau²)>ell 与本门 ell<q/(32T) 精确对应。source379的曲边因子16也原样保留。当前 v2依然只给通用 S/T/b 与明确局部三次下界 hI；真实协方差/Hessian/Legendre/Taylor 构造不能由此记为完成。局部确定性比较不需全局唯一性，不据此升级完整(17)概率结论。

## 第三阶段：独立数学证明可行性与所有系数门

以下给出完整独立数值论证以检验该声明，而非写 Lean 实现。设

`A=1/(2T), d0=16/q, B=|b|/T, g=A−ell*d0, E=B*d0+4D*(d0+1)`。

由 q>0、T>0，A,d0>0、B≥0。严格 hgap 乘 d0>0 后恰好得到 ell*d0<A，即 g>0；这里确实使用32=2*16，不能误用 ell<q/(16T) 或 T=tau。D≥0 给 E≥0，故 E+1>0。S>0 后续只用于舍去非负项，不偷加对 S 的大小门。

可以同时选择

`delta=min 1 (min (radius/2) (g/(2*(E+1)))), gamma=g/(4*d0), c=g/4`。

1、radius/2、g/(2(E+1)) 都严格正，所以 delta>0；同时 gamma,c>0。delta≤1、2delta≤radius，且 delta(E+1)≤g/2；再用 delta≥0 得 delta E≤g/2。没有除 E，所以 D=0、b=0、E=0 时选择依旧合法。所有见证只依赖先固定的数值参数；虽然类型允许它们也依赖 I/hI，此处甚至不需要这样依赖。它们在全部 n/k/r 之前一次性确定。

任取 n≥1，记 N=(n:ℝ)>0。取任何实 k≥0 和带符号 r，令 u=k/N≥0、v=|r|/N≥0、w=r²/N≥0。由两个小比值门，u,v≤delta。由事件 N q k/16≤r²，分别除以正数 N、q 得 k≤d0*w，再除 N 得 u≤d0*v²，其中 w=N v²；所有等式及除法门在 N>0、q>0 之后使用。

邻域门必须先建立：|−k/N|+|r/N|=u+v≤2delta≤radius。于是实际 hI 可在 y=−u、z=r/N 合法实例化。这里不能把单独 u≤radius、v≤radius 当成 l1 邻域，也没有将 hI 应用到未知是否合法的点。

完整二次型先独立下界。对任意 y,z，展开平方、利用 S,T>0 舍掉 y²/(2S) 和 b²y²/(2T) 两个非负项，再用 −(b/T)yz≥−(|b|/T)|yz|，得

`gaussianRateProfile S T b y z ≥ A*z²−B*|y*z|`。

这一步保留并控制交叉项，不将 b 默认正或直接丢掉可能为负的交叉项。在 y=−u、z=r/N 处，|yz|=uv、N*z²=w。因此 hI 乘 N>0 后给

`N*I(−u,r/N) ≥ A*w−B*N*u*v−D*N*(u+v)^3`。

交叉误差：由 N u≤d0*w 且 v≤delta、所有量非负，有 Nuv≤d0*delta*w。注意 r 可为负，实际估计只用了 v=|r|/N，不用错误的 r≥0。

三次误差可逐步控制为：

`(u+v)^2≤2(u²+v²)`，因为 (u−v)²≥0；
`(u+v)^3≤4delta*(u²+v²)`，因为 0≤u+v≤2delta；
`u²≤delta*u≤delta*d0*v²≤d0*v²`，因为 u≤delta、u≤d0 v²、delta≤1；
所以 `N*(u+v)^3≤4delta*(d0+1)*w`。

乘 B,D≥0 后误差方向不变，得到真实

`N*I(−u,r/N) ≥ (A−delta*E)*w`。

再以 ell≥0 和 k≤d0*w 给 −ell*k≥−ell*d0*w，从而

`N*I(−u,r/N)−ell*k ≥ (g−delta*E)*w ≥ (g/2)*w`。

ell≥0 在这个替换方向上真实有用，并非仅为源叙述；ell=0 则等式边界完全允许。最后 gamma>0 与 k≤d0*w 给

`gamma*k+c*w ≤ (gamma*d0+c)*w = (g/2)*w`，

精确得到目标 gamma*k+c*r²/N≤N I(−k/N,r/N)−ell*k。上述选择及每个比较均同时对全部 n/k/r 成立，未逐点缩半径或调整 gamma/c。三次余项系数、交叉项与两个源数值因子均已独立验算，scope 的 E 选择确实充分。

边界审查：b 任意负/正/0 均由 |b| 控制；D=0 不触发除0；ell=0 仍有 g=A>0；n=1 时 N=1、所有步骤同样成立；n=0 被显式排除，不从0分母总化获结论。k=0 时只需控制 z² 与三次误差，逻辑不除 k；r=0 时正 N/q 和事件强制 k=0，hI 给 I(0,0)≥0，输出成立；k=r=0 亦无例外。delta,gamma,c 严格正且 q/S/T/radius 的严格正门均保持，没有移用源中固定 q 范围或概率存在性条件。

## 第四阶段：v2 规范导入与实际静态环境

指定服务器重新只读核对 canonical 模块及其 public import 图、既有 olean 和 pins；没有执行 Lean/API probe/构建或写缓存。v2直接导入 `Mathlib.Basic.Real.Basic`，规范源 SHA256 `f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f`，实际无 deprecated_module 标记；第8–10行 public import CauSeq.Completion、Order.Ring.Rat、Rat.Cast.Defs，第359行 instIsStrictOrderedRing、第471行 linearOrder、第481行 instField 为真实 ℝ 提供声明所需的有序域结构。

历史 `Mathlib.Data.Real.Basic` 兼容源 SHA256 `a1d6fa90c0e6ddc98b82933e33801713f937030bc1d70052afb6794c3637a65d` 仅 `public import Mathlib.Basic.Real.Basic` 加弃用标记。因此 v2直接规范导入精确保留原有数学环境，去掉旧兼容入口，没有为证明增加公理、改实例、改实除法或削弱门。其既有规范 olean 实际存在，326160字节；没有重新编译模块，也不由此承诺尚不存在的目标构建无任何其他警告。

v2其余直接 imports 为 Mathlib.Tactic.FieldSimp、Ring、Positivity、Linarith、NormNum，均实际有既有 olean。沿 v2六个直接导入的真实 public 路径递归699个 Mathlib 模块，无缺失源码；相对 v1公开图700个节点只去掉兼容入口。没有任何 Shao 项目依赖，更无未来率函数/概率/CLT缓存依赖。scope 的 namespace Shao.OQ3、noncomputable section 不改ℝ域实例，不需 open scoped Matrix、BigOperators 或默认 volume。

实际所需 API 的完整静态语义仍为：

- `Mathlib/Algebra/Order/GroupWithZero/Basic.lean` SHA256 `28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c`874–875行 div_pos；1128–1141行 le_div_iff₀/div_le_iff₀/lt_div_iff₀/div_lt_iff₀ 都要求正分母。上文为 N/q/T/d0/E+1 逐一提供正性，不会反转不等式或用总化除0。FieldSimp → FieldSimp.Lemmas → 该实际模块的公开导入路径存在。
- `Mathlib/Algebra/Order/Field/Basic.lean` SHA256 `fabd3062223bbdcd4efae38a4a586f88241f67da533e79ee06c56ba507c27b2d`673–674行 abs_div；Positivity直接 public import该模块，因此|r/N|=|r|/N在N>0后可见可用。
- `Mathlib/Algebra/Order/Ring/Abs.lean` SHA256 `afad3c8ac856f0019cb16aeb194e452613aee2bfe400e82c2e2a7becd89a5abe`49–52行 abs_mul、第81行 sq_abs，经 Positivity → Field.Basic → Ring.Abs 的实际公开路径可见，用于有符号交叉项与 v² 的精确表达。
- min的有序性质、平方非负、正数乘法和自然数cast正性都在现有有序域环境；FieldSimp/Ring/Linarith/NormNum足以承担上述有限域运算和多项式比较，不需任何测度、Hessian、积分、矩阵范数、平方根或额外实例。当前仍是声明可行性审查，尚未核验任何目标证明脚本。

真实 toolchain `leanprover/lean4:v4.36.0-rc1`，lean-toolchain SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`，实际 mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`，与此前核实的库源语义相同。v2规范导入不缺缓存、类型、实例或所需公开 API，没有静态环境阻塞。

## 最终 v2 独立声明裁决

STATUS: CORRECT

JUSTIFICATION: v2完整公开定义体与完整目标签名经原始字节核对和v1完全相同，重新盲译已先落盘；来源、严格系数间隙、统一正见证、真实hI邻域、有符号交叉项与三次误差吸收的完整数值论证如上自包含成立。D0/ell0、b任意符号、k/r零边界、n≥1正分母、全部n/k/r之前的delta/gamma/c量词均无缺口。唯一实质环境修改直接使用实际规范 Basic.Real.Basic，保留原有有序域与API、已有缓存且不再通过弃用wrapper；旧v1scope和票的原字节/哈希保持。未发现需修订的数学、来源、类型或静态环境问题，可批准v2进入实现；本票不是内核或目标/Audit验收。

本单元仅为显式局部下界假设之后的确定性局部余量步骤。不证明实际率为Legendre变换，不生产实际Taylor三次下界或Hessian/协方差绑定，不给真实负层概率/Chernoff、紧倾斜族统一质量常数、全局唯一最小值或远区间隙；无完整LLT/hW/根闭合/最优性/新颖性结论。实际率Taylor、Hessian、负层概率、完整LLT、hW及根A/B/C/D均OPEN。只写本新报告及授权远端v2副本，未改任何源/scope/旧票/共享文件/缓存，未spawn/Lean/probe/build。
