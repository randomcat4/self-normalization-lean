# 第36单元独立最终审查

STATUS: CORRECT

本审查覆盖冻结的 `Shao.C2.HalfLineTaylorPath` 全部五个公开定理、两个透明定义、全部证明，以及服务器实际所属的16个完整类型和两个完整定义值。冻结目标内没有关键缺口。本单元只闭合显式半直线表达式的路径微分及二阶补偿恒等式；所有原始 C12/OQ3/OQ4/OQ56 根结论仍为 OPEN。

## 独立性与精确版本

审查者为全新上下文 `/root/halfline_taylor_path_final_review`，与作者分离；指定模型 gpt-6.1-sol、推理强度 xhigh。实际模型遥测与分项用量未向本上下文暴露，因此 input、cachedInput、output、reasoningSubset 均记 null，不估算订阅比例。本上下文没有子代理，没有生产、冻结、共享、Git 或缓存写入。仅在本审查目录写报告。没有运行 Lean、审计或旧生产者编译。

| 精确工件 | SHA256 |
|---|---|
| 最终源，6838字节 | `583f9a625518a3aebd9dc8aa6831c54928cdf0a86336303db5d5f0806960cb2b` |
| 输出及已安装对象 | `2e486b607214ced2ec698879ff67cc81bcea4264458510b2905de155661b127e` |
| 冻结，2203字节 | `2190681b1367f342e8e57b10436dd9625dfc1513e6ffa8705f188cdb2e70d5ba` |
| 作者检查收据 | `fd12df89080942cc33a2b96bc04796d031f5ab45dcc5528739e0eedd7afd6ec2` |
| 作者写入及执行释放 | `45b7cfb17bfeb244e915f8051607d0cf2127cd683e4e85678cdf5154b572c44b` |
| 完整实际类型导出，43375字节 | `4464e98fb80ff80d60ed4219018631b0f68bb58552f3ce0c29b07243108385c6` |
| 完整定义值导出，1612字节 | `b284159611822892934847d142a1abbeceecc9a4202722ccd7a5effcdd527e55` |

首次只读服务器观察分支为 `author/c12-halfline-spacetime-v71`，HEAD 为 `b677029b26987a90d0dbfa50a3500d19b062208d`。定稿前再次只读核对，分支已按父实例授权转换为 `author/c12-halfline-taylor-v71`，HEAD 为 `39f0716ef70c0c388f2902a374860451df10ea27`；第36单元及三个已审查依赖的全部源和已安装对象均逐字节不变，见 `final-state.json`。最终工具链、mathlib manifest/实际HEAD、共享包视图也与固定版本相符。当前源、attempt006源快照、输出对象、已安装对象均与收据相符。17个收据工件的字节数和哈希全部匹配。attempt001–006 的完整 imports/namespace/声明头/两个定义值投影均与同一冻结文件逐字节相同；保留001–005的源和失败日志。最终源为 UTF-8、无 BOM、LF，未发现 sorry/admit/新 axiom/unsafe/native_decide。

## 原文语义与真正路径

完整读取只读 `C:/game/shao/current/c12/supplement.tex` 第4192–4253行。第4234–4237行定义 actual reveal 从 `(y,T)` 到 `(y+b,T-b²)`，减去 `(b-b²d/T)f_y`；第4247行给出半直线显式式 `1-exp(-2uv/T)`。本模块的参数化为

\[
U_\theta=u-\theta b,\quad E_\theta=T-\theta b^2,\quad
q_\theta=-2U_\theta v/E_\theta,\quad g(\theta)=1-e^{q_\theta}.
\]

这正是二变量泰勒线段的标量参数，时间方向是 `−b²`，不是对空间位移 `θb` 再平方。两透明定义的完整实际值与该表达式完全相同。`A=exponentSlope=2vb(T-ub)` 不依赖 θ。无须 u、v 为正即可证明这里的局部解析等式；物理概率解释和三次余项估计没有包含在冻结目标中。

## 五个证明的逐项审查

**一阶导数，源14–33。** 先对真实仿射函数证明 `E′=−b²`、`U′=−b`，商法则所需 `E≠0` 由 `E>0` 得出。独立化简为
\[
q'=\frac{2vb(E-Ub)}{E^2}=\frac{2vb(T-ub)}{E^2}=A/E^2,
\quad g'=-A E^{-2}e^q.
\]
源中的函数外延转换只识别同一个函数；随后 field_simp/ring 使用已给出的非零分母，未添加前提。实际完整 HasDerivAt 类型的函数、点和实数导数均与冻结头一致。

**二阶导数，源35–66。** 对显式一阶函数 `−A E⁻² exp(q)` 使用商法则及乘法则。因 `(E⁻²)′=2b²E⁻³`，所得导数为
\[
g''=-(A^2/E^4+2Ab^2/E^3)e^q.
\]
源64–66不是对一点等式求导：由 E 的连续性和开正半轴得到 θ 的完整邻域上 E(t)>0，再逐点使用一阶 HasDerivAt 的 `.deriv`，以 `congr_of_eventuallyEq` 将显式函数转移成真正的 `deriv g`。实际导出确实是 `HasDerivAt (deriv g)`。

**三阶导数，源68–104。** 对 `−(A²E⁻⁴+2Ab²E⁻³)exp(q)` 求导。系数部分导数为 `−4A²b²E⁻⁵−6Ab⁴E⁻⁴`，再乘指数导数项 `A/E²`，合并得
\[
g'''=-(A^3/E^6+6A^2b^2/E^5+6Ab^4/E^4)e^q.
\]
源102–104同样先在完整正能量邻域以二阶证书识别 `deriv (deriv g)`。实际类型中的嵌套 deriv、三个幂次及两个系数6完整一致，未把“显式二阶公式的导数”冒充真实三阶导数。

**有限阶光滑性，源106–116。** 任意自然数 n 下，E 与 U 均为仿射函数；E(θ)>0 给出局部商所需非零分母，常数、乘法、商、指数和减法组合产生 `ContDiffAt ℝ n g θ`。完整实际类型中 n 被正确转换为 WithTop ENat 的有限阶数。n=0 与任意更高有限 n 均包括；冻结声明没有另行声称一个形式化的无限阶参数结论。

**源补偿恒等式，源118–131。** 由 T>0 得 E(0)=T>0，合法代入前两个真实导数证书及已合格审查的 slopeTime/timeCompletion 时间导数证书。全部分母只需 T≠0。独立源语义推导：上半线 `f_y=−slopeTime`、`d=u−v`，路径给出 `g′=bf_y−b²f_T`、`g″=b²f_yy−2b³f_yT+b⁴f_TT`。因此
\[
g'(0)+\tfrac12g''(0)-(b-b^2d/T)f_y
=b^2[-f_T+\tfrac12f_{yy}+(d/T)f_y]
 -b^3f_{yT}+\tfrac12b^4f_{TT}.
\]
对显式半直线式，中括号的精确代数抵消正好是源 PDE；最后两项等于 `b³ deriv(slopeTime u v) T + (b⁴/2) deriv (deriv (timeCompletion (2uv))) T`。实际证明直接代入已验证公式再做有理环等式，并未把未证明 PDE 当作新增前提。冻结头两边、1/2、补偿系数和全部符号逐项相符。

下半线取 η=−1、β=ηb=−b、`u=a+y`、`v=a+z`，则 `u-v=−d` 且物理 `f_y=+slopeTime`。归一化补偿 `(β−β²(u-v)/T)(−slopeTime)` 正是 `(b−b²d/T)f_y`；三次混合项随 β³ 反号，四次时间项不反号。原文墙与终点固定的约定保持一致。这是参数替换的语义核对，不扩大成概率识别定理。

边界核对：b=0 使 A=0，三个导数与补偿式均正确退化；v=0 或 A=0 同理。u=0 不妨碍局部解析公式。θ 可为任意实数，只要求使用点 E>0；不要求 θ∈[0,1] 或 b²≤T，因为本单元未断言全线段余项界。E=0、墙外零延拓及完整概率边界仍在本单元范围外。

## 完整实际所属覆盖

完整 pp.all 类型导出第1–319行与320–663行均已原样读完；两个定义值也完整读完，没有以摘要或缩略表达式代替实际阅读。16个完整类型块和两个完整值块均逐块验证为哈希绑定的原始 `owned-audit.log` 中连续原文。逐块哈希、字节数、行号及语义结论见 `complete-type-value-coverage.json` 与 `full-review.json`。

审计的归属选择为 `env.getModuleIdxFor?`，不是命名空间前缀。计数由实际映射导出：16常量=14定理+2定义，14定理=5公开+9生成/辅助。特别纳入名称位于旧命名空间但实际属于本模块的 `Shao.C2.HalfLineTaylorSegment.segmentEnergy.eq_1`，其完整类型确认为 `T−θb²` 的展开等式。七个 `_simp_1_2` 至 `_simp_1_8` 分别是2、3、4非零、非零乘积、自然幂、整数幂及自然数铸型加一非零的通用命题，条件全部实际存在；`completionAlongSegment._proof_1` 为自然数1+1的 AtLeastTwo 辅助证书。没有遗漏私有或生成常量。

## 检查收据与既有依赖复用

复用作者 attempt006 退出0的定向内核检查及退出0的实际全所属递归公理审计。所读审计脚本对每个实际所属常量调用 `Lean.collectAxioms`，拒绝白名单外依赖；所有16项只使用 `propext`、`Classical.choice`、`Quot.sound`。固定 Lean 为 `leanprover/lean4:v4.36.0-rc1`，mathlib 为 `807d3836b165983210ee2ecf3cd28f239436949c`，共享包视图 `cache-overlays/shared-v34/packages`。作者资源为 CPU14–17、c12-heavy.lock、-M8192 -j4。成功日志无 error，现有提示为继承的包工作区提示和 tactic/linter 提示，不影响内核通过。

已完整读取本单元实际消费的 `segmentEnergy`、`segmentDistance`、`slopeTime`、`timeCompletion` 类型/透明值，以及 `slopeTime_hasDerivAt` 和 `timeCompletion_second_hasDerivAt` 的完整实际类型与源声明头。复用三个既有完整独立审查，不重读旧证明、不重编译旧生产者：

| 单元 | 合格完整独立审查 SHA256 | 当前源/已安装对象 |
|---|---|---|
| 35 HalfLineTaylorSegment | `0ff0cc92f656a87761ab28d636b7c4d141b13f4d0c89ad874e0273fec9f6fae7` | 匹配 |
| 34 HalfLineMixedProfiles | `08f1a0c45b250d3763b38dec80a1b5e834af6e55a474f0fbfa5f41d5646d90a3` | 匹配 |
| 33 HalfLineTimeProfiles | `92378ff6a2bf4a732a27927ccc9989ea1f8d4fd94e3885c8a7f5af1bff521c14` | 匹配 |

三个旧审查均为 CORRECT、具完整合格独立审查标记，其绑定的源、对象、收据、作者释放及本地导出工件全部一致；当前服务器对象未变。没有发现新交互风险或未覆盖的声明范围需要重复旧证明审查。

## 接受边界与释放

本单元可按上述精确源版本接受；冻结目标内未发现关键缺口。尚需另行闭合实际半直线概率识别、带合法区间前提的泰勒余项应用、原文一致三次 profile 余项界、墙/零延拓/零能量以及其他原始 C1/C2 根依赖。本审查不主张原创研究新颖性，也不将局部解析恒等式提升为完整源定理。

审查已完成。审查者释放本目录写入与执行权；heavyInFlight=false、inFlight=[]，没有待完成的后台作业或检查。确切报告哈希见 `writer-release.json`。
