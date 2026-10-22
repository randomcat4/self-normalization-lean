# OQ4 弱格点位移 DA1：匿名独立数学审查 v1

STATUS: CORRECT
MODE: MATH_ONLY
SCOPE: DA1_AND_SAME_DOMAIN_LEGALITY
MATHEMATICAL_RESULT: CORRECT_RELATIVE_TO_FIXED_SCA0_SCA1_SCA2
NEW_RAW_LEAF_COUNT: 0
LEAN_STATUS: NOT_RUN
FORMAL_CERTIFICATION: NOT_GRANTED_BY_THIS_REPORT

本轮为全新隔离上下文中的匿名数学独立审查。结论是：以指定固定 Scalar 接口 SCA0、SCA1、SCA2 的精确结论为唯一项目数学上游，匿名稿完整证明了冻结 DA1 及全部同域合法性；未发现关键缺口、量词弱化、隐藏尺度条件或反例。此结论由下文逐步推导核对得到，不依据作者的 PROOF_READY 标签或任何调度状态。

这里的“相对于固定上游”是依赖账说明，不能据此将最终 DA1 改写为带自由 Taylor 界、自由参数函数或任意上游估计假设的条件定理。后续形式实现必须实际承接同一固定对象的已认证 SCA 声明。当前上游尚待形式认证；本报告不声称 Lean 通过、canonical 写入、DA2、实际 S3/S4 或 OQ4 根已完成。

## 一、输入锁定与读取边界

以下四份文件是本轮全部数学输入。读取时逐一测得 SHA256 与字节数，均与派发值相同；后文行号针对这些锁定字节。

| 数学输入 | SHA256 | 字节数 | 本轮用途 |
| --- | --- | ---: | --- |
| drafts/oq4/frozen-rademacher-lattice-shift-v1.md | 9cf9dba01aa9582ceb8e4d30af06c4778b8b367b61e61562dfc42c7ffb0e2b56 | 6067 | 最终冻结命题、同域合法性、完整量词及排除范围 |
| drafts/oq4/rademacher-lattice-shift/proof.md | aefff15a1b80173ee362f58b60448699df70bbc8bc729a44f593a8b4099a6bb8 | 9818 | 唯一受审匿名证明 |
| drafts/oq4/frozen-rademacher-scalar-bounds-v1.md | 225b63ae8522a126cb5c126f83cb782b024e95f592e9e2da5f36f56e0ce21356 | 9414 | 仅以固定定义及 SCA0/SCA1/SCA2 精确结论作为项目数学上游 |
| C:/game/shao/current/oq4/c01/spectrum01.md | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 4306 | 核对弱胞元、真实 a/rho、lambda 与确定性位移系数；只读 |

原来源提交标识 35d4580b61e22e7145f47730045a09874ef93259 按允许材料登记；本轮没有另外检查 Git 历史。来源第11–12行规定弱胞元 m=floor(h)、H=m+1；第36行的 a_H、rho_H 与冻结定义相同；第60行的 lambda=pi²/8 与受审稿相同；第66–67、70–77行分别识别待处理的确定性表达式和位移系数。原文的渐近尺度没有充当本有限界的假设；原文也没有被当成全域统一界的现成证明。

另读取了工作区 AGENTS.md、SERVER.md、coordination/TEAM.md，以及 math-theorem 技能及其 prompt-library、openai-workflow、lean-verification 必需规则、chinese-output-style 与 windows-shell7 技能。这些仅提供职责、隔离和执行约束，不提供本命题的数学证明。所有 shell 调用的工作目录均为 C:/game/shao lean。

未读取 intake/candidate/source-semantic 报告、任何其他匿名数学证明或数学/形式审查、作者 notes/checkpoints、任何新实现或旧项目证明体、上游 Scalar 证明/实现/审查。允许文件中出现的其他文件指针、历史状态字段和范围外来源段落可见，但没有沿指针打开其他数学文件，也没有将其状态文字或范围外概率结论用作证明依据。禁读文件曝光：无。本轮没有联网、没有运行 Lean、没有做形式声明忠实性或传递公理审计。唯一写入物为本审查报告；四份输入均未改动。

## 二、精确目标与假设账

冻结文件第33–47行固定：m 为自然数且 m>=1；H(m)=(m:Real)+1；u(m)=pi/(4H(m))；a(m)=H(m)^(-1) cos(u(m))/sin(u(m))；rho(m)=cos(pi/(2H(m)))；lambda=pi²/8。实数 h 只满足 (m:Real)<=h<(m:Real)+1；delta=H(m)-h 是其确定函数；n 为任意自然数，N=(n:Real)。

冻结第61–81行要求存在一个绝对 C>0，在选取全部 m、h、n 之前选定，使

\[
\left|\lambda N/h^2+N\log\rho(m)+\log(\pi a(m)/4)
       -2\lambda N\,\bigl(H(m)-h\bigr)/h^3\right|
\le C\left(N/h^4+1/H(m)^2\right).
\]

2lambda=pi²/4，故此式的符号、系数与冻结 DA1 完全一致。目标还要求冻结第49–57行的合法性，不能额外假定正分母、a>0、rho>0 或对数自变量为正。

唯一项目上游的精确可用内容如下。

| 依赖 | 精确内容 | 本轮处理 |
| --- | --- | --- |
| SCA0 | 同一固定 m/H/u/z/a/rho 的 H>=2、H>0、H²>0、H⁴>0；0<u<=pi/8<pi/2、0<z<=pi/4<pi/2；sin u>0、cos u>0、cos z>0；a>0、0<rho<1、pi a/4>0 | 逐项与 Scalar 冻结第53–68行核对，作为固定上游结论承接，未重新假定为 DA1 参数条件 |
| SCA1 | 存在绝对 C_a>0，对所有 m>=1，\(\lvert a(m)-4/\pi\rvert\le C_a/H(m)^2\) | 只用于内部对数界；未读取其证明 |
| SCA2 | 存在绝对 C_rho>0，对所有 m>=1，\(\lvert\log\rho(m)+\lambda/H(m)^2\rvert\le C_{\rm rho}/H(m)^4\) | 用于 DA1 汇总；未读取其证明 |

Scalar 冻结第74–91行将 C_a、C_rho 联合存在性置于全部 m 之前。受审稿第47–56行忠实承接这一量词顺序。H、a、rho 从未替换成自由实参数或代用函数。Scalar 冻结第106–114行明确没有冻结 C_log 为上游输出，受审稿确实另行证明；C_tan 未消费。

基础分析依赖为实数有序域运算、pi>0、正弦余弦的基本值域与符号、三角函数及实对数的导数、单调性判据与拉格朗日中值定理。以下同时核对了其使用点的区间和符号条件；这些标准基础事实没有藏入新的项目待证核心。

## 三、同域合法性审查

受审稿第78–94行逐步给出：由 m>=1 和 h>=m 得 h>=1>0；H=m+1>=2>0。故 h²、h³、h⁴、H²、H⁴ 都严格为正且非零。h<H 给 delta=H-h>0，h>=m 给 delta<=H-m=1；定义本身给 H=h+delta。因此所有固定域结论

\[
h\ge1,\quad h>0,\quad H\ge2,\quad H>0,\quad H=h+\delta,
\quad 0<\delta\le1
\]

都真实推出。这里没有独立量化 delta，也没有将 H 扩成任意实数。

同一 m 的 SCA0 给 sin u>0、cos u>0、a>0、0<rho<1、pi a/4>0。H、2H、4H、sin u 均严格正；数值分母 2、4、8 及后续约分中的 pi 均非零。rho 与 pi a/4 的实对数均在严格正自变量上使用。后续新增的 c、xi 也分别证明严格正，见下一节。因此分母与对数合法性均为结论或固定上游结论，没有进入最终 DA1 的自由前提。

## 四、内部 C_log 的独立核查

对应受审稿第98–151行。由固定 SCA1 的 C_a，先于任何 m、h、n 定义

\[
c=\cos(\pi/8),\quad D_a=\pi C_a/4,\quad C_{\log}=D_a/c.
\]

因 0<pi/8<pi/2，c>0；由 cos 的值域 c<=1，故 0<c<=1。pi>0、C_a>0 给 D_a>0、C_log>0；这三个常数均绝对。

1. 对 t>=0，f(t)=t-sin t 满足 f(0)=0、f'(t)=1-cos t>=0，因而 sin t<=t。对 0<=s<=t<=pi/2，cos 的导数为 -sin，sin 在该区间非负，故 cos s>=cos t。两项基础估计均适用于 SCA0 给出的 0<u<=pi/8。因此 0<sin u<=u，且 cos u>=c>0。
2. 令 q=pi a/4。按固定 a 和 u 的定义及已核对的非零分母，精确有 q=(u/sin u)cos u。由 sin u>0 和 u>=sin u 得 u/sin u>=1；乘以 cos u>0，得到 q>=cos u>=c。该正下界覆盖全部 m>=1，不依赖 SCA1 的误差在某阈值后变小。
3. 用 pi 非零约分，q-1=(pi/4)(a-4/pi)。因 pi/4>0，SCA1 给 \(\lvert q-1\rvert\le D_a/H^2\)。这里未使用任何未冻结的二阶系数。
4. q=1 时 \(\lvert\log q\rvert=0\)，结论直接成立。q!=1 时，将中值定理应用于闭区间 [min(q,1),max(q,1)]。因 q>=c、1>=c、c>0，整个闭区间位于正半轴；log 在其上连续、内部可微，导数为 1/x。存在内部 xi，满足 xi>=c>0 且 log q-log 1=(q-1)/xi。这同时覆盖 q<1 与 q>1，不需要事先断言 q 的上界。
5. 因 log 1=0 及 xi>=c>0，得到

\[
|\log q|=|q-1|/\xi\le |q-1|/c
\le D_a/(cH^2)=C_{\log}/H^2.
\]

因此受审稿式(8)是真正在本文内部证明的全域统一界。MVT 的非退化区间、连续可微、导数和正分母条件全部满足；退化情形 q=1 已单独处理。未将 C_log 当成上游输出或自由输入，也没有 H0、充分大 m 或 C_tan 依赖。该推导正是 n=0 分支所需的承重义务。

## 五、精确位移恒等式、符号与误差阶

对应受审稿第155–198行。定义

\[
D=1/h^2-1/H^2-2\delta/h^3.
\]

h>0、H>0 保证通分合法。独立展开验证为

\[
\begin{aligned}
D
&=\frac{h(H^2-h^2)-2\delta H^2}{h^3H^2}\\
&=\frac{\delta\{h(H+h)-2H^2\}}{h^3H^2}\\
&=-\frac{\delta^2(3h+2\delta)}{h^3H^2}.
\end{aligned}
\]

第二行用 H-h=delta；第三行用 H=h+delta，且 h(2h+delta)-2(h+delta)²=-3h delta-2delta²。故受审稿式(9)准确，D 严格为负，领先校正项确实为减去 2delta/h³，未反转位移符号。

由 h>0、delta>0，分子因子 3h+2delta>0，故

\[
|D|=\frac{\delta^2(3h+2\delta)}{h^3H^2}.
\]

再独立核对

\[
3H^2-h(3h+2\delta)=4h\delta+3\delta^2\ge0.
\]

将 h(3h+2delta)<=3H² 除以正数 h⁴H²，并乘以非负 delta²，正好得到

\[
|D|\le3\delta^2/h^4\le3/h^4.
\]

末步使用 0<delta<=1。这是全部有限域上的代数不等式，没有对 delta/h 作小量假设，也没有丢弃 h=m、delta=1。受审稿式(10)的系数、余项阶及除法方向均正确。

## 六、DA1 汇总与绝对常数量词

对应受审稿第202–262行。先选取固定 SCA1/SCA2 给出的绝对 C_a、C_rho，再按第四节选取 C_log，并定义

\[
A=C_{\rm rho}+3\lambda,\quad B=C_{\log},\quad
C=A+B=C_{\rm rho}+3\pi^2/8+
\frac{\pi C_a}{4\cos(\pi/8)}.
\]

C_rho>0、lambda>0、C_log>0，故 A、B、C 均严格正。此公式不含 m、h、n、delta、序列或 S4 常数 M，是真正先于全部目标参数选定的同一个见证。

任取全部冻结域内的 m、h、n，N=(n:Real)>=0。将 DA1 绝对值内部记为 E。加减 lambda N/H² 后，逐项抵消得到精确分解

\[
E=N(\log\rho+\lambda/H^2)+\lambda N D+\log q.
\]

N/H² 项在两个括号间恰好相消；lambda N D 提供 -2lambda N delta/h³。因此这里没有改动冻结的 pi²/4 系数、符号或乘法顺序的数学含义。

由三角不等式、N>=0、lambda>0、SCA2、已证的 D 界和 C_log 界，得到

\[
|E|\le C_{\rm rho}N/H^4+3\lambda N/h^4+C_{\log}/H^2.
\]

因 H>h>0，H⁴>=h⁴>0，故 1/H⁴<=1/h⁴。乘以非负 C_rho N 保持方向，推出

\[
|E|\le A\,N/h^4+B/H^2.
\]

令 X=N/h⁴>=0、Y=1/H²>0，则

\[
(A+B)(X+Y)-(AX+BY)=AY+BX\ge0.
\]

故 \(\lvert E\rvert\le C(N/h^4+1/H^2)\)，恰为冻结 DA1。没有用 n>0，没有除以 N；即使 n=0，以上所有乘法和不等式仍成立。C 的选择顺序实现的是“存在 C，随后对所有 m、h、n”，并非逐 m 或逐序列选择常数。

## 七、逐结论与边界核对表

| 冻结义务或边界 | 受审证据及独立核对 | 裁决 |
| --- | --- | --- |
| 固定 H=m+1 与固定 a/rho；无自由替代函数 | 证明第24–35、37–56行与两份冻结定义逐项相同；所有别名字母仅省略参数 | 通过 |
| h>=1、h>0、H>=2、H>0 | 证明第78–85行，由自然数保序与胞元不等式推出 | 通过 |
| H=h+delta、0<delta<=1 | 证明第85–92行，严格上界 h<H 与左端 h>=m 均实际使用 | 通过 |
| 全部分母、对数自变量的正性 | 证明第94、105、110–140行；本报告第三、四节逐个核对 | 通过 |
| 内部统一 C_log | 证明式(4)–(8)，固定正下界 q>=cos(pi/8)>0 与 SCA1 联合推导 | 通过 |
| 精确位移恒等式与残差符号 | 证明式(9)，本报告第五节独立通分展开；D<0 | 通过 |
| 位移误差不超过 3/h⁴ | 证明式(10)，正分母、代数比较及 delta²<=1 均满足 | 通过 |
| 完整 DA1 及系数 pi²/4 | 证明式(11)–(14)，本报告第六节逐项分解并吸收 | 通过 |
| C 先于全部参数选定 | C=C_rho+3pi²/8+pi C_a/(4cos(pi/8))，只依赖固定上游绝对常数与数值常量 | 通过 |
| m=1 | H=2、h 属于 [1,2)、u=pi/8；cos 单调性含右端，所有正性与 delta 界成立 | 通过 |
| m=2 | H=3、h 属于 [2,3)、u=pi/12；无新增阈值或例外 | 通过 |
| 任意 m 的 h=m、delta=1 | 精确代数恒等式及 delta²<=1 包含等号，弱整数端点完整保留 | 通过 |
| h<m+1 的严格上端 | delta>0 始终保持；没有纳入 h=H、delta=0 或换成严格事件的整数端点 | 通过 |
| n=0 | N=0 时 E=log q；内部界给 \(\lvert E\rvert\le B/H^2\le C/H^2\) | 通过 |
| 无 H0、充分大、正时间或尺度前提 | 全部推导只用冻结域；未用 n/h³ 有界、h 趋于无穷或奇偶限制 | 通过 |
| 误差仍为 N/h⁴+H^(-2) | SCA2 的 N/H⁴ 仅按 H>h 合法增大为 N/h⁴；对数余项保持 H^(-2) | 通过 |

## 八、依赖状态、缺口与范围裁决

本轮未发现需要退回修订的数学缺口，也没有通过补前提接受证明。C_log、精确位移恒等式与全域位移界均已在受审稿内部证明；NEW_RAW_LEAF_COUNT=0 只是来源计数，不能代替这些证明或独立审查。

上游状态只按派发信息登记：固定 Scalar 接口已有匿名数学独立 CORRECT，处于 privateSource/no-oREADY，尚无 canonical；上游形式认证仍待完成。本轮没有读取或重新认证其证明、实现、审查，更没有依据该状态推断本稿正确。本稿的数学依赖明确止于锁定的 SCA0/SCA1/SCA2 精确结论；将来实际导入何种声明、其定义等式是否匹配、传递公理是否合法，仍须由独立形式门检查。本报告不给出任何当前 Lean 通过或 canonical 完成声明。

排除范围保持冻结：没有证明 DA2 的序列特化、H/h 趋一、时间域最终成立或残差趋零；没有消费真实路径概率、S1/Pair/U1、谱余项 R、真实 Brownian 概率或其尾展开；没有证明实际 S3/S4、S5、临界倍率或全部极限点、strict 事件、其他 cosets、Spectrum 或 OQ4 根。来源中这些段落的可见性不构成依赖或认证。它们的 OPEN 状态不因本次数学审查改变。

最终数学裁决：CORRECT / MATH_ONLY，严格限于固定 SCA0/SCA1/SCA2 下的 DA1 与同域合法性。未运行 Lean。
