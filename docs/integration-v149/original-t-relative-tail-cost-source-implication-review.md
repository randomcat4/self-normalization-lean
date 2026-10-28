# 原统计量 T、相对尾付款与当前层级费用：249–251 独立来源衔接审查

日期：2026-10-28。审查角色：Root5 既有独立数学审查上下文 /root/original_b_scope_implication_review；本次沿用 sol/xhigh 规定角色，未另开上下文。仅审查来源到公共结论及其联合应用，不重新审查各单元已合格的完整局部证明。

**裁决：249、250、251 各自已 qualified 的精确公共范围可复用。249 已给出原物理统计量的条件性 Gaussian-relative 闭尾界，以及全实阈值的 clipped-to-physical 尾/CDF 传递；其异常事件付款已实际完成到 R。250/251 已给出原模型当前层级 z 的真实加权三次费用及合法截断包。三者合在一起，仍不能自动得到原 p51 S14 的三次费用相对尾应用：249 尾界中的费用使用固定 clipping 参数 1，250/251 的费用使用 clipping 参数 z。这个差异有实质数学内容，不能当作缺少一条命名包装。**

下面不仅指出不同的 RHS，还给出可成立的比较界及一个固定有界二点模型，证明将固定 clip1 费用普遍压到三次阶确实不成立。这不反驳 249 的条件式尾界，也不反驳 250/251 的当前层级费用定理。未读取或使用未发布的 252/253。

## 1. 精确输入与复用范围

本次按任务核对 PR531、PR533 的 packet 及两份 public-heads-and-source-values.txt。数学读取覆盖 250 的完整公共结论、251 的完整公共结论，以及 249 的全部公共量词、普通 let 上下文、同见证分支、旧实际付款分支和新增相对付款分支。完整局部 SOURCE/proof/allactualTYPE/AX 资格直接复用。

| 单元 | packet 中源码 | 实际 SHA256 |
|---|---|---|
| 249 | intake-pr533/packet/Shao/OQ6/OriginalSameWitnessPhysicalRelativeTailApplication.lean | 19c3e659b538c19d7e73a55bcaec1dc6727b435665e215890cc6c219c88704a0 |
| 250 | intake-pr531/packet/Shao/OQ6/OriginalLevelDependentWeightedSourceCost.lean | 9eab174ed67833ed40df18ea889fb60a98e0c49401d4955872560e15bc4ebe6f |
| 251 | intake-pr533/packet/Shao/OQ6/OriginalLevelDependentClippedSourcePackage.lean | ab6f36156e138a4616fa769bd7ad123b3cd0adf92be79414e6ab226598291e53 |

上述三个 packet 文件分别为 240965B、19238B、14424B，均与各自 qualified-evidence.json 的源绑定一致。独立最终审查报告的实际哈希也与其资格绑定一致：

| 单元 | qualified-evidence.json SHA256 | 复用的最终独立报告 SHA256 |
|---|---|---|
| 249 | 0c7e16ecbe5ad6b42f7080886c405d0ad52ddff03bcd8b8488e286880b487b86 | 90c1f0e794ac6c5fdf37f8e5e494665bec181a6c30d86c8d58af7054f5158052 |
| 250 | dfa95f74f65ae94613f514cf5cd0f75e3719876cc76823460a27da66104d5738 | a860afa3eca7b06abdb95bdfeaa56e479406eaae45ffe056b6e6f8148cd1961d |
| 251 | 4fcd76676abfb79c7e1aac9c8fec68f4bb58d5b12adf13d5b4361113a096c5f0 | 6567047744723480ee74c2b13924e9a64087558059e94df48aeadc21cfb75119 |

头部提取文件 SHA256：PR531 为 7ec0df680f10b34cdd3b236298719c1f8abeca9d5bc18e2b9bd278cdb945adc8；PR533 为 07b0c5533a1a0116054c245975e5cddb3f04f41746ef33fddad5b6f18584df7f。以下引用 PR533 行号均指这份精确提取文件。

来源全文读取：

- C:/game/shao/current/oq56/inputs02/p51.md，SHA256 96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359，重点 S1–S5、S10–S19、S22–S27。
- C:/game/shao/current/oq56/inputs02/p54.md，SHA256 e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43，重点 F4–F6、紧区间与实际坏事件的区别。

辅助读取为实际预算、删一预算、原 finite-row/statistic 定义、literal clipped comparison、OriginalExceptionalTailAbsorption 及 ScalarShaoZhouFiniteCostTailInput 的精确定义。已接受 248/228/231/232 的范围按其资格及承重公共结论复用。读取时当前已接受公共快照仍为 v148；本报告不自行宣告 PR531/533 或 v149 的 Root 接受状态。

## 2. 原 T 的数学对象没有被替换

共同原模型前提为：任意可测观测空间上的同一概率律 $\mu$，产品可测、平方可积、对称的原核 $h$，$E_{\mu^2}h=0$，真实投影

\[
 g(o)=\int h(o,y)\,d\mu(y),\qquad
 \int g^2\,d\mu=1,\qquad r(o,y)=h(o,y)-g(o)-g(y).
\]

此 $r$ 为同一原模型的典范残差；$\rho^2=\int r^2\,d\mu^2$，没有换成一个便于集中但不再属于原核的余项。对原长度 $n$：

\[
 W=n^{-1/2}\sum_i g_i,\quad V^2=n^{-1}\sum_i g_i^2,\quad
 F=\sum_{i<j}r_{ij},\quad
 D=\frac{F}{\sqrt n(n-1)},\quad
 J=\frac{\sum_i(\sum_{j\ne i}r_{ij})^2}{(n-2)^2}.
\]

实际 studentizer 为

\[
 s=\sqrt{\operatorname{centeredSq}(n,g,r)}
   =\frac{\|P_n(g+u)\|}{\sqrt{n-1}},
 \qquad u_i=\frac{\sum_{j\ne i}r_{ij}}{n-2}.
\]

原 jackknife 满足 $R_h=2s$，且 $\sqrt n\,U_h/2=W+D$，故

\[
 T_{\rm physical}=
 \begin{cases}(W+D)/s,&s\ne0,\\0,&s=0,\end{cases}
\]

是原 $\sqrt n U_h/R_h$ 的同一归一化统计量。这恰是 249（PR533 900–903）与 251（54–55）的 Tphysical。最终概率始终是原 $P=\mu^{\otimes n}$，不是编码扩展律或二次倾斜律的物理概率。

删一量保留原 $n$ 的系数：$D^{(i)}$ 分母仍为 $\sqrt n(n-1)$，$J^{(i)}$ 分母仍为 $(n-2)^2$；不是在 $n-1$ 个样本上重算另一统计量。251 的保留坐标可测三元因子确实包括这个原 $D^{(i)},J^{(i)}$ 和当前预算 $B_z^{(i)}$。

$V=0$ 与 $s=0$ 是两个不同事件。249 通过实际好集补集同时付款；251 对两种零事件分别给出其定义/可测性约定。不能从编码后 $V_\eta>0$ 几乎处处推断原 $s>0$ 几乎处处，也没有用这个错误推断。

## 3. 249 的实际闭尾结论、窗口与量词

249 先固定原 $\mu,h$、$2<p\le3$、$\beta=\int|g|^p\,d\mu<\infty$ 及 $c_{\rm Budget}>0$，然后选出一个共同的 $c_g>0$、同一可数生成子 $\sigma$ 域 $m_0\le m_\Omega$。它的所有编码、trim、full/deleted 因子、费用极限、上尾坏事件及层级 1/当前层级付款保留在同一存在见证的作用域内。

记

\[
 c_{\rm Moment}=\left(\frac{\min(1/2,c_{\rm Budget})}{2}\right)^{1/p}.
\]

固定 $C_{\rm env},a_{\rm env},M_{\rm env}\ge0,t_0>0$ 后，249 定义

\[
 c_{\rm Paid}=\min\left\{
 c_{\rm Rem}(\operatorname{tailScale}(M_{\rm env}),t_0),
 1,\frac{\sqrt{t_0}}2\right\}>0.
\]

随后存在一个共同的 eventually-$n$ 范围，先保证

\[
 n\ge4,\quad1+\rho\le\sqrt n,\quad1\le c_{\rm Paid}n^{1/6},
\]

之后才对全部合法的原模型包络 $w$ 和全部

\[
 1\le z\le c_{\rm Paid}n^{1/6}
\]

量化。包络前提实际是原 $\mu,\mu^2$ 下

\[
 0\le w\le C_{\rm env}(\log n)^{a_{\rm env}}\ {\rm a.e.},\quad
 w^2\in L^1,\quad Ew^2\le M_{\rm env},\quad
 |r(o,y)|\le w(o)w(y)\quad\mu^2{\rm-a.e.}
\]

原固定 $\rho$ 在 eventually-$n$ 之前，故物理 guard 不是随 $n$ 重选残差后得到的伪一致性。正窗口且最终非空确实是结论。包络 $w$ 可以在 $n$ 之后选择，但定理没有给出这样的包络的存在性。

最终还须同时满足严格矩预算窗口

\[
 \beta=0\quad\text{或}\quad
 \left(\beta>0,\quad
 z\le c_{\rm Moment}\beta^{-1/p}n^{(p-2)/(2p)}\right).
\]

$\beta=0$ 分支是原类型中保留的形式分支，不是凭它绕过单位投影方差的实际模型要求。两个窗口都不能删除；$p\le3$ 时矩窗口指数不超过 $1/6$。

给定真正的外部输入

ScalarShaoZhouFiniteCostTailInput$(c_{\rm Budget},C_1,C_2,C_3,C_4)$，

249 对上述所有 $z$ 给出

\[
 \Psi(z)\left[e^{-C_1L(z)}(1-C_2\mathcal C_1(z))-R_n\right]
 \le P\{T_{\rm physical}\ge z\}
 \le
 \Psi(z)\left[e^{C_3L(z)}(1+C_4\mathcal C_1(z))+2R_n\right],
\tag{249}
\]

\[
 L(z)=\sum_i E[(z\xi_i)^2\min(|z\xi_i|,1)],\quad
 \xi_i=g(O_i)/\sqrt n,\quad
 R_n=\exp\{-t_0n^{1/3}/2\}.
\]

这是**真实原物理闭尾**的上下界，$\ge$ 保留边界原子。因 Gaussian $\Psi(z)>0$，数学上也可两边除以 $\Psi(z)$；形式声明选用乘法型表达并不削弱它。它不要求 $1-C_2\mathcal C_1>0$，所以费用很大时下界可能不具信息，定理仍成立。

原预算已有

\[
 L(z)\le\beta z^pn^{-(p-2)/2}.
\]

但 $R_n\to0$ 只控制新增异常付款；要把 (249) 化成“与 Gaussian 相对误差小”的目标，仍须控制**同一个** $\mathcal C_1(z)$。在 $L$ 有固定上界时，展开指数可把误差控制为常数倍 $L+\mathcal C_1+R_n$；不能把 $R_n$ 单独称为整个相对误差。

## 4. 249 的 R 已支付哪些实际事件

记 $q=t_0n^{1/3}$，

\[
 b_z=3e^{-q}+e^{-c_gn}+4e^{-z\sqrt n/2},\qquad
 b_1=3e^{-q}+e^{-c_gn}+4e^{-\sqrt n/2}.
\]

249 保留了同一原模型的

\[
 H_z=G_z\cap C_2,\qquad
 C_2=\{|F|\le K n q,\ \|\operatorname{originalRows}\|^2\le K n^2q\}.
\]

不是只给 $C_2$ 一个形式名字：在真实原产品律下，公开结论实际给 $P(H_z^c)\le b_z$。其 safe 集控制 $V>0,z|D|\le V/8,z^2|e_1|\le1/8$；编码后的真实分子坏事件 $E_k=\{z|D_\eta|>V_\eta/4\}$ 有实际 $\limsup_kP(E_k)\le b_z$，分母坏事件和原 $V=0$ 也有对应的实际付款。这里 $e_1$ 是固定 clip1 correction，不是 $B_1$ 本身。

另用同一见证和同一实际 $C_2$ 构成 $H_1=G_1\cap C_2$，在 $1+\rho\le\sqrt n$ 下给

\[
 \{T_{\rm clip,1}\ne T_{\rm physical}\}\subset H_1^c,\qquad
 P(H_1^c)\le b_1,
\]

并付款原 $V=0$ 与原 $s=0$。其物理闭尾的旧上下界付款分别为 $b_z+b_1$ 和 $3b_z+b_1$（PR533 850–855）。

异常吸收定理在缩小后的同一窗口给

\[
 6e^{-q}+2e^{-c_gn}+8e^{-\sqrt n/2}
 \le R_n\Psi(z).
\]

因为 $z\ge1$，$b_z\le b_1$，所以

\[
 b_z+b_1\le R_n\Psi(z),\qquad
 3b_z+b_1\le2R_n\Psi(z),
\]

恰得 (249) 的 $-R_n$ 和 $+2R_n$。因此不能再把“原物理闭尾的实际 S15 付款尚未存在”当作 249 的缺口；在其**明确原包络与窗口前提**内，这些付款已经给出。仍不能推广为任意仅有 $Er^2<\infty$、任意未截断次 Weibull 包络或 DC 结构的普遍付款。

## 5. 250/251 控制的费用与 249 的费用不同

令 $\sigma=1+\rho,N=\sqrt n,C_0=512$。实际定义为

\[
 B_y=\frac{C_0}{N}\left(\sigma y+\frac{J}{\sigma y}\right),\qquad
 B_y^{(i)}=\frac{C_0}{N}\left(\sigma y+\frac{J^{(i)}}{\sigma y}\right).
\]

在估计阈值为 $z$ 时，定义二参数费用

\[
 \mathcal C_y(z)=\frac1{I_z}\left\{
 E[(z|D|+z^2B_y)e^{S_z}]
 +\sum_iE\left[\min(|z\xi_i|,1)
 (\,||D|-|D^{(i)}||+z|B_y-B_y^{(i)}|\,)e^{S_z^{(-i)}}\right]\right\},
\]

\[
 S_z=\sum_j(z\xi_j-(z\xi_j)^2/2),\quad
 S_z^{(-i)}=\sum_{j\ne i}(z\xi_j-(z\xi_j)^2/2),\quad I_z=Ee^{S_z}>0.
\]

三者的精确比较是：

| 对象 | 249 | 250/251 |
|---|---|---|
| 倾斜阈值/权重 | $z,S_z,S_z^{(-i)},I_z$ | 同一形式的 $z,S_z,S_z^{(-i)},I_z$ |
| clipping 参数 | $y=1$ | $y=z$ |
| 预算/删一预算 | $B_1,B_1^{(i)}$ | $B_z,B_z^{(i)}$ |
| 费用 | $\mathcal C_1(z)$ | $\mathcal C_z(z)$ |
| 过程 | $T_{\rm clip,1}$ | $T_{\rm clip,z}$ |
| 现成结论 | 同见证 coded tail、实际坏事件付款、physical relative tail | 当前层级三次费用、可测/删一因子、全局 clipping 契约、几何比较 |

250 对 $n\ge4,1\le z\le\sqrt n/(2e^{1/2})$、任意 $C_0\ge0$ 给完整 full/partial 可积性、同一个 $I_z>0$ 与

\[
 0\le\mathcal C_z(z)
 \le64e^2(1+4C_0)(1+\rho)\frac{(1+z)^3}{\sqrt n}.
\tag{250}
\]

它不是未加权费用，部分倾斜的分母仍为 full $I_z$；没有改成 $I_z^{(-i)}$，也没有给预算加入 $G_z$ 指示。

251 在 $C_0=512$ 构造同一个当前层级 $B_z,e_z,T_{\rm clip,z}$ 的包，给出对每个删一指标的真实保留坐标因子，并将 (250) 接在其后。它还在显式几何条件

\[
 (1+\rho)z\le\sqrt n
\]

下给 $G_z\cap\{d\ge-1/2\}$ 上 $e_z=d$、两个真实分母为正且相等、$T_{\rm clip,z}=T_{\rm physical}$，以及精确 exception inclusion。**这个包含自身不支付任何概率。** 251 的 tilt window 不自动蕴含该几何条件；对固定 $\rho$ 和 $z\le c n^{1/6}$，可另由充分大 $n$ 推出，不需要新统计假设，但必须在联合声明中落实。

最关键的是：251 没有供应当前层级全套量化编码、归一化 scalar source-law consumer、相同 sequence/strict budget 的上尾输入与实际坏事件付款的联合分支。249 已有的编码见证/费用极限不能仅凭函数名相似改成 $e_z,B_z,B_z^{(i)}$。需要证明当前层级原 observables 与删一量在同一 $m_0$ 中可测并用同一编码、exact signed correction、full/partial 费用极限及合法严格预算。可以复用 228 的加权极限机制、231 的严格矩预算及 232 的原子安全 upper-event 机制；这些旧条件式结果不能省略实际参数/同一见证的连接。

## 6. 一个真实比较界，以及固定 clip1 三次界的反例

以下是本次来源衔接审查中的普通数学推导，未声称新增 Lean 定理或机器认证。

在 $n\ge4$、$1\le z\le\sqrt n/(2e^{1/2})$ 的共同费用有效范围内，$J\ge0$ 给

\[
 B_1\le zB_z,\qquad
 |B_1-B_1^{(i)}|=z|B_z-B_z^{(i)}|.
\]

第二式来自**先消去相同确定项**后预算差均为 $C_0(J-J^{(i)})/(\sigma yN)$，不是以 $B_1\le zB_z$ 推出绝对差的错误论证。因此每个非负 full/deleted 被积项可比较，且同一 $I_z>0$ 给

\[
 \mathcal C_1(z)\le z\mathcal C_z(z)
 \le64e^2(1+4C_0)(1+\rho)\frac{z(1+z)^3}{\sqrt n}.
\tag{*}
\]

这是可用于较小窗口的四次增长后果，不是原目标三次界。$B_1$ 和 $B_z$ 本身也没有普遍的单调方向，因为一项随 $y$ 增大而另一项随 $y$ 减小。

更强地，不能期望只补一个无损比较引理就把固定 clip1 普遍压到三次阶。取固定原模型：

\[
 \Omega=\{-1,1\},\quad\mu(\pm1)=1/2,\quad
 h(x,y)=x+y+xy.
\]

则 $g(x)=x,r(x,y)=xy,\rho=1,\beta_p=1$，所有原核前提成立；残差具有固定有界乘积包络 $w=1$，所以不是通过离开 249/250/251 模型范围制造的例子。

由于 $\xi_i=X_i/\sqrt n$ 且 $X_i^2=1$，full 二次倾斜是独立二点乘积律，参数 $a=z/\sqrt n$ 下均值为 $m=\tanh a$。其真实行能量满足精确恒等式

\[
 E_aJ=\frac{n(n-1)}{(n-2)^2}
       [1+(n-2)m^2].
\]

推导只用第 $i$ 行平方
$(X_i\sum_{j\ne i}X_j)^2=(\sum_{j\ne i}X_j)^2$ 及倾斜下独立性。固定 $n,z$ 的 full 加权期望除以 $I_z$ 就是这个 $E_a$。

当 $z/\sqrt n\to0$，最终 $m\ge a/2$，故

\[
 E_aJ\ge\frac{n-1}{4(n-2)}z^2\ge z^2/4.
\]

费用的全部项非负。只取其 full $z^2B_1$ 项、$C_0=512,\sigma=2$，就有

\[
 \mathcal C_1(z)\ge E_a[z^2B_1]
 \ge\frac{256z^2}{\sqrt n}E_aJ
 \ge\frac{64z^4}{\sqrt n}.
\]

取 $p=3$，并取固定足够小的 $d>0$，令 $z_n=dn^{1/6}$，可同时满足 paid、moment 与 250 的 tilt 窗口。此时 $z_n/\sqrt n\to0$ 且 $z_n\to\infty$，所以

\[
 \frac{\mathcal C_1(z_n)}
 {(1+\rho)(1+z_n)^3/\sqrt n}\longrightarrow\infty.
\]

不存在针对这个固定模型、在全部合法 $z_n$ 上有效且与 $n,z$ 无关的固定 clip1 三次费用常数。该结论是对一种**拟议错误联合应用**的反例，不是对 249 条件尾界或原真实统计量目标尾展开的反例。当前层级 $B_z$ 的 $J/z$ 正是源 S14 保持三次阶的承重因子。

从 (*) 可以在 $z=o(n^{1/8})$ 且相应矩窗口内得到固定 clip1 费用趋零的较窄数学后果；这仍不完成原 $n^{1/6}$ 三次费用窗口，也不能被记录为当前层级 source-law consumer 已完成。

## 7. CDF、原子和外部 SZ：已给与未给

249 保留 248 的全实阈值传递（PR533 823–843）。在同一物理 guard 下，对每个 $t\in\mathbb R$：

\[
 |P(T_{\rm physical}\ge t)-P(T_{\rm clip,1}\ge t)|\le b_1,
\]

\[
 |P(T_{\rm physical}\le t)-P(T_{\rm clip,1}\le t)|\le b_1.
\]

共同的 $b_1$ 不依赖 $t$，因此也给这两类分布函数的全阈值绝对距离界。它保留边界原子，并且是实际概率付款，不只是可测性或事件包含。

然而，该传递没有给 $P(T_{\rm clip,1}\le t)$ 自身与 Gaussian CDF 的新误差界；新增相对尾分支 (249) 也只在 $z\ge1$ 及双窗口内，并不覆盖 $0\le z\le1$、$z=0$ 或任意负阈值。闭尾 $\ge$ 的补集是严格下尾 $<$，不是 $\le$；不能未经极限论证把它当作 CDF。

这不意味着正窗口 CDF 数学上不可从尾界推导：在窗口内点，对 $z_j\downarrow t$ 的闭尾用测度连续性，并证明 RHS 中 $L(z),\mathcal C_1(z)$ 连续后，可以处理严格上尾及相应 CDF；这种派生仍携带同一固定 clip1 费用，没有消除第 6 节的问题。249 公共声明本身未交付这项额外推导。源 p51 S5/p54 §3 的紧区间路线需要的是另一个外部 compact/CDF 引擎、连续截断删一费用和反射/单侧极限，不是 Theorem 2.1 的上尾输入。

实际已接受库中存在 ActualPhysicalSignedGlobalCDF/ActualPhysicalCompactRelative 等**条件式**接口，其前提明确包含 ScalarShaoZhouFiniteCostCDFInput，并有自己的可数生成空间/原模型条件。它们可按其精确既有资格复用，但不能把 249 的 TailInput 当作这个不同 CDFInput，也不能因为 249 选出了 $m_0$ 就免除实际统计量和 CDF 在原 $\mu$ 与 trim 模型之间的连接。不得因此宣称所有 Gaussian-CDF/compact/atom 原题义务已经由新三件一起关闭；也不应把已存在的全实物理传递或既有条件式 CDF 定理抹去。

外部 TailInput 本身是一个强而明确的命题：固定 $c_{\rm Budget}>0$ 及正 $C_1,\ldots,C_4$，对所有合法的独立标量族、同一标量可测余项/非负包络/删一因子，在正分母、full/partial 可积与严格矩预算条件下给 finite-cost 上下界。249 量化“对任何满足此输入的 $C_1,\ldots,C_4$”，**没有证明这样一组常数/输入存在**。原 Shao–Zhou 结果的精确来源匹配及合法使用仍是显式义务，不能通过新增 axiom 或把它误当已证明的内部结论来消去。

## 8. 原模型仍需什么，哪些已经不是缺口

| 项目 | 本次精确裁决 |
|---|---|
| 原 $T=(W+D)/s,s=0\Rightarrow T=0$ 的定义与 249 最终事件 | 已实际接回；不是仅有 clipped 统计量结论。 |
| 原 $H_z^c,H_1^c$、编码 upper-event、两种零分母事件的概率付款 | 在 249 原包络/窗口前提内已完成，且已吸收至 $R_n\Psi(z)$。 |
| 当前层级原 full/deleted 加权费用及真实 $I_z$ | 250/251 已给三次界。 |
| 固定 clip1 同一原费用的三次界 | 不由 250/251 推出；按第 6 节它甚至不普遍成立。不能把此项交给“包装”解决。 |
| 当前层级三次费用与一套同见证原 scalar-tail/physical-payment 应用联合 | 新三件没有给出。应保持当前 $e_z,B_z,B_z^{(i)}$、同一模型、同一编码/严格预算与实际 good-event 付款的完整参数连接。 |
| 当前层级物理 guard | 251 明确要求 $(1+\rho)z\le\sqrt n$；固定模型及 $z=O(n^{1/6})$ 下可最终推出，须在联合量词中记录。 |
| 原模型包络存在 | 249 是“对所有合法包络”的条件式结论。有限残差二矩不提供此包络。固定原核若不具任一有限的本质有界乘积包络，不能直接满足这个 bounded-polylog 原模型前提。 |
| 原未截断次 Weibull/PE-L/PE-R 或 DC 应用 | 需其精确截断/条件模型、真实重投影与残差、同一参数与实际事件转回。DC 行集中需要其实际结构；不能从二阶矩或这三件的新结论自动取得。 |
| 条件 $p$ 矩 | 保留 p54 修正：需要足够的统一上界/收敛，不能恢复任意多项式变化率的假句。 |
| 原 Gaussian compact/CDF/atoms | 新 249 给全实 physical-vs-clip1 传递；Gaussian CDF 输入/误差或严格尾极限各按相应独立接口处理，未被 TailInput 自动替代。 |
| 整个 S11/S15/DC/full OQ56/root | 本报告不关闭。各项只能按精确假设内的已付款/已 qualified 范围记账。 |

可复用的实际数学成果已经相当具体：异常事件的相对付款不再是空接口；三次费用也确实属于原核和原删一归一化。剩余关键是把**当前层级**过程送进已有 scalar coding/strict budget/upper-event 机制，并按该过程转回原物理统计量。把已证明的固定 clip1 应用和当前层级费用直接合并，会隐去一个真实且不可无损替换的成本差异。

## 9. 封存与使用限制

本次唯一写入为本报告；没有写原 source、REGISTRY、任何已封存旧报告或其他协作文件。未运行 Lean、AX、SSH、编译、网络/Git/API；未建立子上下文。报告中的新比较式与二点模型计算属于本次独立数学衔接审查，不冒充新 Lean 验证结果。局部已 qualified 证明、机器对象与公理证据原样复用。Root 决定本报告采纳、PR 接受及原题状态更新。

~~~json
{
  "reviewKind": "INDEPENDENT_ORIGINAL_T_RELATIVE_TAIL_COST_SOURCE_IMPLICATION",
  "qualifiedUnitProofsReused": [249, 250, 251],
  "individualQualifiedScopesDisputed": false,
  "physicalConditionalRelativeTailAtFixedClip1Established": true,
  "actualExceptionalPaymentsAbsorbedToR": true,
  "currentLevelCubicWeightedCostEstablished": true,
  "automaticFixedClip1CurrentLevelJointApplicationValid": false,
  "universalFixedClip1CubicCostClaim": "FALSE_BY_FIXED_BOUNDED_TWO_POINT_MODEL",
  "fullOriginalRelativeRateOrCDFClosureClaimed": false,
  "unpublished252253Used": false,
  "requestedModel": "gpt-6.1-sol",
  "requestedEffort": "xhigh",
  "actualModel": null,
  "actualEffort": null,
  "inputTokens": null,
  "cachedInputTokens": null,
  "outputTokens": null,
  "reasoningSubsetTokens": null,
  "newLeanOrAxiomRuns": 0,
  "duplicateCompleteProofReviews": 0
}
~~~
