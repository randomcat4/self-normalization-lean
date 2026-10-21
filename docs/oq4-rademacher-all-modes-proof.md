# 全部正弦模态的真实有限幂与未化简生存谱

STATUS: PROVED
SCOPE: MATH_ONLY；仅为冻结命题 D1 与 D2 的常数一分支。

## 1. 命题、对象与固定依赖

本证明对应 `frozen-rademacher-all-modes-v1.md`，SHA256 为
`dac2fd30e7c759137e14ebd64c4d7457155a201da04a7226449304d0b4abbe10`。
原始数学对象来自 `C:/game/shao/current/oq4/c01/spectrum01.md`，SHA256 为
`b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`。

固定任意自然数 $m\geq1$，并置
\[
H=(m:\mathbb R)+1,\qquad
I_m=\{-m,-m+1,\ldots,m\}\subset\mathbb Z,\qquad
J_m=\{1,2,\ldots,2m+1\}\subset\mathbb N.
\]
这里整数区间的两个端点均包括在内。固定任意实数 $h$ 满足
\[
m\leq h<m+1=H.
\]
整数与自然数进入实数表达式时一律使用通常的实数强制转换。因此 $H>0$ 且 $h\geq0$。

实际增量律固定为
\[
\nu_R=\tfrac12\delta_1+\tfrac12\delta_{-1}
       =\texttt{Shao.OQ4.RademacherCosine.law}.
\]
其概率性是该实际律已有的内部性质。记
\[
a=\texttt{RademacherCosine.angle}\ m=\frac{\pi}{2H},\qquad
\theta_j=j a,\qquad \mu_j=\cos\theta_j,
\]
\[
\phi_j(w)=\sin\bigl(\theta_j(w+H)\bigr)\quad(w\in\mathbb R),
\qquad v_j(s)=\phi_j(s)\quad(s\in\mathbb Z).
\]
所有有限求和均为未归一化计数和，尤其定义
\[
q_j=\frac1H\sum_{s\in I_m}v_j(s).
\tag{1}
\]
$q_j$ 是一个确定的有限实数，且正是冻结系数 $c_{m,j}(F_1)$，其中 $F_1(s)=1$。

为简化记号，写
\[
K(z)=\texttt{killedKernel}\ \nu_R\ h\ z,
\quad
K_n(z)=\texttt{killedIterKernel}\ \nu_R\ h\ n\ z,
\]
\[
A_nf(z)=\texttt{killedAction}\ \nu_R\ h\ n\ f\ z
        =\int_{\mathbb R}f(w)\,K_n(z,dw),
\qquad
M_n(z)=\texttt{killedMass}\ \nu_R\ h\ n\ z=A_n1(z).
\tag{2}
\]
这些记号始终指已有的真实核及真实积分。具体而言，
\[
K(z)=\bigl((y\mapsto z+y)_*\nu_R\bigr)\big|_{[-h,h]},
\qquad K_n=K^n,
\tag{3}
\]
其中右端的幂是原核的组合幂，零次幂为恒等核。没有引入另一个矩阵或另一个递归过程。

以下是本证明明确使用的固定上游数学引理接口。

1. **真实有限核与作用接口。** `KilledKernel` 与 `KilledIteration` 的已有接口给出：对所有自然数 $n$ 和实数 $z$，$K_n(z,\mathbb R)\leq1$，故 $K_n$ 是有限核，且每个 $K_n(z)$ 是有限测度；$K_0(z)=\delta_z$ 且 $K_1=K$。每个有界 Borel 可测实函数 $f$ 对每个 $K_n(z)$ 真正可积。$A_nf$ 可测，并且原核作用满足
   \[
   A_{p+q}f(z)=A_p(A_qf)(z)
   \tag{4}
   \]
   对全部自然数 $p,q$ 成立；此处 $A_qf$ 亦对 $K_p(z)$ 真正可积。相关公开接口为 `killedIterKernel_zero`、`killedIterKernel_mass_le_one`、`killedIterKernel_isFiniteKernel`、`killedAction_integrable`、`killedAction_measurable`、`killedAction_iterated_integrable` 与 `killedAction_semigroup`。式 (4) 的前提是 $f$ 可测且在全实轴上有界。
2. **真实整数网格支持。** 冻结的 `frozen-rademacher-iteration-v1.md`，SHA256 为 `15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80`，提供如下固定数学引理：令
   \[
   G_m=\{w\in\mathbb R:\exists s\in I_m,\ w=(s:\mathbb R)\}.
   \]
   则 $G_m$ 有限且为 Borel 集，并且对所有 $r\in I_m$ 及所有 $n\in\mathbb N$，
   \[
   K_n(r)(G_m^{\mathsf c})=0,
   \quad\text{等价地}\quad
   w\in G_m\quad\text{对 }K_n(r)\text{ 几乎处处成立}.
   \tag{5}
   \]
   这个接口包括零步，且是对实际 $K_n$ 的结论。
3. **实际正弦基接口。** 冻结的 `frozen-rademacher-finite-basis-v1.md`，SHA256 为 `4672baa6bc550de2a97ca9adc0730b5633f71458b2c3da8b02c2318131e05a7f`，固定了相同的 $I_m,J_m,H,\nu_R,\theta_j,\mu_j,\phi_j,v_j$。其中 B2 给出
   \[
   F(s)=\sum_{j\in J_m}\left(\frac1H
                  \sum_{t\in I_m}F(t)v_j(t)\right)v_j(s)
   \quad(s\in I_m)
   \tag{6}
   \]
   对所有 $F:\mathbb Z\to\mathbb R$ 成立；B3 给出对所有 $j\in J_m$ 及 $s\in I_m$，
   \[
   \phi_j\in L^1(K(s)),\qquad
   \int\phi_j(w)\,K(s,dw)=\mu_jv_j(s).
   \tag{7}
   \]
   B0 还给出 $\phi_1(w)=\cos(aw)$、$\mu_1=\texttt{RademacherCosine.rho}\ m$；B1 的范数是 $H$，与式 (6) 的唯一归一化因子 $1/H$ 一致。本证明直接将 B2 与 B3 作为上述固定上游数学引理使用，不把它们作为可任意选取的核或特征关系假设。尤其，本文不重证 B2 的来源证明，也不将其仅由 B1 略称为自动成立。
4. **实际路径概率接口。** 对实际概率律 $\nu_R$，已有 `killedMass_eq_path_probability` 与 `killedMass_eq_closedStrip_probability` 给出第 6 节所列的路径概率等式，后一个接口要求 $0\leq h$。

除了这些固定上游结论，本证明只使用有限测度上有界可测函数的可积性、积分的几乎处处同余、有限和与常数乘法的线性，以及实数自然数幂的代数法则。以上依赖并非本命题新增的自由前提；以下证明在其固定对象上推出 D1 与 D2。

## 2. 可积性及半群使用的全部条件

先固定任意 $j\in J_m$。函数 $w\mapsto\theta_j(w+H)$ 连续，正弦连续，故 $\phi_j$ 连续、Borel 可测，且
\[
|\phi_j(w)|\leq1\quad\text{对所有 }w\in\mathbb R.
\tag{8}
\]
由上游的次概率质量界，任意 $n,z$ 均满足
\[
\int |\phi_j(w)|\,K_n(z,dw)
\leq K_n(z,\mathbb R)\leq1<\infty.
\tag{9}
\]
因此 $\phi_j$ 对每个 $K_n(z)$ 真正可积。这一可积性在任何模态幂等式之前已成立，并且不依赖 $\mu_j$ 的符号、非零性或生存质量的正性。

令
\[
b_j(w)=A_1\phi_j(w)=\int\phi_j(u)\,K(w,du).
\tag{10}
\]
由真实作用的可测性接口，$b_j$ 可测。利用式 (8)、$K_1=K$ 与次概率界，
\[
|b_j(w)|\leq\int|\phi_j(u)|\,K(w,du)
\leq K(w,\mathbb R)\leq1
\tag{11}
\]
对所有实数 $w$ 成立。因此 $b_j$ 对所有外层有限测度 $K_n(z)$ 真正可积。又 $\mu_j\phi_j$ 可测且有界，因为 $\mu_j$ 是固定实数；它亦对这些测度真正可积。

式 (8) 已核对了半群接口 (4) 的全部测试函数前提。取 $p=n,q=1,f=\phi_j$，得到实际核积分的等式
\[
A_{n+1}\phi_j(z)
 =A_n(A_1\phi_j)(z)
 =\int b_j(w)\,K_n(z,dw).
\tag{12}
\]
外层 $b_j$ 的可积性也已由式 (11) 单独核对；这个步骤没有把形式积分或未定积分当作可积函数使用。

## 3. D1：全部模态的真实自然数幂

先在每个 $w\in G_m$ 上核对一步身份。按 $G_m$ 定义，存在整数 $s\in I_m$ 使 $w=(s:\mathbb R)$。在该合法整数状态上使用 B3 的式 (7)，得到
\[
b_j(w)=\mu_jv_j(s)=\mu_j\phi_j(w).
\tag{13}
\]
这里 B3 仅用于网格点，未将其延伸到整个实区间。

固定任意 $r\in I_m$ 和任意 $n\in\mathbb N$。式 (5) 与网格点上处处成立的式 (13) 给出
\[
b_j=\mu_j\phi_j\quad K_n(r)\text{-几乎处处}.
\tag{14}
\]
结合式 (12)、式 (14)、两边的真正可积性与积分的常数乘法，
\[
\begin{aligned}
A_{n+1}\phi_j(r)
 &=\int b_j(w)\,K_n(r,dw)\\
 &=\int\mu_j\phi_j(w)\,K_n(r,dw)\\
 &=\mu_j A_n\phi_j(r).
\end{aligned}
\tag{15}
\]
注意式 (15) 的左端和右端均由实际 $K_n$ 定义；它是从真实半群及真实网格支持导出的等式，而非一个替代过程的定义。

现对自然时间作归纳。零步由实际 Dirac 核给出
\[
A_0\phi_j(r)
 =\int\phi_j(w)\,\delta_r(dw)
 =\phi_j(r)=v_j(r)=\mu_j^0v_j(r).
\tag{16}
\]
连续性保证这里的 Dirac 积分合法；可积性也已包含于式 (9)。假设 $A_n\phi_j(r)=\mu_j^n v_j(r)$，由式 (15)，
\[
A_{n+1}\phi_j(r)
 =\mu_j\,\mu_j^n v_j(r)
 =\mu_j^{n+1}v_j(r).
\tag{17}
\]
最后一步仅是实数自然数幂法则与乘法结合、交换律，适用于零或负的 $\mu_j$。归纳证明了对所有 $n\in\mathbb N$，
\[
\boxed{\quad
\phi_j\in L^1(K_n(r)),\qquad
A_n\phi_j(r)
 =\int\phi_j(w)\,K_n(r,dw)
 =\mu_j^n v_j(r).
\quad}
\tag{18}
\]
由于 $m,h,r,j$ 均是在冻结量词下任意固定，式 (18) 正是 D1 的全部量词。

## 4. 常数一的网格重建与积分条件

本节只在式 (6) 中使用固定函数 $F_1(s)=1$，不推导任意测试函数或逐原子核的谱表示。由式 (1) 与 B2，
\[
1=\sum_{j\in J_m}q_jv_j(s)\qquad(s\in I_m).
\tag{19}
\]
在全实轴上定义辅助测试函数
\[
\Psi(w)=\sum_{j\in J_m}q_j\phi_j(w).
\tag{20}
\]
这是有限个连续函数的线性组合，故连续、可测。每个 $q_j$ 都是有限实数，且由式 (8)，
\[
|\Psi(w)|\leq\sum_{j\in J_m}|q_j|=:C<\infty
\quad(w\in\mathbb R).
\tag{21}
\]
这里没有为 $\Psi$ 引入替代核。

若 $w\in G_m$，取整数 $s\in I_m$ 使 $w=s$。式 (19) 便给出
\[
\Psi(w)=\sum_{j\in J_m}q_jv_j(s)=1.
\]
因而对固定任意合法 $r,n$，式 (5) 推出
\[
\Psi=1\quad K_n(r)\text{-几乎处处}.
\tag{22}
\]
该结论不要求 $\Psi=1$ 在整个实区间成立；它只使用真实整数网格上的 B2 和该真实测度的全测度网格支持。

积分交换的条件如下逐一成立。

- $K_n(r,\mathbb R)\leq1$，故它是有限测度，常数一可测且真正可积；其绝对积分等于有限总质量。
- 每个 $\phi_j$ 都已由第 2 节证明对 $K_n(r)$ 真正可积。因此每个 $q_j\phi_j$ 真正可积，并满足
  \[
  \int q_j\phi_j\,dK_n(r)=q_j\int\phi_j\,dK_n(r).
  \tag{23}
  \]
- $J_m$ 有限，故这些可积函数的有限和 $\Psi$ 真正可积；逐项积分合法。也可直接由式 (21) 和测度有限性得到此可积性。两种论证均不使用 D2 的目标等式。
- 式 (22) 是同一真实测度 $K_n(r)$ 下的几乎处处等式，因此可在上述可积函数之间使用积分同余。

由此，所有随后使用的积分都是通常的有限实积分；没有把不满足可积性条件的有限和或几乎处处替换写成形式运算。

## 5. D2：实际质量等于完整未化简有限谱和

令 $\eta=K_n(r)$。由定义 (2)，
\[
M_n(r)=\int1\,d\eta.
\tag{24}
\]
另一方面，$\eta(\mathbb R)\leq1$ 排除了无穷总质量。因此有限测度的常数积分公式给出
\[
\int1\,d\eta
 =\bigl(\eta(\mathbb R)\bigr).\mathrm{toReal}
 =\eta.\mathrm{real}(\mathbb R).
\tag{25}
\]
这也正是已有 `killedMass_eq_real` 的内容。这里 `real` 表示实际测度值的有限实数质量，不是条件生存后的归一化质量；式 (25) 使用的有限性来自上游次概率界，未由所求谱式反推。

利用式 (22)、第 4 节已核对的全部积分条件及 D1，得到
\[
\begin{aligned}
M_n(r)
 &=\int1\,dK_n(r)\\
 &=\int\Psi(w)\,K_n(r,dw)\\
 &=\sum_{j\in J_m}\int q_j\phi_j(w)\,K_n(r,dw)\\
 &=\sum_{j\in J_m}q_j\int\phi_j(w)\,K_n(r,dw)\\
 &=\sum_{j\in J_m}q_j\mu_j^n v_j(r).
\end{aligned}
\tag{26}
\]
第三行只交换有限和与积分，第四行只提取固定实系数，第五行逐项应用式 (18)。式 (24)–(26) 合起来证明
\[
\boxed{\quad
\texttt{killedMass}\ \nu_R\ h\ n\ (r:\mathbb R)
 =\bigl(\texttt{killedIterKernel}\ \nu_R\ h\ n\ (r:\mathbb R)\bigr)
       .\mathrm{real}(\mathrm{univ})
 =\sum_{j\in J_m}
   \left(\frac1H\sum_{s\in I_m}v_j(s)\right)
   \mu_j^n v_j(r).
\quad}
\tag{27}
\]
这就是 D2。唯一的归一化因子是 B2 给定的 $1/H$，内外两层求和均保持原来的未归一化计数和。证明没有除以 $M_n(r)$，所以质量为零时式 (27) 仍按同一推导成立。

## 6. 真实路径事件与零起点事件

为明确左端的概率意义，对路径 $x=(x_0,\ldots,x_{n-1})\in\mathbb R^{\mathrm{Fin}\,n}$ 和整数 $0\leq k\leq n$，令
\[
S_k(x)=\sum_{i=0}^{k-1}x_i,\qquad S_0(x)=0,
\]
并写
\[
E_{n,h,z}
 =\{x:\forall k,\ 1\leq k\leq n\Longrightarrow
                       |z+S_k(x)|\leq h\}.
\tag{28}
\]
这正是已有 `shiftedClosedSurvival h z`。它是可测事件；已有路径桥在同一真实增量律下给出
\[
M_n(r)
 =\left(\bigotimes_{i\in\mathrm{Fin}\,n}\nu_R\right)
      .\mathrm{real}(E_{n,h,r}).
\tag{29}
\]
因此式 (27) 对每个合法整数 $r$ 表示的是真实平移起点生存事件 (28) 的概率。这里的有限乘积律是概率测度，`real` 就是该事件概率。

特别地，$0\in I_m$。由 $m\geq1$ 和 $m\leq h$，有 $0\leq h$，正好满足已有零起点事件桥的额外前提。因此该桥可用，并给出
\[
M_n(0)
 =\left(\bigotimes_{i\in\mathrm{Fin}\,n}\nu_R\right)
      .\mathrm{real}(\texttt{Shao.closedStrip}\ h).
\tag{30}
\]
式 (29) 与式 (30) 的使用范围不同：任意整数 $r$ 使用平移起点事件，原来的零起点 `closedStrip` 概率只在 $r=0$ 时由式 (30) 得到。式 (27) 未对 $v_j(0)$ 或 $\sum_s v_j(s)$ 作进一步奇偶或三角和化简。

## 7. 退化模态、零步、弱边界与范围核对

**零步。** 对每个合法起点 $r$，真实 $K_0(r)=\delta_r$，并未先杀死起点。式 (16) 给出 D1 的零步身份。所有实数的自然数零次幂均为一，包括 $0^0=1$。将 $n=0$ 代入式 (27)，其右端成为 $\sum_{j\in J_m}q_jv_j(r)=1$，正是式 (19)；左端则是 $\delta_r$ 的总质量一。式 (28) 在 $n=0$ 时没有需要检查的正时间，故为空路径全事件，概率亦为一。由于本范围已经给出 $0\leq h$，零起点 `closedStrip` 桥在零步也适用。

**零与负特征值。** $j=m+1$ 属于 $J_m$，此时 $\theta_j=\pi/2$ 且 $\mu_j=0$。D1 的零步用 $0^0=1$，正步才由普通自然数幂得到零。对 $m+1<j\leq2m+1$，有 $\pi/2<\theta_j<\pi$，故 $\mu_j<0$。归纳式 (15)–(17) 从未要求 $\mu_j$ 非零或为正，也没有用 $|\mu_j|$ 代替 $\mu_j$。因此负模态的自然时间符号以及实际周期所对应的正负抵消完整保留于式 (27)；没有加入无周期、混合性或平稳概率律前提。特别是，零模态没有因为正步消失而被从包含零步的求和指标中删除。

**弱闭端点与质量丢失。** 由 $m\leq h<H$，原状态 $\pm m$ 属于真实闭区间 $[-h,h]$，而吸收格点 $\pm H$ 在其外。由实际定义 (3)，从 $r=m$ 向外的增量 $+1$ 被限制掉，向内的增量 $-1$ 留下质量 $1/2$；从 $r=-m$ 的情况相反。这个结论也包括 $h=m$。本文始终使用这同一个限制核和它的实际组合幂，没有把退出行重新归一化，亦未将弱闭事件改成严格事件。

**主模态一致性与量词。** 上游 B0 将 $j=1$ 的式 (18) 化为已有主余弦的精确有限幂；但式 (18) 的证明逐个覆盖了全部 $j\in J_m$。时间为任意自然数，起点为每个 $r\in I_m$，阈值为每个 $m\leq h<m+1$。没有增加正生存质量、奇数模态、奇偶匹配、长时间或渐近条件。

本证明限于冻结的 D1 与 D2 常数一分支；不声称任意有限数据或任意实测试函数的完整核谱，不推导逐原子核谱、有限余切和、显式 S1 或 S2–S4，也不扩展到非整数起点、$m=0$ 或 $0\leq h<1$ 的其他分支。
