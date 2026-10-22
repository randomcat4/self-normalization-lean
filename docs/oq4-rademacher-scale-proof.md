# OQ4 确定性尺度序列装配：匿名证明

STATUS: PROOF_READY
RESULT: PROVED_RELATIVE_TO_FIXED_PROJECT_DA1
SCOPE: DA2_DETERMINISTIC_DERIVED_ASSEMBLY
NEW_RAW_LEAF_COUNT: 0
LEAN_STATUS: NOT_RUN

本文证明冻结文件 `drafts/oq4/frozen-rademacher-scale-assembly-v1.md` 的全部 DA2.0–DA2.4。该文件的 SHA256 为 `9e7f840f25038e4ef55ba561eaca112802a6b373849722898f6d6a550ca9e946`，字节数为 5248。本文是数学证明稿，尚待独立数学审查；不宣称 DA2 已获形式认证。

## 1. 固定项目依赖、对象与量词

唯一使用的项目数学上游是以下两个固定接口的相关结论。

1. Scalar：`drafts/oq4/frozen-rademacher-scalar-bounds-v1.md`，SHA256 `225b63ae8522a126cb5c126f83cb782b024e95f592e9e2da5f36f56e0ce21356`，9414 字节。本文承接其 SCA0 的真实定义及全域合法性。对应的实际认证 Scalar 模块为 `Shao.OQ4.RademacherScalarBounds`，固定 PR104 head 为 `38648924aa3732ed3653363ad91872d237261fc2`。
2. DA1：`drafts/oq4/frozen-rademacher-lattice-shift-v1.md`，SHA256 `9cf9dba01aa9582ceb8e4d30af06c4778b8b367b61e61562dfc42c7ffb0e2b56`，6067 字节。本文直接使用其第 4 节的全有限参数绝对常数界。该固定结论已过独立数学门，其 Lean 状态仍为 pending；本文相对于这一固定项目结论展开，不重新证明 DA1。

具体地，在选择任何序列之前，由固定 DA1 取一个绝对实常数 \(C>0\)，使得对所有 \(m\in\mathbb N\)、所有实数 \(h\)、所有 \(n\in\mathbb N\)，只要
\[
1\le m,\qquad (m:\mathbb R)\le h<(m:\mathbb R)+1,
\]
就有
\[
\begin{split}
\Big|\,\lambda\frac{N}{h^2}
 +N\log\rho(m)+\log\frac{\pi a(m)}4
 -\frac{\pi^2}{4}\frac{N}{h^3}\bigl(H(m)-h\bigr)\,\Big|
 \le C\left(\frac{N}{h^4}+\frac1{H(m)^2}\right),
\end{split}
\tag{1}
\]
其中
\[
\begin{gathered}
N=(n:\mathbb R),\qquad H(m)=(m:\mathbb R)+1,\qquad
u(m)=\frac{\pi}{4H(m)},\\
a(m)=\frac1{H(m)}\frac{\cos u(m)}{\sin u(m)},\qquad
\rho(m)=\cos\frac{\pi}{2H(m)},\qquad \lambda=\frac{\pi^2}{8}.
\end{gathered}
\tag{2}
\]
这里的 \(C\) 是 DA1 本身的统一常数，先于 \(m,h,n\) 以及以下全部序列选定；它不是本定理新加入的自由误差假设，也不依赖以下的 \(M\) 或任何起点。式 (1) 包括 \(n=0\)。本文不调用独立的 Taylor 余项假设或自由的 \(C_{\log}\)。

现在任取
\[
m_\bullet,n_\bullet:\mathbb N\longrightarrow\mathbb N,\qquad
h_\bullet:\mathbb N\longrightarrow\mathbb R,
\]
满足对每个 \(k\in\mathbb N\) 均有
\[
1\le m_k,\qquad (m_k:\mathbb R)\le h_k<(m_k:\mathbb R)+1.
\tag{3}
\]
定义
\[
\begin{gathered}
N_k=(n_k:\mathbb R),\qquad H_k=(m_k:\mathbb R)+1,\qquad
\delta_k=H_k-h_k,\\
u_k=\frac{\pi}{4H_k},\qquad
a_k=H_k^{-1}\frac{\cos u_k}{\sin u_k},\qquad
\rho_k=\cos\frac{\pi}{2H_k},\qquad
\lambda=\frac{\pi^2}{8}.
\end{gathered}
\tag{4}
\]
所有对数均指实对数。由 (2)、(4) 的同一透明表达式，
\[
H_k=H(m_k),\quad u_k=u(m_k),\quad
a_k=a(m_k),\quad \rho_k=\rho(m_k).
\tag{5}
\]
其中 \(H_k^{-1}=1/H_k\)，且乘除结合给出两种 \(a_k\) 写法的相等性。因此这里只使用同一固定 Scalar/DA1 对象，没有替换为自由的 \(H,a,\rho,\delta\)。

假设且只假设以下三个尺度条件：
\[
h_k\longrightarrow+\infty,\qquad
\frac{N_k}{h_k^2}\longrightarrow+\infty,
\tag{6}
\]
以及
\[
\exists M\in\mathbb R\;\exists K_B\in\mathbb N:
\quad M>0\quad\hbox{且}\quad
\forall k\ge K_B,\quad \frac{N_k}{h_k^3}\le M.
\tag{7}
\]
固定 (7) 的一个见证 \(M,K_B\)。此后 \(M\) 与 \(K_B\) 均不随 \(k\) 改变，可以依赖所选序列；这与 (1) 的绝对常数 \(C\) 不同。不假设任何序列单调，也不假设每个 \(n_k\) 都为正。

以下所有极限均沿自然数 \(k\to\infty\)。对于趋向 \(+\infty\)，使用通常定义：对每个实数 \(R\)，存在自然数起点，使所有其后的项都大于 \(R\)。

## 2. DA2.0：每一项的合法性和弱端点

固定任意 \(k\in\mathbb N\)。由 \(1\le m_k\) 的实数转换及 (3)，
\[
h_k\ge (m_k:\mathbb R)\ge1,\qquad H_k\ge2.
\tag{8}
\]
特别地，\(h_k>0\)、\(H_k>0\)。由 \(\delta_k=H_k-h_k\) 及 (3)，
\[
0<\delta_k,\qquad
\delta_k=(m_k:\mathbb R)+1-h_k\le1,\qquad
H_k=h_k+\delta_k.
\tag{9}
\]
若 \(h_k=(m_k:\mathbb R)\)，则直接代入得 \(\delta_k=1\)。严格上端条件 \(h_k<H_k\) 保证 \(\delta_k\ne0\)；整数弱端点没有被改为 strict 事件端点。

对任意正整数 \(r\)，(8) 给出 \(h_k^r>0\)、\(H_k^r>0\)。因此本文使用的 \(h_k,h_k^2,h_k^3,h_k^4,H_k,H_k^2,H_k^3,H_k^4\) 均非零；\(2H_k\) 与 \(4H_k\) 亦严格为正。

将 Scalar 的 SCA0 用于满足 \(1\le m_k\) 的同一 \(m_k\)，并使用 (5)，得到
\[
0<u_k\le\frac{\pi}{8}<\frac{\pi}{2},\qquad
0<\frac{\pi}{2H_k}\le\frac{\pi}{4}<\frac{\pi}{2},
\tag{10}
\]
以及
\[
\sin u_k>0,\quad \cos u_k>0,\quad
a_k>0,\quad 0<\rho_k<1,\quad \frac{\pi a_k}{4}>0.
\tag{11}
\]
这里 \(\pi>0\)，故各固定常数分母也非零；特别是 \(a_k\) 中的正弦分母非零。两处对数 \(\log\rho_k\) 与 \(\log(\pi a_k/4)\) 的自变量确实严格为正。这些结论对每个 \(k\) 成立，没有使用 (6)–(7) 或正时间。

同时，作为自然数的实数转换，
\[
N_k\ge0\qquad\text{对所有 }k.
\tag{12}
\]
当 \(n_k=0\) 时 \(N_k=0\)，上述合法性仍然全部成立。

由 (8)–(9) 还得到以下对每个 \(k\) 有效的几何比较：
\[
h_k<H_k=h_k+\delta_k\le h_k+1\le2h_k.
\tag{13}
\]
最后一步仅用 \(h_k\ge1\)。

## 3. DA2.1：几何极限与最终时间域

首先，由 \(h_k\to+\infty\) 及 \(H_k\ge h_k\)，直接依定义得到
\[
H_k\longrightarrow+\infty.
\tag{14}
\]
由 \(h_k>0\) 及 \(h_k\to+\infty\)，有
\[
\frac1{h_k}\longrightarrow0.
\tag{15}
\]
确切地，对任何 \(\varepsilon>0\)，(6) 给出自然数 \(K_h(\varepsilon)\)，使
\(k\ge K_h(\varepsilon)\) 时 \(h_k>1/\varepsilon\)，于是
\(0<1/h_k<\varepsilon\)。

用 (9) 与 \(h_k>0\)，对每个 \(k\) 有恒等式和界
\[
\frac{H_k}{h_k}-1=\frac{\delta_k}{h_k},\qquad
0<\frac{\delta_k}{h_k}\le\frac1{h_k}.
\tag{16}
\]
由 (15) 夹逼，得到
\[
\frac{H_k}{h_k}\longrightarrow1.
\tag{17}
\]
这里没有要求 \(\delta_k\) 本身有极限。

为传递二次时间尺度，由 (12)–(13) 和正分母，
\[
0\le\frac{N_k}{H_k^2},\qquad
\frac{N_k}{H_k^2}\ge\frac{N_k}{4h_k^2}
=\frac14\frac{N_k}{h_k^2}
\quad\text{对所有 }k.
\tag{18}
\]
任取 \(R\in\mathbb R\)。由 (6)，存在自然数 \(K_R\)，使对所有 \(k\ge K_R\)，
\[
\frac{N_k}{h_k^2}>4\bigl(\max\{R,0\}+1\bigr).
\]
式 (18) 因而给出
\[
\frac{N_k}{H_k^2}>\max\{R,0\}+1>R.
\]
这逐个实数阈值证明了
\[
\frac{N_k}{H_k^2}\longrightarrow+\infty.
\tag{19}
\]

在 (19) 中取固定阈值 \(1\)，选得一个自然数 \(K_T\)，使
\[
\forall k\ge K_T,\qquad \frac{N_k}{H_k^2}>1.
\]
因为每个 \(H_k^2>0\)，乘以它即得
\[
\forall k\ge K_T,\qquad H_k^2<N_k,
\tag{20}
\]
从而得到所需的 \(H_k^2\le N_k\)。此 \(K_T\) 是一个固定起点，不依赖其后所取的 \(k\)。

再令 \(K_+=K_T\)。对 \(k\ge K_+\)，(20) 与 \(H_k^2>0\) 给出 \(N_k>0\)。若相应自然数 \(n_k=0\)，则其实数转换 \(N_k=0\)，矛盾。因此
\[
\forall k\ge K_+,\qquad 0<n_k.
\tag{21}
\]
这严格区分了实数 \(N_k>0\) 与自然数 \(0<n_k\)，并只证明最终正时间；早期 \(n_k=0\) 仍被允许。

## 4. DA2.2：余项尺度与三次幂替换

设
\[
B_k:=\frac{N_k}{h_k^3}.
\tag{22}
\]
由 (8)、(12)，每个 \(B_k\ge0\)。对 \(k\ge K_B\)，(7) 给出固定界 \(0\le B_k\le M\)。正分母下的代数恒等式给出
\[
\frac{N_k}{h_k^4}=\frac{B_k}{h_k}.
\]
因此对所有 \(k\ge K_B\)，
\[
0\le \frac{N_k}{h_k^4}\le\frac{M}{h_k}.
\tag{23}
\]
对任意 \(\varepsilon>0\)，由 \(h_k\to+\infty\) 选一个自然数 \(K_4(\varepsilon)\)，使 \(k\ge K_4(\varepsilon)\) 时 \(h_k>M/\varepsilon\)。于是 \(k\ge\max\{K_B,K_4(\varepsilon)\}\) 时，(23) 的右端小于 \(\varepsilon\)。这证明
\[
\frac{N_k}{h_k^4}\longrightarrow0.
\tag{24}
\]
此结论是三个尺度条件的推论，没有被预设。

由 \(H_k\ge h_k\ge1\)，对每个 \(k\) 有
\[
0<\frac1{H_k^2}\le\frac1{H_k}\le\frac1{h_k}.
\tag{25}
\]
用 (15) 夹逼，得到
\[
\frac1{H_k^2}\longrightarrow0.
\tag{26}
\]

又由 \(N_k\ge0\) 及 \(H_k\ge h_k>0\)，
\[
0\le\frac{N_k}{H_k^3}\le\frac{N_k}{h_k^3}=B_k
\quad\text{对所有 }k.
\tag{27}
\]
故可明确选择
\[
M':=M>0,\qquad K':=K_B,
\tag{28}
\]
使
\[
\forall k\ge K',\qquad 0\le\frac{N_k}{H_k^3}\le M'.
\tag{29}
\]
\(M'\) 与 \(K'\) 都是固定见证，可以依赖序列，但不随 \(k\) 改变。

最后证明三次幂替换。令
\[
D_k:=\frac{N_k}{h_k^3}-\frac{N_k}{H_k^3}.
\]
由正分母、\(H_k-h_k=\delta_k\)，每个 \(k\) 均有完整恒等式
\[
\begin{split}
D_k
&=\frac{N_k(H_k^3-h_k^3)}{h_k^3H_k^3}\\
&=\frac{N_k}{h_k^3}\,
  \frac{\delta_k(H_k^2+H_kh_k+h_k^2)}{H_k^3}\\
&=B_k\,\frac{\delta_k}{H_k}
  \left(1+\frac{h_k}{H_k}
             +\left(\frac{h_k}{H_k}\right)^2\right).
\end{split}
\tag{30}
\]
因为 \(0<h_k/H_k<1\)、\(B_k\ge0\) 和 \(0<\delta_k\le1\)，括号内的量至多为 \(3\)，于是
\[
0\le D_k\le\frac{3B_k}{H_k}
\le\frac{3B_k}{h_k}
=3\frac{N_k}{h_k^4}
\quad\text{对所有 }k.
\tag{31}
\]
特别地，在 \(k\ge K_B\) 时亦有 \(D_k\le3M/H_k\)。用 (24) 和 (31) 夹逼，得到
\[
\frac{N_k}{h_k^3}-\frac{N_k}{H_k^3}\longrightarrow0.
\tag{32}
\]
这里直接估计了差本身，未对两项分别取极限，也未假设 \(B_k\) 或 \(\delta_k\) 收敛。

## 5. DA2.3：消费同一 DA1 界使确定性残差消失

对每个 \(k\)，定义所需的完整确定性残差
\[
E_k:=
\lambda\frac{N_k}{h_k^2}
+N_k\log\rho_k
+\log\frac{\pi a_k}{4}
-\frac{\pi^2}{4}\frac{N_k}{h_k^3}\delta_k.
\tag{33}
\]
第 2 节已证明每个分母及对数自变量合法。将 (1) 逐项用于
\[
m=m_k,\qquad h=h_k,\qquad n=n_k
\]
是合法的，因为 (3) 对每个 \(k\) 成立，且 (1) 包括全部自然数时间。用 (5) 及 \(\delta_k=H_k-h_k\)，所得到的恰好是
\[
|E_k|\le C\left(\frac{N_k}{h_k^4}+\frac1{H_k^2}\right)
\quad\text{对每个 }k.
\tag{34}
\]
这实际消费了同一个固定 DA1 的全有限参数界及其同一个绝对常数 \(C\)，没有另设沿本序列的 \(o(1)\) 或逐项误差常数。

由 (24)、(26) 和 \(C>0\)，(34) 右端趋于零。具体地，对任意 \(\varepsilon>0\)，由 (24) 选自然数 \(K_{E,1}\)，使 \(k\ge K_{E,1}\) 时
\[
\frac{N_k}{h_k^4}<\frac{\varepsilon}{2C};
\]
由 (26) 选自然数 \(K_{E,2}\)，使 \(k\ge K_{E,2}\) 时
\[
\frac1{H_k^2}<\frac{\varepsilon}{2C}.
\]
因此在固定起点 \(\max\{K_{E,1},K_{E,2}\}\) 之后，式 (34) 给出 \(|E_k|<\varepsilon\)。故
\[
E_k\longrightarrow0,
\tag{35}
\]
即 DA2.3。

这里从未把 \(\lambda N_k/h_k^2\) 与 \(N_k\log\rho_k\) 分别取极限后相加；它们可能分别发散。趋于零的是由 (34) 直接控制的完整残差。

## 6. DA2.4：次临界确定性特化

现在仅在本节进一步假设
\[
B_k=\frac{N_k}{h_k^3}\longrightarrow0.
\tag{36}
\]
仍保留此前全部固定域和三个尺度条件。令 \(c:=\pi^2/4>0\)。由 \(B_k\ge0\) 和 \(0<\delta_k\le1\)，对每个 \(k\) 有
\[
\left|cB_k\delta_k\right|
=cB_k\delta_k\le cB_k.
\tag{37}
\]
式 (36) 因而推出 \(cB_k\delta_k\to0\)，不需要 \(\delta_k\) 有极限。

定义不带位移的确定性表达式
\[
F_k:=
\lambda\frac{N_k}{h_k^2}
+N_k\log\rho_k+\log\frac{\pi a_k}{4}.
\tag{38}
\]
由 (33) 有每项精确恒等式 \(F_k=E_k+cB_k\delta_k\)，故
\[
|F_k|\le |E_k|+cB_k.
\tag{39}
\]
对任意 \(\varepsilon>0\)，(35) 给出一个自然数起点，其后 \(|E_k|<\varepsilon/2\)；(36) 给出另一个自然数起点，其后 \(B_k<\varepsilon/(2c)\)。取两者的最大值后，(39) 给出 \(|F_k|<\varepsilon\)。因此
\[
\lambda\frac{N_k}{h_k^2}
+N_k\log\rho_k+\log\frac{\pi a_k}{4}
\longrightarrow0.
\tag{40}
\]
这就是 DA2.4。其取整位移项的消失来自 (37)，不依赖任何关于相位或取整误差收敛的额外条件。

## 7. 覆盖范围与结论

以上对任意满足 (3)、(6)、(7) 的三条序列，已经证明冻结的全部 DA2.0–DA2.3；进一步有 (36) 时，亦证明 DA2.4。全部逐项合法性和 (34) 都覆盖 \(k=0\) 及任何早期 \(n_k=0\)。只有 (20)–(21) 和 (29) 被声明为最终成立；它们的自然数起点与实数上界均已固定。除 DA1 的绝对常数 \(C\) 外，出现的 \(M,M'\) 和各起点可以依赖序列，始终不依赖正在量化的 \(k\)。

任意自然数时间序列 \(n_k\) 是本文已证明的辅助推广；取 \(n_k=k\) 即得到以原时间索引表述的相应确定性结论。本文的域是 (3) 对全部 \(k\) 成立。若后继实际应用仅最终满足该域，仍须另行合法处理有限前缀，本文没有把这一步当作实际概率应用已经完成。

本证明只装配固定 Scalar/DA1 后的确定性分析输出，不给出 S1/Pair/U1、真实概率或 Brownian 的认证。DA2.1 仅交付后继 U1 的最终时间域；实际 S2、S3、S4、S5、Brownian、Spectrum 及 OQ4 根结论均保持 OPEN。未来 Lean 实现必须连接实际认证后的 DA1 声明；本稿没有运行 Lean，也没有把该形式认证提前宣称为完成。
