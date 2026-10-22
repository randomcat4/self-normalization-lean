# Rademacher 标量界的完整数学证明

STATUS: PROOF_READY
SCOPE: MATH_ONLY
MATHEMATICAL_RESULT: PROVED
INDEPENDENT_REVIEW: PENDING
LEAN_STATUS: NOT_RUN

本稿只证明冻结版本的 SCA0、SCA1、SCA2。证明中的全部定量估计均在文内推导；不把泰勒估计或余项界作为额外前提。不涉及概率谱身份、谱配对、谱尾、布朗运动或其任何证明。本稿是待独立审查的匿名数学作者稿，不构成机械认证。

## 一、冻结对象、量词与常数

令 \(m\in\mathbb N\) 满足 \(1\le m\)，严格沿用冻结定义：

\[
H=H(m)=(m:\mathbb R)+1,\qquad
u=u(m)=\frac{\pi}{4H},\qquad
z=z(m)=\frac{\pi}{2H},
\]
\[
a=a(m)=\frac1H\frac{\cos u}{\sin u},\qquad
\rho=\rho(m)=\cos z,\qquad
\lambda=\frac{\pi^2}{8}.
\]

这里的 \(H\) 始终是这个 \(m\) 所决定的数，不是独立实参数。正切仅作为证明中的辅助函数，按
\(\tan t=\sin t/\cos t\) 使用。

在量化 \(m\) 之前，取定两个绝对实常数

\[
\boxed{C_a=\frac{\pi}{3},\qquad
C_\rho=\frac{\pi^4}{48}.}
\tag{1}
\]

由于 \(\pi>0\)，两者均严格为正。下面证明：对每个上述 \(m\)，SCA0 的全部合法性结论成立，且

\[
\left|a-\frac4\pi\right|\le \frac{C_a}{H^2},
\qquad
\left|\log\rho+\frac{\lambda}{H^2}\right|
\le \frac{C_\rho}{H^4}.
\tag{2}
\]

所有对数均为实自然对数。下文先证明其自变量为正，再求导或积分。

## 二、SCA0：全部定义合法性

由自然数到实数的序关系保持性，\(1\le(m:\mathbb R)\)。因此

\[
H\ge2>0,\qquad H^2>0,\qquad H^4>0.
\tag{3}
\]

由 \(\pi>0\)、\(4H\ge8>0\)、\(2H\ge4>0\)，得到

\[
0<u\le\frac{\pi}{8}<\frac{\pi}{2},
\qquad
0<z\le\frac{\pi}{4}<\frac{\pi}{2}.
\tag{4}
\]

正弦在 \((0,\pi)\) 上为正，余弦在
\((-\pi/2,\pi/2)\) 上为正，所以

\[
\sin u>0,\qquad \cos u>0,\qquad \cos z>0.
\tag{5}
\]

因而 \(a=(1/H)(\cos u/\sin u)>0\)，以及
\(\rho=\cos z>0\)。另一方面，

\[
1-\rho=1-\cos z=2\sin^2(z/2)>0.
\tag{6}
\]

最后一个严格不等式成立，是因为
\(0<z/2\le\pi/8<\pi\)，从而 \(\sin(z/2)>0\)。
于是

\[
a>0,\qquad 0<\rho<1,\qquad \frac{\pi a}{4}>0.
\tag{7}
\]

这证明了冻结 SCA0 的每项结论。特别地，\(H\)、\(2H\)、\(4H\)、
\(H^2\)、\(H^4\)、\(\sin u\) 和 \(\cos u\) 均非零；
\(\pi\) 也非零。故冻结定义中的商以及下面使用的正切、倒正切商均合法。
\(\log\rho\) 和后继可能使用的 \(\log(\pi a/4)\) 的自变量是真实正数。
后一项在本稿只核对合法性，不声明其定量界。

## 三、文内证明的角度估计

下面在固定角度区间 \(I=[0,\pi/4]\) 上证明三个辅助估计：

\[
0\le\tan t\le2t,\qquad
0\le\tan t-t\le\frac43t^3,\qquad
0\le-\log(\cos t)-\frac{t^2}{2}\le\frac{t^4}{3}
\quad(t\in I).
\tag{8}
\]

这只是实变函数的辅助引理；最后只在冻结定义给出的 \(u(m)\)、
\(z(m)\) 上使用它，不改动 \(m,H\) 的量化范围。

对 \(s\in I\)，有 \(\cos s>0\)，而 \(0\le2s\le\pi/2\)，
故 \(\cos(2s)\ge0\)。倍角恒等式给出

\[
\cos^2s=\frac{1+\cos(2s)}2\ge\frac12,
\qquad
0<\frac1{\cos^2s}\le2.
\tag{9}
\]

正切在整个开区间 \((-\pi/2,\pi/2)\) 上光滑；
由商法则和 \(\sin^2s+\cos^2s=1\)，

\[
\frac{d}{ds}\tan s
=\frac{\cos^2s+\sin^2s}{\cos^2s}
=\frac1{\cos^2s}.
\tag{10}
\]

因此，由微积分基本定理和 \(\tan0=0\)，对每个 \(t\in I\)，

\[
\tan t=\int_0^t\frac{ds}{\cos^2s}.
\tag{11}
\]

积分区间非负，结合 (9) 就有 \(0\le\tan t\le2t\)。
这证明 (8) 的第一项，也给出对任意 \(s\in I\) 的
\(0\le\tan^2s\le4s^2\)。

再由 (10)，

\[
\frac{d}{ds}(\tan s-s)
=\frac1{\cos^2s}-1
=\frac{\sin^2s}{\cos^2s}
=\tan^2s.
\tag{12}
\]

利用 \(\tan0-0=0\)，再积分一次：

\[
\tan t-t=\int_0^t\tan^2s\,ds.
\tag{13}
\]

其被积函数非负且不超过 \(4s^2\)，故

\[
0\le\tan t-t\le\int_0^t4s^2\,ds=\frac43t^3.
\tag{14}
\]

这证明 (8) 的第二项；特别地 \(\tan t\ge t\)。

最后，\(\cos s>0\) 使 \(\log(\cos s)\) 在上述开区间上可微，
链式法则给出

\[
\frac{d}{ds}\left(-\log(\cos s)-\frac{s^2}{2}\right)
=\tan s-s.
\tag{15}
\]

该函数在零处等于零。因此由 (14)，

\[
-\log(\cos t)-\frac{t^2}{2}
=\int_0^t(\tan s-s)\,ds,
\]
\[
0\le-\log(\cos t)-\frac{t^2}{2}
\le\int_0^t\frac43s^3\,ds=\frac{t^4}{3}.
\tag{16}
\]

这证明 (8) 的第三项。所有被积函数均在相应闭区间连续，
且各求导处都位于余弦为正的开区间内；包括 \(t=0\) 和
\(t=\pi/4\) 的端点均已由上述积分公式覆盖。
尤其 (16) 是本稿从导数和积分推出的四阶余项估计，
不是借入的待证泰勒假设。

## 四、SCA1：\(a\) 的二阶误差

由 (4)，\(u\in(0,\pi/8]\subset I\)。由 (14)，

\[
\tan u\ge u>0,\qquad
0\le\tan u-u\le\frac43u^3.
\tag{17}
\]

SCA0 已给出 \(\sin u>0\) 和 \(\cos u>0\)，所以
\(\cos u/\sin u=1/\tan u\)。又因
\((4/\pi)u=1/H\)，冻结定义可准确写成

\[
a=\frac4\pi\frac{u}{\tan u}.
\tag{18}
\]

由 \(\tan u\ge u\) 及 \(\pi>0\)，有 \(0<a\le4/\pi\)。
故绝对值可以按下式准确去除：

\[
\left|a-\frac4\pi\right|
=\frac4\pi-a
=\frac4\pi\frac{\tan u-u}{\tan u}.
\tag{19}
\]

由于 (17) 中的分母及 \(u\) 都为正，且 \(4u^3/3\ge0\)，

\[
0\le\frac{\tan u-u}{\tan u}
\le\frac{(4/3)u^3}{\tan u}
\le\frac{(4/3)u^3}{u}
=\frac43u^2.
\tag{20}
\]

将 (20) 代回 (19)，并只使用 \(u=\pi/(4H)\)，得到

\[
\left|a-\frac4\pi\right|
\le\frac{16}{3\pi}u^2
=\frac{16}{3\pi}\frac{\pi^2}{16H^2}
=\frac{\pi/3}{H^2}
=\frac{C_a}{H^2}.
\tag{21}
\]

这就是 SCA1。

## 五、SCA2：\(\log\rho\) 的四阶余项

由 (4)，\(z\in(0,\pi/4]\subset I\)。用 (16) 取 \(t=z\)，
有

\[
0\le-\log(\cos z)-\frac{z^2}{2}\le\frac{z^4}{3}.
\tag{22}
\]

SCA0 已证明 \(\rho=\cos z>0\)，所以这里的对数与冻结
\(\log\rho\) 完全相同。由固定的 \(\lambda,z\) 定义，

\[
\frac{\lambda}{H^2}
=\frac{\pi^2}{8H^2}
=\frac12\left(\frac{\pi}{2H}\right)^2
=\frac{z^2}{2}.
\tag{23}
\]

(22) 左端说明
\(\log\rho+\lambda/H^2\le0\)。因此

\[
\left|\log\rho+\frac{\lambda}{H^2}\right|
=-\log(\cos z)-\frac{z^2}{2}
\le\frac{z^4}{3}
=\frac{\pi^4}{48H^4}
=\frac{C_\rho}{H^4}.
\tag{24}
\]

这就是 SCA2，领先系数严格为冻结的 \(\pi^2/8\)。

## 六、全域、端点与量词闭合

常数 (1) 已先于任意 \(m\) 选定。对每个 \(m\in\mathbb N\)、
\(1\le m\)，第二节都证明 SCA0，第四、五节都证明 (2)。
于是完整量词为

\[
\exists C_a\in\mathbb R\ \exists C_\rho\in\mathbb R,\quad
0<C_a\ \land\ 0<C_\rho\ \land\
\forall m\in\mathbb N,\quad 1\le m\Longrightarrow
\left(
\left|a(m)-\frac4\pi\right|
\le\frac{C_a}{((m:\mathbb R)+1)^2}
\ \land\
\left|\log\rho(m)+
\frac{\pi^2/8}{((m:\mathbb R)+1)^2}\right|
\le\frac{C_\rho}{((m:\mathbb R)+1)^4}
\right).
\tag{25}
\]

特别地，\(m=1\) 时 \(H=2,u=\pi/8,z=\pi/4\)；
\(m=2\) 时 \(H=3,u=\pi/12,z=\pi/6\)。
两者全部包含于已经证明的闭区间估计，均无需另加例外、
阈值或更大的 \(m\)。在 \(m=1\) 的最大角度
\(z=\pi/4\) 处，(9) 仍有 \(\cos^2z=1/2>0\)，
所以所有导数、对数和分母仍合法。

证明没有使用“充分大”、自由 \(H\)、任何 \(h,n\)、尺度序列、
奇偶条件或概率正性前提。常数不依赖这些对象。
除 SCA0 中规定的对数合法性外，本稿不输出
\(C_{\log}\) 或 \(C_{\tan}\) 的后继定量声明。

## 七、输入、依赖与访问记录

本稿数学输入仅为以下获准材料；读入时已经核对完整文件的
SHA256 和字节数：

| 材料 | SHA256 | 字节数 | 内容读取范围 |
| --- | --- | ---: | --- |
| 冻结标量声明 v1 | 225b63ae8522a126cb5c126f83cb782b024e95f592e9e2da5f36f56e0ce21356 | 9414 | 全文 |
| 原始 spectrum01.md | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 4306 | 全文，只读 |
| 已认证公开声明账 declarations.md | e9ec045fccfd4ed68f5b6515f1b28310ab90bf71609cb7bba87a0c1b4d7f850c | 39048 | 仅 148–179、599–622 行 |

公开生成等式确认
\(\operatorname{angle}(m)=\pi/(2((m:\mathbb R)+1))=z(m)\)，
以及
\(\operatorname{rho}(m)=\cos(\operatorname{angle}(m))=\rho(m)\)。
本证明只用这些透明定义的识别，不消费旧定理的证明体。

另外只读取了派发要求的项目规则和数学工作流技能说明。
未读取 intake、candidate、source-semantic 报告，未读取任何其他匿名
作者证明、数学或形式审查，未读取 S1 私有实现或草稿、旧库证明体、
Pair/Tail 证明或报告。冻结文件自身关于这些对象的范围说明，
不作为它们已获证的输入。

依赖账如下：

| 所用事实 | 性质 | 本稿中的用途 |
| --- | --- | --- |
| 实数有序域运算、\(\pi>0\)、自然数嵌入保持序 | 基础事实 | 第二节及分母、常数的正性 |
| 正余弦符号、勾股与倍角恒等式、基本导数 | 初等实分析事实 | 第二、三节 |
| 微积分基本定理、连续函数积分保序 | 初等微积分事实 | (11)、(13)、(16) |
| (8) 的正切与对数余项估计 | 本稿完整证明 | 第四、五节闭合冻结定量界 |

未使用需要外部精准文献归属的非初等定理，未联网寻找证明，
未运行 Lean，未生成编译产物，未改动冻结输入或原来源。
在冻结 SCA0、SCA1、SCA2 的纯数学范围内没有遗留未证点；
独立审查和形式实现仍属后续单独工作。
