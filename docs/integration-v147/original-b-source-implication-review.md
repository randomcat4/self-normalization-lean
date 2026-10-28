# 原始 OQ3 修复命题 B 及有界推论 C：来源假设到 IZ341/JA342 的独立蕴含审查

日期：2026-10-28。角色：Root5 委派的独立数学审查者 `/root/original_b_scope_implication_review`。本报告只审查原始来源假设是否足以调用已接受的精确定理，以及这些定理是否给出原固定律、固定点结论；不重新审查已合格的完整旧证明，不更新原题或所有权状态。

**STATUS: CORRECT，限下述明确范围。原 B 的固定概率律、固定 $x\in(0,1)$ 充分修复结论，在保留原假设的情况下，数学上已由接受的 IZ341 推出；原有界 C 的单鞍点弱 Cramér 稳定性及相应固定点尾展开由接受的紧倾斜稳定性结果与 JA342 推出。没有发现还须给 B/C 增加的实质数学假设。** 参数紧集内部性、真实矩阵曲率和真实全局率的衔接论证见下文。若另外编写一个保留 B 全部冗余前提的 Lean 命名包装，那是形式接口工作，不是尚缺的数学定理。D 的八幅值、两个丢番图条件及小正鞍点存在性不因此关闭。

## 1. 精确版本与证据边界

实际读取 `coordination/REGISTRY.json` 的 `currentAuthoritativeState` 与 `library/SNAPSHOT.json`：当前接受快照为 v146 / PR525，main `26ac095ebf977b7f7ffd08f88622f3c6968132c2`；唯一协调者为 Root5。历史 PROPOSED 的 `drafts/oq3/root-contract.md` 仅用于识别 B/C 标签与固定律问题意图，以下数学前提直接取自 R2/RP，不把该旧文档当作已接受 Lean 根声明。

两个原始来源的实际 SHA256 均吻合任务给定值：

| 来源 | SHA256 | 本审查承重位置 |
|---|---|---|
| `C:/game/shao/current/oq3/proofs/r2/report.md`（R2） | `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55` | 1–79，83–104，168–173，278–288，343–373 |
| `C:/game/shao/current/oq3/proofs/r2/repair01.md`（RP） | `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd` | 9–41，边界坐标公式 $8$–$14$，212–226 |

实际读取的接受源码及实际 SHA256：

| 单元 / 源码（相对于 `library/`） | SHA256 |
|---|---|
| IY340 `Shao/OQ3/CanonicalActualSelfNormalizedTail.lean` | `9142fca892e49cbc44b4e39ac533bb47f5bc8baf0540c8b12a959a4d3886a447` |
| IZ341 `Shao/OQ3/CanonicalActualTailScaledExpansion.lean` | `f41f8f56d5db27b26b03fbd983ff9a352ac3c1fffa512c9959fb362bc0677798` |
| JA342 `Shao/OQ3/BoundedCanonicalActualTailScaledExpansion.lean` | `0fd9a975807b524eaeb1b308dffae928f739e91785e05b744d4ee928a44583c1` |
| IX339 `Shao/OQ3/CovarianceRowInverseQuadratic.lean` | `1b4ec8feaf3445d7f7fa2508f66cae0cfcb9bb20d05389787bb860ad61fd9836` |

复用 `coordination/intake-pr524/root-qualification.json` 及 `drafts/oq3/publication-u22-canonical-p54/docs/oq3-u22-canonical-p54/` 中的资格记录。实际核对 IY/IZ/JA 的源码、既有独立审查、receipt、actual-types 文件哈希与资格字段一致；IZ/JA 的同一完整独立审查明确覆盖二者。该目录中 IZ 与 JA 复用的审查文件是 `u22iz-proof-review.md`，不是一个另造的 JA 审查文件。没有安排重复完整证明审查或重跑任何机器检查。

| 单元 | 资格记录 SHA256 | 已有 actual TYPE SHA256 |
|---|---|---|
| IY340 | `9b8d86f677c4bceed0819a5ad24a5c554d23946e857aecb536334fc834288873` | `aaf920a61f8b9aa6a98cd7d7ccc1de6d791ac2f724945300f3ccf6d0958e581d` |
| IZ341 | `1e6be9c4e79013c856f0e9736bcabe1c0fa0dacde8e9dc8dffd4bf3f43c784a1` | `148c6b0860f5f386e49a85d8df4da76c1a9e2bf81fd200788577983b31cab61a` |
| JA342 | `a4a945fd0e2ed532fd1ec5110ed9832cc828a848b5ff4d6401a4ff974cfcd0ad` | `2f5c9c6d92456ce8c2bf7ce42c16bc3cdd8dffe8a64b0b2dbc12a64f076e0c3f` |

辅助定义/接口实际读取：`Shao/Probability/BivariateLegendre.lean`、`JointNonlattice.lean` 中的联合特征函数、`RegularCovariance.lean` 中的实际协方差、`OpenDomainMeanInverse.lean`、`OpenDomainLegendre.lean`、`OpenDomainSmoothMean.lean`、`OpenDomainBoundaryRate.lean`、`CompactTiltWeakCramer.lean`，以及 `ActualSelfNormalizedTailUniqueMinimum.lean`、`ActualExteriorFromUniqueMinimum.lean` 的承重输入输出。以下使用这些接受结果，不声称对它们重新完成一次完整证明审查。

## 2. 原对象与实际 Lean 输入逐项对应

固定原律 $\mu=\mathcal L(X)$，固定 $x\in(0,1)$，设 $W=(X,X^2)$，$\theta_0=(s_0,t_0)$。采用

\[
 Z(p)=\int e^{p_1u+p_2u^2}\,d\mu(u),\quad
 \mathcal D=\{p: e^{p_1X+p_2X^2}\text{ 可积}\},\quad
 K(p)=\log Z(p)\quad(p\in\mathcal D).
\]

R2 40–45 的原倾斜律是

\[
 d\mu_p(u)=Z(p)^{-1}e^{p_1u+p_2u^2}\,d\mu(u).
\]

这与 Lean 的 `mu.tilted (fun u => p.1*u+p.2*u^2)` 相同。IZ341 的 `mu` 始终是**原律**；其最终样本律为 `Measure.pi (fun _ : Fin n => mu)`，没有把倾斜律当作原样本律。

| IZ341 承重输入 | R2/RP 供给或本文完整推出的位置 |
|---|---|
| `0 < level`，`level=x` | R2 固定 $x\in(0,1)$。原上界 $x<1$ 保留，接受定理不需要它。 |
| `theta.2 < 0` | R2 47–49 的 $t_0<0$。 |
| `theta ∈ interior bivariateMGFDomain` | R2 50–51 的开邻域有限性；另见第 3 节直接论证。 |
| 实际倾斜均值 `=(a0,a0²/x²)`，`a0>0` | 原正则鞍点/矩点及 RP 的 $q_0=a_0^2/x^2$；若只先取全局极小矩点，也可按第 3 节推得其位于正边界。 |
| `theta.1 = -2*a0*theta.2/x²` | 原边界鞍点条件；RP $9$ 明写 $s_0+2a_0t_0/x^2=0$，第 3 节亦给出极小性推导。 |
| 实际 `parabolaCovariance` 行列式 $>0$ | R2 的实际 $\Delta(\theta_0)=\nabla^2K(\theta_0)\succ0$，第 3 节识别。 |
| `IsCompact Theta0`，`theta ∈ interior Theta0` | 从 R2 的均值逆像参数集位于原紧 $\Theta$ 完整推出，见第 4 节。 |
| 固定紧族的原 $(X,X^2)$ 联合 WC，$0<\beta<2/5,c>0,R\ge0$ | R2 $WC$、61 及 RP 22–24；必要时仅增大固定 $R$，见第 5 节。 |
| 精确矩阵 `Lambda1 > 0` | R2 49 与 RP $10$ 的同一切向曲率，第 6 节给出链式法则。 |
| 真正扩展实全局率在整个正尾域的唯一极小条件 | R2 62–67 **显式原假设**，与 Lean 的 `hUnique` 等价，见第 6 节。 |

原 $EX=0$、$P(X>0)>0$、一致谱界、一致 $8+\delta$ 阶矩及旧率间隙/显式远场概率条件均可照原样保留。接受定理以更少输入推出同一固定点结论，无需为应用它删改这些原假设。

## 3. 真实 MGF、实际矩点及鞍点关系

首先，$t_0<0$ 已使该参数位于真实 MGF 域内部。对任意 $s\in\mathbb R,t<0,u\in\mathbb R$，

\[
 su+tu^2=t\left(u+\frac{s}{2t}\right)^2-\frac{s^2}{4t}
 \le -\frac{s^2}{4t}.
\]

因此 $e^{su+tu^2}$ 有界并可积，$0<Z(s,t)<\infty$，整个开半平面 $\{t<0\}\subset\mathcal D$。这不是利用 Lean 对不可积函数积分的总化值来构造假的 $K$。原来的“$K$ 在 $\Theta$ 的开邻域有限”还给出整个来源参数集均位于 $\Omega=\operatorname{int}\mathcal D$。

在 MGF 内部可逐阶求导；在上述负二次项邻域也可直接用有界的“多项式乘高斯阻尼”支配。因此

\[
 \nabla K(p)=E_pW=m(p),\qquad
 \nabla^2K(p)=\operatorname{Cov}_{\mu_p}(W)=D(p).
\]

实际矩阵为

\[
 D(p)=\begin{pmatrix}
 \operatorname{Var}_p X&\operatorname{Cov}_p(X,X^2)\\
 \operatorname{Cov}_p(X,X^2)&\operatorname{Var}_p X^2
 \end{pmatrix}.
\]

它正是 `parabolaCovariance`，不是一个任意命名为协方差的参数矩阵。由原 $\Delta(\theta_0)\succ0$，得 $D(\theta_0)=\Delta(\theta_0)$ 且 $\det D>0$。

令 $w_0=m(\theta_0)=(a_0,q_0)$。来源“正则鞍点”及 RP $8$–$10$ 已采用 $q_0=a_0^2/x^2,a_0>0$ 与边界驻点关系。即使从“$w_0$ 是 $D_x$ 中的全局正则率极小点”开始展开其含义，也没有额外条件：$w_0\in D_x$ 给 $q_0>0$。局部 Legendre 对偶给 $\nabla I(w_0)=\theta_0$。若 $a_0>x\sqrt{q_0}$，则 $w_0$ 是尾域内点，局部极小性强迫 $\nabla I(w_0)=0$，与 $t_0<0$ 矛盾。故

\[
 a_0=x\sqrt{q_0}>0,\qquad q_0=a_0^2/x^2.
\]

沿边界 $\gamma(a)=(a,a^2/x^2)$ 的双侧局部极小性又给

\[
 0=\frac d{da}I(\gamma(a))\big|_{a=a_0}
   =s_0+\frac{2a_0t_0}{x^2},
\]

正好得到 IZ341 的 `hmean`、`ha0`、`hsaddle`。这里 $a_0$ 和 $q_0$ 是真实倾斜矩点，未另选一组只满足代数式的数。

## 4. 原参数紧集确实含鞍点的一个完整邻域

仅从“$\theta_0\in\Theta$，$\Theta$ 紧”不能推出内部性。本应用还用到了 R2 50–51 的**矩点邻域存在均值映射的逆，且对应参数集位于 $\Theta$**。以下给出完整推导，避免把这个步骤留作“接口待实例化”。

记来源矩点邻域为 $U$，其逆为 $g$，则 $m(g(w))=w$，$g(U)\subseteq\Theta\subset\Omega$。原假设意味着这是通过鞍点的均值逆；即使不预先指定其分支，下面的单射性也排除了换支问题。

1. MGF 域由 Hölder 不等式为凸集，故 $\Omega$ 为凸开集。在 $\Omega$ 内 $m$ 光滑，导数为实际协方差。正密度指数倾斜与原律互相绝对连续。由 $D(\theta_0)\succ0$，不存在非零 $d\in\mathbb R^2$ 使 $d\cdot W$ 原律几乎处处为常数；否则在 $\theta_0$ 倾斜下其方差也为零。相同支撑/零集性质说明对每个 $p\in\Omega$，每个非零 $d$ 都有
   $d^{\mathsf T}D(p)d=\operatorname{Var}_p(d\cdot W)>0$。所需矩在 MGF 内部有限。
2. 对不同 $p,q\in\Omega$，令 $d=p-q\ne0$，沿其线段积分得
   \[
   d\cdot(m(p)-m(q))=\int_0^1d^{\mathsf T}D(q+td)d\,dt>0.
   \]
   故 $m$ 在 $\Omega$ 上单射。特别地 $g(w_0)=\theta_0$。
3. 由 $D(\theta_0)$ 可逆及逆函数定理，存在开集 $V\ni\theta_0$、$O\ni w_0$，使 $m:V\to O$ 是光滑微分同胚，且 $V\subset\Omega$。这也正是已接受 `open_domain_quadratic_tilt_local_mean_inverse` 所供给的实际均值图。
4. 在 $U\cap O$ 内选开邻域 $U_1\ni w_0$。来源逆 $g$ 与该局部逆均落在 $\Omega$ 且均映到同一点，故由第 2 步二者相同。因此
   \[
   S=(m|_V)^{-1}(U_1)=g(U_1)
   \]
   是含 $\theta_0$ 的开参数邻域，且 $S\subseteq\Theta$。
5. 取足够小的固定 $\varepsilon>0$，使
   \[
   \Theta_0=\overline B(\theta_0,\varepsilon)
   \subset S\cap\Omega\cap\{p:p_2<0\}.
   \]
   在有限维中此集紧，且 $\theta_0\in\operatorname{int}\Theta_0$。R2 对原 $\Theta$ 的统一 WC 原常数直接限制到 $\Theta_0$。所有选择均在 $n$ 之前一次完成。

也可据此直接断定原 $\theta_0\in\operatorname{int}\Theta$，再取同样小球。上述证明没有假设一个新增的开参数带，也没有要求来源的整个紧 $\Theta$ 本身具有特殊形状。Lean 中乘积范数与这里欧氏范数给同一有限维拓扑，内部性和紧性没有范数差异问题。

## 5. 原 WC 作用对象、标准化及一致性

R2 从 $W=(X,X^2)$ 和 $P_\theta$ 引入的 $\varphi_\theta$ 是 **原二维 $W$ 在倾斜下的特征函数**。R2 83–92 随后另外定义标准化变量 $Y_\theta$，并说明把原 WC 转给它；R2 343–369 的二样本公式也直接用 $W-W'$。故实际输入恰好是

\[
 \left|\int e^{i(\xi u+\eta u^2)}d\mu_p(u)\right|
 \le1-c(\xi^2+\eta^2)^{-\beta/2},\quad
 p\in\Theta_0,\quad\sqrt{\xi^2+\eta^2}>R,
\]

与 `jointCharacteristic (mu.tilted ...) xi eta` 逐字对象一致。没有把单点 WC 偷换成无界族的一致 WC。

RP 9–41 的 $Y_p=D(p)^{-1/2}(W-m(p))$ 是用于外部八阶 Edgeworth 输入的标准化变量，不是对原 WC 假设的改义。为消除可能的读法歧义，两方向转换都可显式完成：

\[
 |\phi_{Y_p}(u)|=|\phi_{W,p}(D(p)^{-1/2}u)|,
 \qquad |\phi_{W,p}(v)|=|\phi_{Y_p}(D(p)^{1/2}v)|.
\]

平移只有单位模相位。若 $\lambda_-I\preceq D(p)\preceq\lambda_+I$，原 $W$ 的 $c,R$ 可传给 $Y$，取 $c_Y=c\lambda_-^{\beta/2},R_Y=\sqrt{\lambda_+}R$；反过来若先给 $Y$ 的统一 $c_Y,R_Y$，可取 $c_W=c_Y\lambda_+^{-\beta/2},R_W=R_Y/\sqrt{\lambda_-}$。这些调整均固定且不改变 $\beta$。增大 $R$ 至非负数或更大的固定阈值保持假设。来源明确保留严格 $0<\beta<2/5$，不涉及端点。

## 6. 全局率、实际曲率与修正常数

接受定义是扩展实函数

\[
 I(w)=\sup_{p\in\mathcal D}\{p\cdot w-K(p)\}\in\mathbb R\cup\{+\infty\}.
\]

这正是 `bivariateLegendreRate`；不在 $\mathcal D$ 外使用总化实积分定义 $K$。源文中“率函数/Legendre 对偶/全局率极小”的含义在这里必须保持为该真实全局率，不能另换成只对小参数图取上确界的局部函数。

在真实矩点 $w_0=E_{\theta_0}W$，其值确实是接受定理的 `J0`，而非未证的名字对应。对任何 $p\in\mathcal D$，倾斜恒等式与 Jensen 给

\[
 \frac{Z(p)}{Z(\theta_0)}
 =E_{\theta_0}e^{(p-\theta_0)\cdot W}
 \ge e^{(p-\theta_0)\cdot w_0}.
\]

取对数得 $p\cdot w_0-K(p)\le\theta_0\cdot w_0-K(\theta_0)$，且在 $p=\theta_0$ 取等。因而

\[
 I(w_0)=J_0=s_0a_0+t_0a_0^2/x^2-K(\theta_0)=\Lambda_0<\infty.
\]

这也可直接复用接受的 `open_domain_quadratic_tilt_legendre_attained`。局部逆图上相同论证对邻近矩点给全局 $I$ 与光滑局部 Legendre 函数相等，进而 $\nabla I(w_0)=\theta_0$、$\nabla^2I(w_0)=D^{-1}$。

**上述局部事实不推出全局唯一极小。** 所需全局条件直接来自 R2 62–67 的第 4 条原假设：鞍点是

\[
 D_x=\{(a,q):q>0,\ a\ge x\sqrt q\}
\]

上的唯一全局率极小点。因 $I(w_0)$ 有限，这句话精确等价于 IZ341 的

\[
 \forall w\in D_x,\quad I(w_0)\le I(w),\qquad
 (I(w)=I(w_0)\ \Longleftrightarrow\ w=w_0).
\]

允许 $I(w)=+\infty$ 的点不会破坏此等价。此条件不能从 $EX=0$、正协方差、局部逆图、局部鞍点方程或 WC 自动取得；它在**原 B 中已经是假设**，在某一具体分布应用中仍必须实际证明。R2 称“闭尾域”仅指弱边界 $\ge$；由于 $q>0$，它在全平面并不闭，接受定义同样没有加入 $q=0$。

令 $v=(1,2a_0/x^2)^{\mathsf T}$。沿边界曲线的二阶链式法则给

\[
 \frac{d^2}{da^2}I(a,a^2/x^2)\Big|_{a_0}
 =v^{\mathsf T}D^{-1}v+\frac{2t_0}{x^2}=\Lambda_1.
\]

这是 RP $10$ 的实际定义，也是 IZ341 的 `2*theta.2/level² + dotProduct v (D⁻¹ *ᵥ v)`。IX339 保证以协方差两行定义的真实线性等价之逆与此矩阵逆一致，不要求另交一个抽象 $L$。曲率正性来自原显式 $\Lambda_1>0$；仅有 $D\succ0$ 并不自动给出它，因为 $2t_0/x^2<0$。

因此

\[
 v_{\rm corr}=(-t_0)\sqrt{\det D}\sqrt{\Lambda_1}>0
\]

与 R2/RP 修正 p54 常数完全一致。这里没有改成 ICM 的另一印刷常数，没有遗漏边界 Jacobian，也没有把 $D^{-1}$ 换成协方差本身。

## 7. 显式旧远场条件可保留，但已不承担本次蕴含

RP 215–224 为旧局部路线显式增加

\[
 P^n\{\overline W_n\in D_x\setminus U\}
 \le C_Ee^{-n(\Lambda_0+\eta)}\quad(n\ge N_E),\qquad\eta>0.
\]

本次可以把它完整保留为 B 的额外原前提，直接应用更强的 IZ341。接受的 `actual_exterior_exponential_bound_of_unique_minimum` 从真实全局唯一极小及 $I(w_0)=J_0$ 出发，对实际选定的小鞍点矩形给出完整外域概率付款：低能量与高能量分别有任意指定指数率的**实际尾概率**上界，中段在能量夹层上紧化，再以真实率的紧集间隙/有限指数测试控制。该接口已经被 IY340/IZ341 调用，使用的是原 IID 样本和原正尾事件。

有一处必须分清：缩小 $U$ 会扩大 $D_x\setminus U$，所以旧 $U$ 的远场概率上界**不能仅由单调性**转给缩小后的矩形。本次没有这么做；接受的外域定理直接为其内部选出的那个新矩形付款。这正是旧 RP 条件在本次引用中成为冗余的原因。

因此无需为原无界 B 另加整个经验均值对的指数紧性、$q\ge q_*>0$ 的全局假设，或从局部 $K$ 外推一个未证的全局 LDP。原率间隙与 RP 概率条件仍可保留；本报告不据此宣称旧 R2 322–327 的原论证已在任意无界情形自动有效。

## 8. 有界 C 的准确范围

假设原 $X$ 几乎处处有界，$ |X|\le M<\infty$。JA342 需要的是**单个实际鞍点倾斜律 $\mu_{\theta_0}$** 的联合 WC，以及 B 中相同的实际正则鞍点、正曲率、真实全局唯一极小条件。它并不声称仅凭有界性就产生这些鞍点或全局条件。

稳定性的数学传递没有额外前提。设 $Q=\mu_{\theta_0}$，固定任何紧参数集 $H$，如 JA342 使用的 $\overline B(\theta_0,1)$。令

\[
 B=\sup_{p\in H}\|p-\theta_0\|\sqrt{M^2+M^4}<\infty.
\]

则 $Q$-几乎处处有 $ |(p-\theta_0)\cdot W|\le B$，从而

\[
 \frac{d\mu_p}{dQ}
 =\frac{e^{(p-\theta_0)\cdot W}}{E_Qe^{(p-\theta_0)\cdot W}}
 \ge e^{-2B}=:m>0.
\]

对独立两份样本用

\[
 1-|\phi_H(u)|^2=E_{H\otimes H}[1-\cos(u\cdot(W-W'))]
\]

及非负被积函数，得

\[
 1-|\phi_{\mu_p}(u)|^2\ge m^2(1-|\phi_Q(u)|^2).
\]

因为 $0\le|\phi|\le1$，可推出

\[
 1-|\phi_{\mu_p}(u)|\ge\frac{m^2}{2}(1-|\phi_Q(u)|)
 \ge\frac{m^2c}{2}\|u\|^{-\beta}.
\]

故整个固定紧集以相同 $\beta$、固定新 $c'=m^2c/2>0$ 与同一 $R$ 满足 WC；这正是 R2 343–369 与接受的 `exists_compact_tilted_weakCramer_bound`。所有实参数的 MGF 都有限，负倾斜点的内部性更无困难；局部协方差连续性和正定性可给小紧邻域上的谱界，有界性给所有矩的一致界。因此 C 所需“单点到紧邻域”确已闭合。

无界时这个全紧族密度下界一般不存在。不能由 JA342 将原 B 的族 WC 改成无界单点 WC，也不能由单点条件推出它。若一个具体分布只给原律 $\mu$ 的 WC 而未给鞍点倾斜律，**在有界情形**同一稳定性引理还可取基参数 $0$ 传到鞍点；仍须另外给出其实际鞍点与全局条件。

## 9. 最终量词、统计量与剩余范围

调用 IZ341 后，来源 B 得到

\[
 \exists C>0\ \exists N\in\mathbb N,quad N\ge2,quad
 \forall n\ge N:\quad
 \left|\sqrt{2\pi n}\,e^{n\Lambda_0}
 \\mu^{\otimes n}\!\left\{\frac{S_n}{V_n}\ge x\sqrt n\right\}
 -v_{\rm corr}^{-1}\right|\le\frac C{\sqrt n}.
\]

这里 $\mu,x,\theta_0,\Theta_0,\beta,c,R$ 均在 $n$ 之前固定；$C,N$ 也在所有 $n\ge N$ 之前一次选定。没有 $P_n$、没有随胞/随样本数重选的原律，也没有把固定点结论改成 $x=x_n\downarrow0$ 的一致结论。

`Shao.energy z=Σ_i(z_i)^2` 是原未中心化能量，$V_n=\sqrt{\sum X_i^2}$。最终事件严格采用 **弱尾边界 $\ge$**；没有借连续性删掉边界原子。零能量时统计量定为 0，且 $x>0,n\ge2$ 使其不属于正尾。正能量时它等价于

\[
 \overline W_n\in\{(a,q):q>0,\ a\ge x\sqrt q\},
\]

与原约定和 Lean `T` 完全一致。最终概率是原 $\mu^{\otimes n}$ 的概率，`P.real T` 在概率测度下就是普通有限概率。

接受结果比 B 的原假设更强，故 B 的 $EX=0$、$x<1$、一致 $8+\delta$ 阶矩/谱界、旧率间隙与显式远场条件均可保留而仍得结论。无需为“没有一条额外保留全部前提的命名包装”宣称存在实质数学缺口。本裁决针对固定律/固定 $x$ 的存在 $C,N$ 命题；不额外认证 R2 69–72 若被强化解读为跨不同分布、仅由某组粗数值界控制的统一定量模数，也不认证任何 $x$ 窗口、$\beta=2/5$ 端点或最弱充分条件。

剩余实质事项在**具体应用**：必须为目标律证明实际鞍点存在、实际正曲率与真实全局唯一极小，且无界应用仍须实际紧族 WC。原 D 尤须给出八个互异正幅值、两个同时所需的丢番图性质及其诱导的真实单点/族 WC，并证明充分小正 $x$ 的正则全局鞍点。IZ341/JA342 都是条件式定理，不能自己提供这些存在见证。原反例证据与来源归属保持原范围；本报告没有宣称整个 OQ3 完成。

## 10. 封存说明

本次唯一写入是本报告。未运行任何本地或服务器 Lean/AX/编译，未启动子上下文，未写 Git/API、缓存、配置或生产源码。现有独立完整证明、内核及递归公理证据按精确源哈希复用；本次新增的独立工作仅为原来源到这些接受结果的数学蕴含审查。Root 决定是否采纳及更新原题状态。

```json
{
  "reviewKind": "INDEPENDENT_SOURCE_ASSUMPTIONS_TO_ACCEPTED_THEOREM_IMPLICATION",
  "verdict": "CORRECT_FOR_ORIGINAL_FIXED_LAW_FIXED_X_B_AND_BOUNDED_C",
  "newMathematicalHypothesesNeededForBOrC": false,
  "DApplicationClosed": false,
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
```
