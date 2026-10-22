# 固定原律下的联合极限与零质量安全相对传递

结论：PROVED。

冻结目标：`drafts/oq4/frozen-energy-joint-transport-v1.md`，SHA256 `415ae0a03c480d3dcc2d370662a9d4e050d941fe609821d2996c5c69ceb42fb4`，6797 字节。以下证明保持该目标的原律、事件、常数、量词及边界。

## 1. 固定对象、记号和所用有限接口

固定实数 M,T≥0，令

\[
 C=\operatorname{energyE2Constant}(M,T),\qquad
 H=\operatorname{energyE2Threshold}(M,T),\qquad
 P=\operatorname{energyE1Constant}(T).
\]

固定同一个实 Borel 概率测度 ν，假设 x↦x² 与 x↦|x|³ 均关于 ν 真正可积，且

\[
 \int x\,d\nu=0,\qquad \int x^2\,d\nu=1,\qquad
 \beta:=\int |x|^3\,d\nu\le M.
\]

由非负被积函数的积分非负，β≥0。所有序号使用这个 ν。以下引用的有限接口均为已认证声明；它们的原律概率性、二阶及三阶可积性、均值、二阶矩、β≤M、M,T≥0 等前提就是本段固定前提。

`energyE2Constant_dominates` 和 `energyE1Constant_dominates` 给出 C≥1、P≥1。由 `energyE2Threshold` 的定义和 `energyLinearCentering_height_bounds`，对任何 u≥H 均有

\[
 u\ge2,\qquad \operatorname{energyLogThreshold}(M,T)\le u.                 \tag{1}
\]

因此，若另外 |v|≤T，则 `energyE1_common_bounds` 可用于 (ν,M,T,u,v)。它给出实际测度 energyTiltedLaw ν u v 的概率性、x、x²、|x|³ 的可积性、几乎处处 |x|≤2u，以及

\[
 \tfrac12\le \operatorname{energyNormalizer}(\nu,u,v)\le\tfrac32,
 \quad
 \left|\log\operatorname{energyNormalizer}(\nu,u,v)-\frac v{u^2}\right|
       \le\frac{P\beta}{u^3}.                                          \tag{2}
\]

同样，`energyE2_common_bounds` 给出一个 t，使 energyE2Conclusion ν M T u v t 成立。其内容是：实际线性倾斜律 energyLinearTiltLaw ν u v t 为概率律，几乎处处 |x|≤2u；x、x²、|x|³ 均真正可积；energyLinearMean 为零且实际一阶积分也为零；并有

\[
 |t|\le C/u^2,\qquad
 |\log\operatorname{energyLinearNormalizer}(\nu,u,v,t)|\le C/u^4,
\]

\[
 \left|\int x^2\,d\operatorname{energyLinearTiltLaw}(\nu,u,v,t)-1\right|
       \le C/u,
 \qquad
 \int|x|^3\,d\operatorname{energyLinearTiltLaw}(\nu,u,v,t)\le C.          \tag{3}
\]

对任何满足这个 E2 结论的同一个 t，`energyRelativePath_bounds_of_e2` 给出每个 m∈ℕ 的 energyRelativePathConclusion。等价地，可直接用 `energyRelativePath_common_bounds` 一次取得 t、E2 及全部 m 的有限结论。这里的存在选择不依赖 m。

实际定义为

\[
 w_{u,v}(x)=\mathbf1_{\{|x|\le2u\}}\exp(vx^2/u^2),\qquad
 Z(\nu,u,v)=\int w_{u,v}\,d\nu,
\]

其中指标式按原定义解释为区间外取零。实际能量倾斜律为

\[
 \operatorname{energyTiltedLaw}(\nu,u,v)
 =\nu.\operatorname{withDensity}
       \bigl(x\mapsto\operatorname{ENNReal.ofReal}(w_{u,v}(x)/Z(\nu,u,v))\bigr).
]

若 μ=energyTiltedLaw ν u v，则

\[
 L(\nu,u,v,t)=\int e^{tx}\,d\mu,
 \qquad
 \operatorname{energyLinearTiltLaw}(\nu,u,v,t)
 =\mu.\operatorname{withDensity}
       \bigl(x\mapsto\operatorname{ENNReal.ofReal}(e^{tx}/L(\nu,u,v,t))\bigr).
\]

在 u≥H、|v|≤T 时，(1) 使 `energyLinearNormalizer_pos` 的 u≥1 前提成立；原二阶可积性及二阶矩为 1 的前提已固定。因此对每个实 t，实际 L(ν,u,v,t)>0。实际 Z>0 也由 (2) 给出。这是随后使用对数和正底数幂恒等式的依据。

路径空间为 Shao.Path m=Fin m→ℝ，prefixSum a k 是前 k 个坐标之和，energy a=∑ᵢ(aᵢ)²；事件始终是

\[
 \operatorname{closedStrip}_m(u)
 =\{a:\ \forall k\in\mathbb N,\ k\le m\Longrightarrow
                       |\operatorname{prefixSum}(a,k)|\le u\}.          \tag{4}
\]

特别包括 k=0，端点不等式为弱不等式。实际能量被积函数是

\[
 F_{m,u,v}(a)=\operatorname{energyPathIntegrand}(u,v,a)
 =\begin{cases}
 \exp\bigl(v(\operatorname{energy}(a)-m)/u^2\bigr),
                         &a\in\operatorname{closedStrip}_m(u),\\
 0,                       &a\notin\operatorname{closedStrip}_m(u).
 \end{cases}                                                            \tag{5}
\]

有限路径接口始终涉及这些实际测度、Measure.pi、(4) 及 (5)，没有用抽象概率数替换它们。以下新增论证只把这些有限结论接成联合极限，并明确证明相对误差和样本转接。

## 2. 先选择中心参数，再引入任何长度或样本

令 h,s:ℕ→ℝ 满足 hⱼ→+∞ 及每个 j 的 |sⱼ|≤T。先在集合

\[
 D=\{(u,v)\in\mathbb R^2:u\ge H,\ |v|\le T\}
\]

上作一次选择。对 (u,v)∈D，令 G(u,v) 为所有满足

\[
 \operatorname{energyE2Conclusion}(\nu,M,T,u,v,t)
 \ \land\ \forall m\in\mathbb N,
 \operatorname{energyRelativePathConclusion}(\nu,M,T,u,v,t,m)            \tag{6}
\]

的实数 t 所成的集合。第 1 节的共同有限定理证明每个 G(u,v) 非空。选择公理因此给出一个函数 Θ，在 D 上满足 Θ(u,v)∈G(u,v)。这个选择只使用已经固定的 ν,M,T 和输入对 (u,v)；尚未引入长度序列、概率空间或样本。定义

\[
 \theta_j=
 \begin{cases}
 \Theta(h_j,s_j),&h_j\ge H,\\
 0,&h_j<H.
 \end{cases}                                                            \tag{7}
\]

不要求 Θ 或 θ 可测、连续或唯一。

因为 hⱼ→+∞，存在 J_H∈ℕ，使每个 j≥J_H 都满足 hⱼ≥H。这是从趋于正无穷内部取得的尾部，不是对全部 j 新增的条件。对这些 j，(7) 和 (6) 给出

\[
 \operatorname{energyE2Conclusion}(\nu,M,T,h_j,s_j,\theta_j)
 \ \land\ \forall m\in\mathbb N,
 \operatorname{energyRelativePathConclusion}(\nu,M,T,h_j,s_j,\theta_j,m).
                                                                         \tag{8}
\]

J_H 与 θ 均不依赖后续的长度序列或样本。由 (1)，这个尾部上 hⱼ≥2；第 1 节的实际概率性、归一化正性及矩可积性均成立。早期 hⱼ 可以为零、负数或小于 H，(7) 不在那些序号声称 (8) 或概率性。

## 3. 任意允许长度序列的确定性误差极限

现在才固定任意 n:ℕ→ℕ，只假设

\[
 q_j:=\frac{N_j}{h_j^3}\longrightarrow0,
 \qquad N_j:=(n_j:\mathbb R)\ge0.                                     \tag{9}
\]

以下证明对每个满足 (9) 的 n 都成立，始终使用第 2 节已选定的 θ。允许依赖 n 的收敛尾部；参数选择和 (8) 的共同尾部已经在 n 之前确定。

令 uⱼ=1/hⱼ，使用实数除法的原定义给全部序号的表达式赋值。它趋于零：给定 ε>0，由 hⱼ→+∞，最终 hⱼ>max(1,1/ε)，从而 0<uⱼ<ε。此推导只在 hⱼ>0 的尾部使用倒数，不使用早期值的符号。

在 j≥J_H 的尾部，hⱼ≠0，通常的实数除法恒等式给出

\[
 v_j:=\frac{N_j}{h_j^4}=q_j u_j.                                     \tag{10}
\]

由 qⱼ→0、uⱼ→0 及实数乘法保持极限，vⱼ→0。因 C、P、M 是固定有限实数，由透明误差定义及 (9)—(10)，

\[
 e_{2,j}=C u_j+C v_j\longrightarrow0,
 \qquad
 e_j=PMq_j+e_{2,j}\longrightarrow0.                                  \tag{11}
\]

在共同有效尾部，C≥1、P≥1、M≥0、Nⱼ≥0、hⱼ>0，故 e₂,ⱼ≥0、eⱼ≥0。负号保持趋零，指数函数在 0 连续，因此

\[
 e^{e_{2,j}},e^{-e_{2,j}},e^{e_j},e^{-e_j}\longrightarrow1.
\]

于是

\[
 \delta_{2,j}:=e^{e_{2,j}}-1\longrightarrow0,
 \qquad \delta_j:=e^{e_j}-1\longrightarrow0.                           \tag{12}
\]

在相同尾部，指数单调性又给出 δ₂,ⱼ≥0、δⱼ≥0。至此没有假设 nⱼ→∞，也没有使用 nⱼ/hⱼ²→∞。

## 4. 实际有限界及两侧相对误差

对这个 n，按冻结定义记

\[
 \mu_j=\operatorname{energyTiltedLaw}(\nu,h_j,s_j),\quad
 \mu_{\theta,j}=\operatorname{energyLinearTiltLaw}(\nu,h_j,s_j,\theta_j),
\]

\[
 Z_j=\operatorname{energyNormalizer}(\nu,h_j,s_j),\quad
 L_j=\operatorname{energyLinearNormalizer}(\nu,h_j,s_j,\theta_j),
 \quad A_j=\operatorname{closedStrip}_{n_j}(h_j),
\]

\[
 \Pi_j(\lambda)=\operatorname{Measure.pi}(i:\operatorname{Fin}(n_j)\mapsto\lambda),
 \quad p_j=\Pi_j(\mu_j).\operatorname{real}(A_j),\quad
 r_j=\Pi_j(\mu_{\theta,j}).\operatorname{real}(A_j),
\]

\[
 I_j=\int F_{n_j,h_j,s_j}(a)\,d\Pi_j(\nu)(a).                         \tag{13}
\]

对每个 j≥J_H，将 (8) 的全称量词取 m=nⱼ。实际 energyRelativePathConclusion 首先给出

\[
 F_{n_j,h_j,s_j}\text{ 关于 }\Pi_j(\nu)\text{ 真正可积},               \tag{14}
\]

以及

\[
 e^{-e_{2,j}}r_j\le p_j\le e^{e_{2,j}}r_j,\qquad
 e^{-e_j}r_j\le I_j\le e^{e_j}r_j.                                  \tag{15}
\]

所以 (13) 在此处是可积函数的有限积分；没有用总化积分在不可积时的赋值冒充 (14)。E1 和 E2 给出 μⱼ、μθ,ⱼ 的真实概率性，故它们的有限乘积律也是概率律，特别 0≤pⱼ≤1、0≤rⱼ≤1。(5) 非负及 (14) 还给出 Iⱼ≥0。

下面明确证明从两侧指数界到相对误差的通用实数推理。设 a≥0、r≥0，且

\[
 e^{-a}r\le x\le e^a r.
\]

令 t=eᵃ≥1，则 t>0、e⁻ᵃ=1/t、d=t−1≥0。上侧界直接给出

\[
 x-r\le(t-1)r=dr.                                                     \tag{16}
\]

下侧界给出

\[
 r-x\le(1-t^{-1})r=\frac{t-1}{t}r.
\]

因为 t≥1，所以 0<1/t≤1；乘以非负数 t−1 得 (t−1)/t≤t−1，再乘以 r≥0，得到

\[
 r-x\le dr.                                                          \tag{17}
\]

(16) 与 (17) 共同说明 −dr≤x−r≤dr，故 |x−r|≤dr。这里既没有除以 r，也没有要求 x 或 r 严格正。

分别取 (a,x,r)=(e₂,ⱼ,pⱼ,rⱼ) 和 (eⱼ,Iⱼ,rⱼ)，用 (11) 的尾部非负性与 (15)，得到

\[
 |p_j-r_j|\le\delta_{2,j}r_j,\qquad
 |I_j-r_j|\le\delta_jr_j                                             \tag{18}
\]

对每个 j≥J_H 均成立。若其中某个 rⱼ=0，(15) 的下侧为 0≤pⱼ、0≤Iⱼ，上侧为 pⱼ≤0、Iⱼ≤0，因此 pⱼ=Iⱼ=0；(18) 保留零尺度的完整信息。

给定任何 η>0，由 (12)，存在 J₂、J₁，使 j≥J₂ 时 δ₂,ⱼ≤η，j≥J₁ 时 δⱼ≤η。取 j≥max(J_H,J₂,J₁)，以 rⱼ≥0 乘这些不等式并结合 (18)，便有

\[
 |p_j-r_j|\le\eta r_j,\qquad |I_j-r_j|\le\eta r_j.                   \tag{19}
\]

另外由 (11)，可在尾部同时要求 e₂,ⱼ≤η、eⱼ≤η。此时 −η≤−e₂,ⱼ、−η≤−eⱼ，指数单调性和 rⱼ≥0 将 (15) 改写为

\[
 e^{-\eta}r_j\le p_j\le e^{\eta}r_j,\qquad
 e^{-\eta}r_j\le I_j\le e^{\eta}r_j.                                \tag{20}
\]

(18)—(20) 都保留 rⱼ 这一误差尺度，不以绝对差趋零代替相对结论，也不声称无条件的比值极限。

## 5. 同一参数的归一化及终点支付极限

在整个共同有效尾部，第 1 节已从实际 law 接口得到

\[
 L_j>0,\qquad Z_j\ge\tfrac12>0.                                     \tag{21}
\]

因此这里的 log 是实际正归一化常数的实对数。

由 (3) 及 Nⱼ≥0，

\[
 |N_j\log L_j|=N_j|\log L_j|
       \le C\frac{N_j}{h_j^4}=Cv_j\longrightarrow0.
\]

这证明 Nⱼ log Lⱼ→0。也由 (3) 及 hⱼ>0，

\[
 0\le|\theta_j|h_j\le\frac C{h_j^2}h_j=\frac C{h_j}=Cu_j\longrightarrow0.
                                                                         \tag{22}
\]

所以 |θⱼ|hⱼ→0，连同 exp(±|θⱼ|hⱼ)→1。

为明确幂恒等式的正性要求，现对任意 x>0 和 m∈ℕ 证明

\[
 x^m=\exp((m:\mathbb R)\log x).                                     \tag{23}
\]

m=0 时两边均为 1。若 m 时成立，利用 exp(log x)=x 和指数的加法公式，

\[
 \exp((m+1)\log x)=\exp(m\log x)\exp(\log x)=x^m x=x^{m+1}.
\]

归纳完成 (23)；正性 x>0 正是 exp(log x)=x 的依据。把 x=Lⱼ、m=nⱼ 代入 (23)，由 (21) 及 Nⱼ log Lⱼ→0，得到

\[
 L_j^{n_j}=\exp(N_j\log L_j)\longrightarrow1.                         \tag{24}
\]

再由 E1 的 (2)，令

\[
 b_j=N_j(\log Z_j-s_j/h_j^2).
\]

在有效尾部，有

\[
 |b_j|=N_j|\log Z_j-s_j/h_j^2|
 \le P\beta\frac{N_j}{h_j^3}
 =P\beta q_j\le PMq_j\longrightarrow0.                              \tag{25}
\]

最后一个不等式使用 P≥0、qⱼ≥0、β≤M；趋零只使用 (9)。故

\[
 N_j(\log Z_j-s_j/h_j^2)\longrightarrow0.                             \tag{26}
\]

借助 Zⱼ>0，将 (23) 用于 x=Zⱼ。指数加法公式和实数运算给出逐 j 的真实等式

\[
 \begin{aligned}
 B_j&:=\exp(-s_jN_j/h_j^2)Z_j^{n_j}\\
    &=\exp(-s_jN_j/h_j^2)\exp(N_j\log Z_j)\\
    &=\exp\bigl(N_j(\log Z_j-s_j/h_j^2)\bigr)=\exp(b_j).
 \end{aligned}                                                       \tag{27}
\]

由 (26) 及 exp 在 0 连续，Bⱼ→1。更精确地，(25) 在有限 j 给出

\[
 \exp(-P\beta q_j)\le B_j\le\exp(P\beta q_j),\qquad
 \exp(-PMq_j)\le B_j\le\exp(PMq_j).                                 \tag{28}
\]

因此能量归一化误差始终由 E1 的 PβNⱼ/hⱼ³ 支付，随后才以 β≤M 放大界；没有在有限 j 将 Bⱼ设成 1。

这些归一化量的实际路径含义也保持精确。`energyPathLaw_integral` 的所有前提由 hⱼ≥2、|sⱼ|≤T 及原二阶矩前提满足，故给出

\[
 I_j=B_jp_j.                                                         \tag{29}
\]

`energyLinearPathLaw_integral` 在同一尾部、同一个 θⱼ 给出

\[
 p_j=L_j^{n_j}\int
       \mathbf1_{A_j}(a)\exp(-\theta_j\operatorname{prefixSum}(a,n_j))
       \,d\Pi_j(\mu_{\theta,j})(a),                                \tag{30}
\]

且 (30) 的实际被积函数真正可积。对每条 a∈Aⱼ，由 (4) 的 k=nⱼ 项，

\[
 |\theta_j\operatorname{prefixSum}(a,n_j)|
       \le|\theta_j|h_j.
\]

所以终点因子在事件上的每一点都位于 exp(−|θⱼ|hⱼ) 与 exp(|θⱼ|hⱼ) 之间。(22) 使这两个端点趋于 1；(24) 同时处理正归一化幂。这里没有移动 closedStrip 的边界，也没有用累积均值漂移替代原事件。

## 6. 三个不同概率空间上的真实 iid 转接

本节的 θ 仍严格是 (7) 已经选定的序列。先给出逐 j 的转接，再对任意样本族应用。固定一个 j≥J_H，写 m=nⱼ。在三个任意概率空间

\[
 (\Omega_{\nu,j},\mathcal F_{\nu,j},\mathbb P_{\nu,j}),\quad
 (\Omega_{\mu,j},\mathcal F_{\mu,j},\mathbb P_{\mu,j}),\quad
 (\Omega_{\theta,j},\mathcal F_{\theta,j},\mathbb P_{\theta,j})
\]

上，分别给定有限族 Xᵢ、Yᵢ、Wᵢ，i∈Fin m。要求每个坐标可测；每族关于各自概率测度满足 iIndepFun；并且逐坐标分别满足

\[
 \operatorname{IdentDistrib}(X_i,\operatorname{id};\mathbb P_{\nu,j},\nu),
\]

\[
 \operatorname{IdentDistrib}(Y_i,\operatorname{id};\mathbb P_{\mu,j},\mu_j),
 \qquad
 \operatorname{IdentDistrib}(W_i,\operatorname{id};\mathbb P_{\theta,j},\mu_{\theta,j}).
                                                                         \tag{31}
\]

这些边缘是实际 ν、μⱼ、μθ,ⱼ；有效尾部上的概率性已经由 E1、E2 供应。不同概率空间之间没有任何独立或耦合前提。

令 S_X(ω)=samplePath X ω，即坐标 i 为 Xᵢ(ω) 的真实样本路径；S_Y、S_W 同样定义。既有有限 iid 定理 `Shao.Probability.iid_samplePath_map_eq_pi`，在坐标可测、iIndepFun 及 (31) 这三组已写前提下，逐一给出精确推前等式

\[
 (S_X)_*\mathbb P_{\nu,j}=\Pi_j(\nu),\quad
 (S_Y)_*\mathbb P_{\mu,j}=\Pi_j(\mu_j),\quad
 (S_W)_*\mathbb P_{\theta,j}=\Pi_j(\mu_{\theta,j}).                    \tag{32}
\]

Aⱼ 是有限个连续前缀和的弱闭条件之交，所以是 Borel 集；样本路径映射由坐标可测而可测。因此对后两个等式在 Aⱼ 上取值，依推前测度定义并取 real，得到

\[
 \widehat p_j:=\mathbb P_{\mu,j}.\operatorname{real}\{\omega:S_Y(\omega)\in A_j\}
       =p_j,
\]

\[
 \widehat r_j:=\mathbb P_{\theta,j}.\operatorname{real}\{\omega:S_W(\omega)\in A_j\}
       =r_j.                                                        \tag{33}
\]

这也正是既有 `energyLinearPathLaw_base_probability_iid` 和 `energyLinearPathLaw_probability_iid` 的精确结论；它们所需的 hⱼ≥1、|sⱼ|≤T、T≥0、原二阶可积性及原二阶矩为 1 在这里均已满足。

对于原律上的能量积分，`energyRelativePath_integral_iid` 可用于这个同一 θⱼ：其 E2 前提由 (8) 给出，其余固定矩条件、共同高度和 s 界已逐项满足，而样本前提就是 X 的可测性、独立性及 (31)。它明确给出

\[
 F_{m,h_j,s_j}\circ S_X\text{ 关于 }\mathbb P_{\nu,j}\text{ 真正可积},
\]

\[
 \widehat I_j:=\int F_{m,h_j,s_j}(S_X(\omega))\,d\mathbb P_{\nu,j}(\omega)
       =\int F_{m,h_j,s_j}(a)\,d\Pi_j(\nu)(a)=I_j.                  \tag{34}
\]

因此 (34) 包含真实可积性，而不只是两个总化积分值的等式。从 (32) 看，它是可测样本路径下对实际可积函数 (14) 的积分换元；既有有限积分转接接口已经同时保证所需的可积性与精确等式。

现在将 (33)—(34) 精确代入 (15) 及 (18)，得到同一 j、同一 θⱼ 的全部样本界

\[
 e^{-e_{2,j}}\widehat r_j\le\widehat p_j\le e^{e_{2,j}}\widehat r_j,
 \qquad
 e^{-e_j}\widehat r_j\le\widehat I_j\le e^{e_j}\widehat r_j,
\]

\[
 |\widehat p_j-\widehat r_j|\le\delta_{2,j}\widehat r_j,
 \qquad
 |\widehat I_j-\widehat r_j|\le\delta_j\widehat r_j.                  \tag{35}
\]

这不是不同空间随机变量的逐点相等；(33)—(34) 是事件概率及积分这三个确定实数的精确相等，足以进行代入。若样本实现随 j 改变，甚至各个 j 使用不同可测空间，只要每个有效 j 各自满足上述有限前提，就可逐 j 使用同一论证。无需跨 j 的独立性、联合可测性、共同概率空间或跨空间耦合。选择样本、样本所在空间及长度时都不得重选 θ。

对任何这样的样本族，(19) 中的尾部仅由确定性误差和 J_H 决定，因而同样给出：每个 η>0，最终

\[
 |\widehat p_j-\widehat r_j|\le\eta\widehat r_j,
 \qquad
 |\widehat I_j-\widehat r_j|\le\eta\widehat r_j.
\]

(20) 的 exp(±η) 夹逼也由相同代入得到。若给定所有序号的样本族，限制到有效尾部即可；若仅在有效尾部给定样本，其早期实值表达式可任意延拓而不影响这些最终结论。没有为早期可能不为概率的倾斜测度要求额外概率声明。

## 7. 量词、退化情形与范围核对

上述顺序是：固定 M,T,ν 及其矩条件；给定 h→+∞ 和逐项 s 界；只依赖 ν,M,T,hⱼ,sⱼ 选择 (7) 的 θ；取得不依赖长度的 (8)；然后对每个满足 (9) 的 n 证明 (11)—(30)，并对每个满足有限 iid 前提的样本实现证明 (33)—(35)。所以这是先存在同一 θ，后全称量化所有长度序列和样本实现的总入口。θ 的选择不观察任何 nⱼ、任何后续 n 或任何样本。

若 nⱼ=0，则有效尾部上的 Fin 0 路径空间只有空路径，所有前缀和及 energy 均为 0，(4) 因 hⱼ≥2 对空路径成立；相应概率为 pⱼ=rⱼ=1，(5) 的值为 exp(0)=1，故 Iⱼ=1。Lⱼ⁰=Zⱼ⁰=1，Nⱼ log Lⱼ 和 (25) 的左端均为 0。指数误差界仍成立。此论证适用于每个取零的序号，尤其覆盖恒零长度序列；有界或任意变化的长度也只受 (9) 约束。

若 rⱼ=0，第 4 节已直接证明 pⱼ=Iⱼ=0；样本版本由精确等式给出同一结论。对弱闭端点上的原子、格点分布或全零样本路径，没有任何删去边界或要求密度的步骤。原律不被要求有界支持、指数矩、四阶矩、对称性或非格点性。

早期 hⱼ=0、hⱼ<0 或 hⱼ<H 不影响证明：所有物理归一化、概率性、对数幂恒等式和有限积分可积性只在内部导出的 j≥J_H 尾部使用；收敛表达式的有限前段取原实值定义而已。M<1 时也没有新添 M≥1，若该固定矩分布类为空，则对应全称命题自然为空。T=0 或 sⱼ=0 也完全保留；特别 sⱼ=0 时 μⱼ仍是实际截断再归一化律，(29) 中仍保留 Zⱼⁿ 的真实因子。

一般 sⱼ 下，Iⱼ 始终是 (5) 在原 ν 有限乘积律下的能量加权积分，不被解释为原 ν 的无权生存概率。证明仅完成冻结的标量联合极限及零质量安全相对传递；式 (9)—(10) 的共享算子、K/Kv、killed 边界问题、条件能量 E4 及完整 E3/OQ4 根的状态仍为 OPEN。
