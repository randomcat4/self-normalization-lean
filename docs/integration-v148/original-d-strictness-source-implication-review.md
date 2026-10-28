# 原始 OQ3 D：同一分布严格性见证的独立来源蕴含审查

日期：2026-10-28。审查者：Root5 委派的新上下文 /root/original_d_strictness_source_review。方法：math-theorem 的精确命题与来源蕴含审查；不使用 math-ultra。

**STATUS: CORRECT_FOR_D_SPECTRAL_STRICTNESS_WITNESS。PR528 的 JT360 已经无条件证明：存在同一个实际、中心、有界、十六个互异原子的实概率律，其真实联合向量 (X,X²) 真正非格点、满足指数 3/8 的二维径向弱 Cramér 条件，却不满足原文的 strong nonlattice 条件。原 D 的这个严格性子命题可以接受。**

**紧倾斜族的一致弱 Cramér、统一协方差正定和标准化矩界，在数学上也由这个见证及既有接受接口直接推出，不需要增加见证假设。PR528 尚未导出这一组命名消费者，不能因此把它说成新的实质数学障碍。仍然 OPEN 的是该实际见证在充分小固定正 x 下的正则、真实全局唯一鞍点及据此得到的尾渐近应用；本报告没有将整项原 D 或 OQ3 判为完成。**

## 1. 精确来源、源码与证据范围

本报告以实际读取的两个只读原来源为准：

| 来源 | SHA256 | 本次承重范围 |
|---|---|---|
| C:/game/shao/current/oq3/proofs/r2/report.md（R2） | 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55 | 1–79 的应用条件、343–373 的倾斜传递、375–491 的严格性构造 |
| C:/game/shao/current/oq3/proofs/r2/repair01.md（RP） | 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd | 全文；尤其统一标准化输入及 212–226 的远场条件 |

为核对术语，另读历史 PROPOSED 根接口 drafts/oq3/root-contract.md，SHA256 a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a。其 38–42 行明确规定真正联合非格点、strong 的无穷远 limsup，以及定量弱 Cramér 三个不同概念；74–78 行明确把小正 x 的鞍点列为另需证明。该文件不是已接受 Lean 根定理，本报告不继承它的旧 OPEN 库存标签。定向读取 R1 的 259–305 行只用于确认近共振术语，整文件 SHA256 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。

本次审查的不可变数学包为：

- [PR528](https://github.com/randomcat4/shao-lean/pull/528)，head 8304c57a497815d89469780f1c62816959579023，tree 7168db214b78c8fe21cab3843cc2e8c25031a19d，parent 43dbb8d0612a5c4b96e29307c4f1f275aca29c47。
- 本地精确 packet：C:/game/shao lean/drafts/oq3/publication-u22-diophantine-witness/。
- publication-record SHA256：590871b8a33f16973b7a0c78a9ddeb314302c09714af5e05b353d8b639216aec。
- publication-plan SHA256：970dc57a01baa66816be0f6c3f563a812691ad220a2737b37d2d433965bc57b0。
- manifest SHA256：4e3b0166fe64990821ae45dd3db05510439a948d67b22706d74cf5c02ba9422e；source-map SHA256：64a3b7c4f90a67cd43366810b19abbae560a77fc4dab988079d4d0e6b4e06271。

实际读完以下十一份当前源码及全部实际 TYPE 文本，用于核对对象、量词和相互消费的接口。既有完整独立证明审查按精确源版本复用，没有重新进行十一份完整证明审查。

| 单元 / packet 中 Shao/OQ3/ 下源码 | 源 SHA256 |
|---|---|
| JI350 RealParameterDiophantine.lean | fce949bf9398a98a8ea7874f3b1f539a3df3796d805ea60b918b70c4c2627b42 |
| JK351 TorusSimultaneousBadSet.lean | 7fe7cc676819bea1edcd9d9e9bb89df328a02f9d01ffd55bbf2adbfcc5d02a2e |
| JL352 TorusMetricDiophantine.lean | fc6e0c3de1346e2fbc2e75faf1fb941e1e098624b93f9ffa98518d39583cc5cc |
| JM353 RealRatioDiophantineAE.lean | 1bc904cce5ebf9e3e7234345fb8fef0dd3168176aa087cabb9c0fff675a255e9 |
| JN354 CoordinateSquareAffineAE.lean | c6a6160fe98134f72dfb52861eeb6138ced09f3116fe6f7992262afd42ebb846 |
| JO355 PositiveBoxSimultaneousDiophantine.lean | f3d6f7c872ba5527d164623d83c6d5898503937fb81a72225b9e953d39ed5921 |
| JP356 SymmetricEightAtomWeakCramerExistence.lean | e6f1cc980bfd0054c8c13f33f8b406e6ba202824caa9601295c13de4d71dd5b7 |
| JQ357 TorusLargeReturns.lean | 2c1b17332a35b3d9aa640c8c7a0ba91d3cd86a4c2442bd3deb4d832c89c6c543 |
| JR358 FiniteAtomicJointNearResonance.lean | 69eb1ea396326eed23002489e67f65cd5284dfdc3caee801bbcadd7e0036c697 |
| JS359 SymmetricEightAtomWeakCramerNonlattice.lean | 262ad75d50eece184c6ab850fad629c4861ed30c7c81e8f1e65b240b8dd3fbf6 |
| JT360 SymmetricEightAtomWeakNotStrong.lean | eb824b983dc57a5101799e85dec6e5d6b180b74e6b0157c241e4e52c1b46b80b |

在 packet 的 docs/oq3-u22-diophantine-witness/ 下，实际核对了 source、actual-types、qualification、receipt、final-source-binding 和七份独立报告的 62 项字节数/SHA256 绑定，均与 publication-plan 相同；十一份 qualification 均为 COMPLETE_QUALIFIED。每份 receipt 的成功源 SHA、首次原对象 SHA 与 qualification/manifest 相同，保存的 audit-record 自然退出码均为 0、且绑定同一原对象；全部递归公理只含 propext、Classical.choice、Quot.sound。这里复用已有服务器证据，没有本次服务器观察或重执行。

终端见证及关键选择接口的精确证据如下；其余单元的完整绑定由上述精确 manifest 保留：

| 单元 | actual-types SHA256 | qualification SHA256 | receipt SHA256 |
|---|---|---|---|
| JO355 | 528ea601968c8e61bd06a96180abf297f48d197f46ca178a6d283fb9c125fa03 | bf8d0bc0e2782e8036f206e3592e553570a7c0624e743c335a166249068d1d15 | 7ed1dde1e88fa723d86027b87d7b34dfc30fc754f17e4a66240aae222b8a86bf |
| JP356 | ff032f16aa271ca7002848be0ec2398cb0bc7819b6120511b341f7e5219f9a9f | 3de967d9645b63ea83ed887145963bab416ce3bf647d7d67a3c297d4cbe2b2f2 | be6eb439ce547088c7bd2e3050678bc8c01e4fddfc8e6d538bbb10d1de3d6fdb |
| JS359 | 18da80ebeeb95799a8330e81bae0ac9cd7dbc8c51cb108e8a8abe526704e5591 | 4cadb20b39b62e164e03df871ee6369155c4c6b1a1207ea7a7f74ff52c85f333 | c56cbffd4046e36f5907a6531587f9dff8c2bfc59b792cfd1447f9a987783c82 |
| JT360 | d907e7485715ae80feca5ed4135f970d4efd95e830cfae767b7338e8c07641d1 | cf194d51b90dbed1b723aa904c24292666061a6c4650f7b47c6fd47ef7765c59 | 06557e2d111e2ec855f6fd8e2f648f3bdb5b2af7d919250940d045784ce3e6dd |

复用的完整独立报告及精确 SHA：

| 报告 | 覆盖 | SHA256 |
|---|---|---|
| u22ji-proof-review.md | JI350 | 313d5072c1c8bd808c8aff84b00a50e568815df0b3a26f0b751c6ef80145d5e3 |
| u22jk-proof-review.md | JK351 | 50f01ec21cb1083b9c97cc6301ef6e16258bfae083165e200755275ada61978b |
| u22jl-proof-review.md | JL352 | fd945bf8dafe192c33c937b6fd4197e2599e1177b57b734bb7b0c3a79c750d92 |
| u22jm-proof-review.md | JM353/JN354 | 8693839e571f8bde5d0e6bb54252dbfe58563b9ec4f1df3dd80c3c362abe3d36 |
| u22jo-proof-review.md | JO355/JP356 | 2bf996fcfcbd25d0db8692b26f46d7b7a953e72bd62eeddcda025760f18c0e50 |
| u22jq-proof-review.md | JQ357/JR358 | dbb8e3bfd4484895f100864ddb2d5fc9bf2e92586f1f11b1efde0e945c2cb920 |
| u22js-proof-review.md | JS359/JT360 | 39328e9d7286ceddbcd94cfd5e3d756f490e13535b66b28c8c63562579f66e1f |

这七份报告已经合格覆盖全部 41 个 standalone 实际 TYPE、所需 VALUE（0）及七个声明 let；本次不把它们的 standalone 数量当作 Root 全工程净新增名数量。对本次语义问题，读了最终两份组装报告中相应结论、量词、来源映射和完整终端 TYPE，复用其完整证明结论。

## 2. 本次冻结的原 D 子命题

要判定的严格性子命题是：

\[
\begin{gathered}
\exists\,0<a_0<\cdots<a_7,\qquad
\mu=\frac1{16}\sum_{j=0}^{7}(\delta_{a_j}+\delta_{-a_j}),\\
E_\mu X=0,\quad X\text{ 有界},\quad
\psi_\mu(\xi,\eta)=E_\mu e^{i(\xi X+\eta X^2)},\\
\forall(\xi,\eta)\ne(0,0),\quad|\psi_\mu(\xi,\eta)|<1,\\
\exists c>0,\ R\ge0\ \forall(\xi,\eta),\quad
r=\sqrt{\xi^2+\eta^2}>R
\Longrightarrow|\psi_\mu(\xi,\eta)|\le1-cr^{-3/8},\\
\limsup_{\|u\|\to\infty}|\psi_\mu(u)|=1.
\end{gathered}
\]

同一 \(\mu\)、同一八幅值必须同时见证所有这些结论，且 \(\mu,c,R\) 在全部频率及全部样本量之前选定。原文使用从 1 开始的八个下标；这里沿 Lean 从 0 开始，只有下标平移。统一质量 1/16 是原文允许的正、对称质量的一种选择。这个目标没有把充分小正 x 的鞍点假设藏在“正则”一词中。

## 3. 两类丢番图性质确由同一八幅值实现

取 \(\gamma=3/16\)。JO355 给出一个共同的 \(r=(r_0,\ldots,r_6)\)，满足
\[
2(j+1)<r_j<2(j+1)+1
\]
及以下两条性质：
\[
\begin{aligned}
&\exists Q_L\ge0\ \forall q\in\mathbb Z,\ |q|>Q_L\quad
\exists j\in\{0,\ldots,6\}\ \forall p\in\mathbb Z,\quad
|q|^{-\gamma}\le|qr_j-p|,\\
&\exists Q_Q\ge0\ \forall q\in\mathbb Z,\ |q|>Q_Q\quad
\exists j\in\{0,\ldots,5\}\ \forall p\in\mathbb Z,\quad
|q|^{-\gamma}\le
\left|q\frac{r_{j+1}^2-1}{r_0^2-1}-p\right|.
\end{aligned}
\]

这是真实的共同见证存在，不是对两个独立 a.e. 结论各自选点再拼接。JK/JL 的实际环面坏集测度与第一 Borel–Cantelli 给出维数 \(m\ge6\) 的整数性质；因为 \(7\gamma=21/16>1\) 及 \(6\gamma=18/16>1\)，分别适用于两组归一化维数 7 和 6。JM 将它转为实向量的 Lebesgue a.e. 性质；JN 处理正正交象限上平方仿射映射的零集原像。JO 的前向 Fubini 先固定 \(r_0\in(2,3)\)，故 \(r_0^2-1>0\)，再在正测度尾部盒内同时选取其余六坐标。

JP356 设置
\[
a=(1,r_0,\ldots,r_6).
\]
盒的间隔给出全正与严格有序。将 JI350 分别应用于
\[
\alpha_L=(2a_0,\ldots,2a_7),\qquad
\alpha_Q=(2(a_1^2-a_0^2),\ldots,2(a_7^2-a_0^2)),
\]
得到固定 \(c_L,c_Q>0,\ T_L,T_Q\ge0\)，使
\[
\begin{aligned}
|t|>T_L&\Longrightarrow
\exists i\in\{0,\ldots,7\}\ \forall k\in\mathbb Z,\quad
c_L|t|^{-\gamma}\le|2ta_i-2\pi k|,\\
|t|>T_Q&\Longrightarrow
\exists j\in\{1,\ldots,7\}\ \forall k\in\mathbb Z,\quad
c_Q|t|^{-\gamma}\le|2t(a_j^2-a_0^2)-2\pi k|.
\end{aligned}
\]

全实 \(t\) 的正负号及绝对值阈值均保留；选择坐标发生在所有格点整数 \(k\) 之前。常数、阈值不依赖于 \(t\)。因参数中已有因子 2，换 \(t\mapsto t/2\) 即给原文 (23) 对八幅值及七平方差本身的版本，只改变常数、阈值。

因此 JH349 的两条算术前提确已被同一 \(a\) 消除。JH349 本身只是条件式解析生产者，不能独自当作存在定理；这项存在性由 JO355→JI350→JP356 实际承担。固定 \(a_0=1\) 是合法的存在构造，不声称此超平面在八维空间满测，也不声称导出了原文关于全部八维开集的完整泛型性定理；原 D 所需存在量词不要求那个更强结论。原文也没有要求八个可逐一数值列出的常数。

## 4. 实际十六点律、均值、矩与径向弱界

JT360 的声明有两个实质 let：
\[
A=\operatorname{append}(a,-a),\qquad
\mu=\sum_{k\in\mathrm{Fin}\,16}\operatorname{ofReal}(1/16)\,\delta_{A_k}.
\]
其后所有合取都使用这个 \(\mu\)。这不是抽象 supplied characteristic，更不是任意二维离散向量。接受的实际定义是
\[
\operatorname{jointPhase}(\xi,\eta,x)=e^{i(\xi x+\eta x^2)},\qquad
\operatorname{jointCharacteristic}(\mu,\xi,\eta)=\int\operatorname{jointPhase}\,d\mu.
\]
所读 JointNonlattice.lean 的 SHA256 为 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559。

严格单调排除同号碰撞，严格正性排除异号碰撞，JT 的 Function.Injective A 覆盖四种符号组合。因此实际每个点质量恰为 1/16，真实支撑有十六点；由 X 坐标单射，抛物线上的联合支撑也有十六点。JP/JT 已显式输出概率归一化、恒等函数可积、实际积分为零以及非负有限 AE 绝对界；均值零不是不可积函数的总化积分造成的假等式。

额外的基本概率条件没有待付义务：
\[
\mu(X>0)=\mu(X<0)=\tfrac12,\qquad
\sigma^2=E_\mu X^2=\tfrac18\sum_{j=0}^7a_j^2>0.
\]
因 \(a_0=1\) 且 \(a\) 严格增加，\(|X|\ge1\) a.s.，也有有限 \(M=\max_j a_j\)。所有实正阶矩均有限。对每个 \(n\ge1\)，同一产品律下 \(\sum X_i^2\ge n\) a.s.，故本见证无零能量事件；这并未改变通用 OQ3 的零分母约定。

解析生产者将两类相位差平方付入同一实际特征函数缺口；当联合半径大时至少一个坐标大，故 JP356 给出完整二维径向界，包含两个坐标轴和任意斜方向：
\[
\exists c>0,\ R\ge0,\quad
\forall(\xi,\eta),\ r>R\Longrightarrow
|\psi_\mu(\xi,\eta)|\le1-cr^{-3/8}.
\]
指数 \(\beta=2\gamma=3/8\) 严格小于 \(2/5\)，差为 \(1/40\)。R2 (28) 的 \(1+r\) 形式更弱：对 \(r>0\)，\(r^{-3/8}\ge(1+r)^{-3/8}\)。这里没有端点 \(\beta=2/5\) 或随分布统一常数的声称。

## 5. 真正联合非格点不是把高频门槛误套到低频

弱界本身仅直接控制 \(r>R\)。JS359 使用了额外、正确且已经形式化的传播论证来覆盖所有非零频率。

若某个 \(u_0=(\xi_0,\eta_0)\ne0\) 满足 \(|\psi_\mu(u_0)|=1\)，十六个严格正质量及相位缺口恒等式迫使所有支持点的单位相位相同。于是对每个自然数 \(N\)，相位分别变为同一个单位复数的 \(N\) 次幂，从而
\[
|\psi_\mu(Nu_0)|=1.
\]
选 \(N\) 使 \(N\|u_0\|>R\)，弱界却给出
\[
1\le1-c(N\|u_0\|)^{-3/8}<1,
\]
矛盾。因此 \(\forall u\ne0,\ |\psi_\mu(u)|<1\)。这是实际同一概率律上的独立完整结论；既没有只证明“没有某一条轴上的共振”，也没有将高频界不经论证地当成低频界。这里的“真正联合非格点”使用原合同的特征函数定义，不混同于“非原子”或仅一维非格点。

## 6. strong Cramér 的定义与极限量词完全相符

原文 strong nonlattice 定义为
\[
\limsup_{\|u\|\to\infty}|\psi_\mu(u)|<1.
\]
因概率特征函数模恒在 \([0,1]\)，这与下式等价：
\[
\exists\delta>0,\ R\ge0\ \forall u,\quad
\|u\|>R\Longrightarrow|\psi_\mu(u)|\le1-\delta. \tag{SC}
\]
一个方向直接取尾部上界；另一个方向在 limsup 与 1 之间选严格中间值，按无穷远 limsup 的尾上确界定义获得统一 \(R\)。使用欧氏范数还是 \(|\xi|+|\eta|\) 不改变这个无穷远性质。SC 不断言特征函数趋零；仅证明“不趋零”也不足以否定 SC。

JR358/JT360 实际给的是更强的全阈值、全容差形式：
\[
\forall R\in\mathbb R\ \forall\varepsilon>0\quad
\exists\xi>R,\quad
|\psi_\mu(\xi,0)-1|<\varepsilon,\quad
1-\varepsilon<|\psi_\mu(\xi,0)|.
\]
递归在第 \(k\) 步取阈值大于 \(k\) 及前一频率加 1，容差 \(1/(k+1)\)，即得 \(\xi_k\uparrow\infty\)、复数 \(\psi_\mu(\xi_k,0)\to1\) 和模趋一。因此原 strong 定义的 limsup 恰为 1。

JT 还直接否定了完整 SC 存在量词：若有 \(\delta,R\)，对近共振使用 \(R+1,\delta/2\)，即在严格半径门槛外同时得到模大于 \(1-\delta/2\) 且不大于 \(1-\delta\)，矛盾。允许任意实阈值、任意正容差，不只是某个预先选定的序列或有限频率试验。

严格性还包含正确的蕴含方向。若某律满足 SC，则对任意固定 \(\beta>0\)，在半径大于 \(\max(R,1)\) 时 \(r^{-\beta}\le1\)，故
\[
|\psi(u)|\le1-\delta\le1-\delta r^{-\beta}.
\]
所以强条件蕴含指数 3/8 的弱条件，而本同一抛物线律满足弱条件且不满足强条件，包含关系确实是严格的。历史 R1 的 “weakly nonlattice” 指真正非格点且存在无穷近共振；它与定量弱 Cramér 不是同义词。本见证同时具备两者所需的具体性质。

## 7. 紧倾斜、协方差及标准化没有额外未付假设

这一节是本次新增的原题语义蕴含核对，不是对 PR528 添加已通过的 Lean 声明。所读既有接受接口为：

| library/Shao/OQ3/ 下接口 | SHA256 |
|---|---|
| CompactTiltWeakCramer.lean，exists_compact_tilted_weakCramer_bound | 87d4560d0a896d7094e17153b2286408b509b605719977ee443cd688ba8b5544 |
| CompactTiltCovarianceSpectrum.lean，parabolaCovariance_pos_of_weakCramer / exists_compact_tilted_covariance_spectral_bounds | 99b8b9b20f1860ddd7890d8b4d317825ce76572e1c0d209d6843340a33b0c634 |
| CompactTiltWhitenedFamily.lean，exists_compact_tilted_whitened_family | 3d83984f21c03755a7bf018755646a6464157b6eff72bc1555c33aafefcbc642 |

将 JP/JT 的概率实例、AE 有界 \(M\ge0\)、\(\beta=3/8\)、\(c>0,R\ge0\) 传给这些接口，取参考参数 \(u_0=v_0=0\)，零倾斜等于原概率律，全部前提均已满足。没有需要另假设的基准协方差正定或未知标准化常数。

也可直接核验这个代入的数学内容。对任意固定紧集 \(\Theta\subset\mathbb R^2\)，
\[
Z(\theta)=\tfrac1{16}\sum_{k=0}^{15}e^{\theta_1A_k+\theta_2A_k^2}>0,\qquad
K(\theta)=\log Z(\theta)
\]
在整个平面有限且光滑。真实倾斜权重
\[
p_k(\theta)=\frac{e^{\theta_1A_k+\theta_2A_k^2}}
{\sum_{\ell=0}^{15}e^{\theta_1A_\ell+\theta_2A_\ell^2}}
\]
连续且严格为正，其在 \(\Theta\) 上的共同正下界给出固定 \(0<m\le1\) 及 \(\mu_\theta\ge m\mu\)。原 R2 (20)–(22) 或既有接口于是给出
\[
1-|\psi_{\mu_\theta}(u)|^2
\ge m^2(1-|\psi_\mu(u)|^2),\qquad
|\psi_{\mu_\theta}(u)|\le1-\frac{m^2c}{2}\|u\|^{-3/8}
\]
对所有 \(\theta\in\Theta\) 及同一个高频门槛一致成立。常数在全部 \(\theta,u,n\) 之前固定，可依赖这个 \(\mu,\Theta\)。这正是 R2 474–475 的紧倾斜一致性。

协方差也不是另加的结论性前提。对任意倾斜参数，若
\(\operatorname{Var}_{\mu_\theta}(b_1X+b_2X^2)=0\)，则该多项式在全部十六个正质量支持点为同一常数；二次多项式在至少三个互异实点取这个常值，迫使 \(b_1=b_2=0\)。故真实 \(\Delta(\theta)=\nabla^2K(\theta)=\operatorname{Cov}_{\mu_\theta}(X,X^2)\) 正定。紧性与连续性给统一
\[
0<\lambda_-I\preceq\Delta(\theta)\preceq\lambda_+I,\qquad
0<\lambda_-<\lambda_+<\infty.
\]
在对称原律还可直接看见
\[
\Delta(0)=\operatorname{diag}\left(
\tfrac18\sum_j a_j^2,\quad
\tfrac18\sum_j a_j^4-\bigl(\tfrac18\sum_j a_j^2\bigr)^2\right)>0,
\]
第二项严格为正，因为八个平方互异。既有 covariance 接口甚至直接从有界 WC 推出正定，因此上述有限支持论证不是一个尚需补给该接口的假设。

令 \(Y_\theta=\Delta(\theta)^{-1/2}(W-E_\theta W)\)。有
\[
\|Y_\theta\|\le
\frac{2(M+M^2)}{\sqrt{\lambda_-}}
\]
对全族 a.s. 一致，故任意固定 \(8+\delta\) 阶矩一致有界；例如取 \(\delta=1\)，既有 whitened-family 的所有整数矩结论已经足够。其均值为零、协方差为单位阵。令 \(L=\lambda_+^{-1/2}\)、\(U=\lambda_-^{-1/2}\)，标准化频率 \(v=\Delta(\theta)^{-1/2}u\) 满足
\[
L\|u\|\le\|v\|\le U\|u\|.
\]
平移仅添模一因子，故标准化族保留指数 3/8，可用门槛 \(R/L\) 和常数 \((m^2c/2)U^{-3/8}\)。这说明没有隐藏的逆矩阵存在性、方差正性、八阶矩或统一频率门槛义务。

每个倾斜律仍是同一十六点上的正质量有限律，JR358 又适用于任意非负、和为 1 的有限权重，因此每个倾斜律也有任意大线性近共振并不满足 strong 条件。对非空紧族，任何一点的失败也排除该族的统一固定正强缺口。真正非格性同样由共同正支持相位条件保持。

\(a_0=1\) 不是 \(EX^2=1\)。原 D/R2 仅要求中心且方差非退化，不要求方差恰为 1；现有 \(\sigma^2>0\) 已足够。如另需一维单位方差，可置 \(X'=X/\sigma\)。此时
\[
\psi_{X'}(\xi,\eta)=\psi_X(\xi/\sigma,\eta/\sigma^2)
\]
是可逆对角频率变换，保留弱指数、真正联合非格性和 strong 失败；均值、有限矩、有界性也保持。自归一化比值正尺度不变。这个可选推前律必须明说是缩放后的律，不能把原来的 \(\mu\) 默认为方差 1；严格性结论本身不需要进行这次缩放。

所以 packet README 和组装 review 所列“尚未导出紧倾斜统一消费者”是其声明覆盖边界；从原题蕴含角度看，这里已经能合法实例化既有接口。若需要一个 Lean 名字把 JT 与三个旧接口的输出并列打包，只是新包装声明，不是新的数学前提或需要重证旧模块的理由。

## 8. 尚未闭合的正参数全局鞍点及应用

R2 489–491 的最后一句比上述谱性质强：它要使本见证落入固定点尾展开的实际正则有界应用类。PR528 的任何声明都不量化正 \(x\)、实际 \(\theta_0\)、边界矩点或全域 Legendre 极小点，因此不能由 JT 的名称或库存直接读出这项应用。

需要覆盖的来源结论至少是：对同一 \(\mu\)，给出某个 \(x_*>0\)，对每个固定 \(0<x<\min(x_*,1)\)，实际存在边界矩点 \((a_*,q_*)\) 和参数 \(\theta_*=(s_*,t_*)\)，满足
\[
a_*>0,\quad q_*=a_*^2/x^2,\quad
\nabla K(\theta_*)=(a_*,q_*),\quad
s_*=-2a_*t_*/x^2,\quad t_*<0,
\]
并有实际 \(\Lambda_0>0\)、正切向曲率 \(\Lambda_1>0\)，以及该点是原尾域
\[
D_x=\{(a,q):q>0,\ a\ge x\sqrt q\}
\]
上真实全域扩展实 Legendre 率函数的唯一极小点。不能用任意有限局部 \(I\)、局部驻点、局部严格极小或某个候选参数代替最后一个全局量词。

本见证已满足有界、中心、\(P(X>0)>0\)、真实 MGF 全域有限、所有参数协方差正定，以及第 7 节全部紧族谱/矩条件。这些事实支持局部均值逆图，却不自动证明原正尾域上的全局唯一性、\(t_*<0\) 或边界切向曲率的符号。R2 的一句隐函数说明不是这些来源范围的已核验替代证明。本次没有构造或认证新的小正 \(x\) 鞍点。

由于 \(|X|\ge1\)，实际可达均值集的 \(q\ge1\)，在其紧凸包内 \(D_x\) 的相对尾部是闭的，零能量边界不造成新的漏口。一旦真实全局唯一极小点和局部正则条件被证明，有界紧性下的正率间隙及实际 Cramér 远场局部化可按既有有界应用接口推出；它们不能在唯一性尚未供应时被预先记作成立。

此前 B/C 来源蕴含报告（C:/game/shao lean/coordination/integration-v146/original-b-source-implication-review.md，SHA256 0a1cb2b7b56accae776f214e1911ca8a5cc8acd8c35275c606be3a200ac65449）已处理条件式固定律、固定 x 的尾展开。本报告只使用该背景结论，不重复它的证明审查，也不把条件式 JA342 当作自动提供当前 \(\mu\) 的实际正鞍点。一旦该实际鞍点接口闭合，才可把同一见证代入尾渐近结论。

## 9. 接受范围裁决

| 原 D 内容 | 数学裁决 | 是否尚需实质新结果 |
|---|---|---|
| 八个互异正幅值、同一选择上的两类丢番图性质 | CLOSED：JO355 与 JP356 的实际构造 | 否；不要求列出数值幅值或证明完整八维满测版本 |
| 真实十六点对称、中心、有界概率律 | CLOSED：JP356/JT360；单射保证十六点而非十六个可碰撞槽 | 否 |
| 同一律的二维径向 WC，\(\beta=3/8<2/5\) | CLOSED：无剩余丢番图假设 | 否 |
| 所有非零频率真正联合非格点 | CLOSED：JS359/JT360 的整数倍传播反证 | 否 |
| 原 limsup 意义的 strong 失败、弱与强严格不同 | CLOSED：JR358/JT360 全阈值近共振及 SC 等价 | 否 |
| 任意固定紧倾斜族的一致 WC、真实统一谱、标准化矩 | CLOSED_AS_MATHEMATICAL_IMPLICATION：JT 已付清既有泛型接口全部前提 | 至多命名组装包装；无新数学假设 |
| 充分小固定正 x 的实际正则 GLOBAL 唯一鞍点 | OPEN：不在 PR528 类型中，未由本报告证明 | 是；需实际来源鞍点与全域极小性结果，非仅包装 |
| 本具体见证的完整尾渐近应用、完整 D | OPEN，以上述实际鞍点接口为承重缺口 | 是；不能由谱严格性替代 |

本裁决仅证明原 D 已有的经典严格性子范围及其明确的数学后果；没有最弱条件刻画、随 x 变化的一致展开、\(\beta=2/5\) 端点、历史新颖性或 OQ3 整体完成的结论。

本次唯一写入为本报告，零 Lean/AX/编译运行、零新证明源码、零 Git/API 写入、零子上下文。既有完整独立审查与服务器内核/同一首次原对象递归公理证据均按上述精确源版本复用。规定模型/强度 gpt-6.1-sol/xhigh；本上下文未获实际模型/强度及分项用量遥测，actual_model、actual_effort、input_tokens、cached_input_tokens、output_tokens、reasoning_subset_tokens 均为 null。
