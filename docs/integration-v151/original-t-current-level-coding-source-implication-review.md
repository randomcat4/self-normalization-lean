# 原 T 当前层级编码与费用运输：P173 / PR538 增量数学范围审查

日期：2026-10-29。角色：Root5 既有独立数学审查上下文 /root/original_b_scope_implication_review，沿用规定 gpt-6.1-sol/xhigh。基线为已接受的 v150 来源衔接报告；本次只核已完整发布 254/255，不读取或使用未发布 256 及以后，不重审已合格局部完整证明。

**裁决：254 已实质闭合 v150 所列“同一当前模型上的实际增广标量编码、保留删除恢复、实际有符号纠正及精确阈值关系”这一段；255 在同一个见证中再把原 P、约化 P0、增广 ν 的当前基底 ξ 费用逐项接通，完整/各部分项的归一化均正确。**

**但 255 的 costCoded 使用增广空间上拉回的原坐标 ξ，既不是 η 相位的费用，也没有加入 Q 的包络扰动。故这些三端精确等式不是 η 编码费用极限。新两件没有实例化当前 η 费用极限、同序列严格矩预算或 E_k 的定量概率消费，也没有新增 Gaussian-relative 原物理尾或 Gaussian CDF 结论。**

Q 的 M 支配在新公共结论中尚未列出；当前实际 Q 已存在后，可由规范量化误差和规范化定义作第 6 节的普通数学推导。这个推导说明不需新增统计假设，但须区分 clipping 层级 y 与任意比较阈值 z：旧 M_y 适用于 z=y 或 |z|≤y，不能声称同一个 M_y 对全部实 z 一致支配。

## 1. 精确输入与独立证据复用

发布：drafts/oq56/publication-v173/PUBLICATION-COMPLETE.json，PR538。

- head：4fb1b58608f3b5ecd28427d7620c894559e5a7e5。
- tree：29eb4a5cb3bd3d2ef243ca8958d95c027cc9271b。
- PUBLICATION-COMPLETE.json 实际 SHA256：dc10fb10002f60de0c6783786f3c6e5142c9c6e5c855ad17310d082fad836852。
- manifest.json 实际 SHA256：aaf76d35e5b1b3a9f9e6be719469360fdfaa3d44897ae590552f80f54510c723；其中两件生产源码条目与以下最终源匹配。

| 单元 | 最终源码 | SHA256 | 字节 / LF |
|---|---|---|---|
| 254 | drafts/oq56/unit254/author-01/OriginalLevelDependentCanonicalCoding.lean | 2d90010762b6d92cbf249512825c8eb429b387288325a21edcc8f90553d95896 | 28956 / 527 |
| 255 | drafts/oq56/unit255/author-01/OriginalLevelDependentCanonicalCostPacket.lean | a2db2c096e444b9ddd63fe4ff0baa451a0d2b834cb5c9049998cee2eeeb18989 | 38774 / 671 |

| 单元 | qualified-evidence.json SHA256 | 最终完整独审 SHA256 | 完整实际 TYPE SHA256 |
|---|---|---|---|
| 254 | d12c222bd79655ff1ba2d7442cc580b962f971b929fa41adaddcd0db829d564f | 2043971d9e4a5518b3a8850c21f9356aaa6fcfdbf407acd21430b172725402de | 7685bd6a721557c914ef2ed01821e3e4d52f5c88db6ed5b9b0ddb38b6b86bcf0 |
| 255 | 3f0421247fcccb0515153b89a2381206243b7ca96c4a049d2caf124284f52713 | f89579fb96501226d6228af91f7c016d021a8104cd9a4a0dff2b3fc8863f0258 | ba17ab6b999fb6c22eb52b37c553afd804799bf4ef8c89e9b933213f01834362 |

冻结完整公共 head 的 SHA256 分别为 defba0bb2a46bd3ce2e24c6cdbb436940aa381c2f651505d66a1b14466f36816（254，10740B）和 78d92960a8ea7142bea38f17133ce757af2f64ee1a304c390cc19f8bfa4863ae（255，18195B）。

本次完整读取两件公开声明的所有承重 let/量词、冻结定位及既有完整最终独审；实际源码、最终独审和 TYPE 文件的哈希均与资格绑定相同。特别定向核对 255 实际 TYPE 中 Sν、fullTestν、Icoded、costCoded 的完整 RHS，以区分 ξ 运输与 η 极限。所需 VALUE 文件均确为空，其依据复用已经合格的完整实际 owner 审查；未重新审查旧证明或重跑机器检查。

基线报告：
C:/game/shao lean/coordination/integration-v150/original-t-current-level-model-source-implication-review.md，
SHA256 147314315c9f76a8cbdaa76e772137e7e739d4e09a13f86517154733e259d78d。
原对象、p51/p54、固定 clip1 反例和前序合格接口的精确范围按该基线及 v149 保留。本报告不自行宣告 Root 集成或原题完成。

## 2. 量词、窗口与容易混同的三个局部记号

254 与 255 保留任意原可测空间 Ω、同一概率 μ、同一产品可测/L²/对称/中心化原核 h，以及真实投影二矩一；没有新增标准 Borel、高阶矩、产品包络、原正分母或阈值无原子前提。外层真实 g、r、ρ 按原 μ 定义。

两件的量词均为

\[
 (\mu,h\text{ 的原前提})
 \Longrightarrow
 \exists(m_0,hm_0,\operatorname{CountablyGenerated}(m_0)):
 \forall n,y,\varepsilon\text{ 满足 (A)，完整结论}.
\]

\[
 n\ge4,\quad
 1\le y\le\frac{\sqrt n}{2e^{1/2}},\quad
 0<\varepsilon<\frac1{4\sqrt n}.
\tag{A}
\]

同一个 m0/μ0 在全部 n、y、ε 之前确定。255 的同一存在见证内保留 254 全部 coding core，随后附加费用运输；不是“分别存在两个模型”后拼接。原 P、约化 P0 及增广 ν 也在同一 let 上下文内明确构造。

clipping 参数 y 与比较阈值 z 是不同量：当前 D2=e_y、Tclip_y、B_y、B_y^(i) 一直取 512ρy；其后才量化全部 z∈ℝ 的阈值关系。y 仍受 (A)，z 不受 y 的正性或窗口限制。

| 源码局部记号 | 本报告记号/含义 | 不得混同 |
|---|---|---|
| Q | 原有限样本的坐标观察映射，结论 Q=id | 不是有符号小纠正 Qε(z) |
| s | Y 的总方差归一化尺度 s_code>1/2 | 不是原物理 studentizer s_phys=√centeredSq |
| κ | V0=0 时的约定值，恒等于 0 | 不是 252 的 L¹ 常数 κ_i |

因此 s_code>1/2 或编码 Vη>0 几乎处处都不能被记作原 s_phys>0 几乎处处。

## 3. 254 的当前 canonical 编码已真实实例化

设 μ0=trim μ，P0=μ0^n；增广单坐标律为 μ0×Uniform(0,1)，ν 为其 n 次有限乘积。q 删除辅助 uniform 坐标。公开结论给

\[
 P_0=\operatorname{map}(\mathrm{id})P,\qquad
 q:\nu\to P_0\text{ 保测}.
\]

这里原 P=μ^n；并无把原样本律换成 ν 的物理概率。

编码的每一个量已由声明实际指定，而非假设存在：

\[
 \xi_i=g(O_i)/\sqrt n,\quad
 c_i=\operatorname{baseFourIndicatorCode}
       (\operatorname{natGeneratingSequence}(\Omega\times\mathbb R)),
\]

\[
 Y_i^\varepsilon
   =\operatorname{quantizedObservation}(\varepsilon,\xi_i,c_i),\quad
 a_i=E_\nu Y_i^\varepsilon,\quad
 s_{\rm code}=\operatorname{actualNormalizationScale}(\nu,Y),
 \quad \eta_i=(Y_i^\varepsilon-a_i)/s_{\rm code}.
\]

ν 对固定 n 不随 y、ε 改变；这些 η 的定义事实上也不依赖当前 clipping y。声明给 η 的真实独立性、中心化、L²、总二矩一、每个标量坐标无原子，以及 ν(Vη=0)=0。原坐标 ξ 的中心化与总二矩一也有明确原/约化积分依据。

整个编码 C=(η_i)_i 满足 comap C(Borel)=mAug，因而所有增广可测实观测都可作为 C 的 Borel 函数。该陈述恢复的是所用可测信息，不是额外保证原 Ω 点可被单射恢复或原全部 σ 域等于 m0。

删除侧也已真实实例化：对每个 i，Ddel、Jdel、当前 B_y^(i) 的联合三元组是只看其他 η_j 的同一个保留坐标 Borel 函数，原 n 的归一化系数不变。此外有任意保留观测函数的因子化条款。

有符号余项已经以当前 e_y 指定。记

\[
 b_y=\sqrt{1+e_y\circ q}>0,\quad
 Q_\varepsilon(z)=W-W_\eta+zb_y(V_\eta-V),\quad
 D_\eta(z)=D\circ q+Q_\varepsilon(z).
\]

254 对 G2=e_y∘q 与每个 z 的 Dη(z) 给同一编码 C 的实际 Borel 因子 G2、G1,z。它没有把 signed Dη 换成 |D| 或不具同一阈值关系的下比较量。v150 中“当前实际编码与 signed correction 尚不存在”的缺口已经消除。

## 4. 所有实阈值、五种关系、原子与 p0

254 对全部 z∈ℝ 逐样本给

\[
 W_\eta+D_\eta(z)-zV_\eta b_y
   =W+D\circ q-zVb_y.
\tag{B}
\]

五种关系为 ≤、<、≥、>、=。令 A_R(z)={R(Tclip_y,z)}，F_R(z) 为对应的原未除法比较

\[
 F_R(z)=\{R(W+D,\ zV\sqrt{1+e_y})\},
\]

并令 E_R^ε(z)={R(Tη(z),z)}。已给精确概率和差集关系

\[
 \nu(E_R^\varepsilon(z))=P_0(F_R(z))=P(F_R(z)),
\]

\[
 A_R(z)\triangle F_R(z)\subset Z_0=\{V=0\},\qquad
 |P(A_R(z))-\nu(E_R^\varepsilon(z))|\le p_0,
 \quad p_0=P(Z_0).
\tag{C}
\]

p0 使用**原 P** 定义，同时 ν(V=0)、P0(Z0)、P(Z0) 完全对应。没有把除法在 V=0 上的比较与交叉相乘事件错误地逐点识别；原 V=0 上 Tclip=0 的约定保留。

这是对有限正 ε 的精确、原子安全阈值运输，不需要 ε→0 才有事件等价，也不要求 P(T=z)=0。特别地，当前 clipped 闭尾、严格尾和 CDF 的阈值事件都能按 (C) 处理。

必须保留一个范围区别：Tη(z) 本身随 z 改变，因为它的分子含 z 的纠正。因此“对所有 z 的阈值关系”不是声称存在一个与 z 无关的单个编码随机变量，它与 Tclip 有全分布相等。对每个 z 用同一实际 C、e_y 和相应 Dη(z) 比较是正确的，直接把 z↦ν(Tη(z)≤z) 当某固定变量的 CDF 则没有依据。

新两件没有给 p0 的数值指数界，但它也不是一条新统计假设。普通数学上，由原单位投影二矩知 q0=μ(g=0)<1，且

\[
 p_0=P(\forall i,\ g(O_i)=0)=q_0^n.
\]

所以固定原律下 p0 可指数付款；q0=0 时同样成立。具体联合应用仍须引用/记录此付款或已有真实好集对 Z0 的包含，不能把 p0 直接丢掉。它只涉及 V=0，不代替原 s_phys=0 的付款。

## 5. 255 的三端费用等式是真的，但运输的是基底 ξ

255 在同一 254 见证中添加原当前

\[
 A=|D|,\quad B=B_y,\quad
 A^{(i)}=|D^{(i)}|,\quad B^{(i)}=B_y^{(i)}
\]

的可测性、无权 L¹、绝对删除差与删除总量 L¹，并把它们经 id、q 送到 P0、ν。它没有从加权可积性倒推这些无权事实。

原基底相位为

\[
 S_y(\xi)=\sum_j(y\xi_j-(y\xi_j)^2/2),\qquad
 S_y^{(-i)}(\xi)=\sum_{j\ne i}(y\xi_j-(y\xi_j)^2/2).
\]

声明中 Sν 使用的是 ξ_i(x)=g((x_i).1)/√n，故

\[
 S_\nu=S_y\circ q,\qquad
 S_\nu^{(-i)}=S_y^{(-i)}\circ q.
\]

fullTestν=fullTest0∘q、deleteTestν,i=deleteTest0,i∘q；它们没有使用 η 或 Q。完整实际 TYPE 的 RHS 与此完全相同。

令

\[
 F_y=yA+y^2B_y,\qquad
 G_{y,i}=\min(|y\xi_i|,1)
  (|A-A^{(i)}|+y|B_y-B_y^{(i)}|).
\]

三端的 full I 均严格为正且相等：

\[
 I_{\rm original}=E_Pe^{S_y}
 =I_{\rm reduced}=E_{P_0}e^{S_y}
 =I_{\rm coded}=E_\nu e^{S_\nu}>0.
\]

每一个 full/partial weighted 积分都可积且逐项相等，故

\[
 \mathcal C_y^{P}
 =\mathcal C_y^{P_0}
 =\mathcal C_y^{\nu,\xi}
 \le64e^2(1+4\cdot512)(1+\rho)
             \frac{(1+y)^3}{\sqrt n}.
\tag{D}
\]

这里所有 partial 项都是除以**同一个完整 I**。没有改成删一 normalizer，也没有损失一个 m_a 的因子或额外乘 m_a^{-n}。因此 v150 中原/约化/增广模型当前费用的真实连接已经被显式交付，而非仍需猜测积分法则。

然而，源引擎用实际 η 时需要的相位是

\[
 S_{\eta,y}=\sum_j(y\eta_j-(y\eta_j)^2/2),
\]

其 correction 包络还应包含 Mε，删除包络也随之改变。一般并无 Sη,y=Sν，也没有 |Dη(y)|≤A∘q 的结论。因此 (D) 不是该 η 费用在有限 ε 时等于原费用，更不是 ε→0 极限已经完成；“coded”这个局部名字不能消除其 RHS 使用 ξ 的事实。

## 6. Q 的 M 支配：已实例化 Q 与普通数学推论的边界

254 已定义实际 Qε(z) 并给 (B)；254/255 的公共结论没有列出 |Qε(y)|≤Mε，也没有列出 Q 的 L¹ 趋零。252 的 M 不能仅凭名称自动绑定。

现在实际 canonical Y、a、s_code、η 已指定，可以作以下普通数学推导，说明这个绑定不需新增矩假设。采用该规范量化机制的已合格误差规格 |Y_i−ξ_i|≤ε，令 δ_i=Y_i−a_i−ξ_i。原 Eξ_i=0 给 |a_i|≤ε，因此逐点 |δ_i|≤2ε。总 L² 范数的反三角不等式给

\[
 |s_{\rm code}-1|\le2\varepsilon\sqrt n=2\varepsilon N,\qquad
 s_{\rm code}>1/2.
\]

于是逐样本欧氏范数满足

\[
 \|\eta-\xi\|_2
 \le s_{\rm code}^{-1}\|\delta\|_2
      +|s_{\rm code}^{-1}-1|\|\xi\|_2
 \le4\varepsilon N(1+V).
\]

结合 |Vη−V|≤‖η−ξ‖₂、|Wη−W|≤N‖η−ξ‖₂，得

\[
 |Q_\varepsilon(z)|
 \le4\varepsilon N(1+V)(N+|z|b_y).
\tag{E}
\]

当前 |e_y|≤B_y 且 b_y=√(1+e_y)≤√(1+B_y)，所以在 z=y 或更一般 |z|≤y 时，

\[
 |Q_\varepsilon(z)|
 \le4\varepsilon N(1+V)
      \{N+y\sqrt{1+B_y}\}
 =M_{\varepsilon,y}.
\tag{F}
\]

这正接上 252 的当前 literal M。全/删除 H 在原模型的 L¹ 由 v150 已给；255 的同一 id/q 运输及当前观测可测性使相应 H、M 在此 ν 下可积，并保留正确的删除 L¹ 包络。也可由 EV²=1、EB_y<∞ 的 Cauchy–Schwarz 直接得到，不需要 E(V²B_y)。

这是明确的普通数学衔接，不是声称 PR538 已发表一条含 (F) 的 Lean 公共结论或机器验收。量化机制本身的误差规格按既有精确资格复用，未在本报告重审其证明。

尤其不能将 (F) 扩展成同一 Mε,y 支配所有 z∈ℝ：若比较阈值 |z|>y，(E) 的自然包络必须含 |z|。全实阈值恒等式 (B) 无此限制，定量包络却有参数依赖。对源相对尾应用取 z=y，完全符合原问题；对 compact/CDF 必须清楚写出所用阈值范围和包络。

## 7. 尚未实例化的 η 费用极限、严格预算及 E_k

对固定 n,y，可以选有效的 ε_k↓0，例如 ε_k=1/[8√n(k+1)]。因同一 m0 先于全部 ε、ν 不随 ε 变化，新声明已经给一个真正可在同一概率空间上比较的 canonical η_k 族，不再是逐 k 独立挑选的不相容见证。第 6 节也给这个实际 Q_k 的可用普通数学误差控制。

但当前公开结论尚未构造并消费下面的**同一个**源费用族：

- A_k=A∘q+M_k，删一 A_k^(i)=A^(i)∘q+M_k^(i)；其真实差扰动须接上 252 的 Δ。
- η 相位 Sη,k 及每个 erase-i 相位、η 的连续 capped 删除权重。
- η 的完整归一化积分 Iη,k，以及全部 full/partial 积分、比值和总 finite-cost 极限。

数学上已有输入足以支持固定 n,y 的通常证明：相位指数≤e^{n/2}，原 A/B 及删除差可积，M_k、Δ_k 的 L¹ 费用趋零，连续 cap 和相位逐点收敛，Iη,k→I_y>0 后取比值。这个论证的承重输入已经接上；PR538 尚未把实际 η 费用及各极限逐项列为当前应用结论。不能以三端 ξ 的有限 ε 等式取代这一步非平凡的扰动/支配收敛消费。

严格预算也尚未在新结论中出现。254/255 只有 L²，没有 p、β_p、cBudget/cMoment 或 δ_{η,k}、L_{η,k} 参数。若原投影另有 2<p≤3 和有限 β_p，原矩窗口及 L0 上界按 v150 可保留；还须针对这里的**同一实际 η_k**证明 δ/L 收敛并在一个共同 k0 后满足外部源引擎的严格余量。编码总二矩一只给粗 Lη≤y²，不给任意指定 cBudget<1 的严格 Lη<cBudget·y²。旧 231 机制可复用，但实际同族实例化不能省略。

对 upper-event 定义

\[
 E_k=\{y|D_\eta(y)|>V_{\eta,k}/4\},\qquad
 E2=\{y^2|e_y\circ q|>1/4\}.
\]

新两件没有 E_k 概率、limsup 或 e^{-t0 n^{1/3}} 数值付款。第 6 节与 v150 的原真实好集严格余量可在实际族上推出：H_y 内最终 y|D+Q_k|≤Vη,k/4；反向 Fatou 再给 limsup ν(E_k)≤P(H_y^c)。E2、原 V=0 及物理 s_phys=0 也必须用同一原 H_y 与 q/原模型法则付款。这个机制没有要求阈值无原子，但尚未作为当前源引擎联合消费交付。

这一步所需 bounded-polylog 包络/实际集中窗口不能从仅 L² 推出；这些附加应用前提仍按 v150 保留。新两件不新增任何这样的概率前提，也不据此证明任意二阶残差的普遍指数付款。

## 8. 原 T、CDF、外部 SZ 和 fixed-clip1 边界

新两件直接运输的是当前 Tclip_y。原

\[
 T_{\rm physical}=(W+D)/s_{\rm phys},\qquad s_{\rm phys}=0\Rightarrow T=0
\]

仍按 v150 的 literal 比较接回：需要 (1+ρ)y≤√n，并在 G_y∩{d≥−1/2} 上 e_y=d、真实分母相等。新两件没有删除这个 guard，也没有从编码 Vη>0 推原 s_phys>0。

当既有原包络/小窗口给 P(H_y^c)≤b_y 后，原子安全的任意阈值比较误差可按事件差直接相加为 p0+P(Tclip_y≠Tphysical)，并以已付款的好集界控制。固定 ρ、y≤cn^{1/6} 下物理 guard 最终成立；它不是 (A) 的无条件推论。

254 的五种关系已解决**编码到当前截断过程**的闭/严格尾和相等事件语义，不需以尾连续性处理原子。它并未给 Gaussian CDF 近似。旧原 compact/CDF 源输入与反射/单侧极限路线保持；新的 Tail 机制也不能自动代替不同 CDFInput。原 s_phys=0 的约定与实际付款须继续保留。

新两件没有外部 ScalarShaoZhouFiniteCostTailInput 或 CDFInput 的存在/证明；精确外部 SZ 输入及其来源归属仍是显式义务。待上述当前 η 费用、严格预算、E_k 及物理连接同族消费完成，才能把当前三次成本实际放进原 Gaussian-relative 尾的上下界。旧异常吸收 R_n=e^{-t0 n^{1/3}/2} 可按其窗口复用；不能在尚无当前源引擎应用时将它叫整个新尾界的误差。

固定 clip1 的二点模型反例保持：原有界 h(x,y)=x+y+xy 下，固定 $\mathcal C_1(y)$ 可为 y⁴/√n 阶，不能普遍代入当前三次界。254/255 的新 B/Bdelete/D2 均为 512ρy，正是按正确当前过程推进，没有证明也无需证明该假 clip1 三次断言。旧 249 的固定 clip1 条件性尾界仍在其精确范围成立，新 ξ 费用运输不把其费用替换成另一个预算。

## 9. 相对 v150 的增量裁决

| 依赖 | P173 后状态 |
|---|---|
| m0/μ0 先于全部 n,y,ε，且同一见证承载当前过程 | 已实际给出；255 同一见证保留全部 254 core。 |
| 当前实际 ν/code/Y/a/s_code/η/C 与独立、归一化、编码正分母 | 已实际实例化；不再是只有输入的通用接口。 |
| 原长度 Ddel/Jdel/B_y^(i) 的 retained 编码恢复 | 已实际给出，只有其他编码坐标。 |
| 当前实际 signed Qε(z)、Dη(z) 及全部五关系 | 已实际给出全实 z 的精确阈值运输，原 p0 保留。 |
| Q 的 M 支配 | 新公共结论尚未列出；当前 canonical 实例下有第 6 节普通数学推导，适用 z=y/|z|≤y，不能对全实 z 用同一 M_y。 |
| 原 P/P0/ν 的当前裸费用、基底 ξ weighted 积分及 full/partial 归一化 | 已逐项精确接通；三端成本相等且有同一三次界。 |
| 实际 η 相位/加 Q 包络的 source-cost 极限 | 尚未作为当前联合应用交付；不是 costCoded 的三端等式。 |
| 同一 η_k 的严格 moment budget、actual E_k 数值付款 | 尚未实例化消费；既有 231/232 及原 H_y 机制可精确复用。 |
| 原物理尾/CDF/原子/s_phys=0 | 语义连接和既有物理比较保持；本次无新 Gaussian 近似或整个原应用闭合。 |
| 外部 SZ、DC、full OQ56/root | 保持原显式条件/未闭合范围，不由本次包装或编码正分母消去。 |

本次完成的是“当前 actual coding＋基底费用运输”的实质增量。剩余层级现在可准确定位为“同一实际 η 的扰动费用极限、严格预算与真实 upper-event/物理付款消费”，不应再泛称当前编码尚不存在，也不应提前记作原 Gaussian-relative 定理完成。

## 10. 封存

本次唯一写入为本报告；未改他人文件、原 source、REGISTRY 或旧封存报告。未执行 Lean/AX/SSH/联网/Git/API，未新增子上下文。局部完整 SOURCE/proof/实际 TYPE/所需 VALUE/递归 AX 及首次对象证据按精确资格复用。第 4、6–8 节标明的普通数学蕴含不冒充新增机器检查。Root 决定采纳及原题状态更新。

~~~json
{
  "reviewKind": "INDEPENDENT_ORIGINAL_T_CURRENT_LEVEL_CODING_SOURCE_IMPLICATION",
  "PR": 538,
  "head": "4fb1b58608f3b5ecd28427d7620c894559e5a7e5",
  "qualifiedUnitProofsReused": [254, 255],
  "individualQualifiedScopesDisputed": false,
  "sameCanonicalModelBeforeAllNYEpsilonEstablished": true,
  "actualCurrentCodingRetainedDeletionAndSignedThresholdsEstablished": true,
  "originalReducedAugmentedXiCostTransportEstablished": true,
  "costCodedUsesEtaPhase": false,
  "QMDominationExplicitInNewPublicConclusion": false,
  "QMDominationOrdinaryDerivationProvidedForAbsZLeY": true,
  "actualEtaCostLimitsStrictBudgetAndUpperPaymentJointlySupplied": false,
  "newGaussianRelativeTailOrCDFClosureClaimed": false,
  "fixedClip1CounterexampleRetained": true,
  "unpublished256OrLaterUsed": false,
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
