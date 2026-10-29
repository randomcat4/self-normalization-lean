# 原 T 的单一正矩窗口：P179 / PR549 unit263 增量范围审查

日期：2026-10-29。角色：Root5既有独立数学上下文 /root/original_b_scope_implication_review，规定gpt-6.1-sol/xhigh。仅审263对原题的单窗口增量；复用合格完整局部SOURCE/proof/allactualTYPE/所需VALUE/AX，不重复全证审计。264的CDF数学内容由另一既有上下文负责，本报告不作其裁决。

**裁决：263已在同一原μ/h和真实物理T上，把262的tilt、包络、geometry、吸收及矩窗口合成一个固定正c，使唯一公开z窗口为1≤z≤cβ^(−1/p)n^((p−2)/(2p))，并明确证明该数值窗口最终非空。β>0由原投影二矩一内部推出，不是新增前提；c在全部n及w/z之前选定。**

**这是固定模型、固定p和固定外部/包络资料后的单窗口原物理相对速率。它没有证明原核自动存在合法包络，没有给三角阵或无界条件化的一致c/N，没有解除更广L² hSZ，也没有把整个常数倍边界上的误差上界升级为趋零。**

## 1. 精确输入与资格复用

基线为 coordination/integration-v155/original-t-current-relative-polynomial-source-implication-review.md，SHA256 81137190d7c249a722636f1701de94af3b0771d1624558799c682dc710d0d74c，11199 B / 154 LF。其原P相对多项式率、R付款及外部hSZ边界继续有效。

发布P179 / PR549的head为abc5b2bf12577e40f2f7060a906fec8bf86e4630，tree为41509195d0a3a7f63df2de17cb7b2323beefc76a。下列路径均在drafts/oq56/：

| 工件 | SHA256 | B / LF |
|---|---|---|
| publication-v179/PUBLICATION-COMPLETE.json | 218f8f52fb4acb08164e21e5b44e815b8e4b7a69e167b30aa2c2db941df6a432 | 9746 / 207 |
| publication-v179/manifest.json | 649016d7a4b3f8c026aeea48cea6c8ed9eaf5e7f97255bd1e255c07e5c0d66d8 | 151720 / 3164 |
| unit263/qualified-evidence.json | 538e165d966067de6002112446689087d4b17f843fc979864093c43ba8f63d04 | 13411 / 331 |
| unit263/author-repair-03/OriginalSingleWindowPhysicalRelativePolynomialRate.lean | 8dc80cf0296cdfa160f57af5618de17bbf45b8fea792a7500249c283acbaf56a | 12686 / 236 |
| unit263/freeze-03/frozen-declaration.json | 16f62b0698b7c621e90c944434b2bc010c40c894e68b1cbb7cfb5bc1ba4c9a73 | 2197 / 51 |
| unit263/source-review-01/FINAL-REPORT.md | 952c6bc20e0b347730f0ae3fbe3d8bd558807548c8cb1ecb3b512d3cebfe93b6 | 14113 / 41 |
| unit263/source-review-01/FINAL-VERDICT.json | c38cbb9a46a46d35bf35862798ddc2535122addd9357aeebc9e0277175192624 | 7353 / 197 |
| unit263/owner-evidence-01/actual-owned-types.txt | 1f03251309b3a871862dbbe93df3543d0e32635588bdca1cfb54f00477bceb9b | 27774 / 375 |

本地实际散列均相合；完整当前冻结头为3c95d7ec4d27d37712930ecba1739606da14d2642dc7c6633452c61678a06d8c，3063 B / 58 LF。已完整读取新承重声明/let、最终独审与裁决，定向核对β正性、c的具体选择、各内部窗传递、非空阈值及原262调用；实际TYPE核对固定资料→∃c→eventually n→全部w/z的完整量词、七个警告前提和最终目标。局部完整证明和全部375 LF实际TYPE审阅资格直接复用，不以新整合为由重做旧262或263完整审计。

实际仅1个theorem owner、0个非定理，必要VALUE确为空，SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855。首次原对象SHA256 7fabf878ee1196c3047dba80661e4c130de8edc54e3681cd6989e2b020210c23，543696 B；正式native04及同首对象审计已有真实RC0/0，递归AX仅propext、Classical.choice、Quot.sound。本次没有执行这些检查。

## 2. β正性是原假设的结论

原前提仍为任意可测Ω、概率μ，原h产品可测/L²/对称/中心化，及
\[
g(o)=\int h(o,y)\,d\mu(y),\qquad E_\mu g^2=1.
\]
r=h−g−g、ρ=√E_(μ×μ)r²与原模型一致。固定2<p≤3和原μ下|g|ᵖ可积后，β就是Eμ|g|ᵖ。

证明先得β≥0。若β=0，由非负可积函数积分为零得到|g|ᵖ=0 μ-a.e.；正实数的p次幂严格正，故g=0 μ-a.e.，从而Eμg²=0，与原二矩一矛盾。因此β>0在内部成立。没有给用户新增β>0、β≥1、物理分母非零或无原子假设。

这使旧β=0分支在当前原模型中被证明不可发生，正β矩窗口可统一使用。后续β^(1/p)β^(−1/p)=1只依赖β>0，不依赖β≥1之类额外比较。

## 3. 同一个c具体怎样合并全部窗口

设
\[
q=\frac{p-2}{2p},\qquad 0<q\le1/6,
\quad
c_m=\{\min(1/2,cSZ)/2\}^{1/p},
\]
\[
c_r={\rm remainderWindowScale}({\rm tailScale}(Menv),t_0),\quad
c_a=\min\{1,\sqrt{t_0}/2\},\quad
c_t=\frac1{2e^{1/2}},\quad
c_g^{\rm geom}=\frac1{1+\rho}.
\]
它们全部严格正。源码实际选择
\[
c_o=\min\{c_r,c_a,c_t,c_g^{\rm geom}\},\qquad
c=\min\{c_m,\ c_o\beta^{1/p}\}>0.
\]
这里的c_g^geom是几何窗口常数，不是原概率付款中的投影浓缩常数cg。令a=cβ^(−1/p)，则
\[
a>0,\qquad a\le c_o,\qquad
a\le c_m\beta^{-1/p}.
\]

因此同一公开窗口z≤a n^q在n≥4时给出：

- z≤c_mβ^(−1/p)n^q，即原p矩窗口；
- q≤1/6，所以z≤c_o n^(1/6)，同时给原包络窗z≤c_r n^(1/6)与吸收窗z≤c_a n^(1/6)；
- n^(1/6)≤√n，所以z≤c_t√n给tilt窗，而z≤√n/(1+ρ)给geometry。

p=3时q=1/6的闭端点保留。源码最后将这四个非矩内部窗口及正β矩窗口连同同一个w/z传给已合格262，并返回原相对误差结论。没有假设这些窗口“迟早会自动成立”，也没有在不同窗口中换用不同模型、ρ、c或z。

公开窗口只剩一个，不表示包络假设被删除：仍要求w≥0、w≤Cenv(log n)^aenv的μ-a.e.界，w²原μ可积且积分≤Menv，以及原r的μ×μ-a.e.乘积界|r(o,y)|≤w(o)w(y)。这些并非L²/p矩的自动结论。

## 4. 常数依赖、最终非空和统一性的边界

公开量词精确为
\[
(\mu,h\text{ 原前提})
\ \forall p,h_{gp},cSZ,C_1,\ldots,C_4,hSZ\
\forall Cenv,aenv,t_0,Menv\ [\text{符号条件}]
\ \exists c>0\
\forall^\infty n:
\]
\[
n\ge4,\quad 1\le c\beta^{-1/p}n^q,\quad
\forall w\ [\text{原包络条件}]\ \forall z\
[1\le z\le c\beta^{-1/p}n^q\Rightarrow\text{原尾率}].
\]

所以c在n、w、z之前固定，但在p、真实β/ρ、外部和包络资料之后选定。具体构造的c依赖p、β、ρ、cSZ、t0、Menv；不含C1–4、Cenv或aenv，尽管公开量词允许在这些资料固定后选择。Ktail保持v155的显式值，仅依赖C1–4。

由于a>0且q>0，a n^q→∞。263实际将保证a n^q≥1的最终集合与262的最终集合取交，故顶层明确包含数值非空结论。它不是“若窗口非空”的新增前提。**这只是z区间数值非空，不证明任意原核都存在满足全部包络条件的w。**

新增非空阈值可依赖a、q，因此可依赖p、β、ρ、cSZ、t0、Menv；上游阈值另依赖原μ/h与Cenv/aenv等固定资料。263只承诺固定这些资料后的一个共同N，对之后所有合法w、z统一。不能把v155里“先于p选择原吸收N”的较强次序原样搬成263对所有p的统一非空N；q在p趋近2时可趋零。

具体构造不需C1–4参与非空阈值，上游262阈值也可先于这些常数选择；但当前顶层没有另抽出这种更强参数一致性声明。无论如何，该结果不是允许μ_n/h_n、p_n、β_n或包络参数任意逐n变化而仍有共同c/N的三角阵定理。一般无界残差的条件化应用还需自己的实际包络和一致性论证。

## 5. 原物理尾与速率保持，小o须另作普通推论

原P=μⁿ，D=residualStatisticD(n,r)，原统计量仍为
\[
T_{\rm phys}=\begin{cases}
0,&\sqrt{{\rm centeredSq}}=0,\\
(W+D)/\sqrt{{\rm centeredSq}},&\sqrt{{\rm centeredSq}}\ne0.
\end{cases}
\]
实际新公共结论是同一弱闭尾的
\[
\left|\frac{P\{T_{\rm phys}\ge z\}}{\Psi(z)}-1\right|
\le K_{\rm tail}\left[
\beta(1+z)^p n^{-(p-2)/2}
+\frac{(1+\rho)(1+z)^3}{\sqrt n}\right],
\]
\[
K_0=64e^2(1+4\cdot512),\qquad
K_{\rm tail}=8(1+C_1+C_2+C_3+C_4)e^{C_3}(1+K_0)>0.
\]
原子、等号边界和真实s=0取零保持；263没有通过尾概率连续性或编码无原子性删除它们，也没有新增随机变量极限换尾事件的步骤。v155已经接受的R付款、真删除费用、正完整I及原物理运输继续复用。

对整个常数倍窗口z≤a n^q，该上界不自动趋零。例如z∼a n^q时第一项一般趋βa^p而非0；p=3时第二项也可有非零常数级边界。因此“窗口最终非空”与“该整个窗口上误差统一趋零”是不同结论。

普通数学上，固定原模型、p和共同合法包络资料，并取z_n≥1、z_n=o(n^q)，则最终在单窗口内，两项均趋零（q≤1/6），得到P(Tphys≥z_n)/Ψ(z_n)→1。对上端b_n≥1、b_n=o(n^q)的小窗口同理可由误差界单调性得到统一趋零。这些是数值界的普通蕴含，不是263另发表的小o或三角阵Lean声明；若实际包络在这些n不成立，不能跳过它。

## 6. 新冻结形式、警告及剩余原题条件

当前权威是freeze-03及其实际TYPE。显式Fin.fintype、Real.decidableEq和原mN/P下Measure.real均指原对象；最后的透明命题值包装展开仍是上述不等式S。实际类型中的have this : Prop := S; this不是增加一个this : S的证明前提，没有免费假设结论或削弱目标。

七条unused警告对应hW、hWR、hSq、hSqBound、hEnv、hz、hWindow；它们在375 LF实际TYPE的外层forall中全部保留。警告不许可删除原包络或窗口。历史正式RC1/noO和无-o诊断RC0按原字节保留；生产成功依据是当前精确源的正式native04首对象及同对象审计，未继承诊断08的RC0，也不据此声称早期问题已唯一归因为编译器bug。接受的是精确终审证据，而非“某个诊断曾返回0”。

更广L² ScalarShaoZhouFiniteCostTailInput仍显式给定；它没有有界观测前提，原g/canonicalη可无界，因此不是可由有界版本名称自动提供的无关标签。本次没有证明该输入的存在、外部文献推广或无界条件化，也没有给p54条件/三角族的一致消费者。已接受p54矩收敛/最终有界修正不重新开放。

本报告只确认263的单窗口固定模型尾率。264的CDF范围由另一既有独审及Root合并，不能拿本报告或旧v155的历史OPEN记录代替其新裁决；本文未读264数学声明/证明。DC/full OQ56/root亦不由当前条件式单窗口尾率自动关闭，fixed-clip1费用反例的边界保持。

本次唯一写入本报告，未改其他工作者或旧报告，未读未发布265及以后；无Lean/AX/SSH/联网、新上下文、共享状态/调度/Git/API写入。实际model/backend/effort及input/cachedInput/output/reasoningSubset用量未暴露，均为null。
