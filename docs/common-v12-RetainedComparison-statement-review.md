# RetainedComparison 独立声明与来源审查

STATUS: CORRECT（声明阶段）

本报告只审查固定哈希提案的 2 个定义、3 个当前公共定理签名是否数学成立、来源对应是否准确、能否由已接受接口闭合。没有候选实现可审；本报告不宣称代码证明完成、服务器编译或传递公理审计完成。未运行本机或服务器 Lean，未重复验证旧依赖。仅新增本报告，没有修改提案、实现或共享文件。

## 绑定材料和来源范围

- 提案：C:/game/shao lean/drafts/c12/RetainedComparison-next-scope.md。
  SHA256：fe2969bf94db460176175726853dc71cd4bdb055279623dcff58c38d89eaa23f。
- 只读源 main.tex：C:/game/shao/current/c12/main.tex。
  SHA256：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- 只读源 supplement.tex：C:/game/shao/current/c12/supplement.tex。
  SHA256：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

本轮复核了提案哈希，并读取下列实际旧依赖公开声明；其独立审查与服务器认证结论复用，不重编译。旧依赖哈希也与提案列明值一致：

- ConditionalIID：855c2eb0e560ac9372505f8b41551a9895b9eb753be3ce2b3f3752be845af787。
- RetentionEvent：e27ec2b7f94d55cba013b1cc578dafba25b0056172a6d5c930eb62228c59bb43。
- RetainedVariance：5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6。
- Deletion：2bb43cdec4e7ccce21e0ca2981d1ca4178d791970c0b983665653543bee69687。

所用其他既有接口为升序 retainedIndex/retainedPath、FiniteIID 的完整路径 map-to-product、MeasurablePath 的原始弱穿越事件可测性，以及已接受 RetainedMoments/RetainedSample 的质量、可积性和大小界。提案作者关于 API 探测与缓存的回执不作为当前数学结论的证明。

## 第一阶段：实际定义和全部当前签名重译

以下记
\[
 B_x=\{u:|u|\le 1/x\},\qquad
 \eta_x=\operatorname{cond}(\nu,B_x),\qquad
 \mu_x=\int u\,d\eta_x,\qquad
 V_x=\int(u-\mu_x)^2\,d\eta_x.
\]
ηₓ 是已有 retainedCutoffLaw，是真正归一化的限制测度，不是新指定的抽象分布。qₓ 是已有 (ν Bₓ).toReal。

### 两个定义

提案 54–63 行在 namespace Shao 中定义：

1. retainedStandardize(ν,x,z)=(z−μₓ)/√Vₓ。量词是任意实测度 ν、任意 x,z∈ℝ；定义本身没有概率、可积性、正质量或正方差前提。积分与除法均使用 Lean 的全定义运算。固定 ν,x 后，μₓ,Vₓ 是常数，所以该 z 函数始终连续可测，包括 √Vₓ=0 的情形。
2. retainedStandardLaw(ν,x)=map(retainedStandardize(ν,x),ηₓ)。这是实际仿射观测的实际 pushforward。定义本身不声称概率质量、标准差可逆或单位方差；后面的来源前提才保证这些性质。

### 公共定理 1：固定正概率 fiber 的完整变换路径律

retained_cond_transform_path_map_eq_pi（提案 90–103 行）量化任意 n∈ℕ、任意带可测结构的 Ω、概率测度 μ:Measure Ω、ν:Measure ℝ、函数族 X:Fin n→Ω→ℝ，并要求：

- 每个 Xᵢ 可测；
- iIndepFun X μ；
- 每个 Xᵢ 在 μ 下与 id 在 ν 下 IdentDistrib；
- 任意固定 s⊆Fin n，且 m=s.card>0；
- 任意 Borel 集 B⊆ℝ；
- 实际精确 fiber Aₛ={ω:retentionSet X B ω=s} 满足 μAₛ≠0；
- 任意固定可测函数 g:ℝ→ℝ。

令 eₛ:Fin m→Fin n 是已有严格递增 retainedIndex。结论为
\[
 \operatorname{map}\left(
   \omega\mapsto(g(X_{e_s(r)}(\omega)))_{r<m},
   \operatorname{cond}(\mu,A_s)\right)
 =
 \bigotimes_{r\in\mathrm{Fin}\,m}
       \operatorname{map}(g,\operatorname{cond}(\nu,B)).
\]
即整条升序变换路径的律等于真实变换后条件边缘律的乘积。结论强于只逐坐标同分布；没有随机长度无条件 iid 断言。没有中心化、矩、截断比例或样本量前提。g 不要求连续或可逆，也不要求有界，但它是一个固定可测函数，不能依赖 ω 或随机保留集。

### 公共定理 2：实际标准化 law 的可积性、矩和 Lyapunov 参数

retainedStandardLaw_moments（130–147 行）量化任意概率实测度 ν、任意自然数 n,j、任意 x∈ℝ，前提精确为
\[
 x\ge2,\quad x^6\le n,\quad j\le x^2/2,\quad
 u\mapsto u^2\in L^1(\nu),\quad
 \int u\,d\nu=0,\quad n\int u^2\,d\nu=1,\quad
 H_x:=n\int F(xu)\,d\nu\le1.
\]
这里 j≤x²/2 使用 Nat j 的实数 cast；Hₓ 是实际 n∫truncationF(xu)，不是 Rₙ(x) 或任意另一截断预算。原全局三阶绝对矩可积不是输入。

令 ζₓ=retainedStandardLaw ν x，m=(n−j:ℕ)，y=√(x²−j)。结论的全部合取为：

1. ζₓ 是概率测度；
2. id、z↦z²、z↦|z|³ 在 ζₓ 下真正可积；
3. ∫z dζₓ=0；
4. ∫z² dζₓ=1；
5. \((\int|z|^3\,d\zeta_x)/\sqrt m\le64/y^3\)。

m 的减法先在 Nat 中完成再转实数。j<n、m>0、y>0、qₓ>0、Vₓ>0 没有作为额外前提输入，须由列明来源条件和旧公开结论推出。最后常数 64 是实际标准化三矩参数界，不是 Gaussian 或 Berry--Esseen 误差界。

### 公共定理 3：原条件弱穿越到 raw product，再到精确标准化事件

retained_cond_upperCrossing_comparison（161–188 行）量化任意概率 μ、ν 及真实可测 iid 同律 X，任意固定 s⊆Fin n、任意 x∈ℝ，除 hX/hIndep/hLaw 外要求：
\[
 x\ge2,\quad x^6\le n,\quad
 j:=n-s.card\le x^2/2,\quad
 u^2\in L^1(\nu),\quad E_\nu u=0,\quad
 nE_\nu u^2=1,\quad H_x\le1,
\]
以及 μA≠0，其中 A={retentionSet X Bₓ=s} 是实际闭 cutoff 的精确 fiber。

设 m=s.card、η=ηₓ、ζ=ζₓ、τₓ=√Vₓ、y=√(x²−j)，Cₘ(y) 表示 upperCrossing hs y，即有某个真正非空前缀 1≤r≤m 满足
\[
 y\sqrt{\sum_{\ell<m}a_\ell^2}\le\sum_{\ell<r}a_\ell.
\]
结论先存在 hn:0<n、hs:0<m，然后断言下列 ENNReal 概率的比较与等式：
\[
 (\operatorname{cond}(\mu,A))\{a(X)\in C_n(x)\}
 \le\eta^{\otimes m}(C_m(y)),
\]
\[
 \eta^{\otimes m}(C_m(y))
 =\zeta^{\otimes m}
   \{a:(\mu_x+\tau_x a_\ell)_{\ell<m}\in C_m(y)\}.
\]
这不是标准化路径自身的弱穿越事件。必须先恢复真实 raw 坐标再取原事件；阈值和 energy 都随这条恢复路径计算。两个非空证明只是导出结论的显式见证，proof irrelevance 保证事件不因证明选择改变。没有 .toReal 相减、隐藏正概率归一化或 Gaussian 比较输入。

## 第二阶段：来源及已有公开接口核对

supplement.tex:82–99 实际给出 Hₓ≤1、x⁶≤n，尾段进一步归约到 x≥8。提案以 x≥2 给出数学上成立的中间桥接；这并未弱化旧预算或换成更强 R 条件。原概率定理适用时 x≥8 当然满足当前范围。

supplement.tex:126–140 的删除引理使用固定坏集 J、j<n、x>0、j<x²，保留路径按原始升序，且弱穿越含平方和为零。已有 Deletion:145–153 正是相同的全路径集合包含式。当前第三定理使用固定坏集 I=sᶜ，而不是把好的 s 本身当作坏集。

supplement.tex:144–162 定义坏集为 |ξᵢ|>1/x，仅考虑正概率固定 fiber 和 j≤x²/2。RetentionEvent 的好集是 |ξᵢ|≤1/x，故 I=sᶜ 精确转换；边界原子 |ξᵢ|=1/x 保留。174–179 行要求保留坐标原顺序及共同条件 law；当前第一定理给出它的完整路径版本，任意 g 是该真实律的可测 pushforward，属于合法自然加强。

RetentionEvent:72–93 的公开定理在 hs>0、hA≠0 下实际给出 νB≠0、真实条件独立性与每个升序保留坐标的条件同分布。FiniteIID:32–43 的公开定理再把一整份实际有限 iid 样本的 map 写成真实 product。二者足以推出第一定理，未用尚未证明的随机保留集无条件 iid。

supplement.tex:187–203 的实际 raw 矩范围对应旧 RetainedMoments/RetainedSample，包含 Hₓ≤1、条件质量、真实二矩、非全局三矩。已接受 RetainedVariance:44–59 给出实际 ηₓ 下中心 id/平方/绝对三次可积、中心均值零、Vₓ=Eηu²−μₓ² 和中心 cube 比较；109–129 进一步给出 Vₓ>0、1/2≤mVₓ≤2；204–222 给出的 Lyapunov 分母精确为 √m·(√Vₓ)³，右端为 64/y³。这与当前标准化后参数完全吻合。

supplement.tex:1075–1084 的 BE 输入是实际中心 cube 除以 τ³√m。当前第二定理构造了这一参数对应的真实标准化 law；它没有给出该段的分布函数不等式、严格 CDF 极限或区间推论。187–209 的源 coarse 证明在乘积事件之后还调用 bounded-random Gaussian 界和 Mills 比较，本提案只到达这些分析结论的真实输入事件，不声称已完成 conditionalcoarse。

main.tex:421–430 使用的是不同 cutoff ε/(1+x) 的 all-good 事件。当前第一定理的任意 B 可以用于它，但第二、三定理固定 Bₓ={|u|≤1/x} 及相应 Hₓ 预算；两者的数值矩界不能自动互换。提案的范围分离正确。

## 第三阶段：三个声明的数学闭合检查

### 1. 任意可测 g 下的完整条件路径律

fiber Aₛ 环境可测由 hX、hB 和既有 measurableSet_retentionSet_eq 给出。μ 概率且 μAₛ≠0，所以真实 cond μ Aₛ 为概率。hs>0 与既有 retained conditional iid 结论推出 νB≠0，因此 cond ν B 也是真概率。

令 Yᵣ=X_{eₛ(r)}、Q=cond μ Aₛ、η_B=cond ν B。已有结论给出 Y 在 Q 下真正 iid、共同律 η_B；完整 FiniteIID path law 给
\[
 \operatorname{map}(Y,Q)=\eta_B^{\otimes m}.
\]
固定坐标映射 G(a)ᵣ=g(aᵣ) 可测；map 的复合及乘积 pushforward 给
\[
 \operatorname{map}(G\circ Y,Q)
 =\operatorname{map}(G,\eta_B^{\otimes m})
 =(\operatorname{map}(g,\eta_B))^{\otimes m}.
\]
全部 mapped marginals 是概率，故所需有限性/σ-有限性可获得。无须 g 的积分或连续性，也没有从条件同分布单独推断独立性的错误。

### 2. 真正标准化 law

旧 size bounds 从 x≥2、x⁶≤n、j≤x²/2 推出 n≥64、j<n、m=n−j≥1 和 y≥1。旧质量界给 qₓ≥1/2>0，使 ηₓ 是真概率；旧 raw/centered 结论给需要的真可积性和 Vₓ>0。因此 τₓ=√Vₓ>0 且 τₓ²=Vₓ，可以在此之后取逆，而不是靠全定义除法制造归一化。

g(u)=(u−μₓ)/τₓ 可测。在 ηₓ 下由中心 id、平方和绝对三次的可积性，经常数缩放得到 g、g²、|g|³ 可积。转到其真实 map ζₓ 后，三种可积性仍成立，实际积分分别为
\[
 E_\zeta Z=\frac{E_\eta(U-\mu_x)}{\tau_x}=0,\qquad
 E_\zeta Z^2=\frac{V_x}{\tau_x^2}=1,\qquad
 E_\zeta|Z|^3=\frac{C_c}{\tau_x^3},
\]
其中 C_c=Eη|U−μₓ|³。τₓ>0 保证绝对值缩放方向正确。故
\[
 \frac{E_\zeta|Z|^3}{\sqrt m}
 =\frac{C_c}{\sqrt m\,\tau_x^3}
 \le\frac{64}{y^3}
\]
就是已接受 Lyapunov 声明，没有增加 Jensen、正方差或全局原三矩假设。这里 integral_map 必须与真可积性配套；没有利用非可积 Bochner integral 的全定义值来虚构标准矩。

### 3. 条件弱穿越概率及标准化事件

先由 s⊆Fin n 得 m=s.card≤n。定义 j=n−m 后，必须在 Nat 中使用 m≤n 得 n−j=m；不能先把未证明的 Nat subtraction 随意换成实数差。旧大小/阈值界于是推出 n≥64、j<n、m≥1、x>0、j<x²、1≤y≤x，并给出所需 hn、hs。

取固定删除集 I=sᶜ。其实际基数为 n−m=j，且 univ\I=s。已有 chronological deletion 对所有原始路径给
\[
 C_n(x)\subseteq
   (\operatorname{retainedPath}(\,\cdot\,,s))^{-1}C_m(y).
\]
在真实 Q=cond μ A 下取测度单调性，再用第一定理 g=id 和 B=Bₓ 的完整 raw 路径律，得到比较式第一部分。该步是概率事件层面的结论；不把 max 逐点分布、坐标同律或条件 iid 的名字当作事件等式替代品。

第一定理再取 g=retainedStandardize ν x，给出同一真实保留路径 Y 标准化后的完整律 ζₓ^{⊗m}。令 R(a)ᵣ=μₓ+τₓaᵣ。已导出的 τₓ≠0 使 R(G(Y))=Y 对所有路径逐点成立。因此
\[
 Q(Y\in C_m(y))
 =Q(G(Y)\in R^{-1}C_m(y))
 =\zeta_x^{\otimes m}(R^{-1}C_m(y)).
\]
这正是第三定理第二部分。R 及 G 的路径映射可测，Cₘ(y) 可测由已有 measurableSet_upperCrossing 给出。链条没有用任何想要证明的尾界、Gaussian 比较或标准化后 iid 作为输入；后者由第一定理导出，故无循环假设。

## 实际恢复事件、能量交叉项与边界

对于 1≤r≤m，确切路径恒等式是
\[
 S_r(Ra)=r\mu_x+\tau_x S_r(a),
\]
\[
 Q_m(Ra)=
   \tau_x^2Q_m(a)+2\mu_x\tau_x S_m(a)+m\mu_x^2.
\]
因此右端事件是存在 1≤r≤m 使
\[
 y\sqrt{\tau_x^2Q_m(a)+2\mu_x\tau_xS_m(a)+m\mu_x^2}
 \le\tau_xS_r(a)+r\mu_x.
\]
提案完整保留了 2μₓτₓSₘ 交叉项、全样本 μₓ²m 和前缀漂移 rμₓ；没有把原始 energy 改成中心 energy、mVar 或 mEZ²，也没有把该事件简化成 Cₘ(y) 关于标准化路径自身的事件。平方根内非负来自它等于实际 raw 平方和，不需要错误地逐项宣称交叉项非负。前缀只用 r≤m，故没有不饱和前缀超出长度的错误。

- 闭 cutoff |u|≤1/x 的边界原子始终保留；坏集是严格 |u|>1/x，且通过 I=sᶜ 精确转换。
- 穿越为弱 ≥，对应非空前缀 1,…,m。完全零 raw 路径仍满足该事件。标准化坐标可以全为 −μₓ/τₓ 而不为零，但 R 恢复后能量仍为零；此分支没有被删去。
- 第一公共定理要求 hs>0；n=0 时不存在这种 s。它不尝试从空保留族推出 νB>0。若 νB=0，则正质量非空保留 fiber 的前提不可能满足；没有条件零质量正常化断言。
- 第二、三定理的 n=0、m=0、Vₓ=0、y=0 都由实际来源前提及已验界排除，而不是额外输入。标准化定义在这些退化处仍是全定义的，但那里没有单位方差结论。
- j=0、s=univ、j=x²/2 的边界均允许；j=0 时 y=x、m=n，不制造阈值余量。
- hA 是固定 fiber 正质量输入；不会把随机保留路径在原 μ 下无条件当作 iid，也不把全体 fiber 同时当作同一个固定长度乘积空间。

## 裁决、实施门槛及未闭合内容

**CORRECT：固定哈希提案的 2 个定义、3 个当前公共声明数学成立，真实条件对象、升序路径、标准化 pushforward、moment 参数与恢复后的原始穿越事件都忠实；无需数学签名修订。**

实现仍须具体完成条件概率实例、νB 非零、路径 map 的复合/乘积换元、积分 pushforward 及各缩放函数真可积性、Nat 基数识别、τₓ 正性和恢复函数逆恒等式。不能将作者 API 探测成功或本轮可证性论证当作实现已获内核认证。此后应仅按授权在服务器进行目标证明检查及传递公理审计。

提案第 7 节另列的 bounded_product_upperCrossing_normal_tail_open_goal 明确是后续开放目标，不计入当前 3 个公共定理，也不是它们的前提。当前桥接不证明 Gaussian 尾界、Petrov BE、strict-CDF/interval BE 推论、Mills 比较、random denominator 的 square tilt/layer sum，或随机删除集的平均与大删除概率界。第二定理的 O(y⁻³) 参数本身不能产生相对 Gaussian 尾精度。当前第三定理只把原条件穿越交给真实 raw product 事件，并给出同一事件的精确标准化表示；完整 conditionalcoarse 与 C1/C2 仍未由此闭合。
