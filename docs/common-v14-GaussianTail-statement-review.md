# GaussianTail 独立声明与来源审查

STATUS: CORRECT（声明阶段）

本报告只审查固定哈希提案的 2 个定义、7 个公共定理签名是否数学成立、是否忠实覆盖所选来源、是否能由真实 Mathlib Gaussian 对象与分析接口闭合。当前没有实现可供证明代码审查。本报告不宣称候选定理已由 Lean 证明、编译或传递公理审计。未运行本机或服务器 Lean，未重复作者 API 探针；只通过指定服务器 broker 读取必要的 Mathlib 源码。没有修改 scope、实现或任何其他文件。

## 冻结绑定和实际来源

- 提案：C:/game/shao lean/drafts/c12/GaussianTail-next-scope.md。
  SHA256：26a01989f5b8169ac37f44f543b3f0312a7e668bd26562e221f64d5c60a6dbef。
- main.tex：C:/game/shao/current/c12/main.tex。
  SHA256：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- supplement.tex：C:/game/shao/current/c12/supplement.tex。
  SHA256：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

上述哈希本轮实际复核。Mathlib 只读路径固定为 /root/rivermind-data/shao-lean-20261021/lean/.lake/packages/mathlib/Mathlib，使用项目已固定版本 807d3836b165983210ee2ecf3cd28f239436949c。作者关于缓存准备和 API #check 成功的叙述不作为候选数学结论的证明。

main.tex:169–171 明确区分 Brownian 绝对最大值尾 H 与标准正态尾 Ψ=Φbar=1−Φ；本候选只定义后者。supplement.tex:1027–1029 的 Mills 范围是 z≥0；205–211 用于删除阈值 y=√(x²−j)；1369–1377 用于实际 denominator layers。main.tex:457–465 只考虑正 t 的相邻阈值；807–814 再次说明 positive neighboring t，且 t≤0 的误差另为零。拟议局部定理的非负端点范围与这些消费点相容。

## 第一阶段：两个实际定义和全部量词重译

### 定义

1. standardNormalDensity(x)=ProbabilityTheory.gaussianPDFReal 0 1 x，定义域为所有 x∈ℝ。这里 1 的类型是 NNReal，含义是方差一。由真实库定义，
   \[
   \phi(x)=\frac1{\sqrt{2\pi}}e^{-x^2/2}.
   \]
   未引入匿名归一化因子或具有指定性质的代理 density。
2. standardNormalTail(x)=((gaussianReal 0 1)(Ioi x)).toReal，定义域同样是全实数。它是同一实际概率测度的严格尾质量实值，不是先指定 CDF、Mills 或导数后命名出的抽象函数。Ioi 是严格 >x；后续弱尾等式必须使用该 Gaussian 的无原子性。

### 七条公开定理

1. **standardNormalTail_representation(x)。** 对每个实数 x，无附加前提，同时断言
   \[
   \Psi(x)=\gamma([x,\infty)),\qquad
   \Psi(x)=1-\operatorname{cdf}(\gamma)(x),\qquad
   \Psi(x)=\int_{(x,\infty)}\phi(a)\,da,
   \]
   其中 γ=gaussianReal 0 1，两个测度质量取实值。最后积分是实 Lebesgue volume，不是 γ 下的密度再积分。没有关于原样本增量无原子的前提或结论。
2. **standardNormalTail_basic。** 一个无参数定理同时给出：全实数上的 Antitone Ψ；Ψ(0)=1/2；对所有有限实数 x 都有 0<Ψ(x)<1；对所有 x 都有 Ψ(−x)=1−Ψ(x)。签名给的是非严格 antitone，未暗加严格单调作为输入。负阈值和零阈值保持真实 Gaussian 值。
3. **standardNormal_derivatives(x)。** 对每个实数 x，无附加前提，
   \[
   \phi'(x)=-x\phi(x),\qquad \Psi'(x)=-\phi(x)
   \]
   都以 HasDerivAt 形式给出。没有让调用者提供可积性、密度可微或尾连续性假设。
4. **standardNormal_mills_bounds(x,hx)。** 仅在 x≥0，断言
   \[
   \frac{\phi(x)}{1+x}\le\Psi(x)
   \le\frac43\frac{\phi(x)}{1+x},\qquad
   \frac{\phi(x)}{\Psi(x)}\le1+x.
   \]
   包含 x=0，不除以 x。Mills 形式不在 x<0、尤其不在极点 x=−1 声称成立。所有常数固定且与阈值无关。
5. **standardNormalTail_ratio_bound(x,y,hx,hy)。** 对任意非负实数 x,y，不要求次序，
   \[
   \Psi(y)\le\frac43\frac{1+x}{1+y}
       e^{(x^2-y^2)/2}\Psi(x).
   \]
   结论没有除以尾概率；两个线性分母在真实量词域严格正。
6. **standardNormalTail_local_comparison(x,t,hx,ht,hneigh)。** x≥0、t≥0 且 |t−x|≤1/(1+x) 时，
   \[
   e^{-2}\Psi(x)\le\Psi(t)\le e^2\Psi(x).
   \]
   允许一个端点为零；不声称覆盖负 t。没有输入预算比较、样本误差或 Gaussian approximation。
7. **standardNormalTail_deletion_comparison(j,x,hx,hj)。** 任意 j∈ℕ、实 x≥0，假设 (j:ℝ)≤x²/2，断言
   \[
   \Psi(\sqrt{x^2-j})\le3e^{j/2}\Psi(x).
   \]
   j 的实数值是 Nat cast，不存在 n−j 之类未证合法的自然减法。没有样本长度、j<n、原始矩、条件方差或非空路径前提；这是纯 Gaussian/数值结论。x=0、j=0 和 hj 取等都允许。

## 第二阶段：真实库对象与 API 核对

本轮服务器只读 Mathlib 源得到以下精确信息：

- Probability/Distributions/Gaussian/Real.lean:47–52 的 gaussianPDFReal 定义是 (√(2πv))⁻¹ exp(−(x−μ)²/(2v))，μ 是实均值、v 是 NNReal 方差。故 μ=0、v=1 确为所列实际标准 density。
- 同文件 60–68 的 pointwise positivity 要求 v≠0；89–108 给实际全局 density 可积性；128–133 给非零方差时实际积分为一。标准方差一满足全部条件，不需要新增 Gaussian integral 假设。
- 220–235 的 gaussianReal 在 v≠0 时是真实 volume.withDensity；库提供 probability instance 和需要 v≠0 的 NullSingletonClass。这里只对真实 Gaussian 应用无原子桥，没有假设或改变原始离散增量事件。
- 245–250 的 gaussianReal_apply_eq_integral 将实际集合质量写成 ENNReal.ofReal 的 density set integral，证明本身使用全局可积性和 density 非负性。取 toReal 时仍须明确使用积分非负性与真实有限质量，而非无条件消掉 ofReal。
- 358–359 的 gaussianReal_map_neg 给真实分布反射，在均值零时回到同一 law。
- Probability/CDF.lean:56–57 的 cdf 是库的实际 StieltjesFunction；81–82 在概率前提下确为 γ.real(Iic x)。因此 Ioi x 是 Iic x 的精确补集，严格尾=1−cdf；Ici x=Ioi x 加 singleton 的弱尾桥另由 Gaussian 原子为零完成。
- Integral/IntegralEqImproper.lean:811–816 的 integral_Ioi_of_hasDerivAt_of_tendsto' 要求在 Ici x 上的真实 HasDerivAt、导函数在 Ioi x 上真可积，以及函数 atTop 的实际有限极限；结论为半线导数积分=极限−端点值。提案的 FTC 步没有可忽略这些前提的特殊接口。

由此，真实概率、积分与 CDF 对象和拟议定义一致。没有用一个仅具有相同方差或相同形式符号的代理 law 替换 Gaussian。

## 第三阶段：声明数学闭合性检查

此处是独立可证性论证，不是尚不存在的 Lean 代码证明审查。

### 严格/弱尾、CDF、正性与反射

γ 是方差一概率 measure，单点质量为零。Ici x 与 Ioi x 只差 {x}，故两尾相等。Ioi x 是 Iic x 的补集；真实概率质量和 cdf_eq_real 得 Ψ=1−cdf。真实 set-integral identity、可积性与 φ≥0 给 Lebesgue density 表示。

对任意有限实数 x，连续严格正 φ 在 (x,x+1) 上给正质量，从而 Ψ(x)>0；在 (x−1,x) 上给正补集质量，从而 Ψ(x)<1。所有严格不等式均在有限阈值，不把 ±∞ 当成实阈值。尾集合包含给 Antitone。Gaussian negation law 把尾反射为另一侧半线，再以单点零质量识别得到 Ψ(−x)=1−Ψ(x)；令 x=0 得半值。

这些步骤合法覆盖 x<0。结合正密度还能得到严格减少，因此 x<0 时 Ψ(x)>1/2，但当前 basic 的接口不必额外公开 StrictAnti，也没有假设它。

### 全实导数，含负 x 的正确有向积分

从真实 φ 的显式指数公式直接微分得 φ′=−xφ，所有实 x 均成立。全局 φ 真可积且连续，半线积分表示给
\[
 \Psi(x)=\Psi(0)-\int_0^x\phi(t)\,dt,
\]
其中 x<0 时必须使用有向 interval integral；不能把负端点积分错当空集。相应局部 FTC-1 得 Ψ′=−φ。全局可积性保证半线分割与有限区间积分运算真实有效，不使用非可积 Bochner integral 的默认值。

实际指数公式还给 φ(t)→0（t→+∞）。此 limit 是后续证明需要证明的具体初等极限，不是新公理或调用者前提。

### 新的 weighted primitive 确实推出两个 Mills 常数

仅在 proof 内令
\[
 F(t)=\frac{\phi(t)}{1+t},\qquad
 A(t)=\frac{t^2+t+1}{(1+t)^2}.
\]
对 t≥0，1+t>0，由真实 density 导数计算
\[
 F'(t)=-\phi(t)A(t).
\]
提案所列两条 polynomial identity 正确：
\[
 (1+t)^2-(t^2+t+1)=t,\qquad
 4(t^2+t+1)-3(1+t)^2=(t-1)^2.
\]
分母正，因此 3/4≤A(t)≤1。对固定 x≥0，Ioi x 内始终在该域；φ≥0 给
\[
 |\phi A|\le\phi.
\]
加上函数可测性和真实 φ 的全局可积性，导数 −φA 在 Ioi x 下真正可积。F 在 Ici x 全部可微，特别在有限端点连续；当 t→∞ 时 0≤F(t)≤φ(t)（最终 t≥0），故 F(t)→0。它不经过 t=−1 的极点，也没有用“F 有极限”替代实际 limit 值。

所以真实半线 FTC 可以合法给出
\[
 \int_x^\infty(-\phi A)=-F(x),\qquad
 F(x)=\int_x^\infty\phi A.
\]
全部 integrable_mono 比较的两边可积，由 3/4≤A≤1 得
\[
 \tfrac34\Psi(x)\le F(x)\le\Psi(x).
\]
这精确等价于拟议下、上 Mills 界；上界常数是 4/3，不是遗漏倒数的 3/4。x=0 原样成立。再用 Ψ(x)>0、1+x>0，从 F≤Ψ 合法移项并除以真实尾，得到 hazard φ/Ψ≤1+x。没有提前假设 Mills 或 hazard。

### 任意非负阈值尾比

实际密度满足对所有实 x,y 的精确恒等式
\[
 \phi(y)=e^{(x^2-y^2)/2}\phi(x).
\]
在 y≥0 用上 Mills，在 x≥0 用下 Mills，所有乘数和线性分母正，直接得到所列比界。无需 x≤y 或 y≤x；指数为负的情况也由同一恒等式处理。

### 非负局部双边 e²

全实正尾和真实导数使 log Ψ 在每个有限实点可微。在非负 s 上，
\[
 |(\log\Psi)'(s)|=\phi(s)/\Psi(s)\le1+s.
\]
令 δ=|t−x|。连接两个非负端点的区间全在 s≥0，而且 s≤x+δ。由真实导数/mean-value bound，
\[
 |\log\Psi(t)-\log\Psi(x)|
 \le(1+x+\delta)\delta.
\]
邻域条件及 1+x≥1 给 (1+x)δ≤1、δ≤1，故右端≤1+δ²≤2。指数化并利用真实尾严格正，得到双边 e²。没有在零尾上取 log；x=0 或 t=0 也不存在导数奇点。该结果足够给源较松 e⁴ 权重因子，但单独不包含预算比较的 factor eight 或样本误差估计。

### 删除阈值、零端点与 Nat/Real 识别

设 J=(j:ℝ)≥0，y=√(x²−J)。由 J≤x²/2 得 x²−J≥x²/2≥0，所以 y²=x²−J。x≥0、y≥0 下平方比较给 y≥x/2；更强 y≥x/√2 也真，但并非使用常数三所必需。因此
\[
 \frac{1+x}{1+y}\le2,\qquad
 \frac{x^2-y^2}{2}=\frac J2.
\]
代入通用尾比，系数至多 (4/3)·2=8/3≤3，得到声明。没有除以 x、j 或 y，也不需要样本非空或 j<n。

当 x=0，hj 和 J≥0 强制 J=0，进而 Nat j=0；两端是真实半尾值，结论成立。j=0 时 y=|x|=x；hj 等号时 y=x/√2。所有转换都是显式 Nat cast 的非负性、实平方和 sqrt 非负分支，不涉及未证成立的 Nat subtraction。

## 来源忠实度与最终裁决

Mills 常数给 source exp(−x²/2)/(1+x) 的真实 c,C，分别为 1/√(2π)、4/(3√(2π))，均严格正且与参数无关；不把源未指定的常数误称其最优常数。hazard≤1+x 蕴含 main:809 的较松 x+4。局部比较覆盖 main:457 和 807 所用的正邻域；main:814 的 t≤0 误差 convention 没有被拿来重新定义 Gaussian 负尾。

通用尾比覆盖非负层阈值所需 deterministic comparison；删除阈值 bound 对应 supplement:209–211，但仍必须先有实际 bounded-random 概率界，才能组合得到原条件样本尾界。本候选没有将 Brownian 绝对最大值 H 等同 Ψ，也没有借任何样本 Gaussian approximation 假设证明这些固定 law 性质。

**CORRECT：固定哈希提案的 2 定义、7 定理均数学正确，来源域、参数、严格/弱桥和常数均合适，无需数学签名修订。**

未来实现须具体完成实际 density 可积性和有限性转化、singleton-null 的严格/弱桥、有向积分的负端点、weighted derivative 在真实半线上的可积性、F 的实际零极限、正尾下 log/除法及合法 sqrt 分支。当前 API 缓存或名称可用不代替这些证明；本报告未宣称候选定理已通过内核。

本单元不闭合 BE/CLT、bounded-random 或 bounded-endpoint 样本比较、Mills 以外的 tilted moment transfer、random denominator 分层、随机删除集平均、Brownian 最大值、clock/Fourier 比较或完整 C1/C2。RetainedComparison 加本候选仍缺 raw product crossing 的 Gaussian 尾概率定理。
