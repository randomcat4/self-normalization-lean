# 完整有限正弦基与真实一步核

STATUS: PROVED
SCOPE: 冻结接口 v1 的 B0–B3；仅数学证明。

## 1. 固定对象、指标与所用基本事实

固定任意自然数 \(m\geq1\)。记
\[
 H_N=m+1,\qquad H_Z=(m:\mathbb Z)+1,\qquad H=(m:\mathbb R)+1,
 \qquad L=2H_N,\qquad N=L-1=2m+1.
\]
自然数或整数出现在实数三角表达式时，均作通常的实数嵌入；因此实数意义下 \(L=2H\)。特别地 \(H>0\) 且 \(L\geq4\)。以下 \(I=I_m\)、\(J=J_m\)，即
\[
 I=\{-m,-m+1,\ldots,m\}\subset\mathbb Z,
 \qquad J=\{1,2,\ldots,L-1\}\subset\mathbb N.
\]
所有和都是未归一化有限和。

固定的已认证定义给出
\[
 a=\operatorname{RademacherCosine.angle}(m)=\frac\pi{2H}=\frac\pi L,
 \qquad \operatorname{RademacherCosine.rho}(m)=\cos a,
\]
以及真实概率律
\[
 \nu_R=\tfrac12\delta_1+\tfrac12\delta_{-1}.
\]
这里的两个 \(1/2\) 是有限的测度权重，作为实数积分系数时就是实数 \(1/2\)。按冻结定义，
\[
 \theta_j=ja=\frac{j\pi}{L},\quad \mu_j=\cos\theta_j,
 \quad \varphi_j(w)=\sin\bigl(\theta_j(w+H)\bigr),
 \quad v_j(s)=\varphi_j(s).
 \tag{1}
\]

有限指标转换将明确使用下列互逆双射。对 \(s\in I\)，整数 \(s+H_Z\) 满足
\[
 1=-m+H_Z\leq s+H_Z\leq m+H_Z=2m+1=L-1.
\]
令 \(Q(s)\in J\) 为这个正整数对应的自然数。反过来，对 \(q\in J\) 令
\[
 b(q)=(q:\mathbb Z)-H_Z.
\]
由 \(1\leq q\leq2m+1\)，得到 \(-m\leq b(q)\leq m\)，故 \(b(q)\in I\)。整数加减直接给出
\[
 b(Q(s))=s,\qquad Q(b(q))=q.
 \tag{2}
\]
于是两集合各有 \(L-1=2m+1\) 个元素；并且 (1) 在此转换下成为
\[
 v_j(b(q))=\sin\frac{j\pi q}{L},\qquad
 v_j(s)=\sin\frac{j\pi Q(s)}{L}.
 \tag{3}
\]

以下使用的基本常识定理仅为：实三角函数的加法公式、
\(\sin(n\pi)=0\)、\(\cos(n\pi)=1\)（\(n\) 偶）及 \(-1\)（\(n\) 奇）、
\(\sin x=0\iff x\in\pi\mathbb Z\)，连续实函数的可测性，以及有限原子测度的积分规则。所有需要的具体有限求和、完备关系及吸收端点身份均在下文证明。特别地不使用任何未证明的特征关系或完备性结论。

## 2. B0：首模态在全实轴上的兼容性

由 (1) 和 \(1\cdot a=a\)，有
\[
 \theta_1=a=\operatorname{RademacherCosine.angle}(m),
 \qquad \mu_1=\cos a=\operatorname{RademacherCosine.rho}(m).
\]
由于 \(H>0\)，\(aH=\pi/2\)。故对任意实数 \(w\)，
\[
 \varphi_1(w)
 =\sin(a(w+H))
 =\sin(aw+\pi/2)
 =\cos(aw).
 \tag{4}
\]
这是全实轴恒等式，并未限制 \(w\) 为整数，证明 B0。

## 3. 一个具体有限余弦和

对整数 \(n\) 定义
\[
 C(n)=\sum_{q=1}^{L-1}\cos\frac{n\pi q}{L}.
\]
直接数项得
\[
 C(0)=L-1.
 \tag{5}
\]
现设 \(0<|n|<2L\)。令 \(x=n\pi/L\) 及 \(t=x/2\)，则
\(0<|t|<\pi\)，所以 \(\sin t\ne0\)。由正弦加法公式，逐项有
\[
 2\sin t\cos(qx)
 =\sin((q+\tfrac12)x)-\sin((q-\tfrac12)x).
\]

对 \(q=1,\ldots,L-1\) 求和，中间项逐项消去：
\[
 2\sin t\,C(n)
 =\sin((L-\tfrac12)x)-\sin(x/2)
 =\sin(n\pi-t)-\sin t.
\]
又因 \(\sin(n\pi)=0\)，
\[
 \sin(n\pi-t)=-\cos(n\pi)\sin t.
\]
除以非零的 \(2\sin t\) 得
\[
 C(n)=-\frac{\cos(n\pi)+1}{2}
 =\begin{cases}
 -1,&n\text{ 为非零偶数},\\
 0,&n\text{ 为奇数}.
 \end{cases}
 \qquad(0<|n|<2L).
 \tag{6}
\]
这个证明同时包含负整数 \(n\)，没有用正指标代替差指标。

## 4. B1：完整正交关系及精确范数

取任意 \(j,k\in J\)。由 (2)–(3) 对状态求和重编号，再用由余弦加法公式推出的积化和差式，得到
\[
 \begin{aligned}
 \sum_{s\in I}v_j(s)v_k(s)
 &=\sum_{q=1}^{L-1}
      \sin\frac{j\pi q}{L}\sin\frac{k\pi q}{L}\\
 &=\frac12\sum_{q=1}^{L-1}
      \left(\cos\frac{(j-k)\pi q}{L}
                  -\cos\frac{(j+k)\pi q}{L}\right)\\
 &=\tfrac12\bigl(C(j-k)-C(j+k)\bigr).
 \end{aligned}
 \tag{7}
\]
若 \(j=k\)，则 \(j-k=0\)，而 \(2\leq j+k=2j\leq2L-2<2L\) 是非零偶数。因此 (5)–(6) 给出
\[
 \sum_{s\in I}v_j(s)^2
 =\tfrac12((L-1)-(-1))=L/2=H.
 \tag{8}
\]
若 \(j\ne k\)，则 \(0<|j-k|\leq L-2<2L\)，且
\(0<j+k\leq2L-2<2L\)。两个整数 \(j-k\)、\(j+k\) 的差为 \(2k\)，故奇偶性相同。它们若均为偶数，(6) 给两项均为 \(-1\)；若均为奇数，(6) 给两项均为 \(0\)。两种情况中 (7) 都等于零。因此
\[
 \sum_{s\in I}v_j(s)v_k(s)
 =\begin{cases}H,&j=k,\\0,&j\ne k.\end{cases}
 \tag{9}
\]
尤其由 \(H>0\)，每一个模态的平方范数严格为 \(H\)，证明 B1。

## 5. B2：对偶恒等式与显式系数重建

先证明对所有 \(r,s\in I\) 的对偶恒等式，不把“正交”直接当作“完备”。设
\[
 p=Q(r)\in J,\qquad q=Q(s)\in J.
\]
由 (2)，\(p=q\iff r=s\)。对任意模态指标 \(j\in J\)，(3) 和实数乘法交换律给出
\[
 v_j(r)=\sin\frac{j\pi p}{L}=\sin\frac{p\pi j}{L}=v_p(b(j)),
 \qquad
 v_j(s)=v_q(b(j)).
 \tag{10}
\]
在 (10) 上对 \(j\in J\) 求和，利用 \(b:J\to I\) 的双射性质及已经证明的 (9)，得到
\[
 \begin{aligned}
 \sum_{j\in J}v_j(r)v_j(s)
 &=\sum_{j\in J}v_p(b(j))v_q(b(j))\\
 &=\sum_{t\in I}v_p(t)v_q(t)\\
 &=\begin{cases}H,&p=q,\\0,&p\ne q\end{cases}
 =\begin{cases}H,&r=s,\\0,&r\ne s.\end{cases}
 \end{aligned}
 \tag{11}
\]
这证明了所需的对偶关系，并且具体说明了从原正交求和到模式求和的全部重编号；没有假定任何矩阵可逆性或基的存在。除以 \(H>0\)，即
\[
 \frac1H\sum_{j\in J}v_j(r)v_j(s)=\boldsymbol1_{\{r=s\}}.
 \tag{12}
\]

现在固定任意函数 \(F:\mathbb Z\to\mathbb R\)，不对它作其他假设。按冻结定义
\[
 c_j(F)=\frac1H\sum_{s\in I}F(s)v_j(s).
\]
对任意 \(r\in I\)，分配律及两个有限和的交换给出
\[
 \begin{aligned}
 \sum_{j\in J}c_j(F)v_j(r)
 &=\frac1H\sum_{j\in J}\sum_{s\in I}
                 F(s)v_j(s)v_j(r)\\
 &=\sum_{s\in I}F(s)
          \left(\frac1H\sum_{j\in J}v_j(s)v_j(r)\right)\\
 &=\sum_{s\in I}F(s)\boldsymbol1_{\{s=r\}}\\
 &=F(r).
 \end{aligned}
 \tag{13}
\]
最后一步中，因 \(r\in I\)，恰有一项 \(s=r\) 保留。式 (13) 就是 B2 的指定重建式；系数恰为 \(1/H\)，而且从头到尾只使用 \(F\) 在 \(I\) 上的有限多个值。

## 6. B3：真实核的原子行与真正可积性

固定任意实数 \(h\) 满足 \(m\leq h<m+1\)，再固定任意 \(r\in I\) 及 \(j\in J\)。记真实核行
\[
 K_{h,r}=\operatorname{killedKernel}\nu_R\,h\,(r:\mathbb R).
\]
先明确这一真实测度。对任意整数 \(t\)，
\[
 |(t:\mathbb R)|\leq h\quad\Longleftrightarrow\quad |t|\leq m.
 \tag{14}
\]
正向蕴含：若整数 \(|t|\) 不满足 \(|t|\leq m\)，则 \(|t|\geq m+1>h\)，矛盾。反向蕴含直接由 \(m\leq h\) 得到。因此 (14) 包含 \(h=m\) 的闭端点。

实际 killedKernel 是 \(y\mapsto r+y\) 对 \(\nu_R\) 的推前测度在闭区间 \([-h,h]\) 上的限制。因此，对任意 Borel 集 \(A\subset\mathbb R\)，由固定的两原子概率律可直接计算
\[
 \begin{aligned}
 K_{h,r}(A)
 &=\tfrac12\boldsymbol1_{\{|r+1|\leq m\}}
                     \boldsymbol1_A((r+1):\mathbb R)\\
 &\quad+\tfrac12\boldsymbol1_{\{|r-1|\leq m\}}
                     \boldsymbol1_A((r-1):\mathbb R).
 \end{aligned}
\]
这里已用 (14) 将真实闭条带限制精确换成整数条件。这也是已认证公开接口 RademacherCosine.killedKernel_row 的内容。设
\(\epsilon_\pm=\boldsymbol1_{\{|r\pm1|\leq m\}}\in\{0,1\}\)，则实际测度等式为
\[
 K_{h,r}=\tfrac{\epsilon_+}{2}\delta_{(r+1):\mathbb R}
        +\tfrac{\epsilon_-}{2}\delta_{(r-1):\mathbb R}.
 \tag{15}
\]
这不是新的转移矩阵，(15) 中的行就是待积分的真实 killedKernel；其总质量为 \((\epsilon_++\epsilon_-)/2\leq1\)。

为证明真正可积，注意 (1) 是连续实函数，因而 Borel 可测，并且
\(|\varphi_j(w)|\leq1\) 对所有实数 \(w\) 成立。对一个有限原子测度 \(\alpha\delta_x+\beta\delta_y\)，其中 \(\alpha,\beta\geq0\) 均有限，标准 Dirac 积分规则给出任意非负可测函数 \(g\) 的扩展非负积分
\[
 \int g\,d(\alpha\delta_x+\beta\delta_y)=\alpha g(x)+\beta g(y).
\]
这是 Dirac 测度对可测简单函数的定义，先对指示函数逐项验证、再由非负简单函数单调逼近得到；故不需要先假定所积函数可积。将此规则用于 (15) 及 \(g=|\varphi_j|\)，得到
\[
 \int |\varphi_j(w)|\,dK_{h,r}(w)
 =\tfrac{\epsilon_+}{2}|\varphi_j(r+1)|
  +\tfrac{\epsilon_-}{2}|\varphi_j(r-1)|
 \leq\tfrac{\epsilon_++\epsilon_-}{2}\leq1<\infty.
 \tag{16}
\]
实值 Borel 可测函数的绝对值积分有限，即为其 Lebesgue/Bochner 可积性；因此 (16) 确实证明
\[
 \operatorname{Integrable}(\varphi_j,K_{h,r}).
 \tag{17}
\]
由可积函数在有限原子测度下的积分规则（也可对正负部应用上面的非负规则再相减），有真正的实积分
\[
 \int\varphi_j(w)\,dK_{h,r}(w)
 =\tfrac12\epsilon_+\varphi_j(r+1)
  +\tfrac12\epsilon_-\varphi_j(r-1).
 \tag{18}
\]

## 7. B3：两个吸收点与全部频率的一步身份

对任意自然数 \(j\)，由 (1) 得
\[
 \varphi_j(-H)=\sin0=0,
 \qquad
 \varphi_j(H)=\sin(2H\theta_j)=\sin(j\pi)=0.
 \tag{19}
\]
这里的 \(\pm H\) 正是整数吸收位置 \(\pm H_Z\) 的实数嵌入。

由 \(-m\leq r\leq m\)，两个相邻整数 \(t=r+1\)、\(t=r-1\) 都满足
\(-H_Z\leq t\leq H_Z\)。对任意这样一个 \(t\)，若 \(|t|\leq m\)，其指示系数为一；若 \(|t|\not\leq m\)，整数性和 \(|t|\leq m+1\) 给出 \(|t|=m+1\)，故 \(t=H_Z\) 或 \(t=-H_Z\)，于是 (19) 给 \(\varphi_j(t)=0\)。这两种情况共同证明
\[
 \boldsymbol1_{\{|t|\leq m\}}\varphi_j(t)=\varphi_j(t)
 \quad\text{对 }t=r+1,r-1\text{ 均成立}.
 \tag{20}
\]
所以 (18) 中删除的实际核质量恰乘在零值上，而非被重新分配给存活点；由 (20)，
\[
 \int\varphi_j(w)\,dK_{h,r}(w)
 =\tfrac12\bigl(\varphi_j(r+1)+\varphi_j(r-1)\bigr).
 \tag{21}
\]
令 \(A=\theta_j(r+H)\)。对两项分别展开正弦加法公式，得到
\[
 \begin{aligned}
 \varphi_j(r+1)+\varphi_j(r-1)
 &=\sin(A+\theta_j)+\sin(A-\theta_j)\\
 &=2\sin A\cos\theta_j.
 \end{aligned}
\]
代入 (21) 及 (1)，即
\[
 \int_{\mathbb R}\varphi_j(w)\,
      d\operatorname{killedKernel}\nu_R\,h\,(r:\mathbb R)(w)
 =\cos\theta_j\,\sin(\theta_j(r+H))
 =\mu_j v_j(r).
 \tag{22}
\]
联同 (17)，这正是 B3 的两个结论。

为明确闭边界的质量，若 \(r=m\)，则 (15) 为
\(K_{h,m}=\tfrac12\delta_{m-1}\)，因为向外点 \(m+1=H_Z\) 被杀死，而向内点满足 \(|m-1|\leq m\)。若 \(r=-m\)，则
\(K_{h,-m}=\tfrac12\delta_{-m+1}\)。这两行质量均为 \(1/2\)，包括 \(h=m\)；(19)–(22) 对它们逐项成立。

最后，证明中所有 \(j,k\) 始终遍历整个 \(J=\{1,\ldots,2H_N-1\}\)。其中 \(j=H_N\) 给 \(\theta_j=\pi/2\)、\(\mu_j=0\)，而 \(H_N<j\leq2H_N-1\) 给 \(\pi/2<\theta_j<\pi\)、\(\mu_j<0\)。任何一步都没有除以 \(\mu_j\)、要求其正性或按奇偶删去模态，所以这些零、负模态以及最后一个模态都已被 B1、B2、B3 完整覆盖。固定的 \(m,h,r,j,k,F\) 均为各自量词允许的任意对象，故 B0–B3 的全部量词成立。
