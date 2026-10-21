# U7 独立声明与来源审查

## 第一阶段：仅 Lean 代码块盲译冻结

本节在读取 scope 解释、真实 R1、Mathlib 实际定义或作者笔记之前落盘。只读取 `thirteenth-unit-scope.md` 的 Lean 代码块；实测 SHA256=`0fd62d524bbe643f076f153b9b7a898b5eb34d756fc631c483ded0508ed44ee8`。三定义、十二目标，尚无实现或本单元机械认证。

三个定义的独立翻译：

- `parabolaCovariance μ` 是2×2实矩阵，两个对角元分别为库的 variance(X)、variance(X²)，两个非对角元同为库的 covariance(X,X²)。X(x)=x。尚须核对这些库对象何时确实等于有限二阶矩公式。
- `normalVariance μ` 是库的 variance(normalValue)，不是该方差的平方根。
- `transverseVariance μ = det(parabolaCovariance μ)/normalVariance μ`，为实数全定义商；尚不自动具有正性或实际横向方差含义。

十二目标签名的独立数学翻译：

1. 对概率μ，若AE有统一紧绝对值上界，则任意实a,b的居中 `(a(X−EX)+b(X²−EX²))²` 的实际积分，等于上述实际矩阵的二次型 `a²Δ00+2abΔ01+b²Δ11`。
2. 相同概率/支撑门，加四个baseAtom的实际单点实质量都>0，则对任意至少一个系数非零的(a,b)，上述实际居中平方积分严格正。
3. 相同门下矩阵行列式严格正；不是仅假定一个任意实矩阵det>0。
4. 概率与紧支撑门下，normalVariance等于 `64Δ00−16Δ01+Δ11`。
5. 再加四旧原子正质量，normalVariance严格正。
6. 同样门下transverseVariance严格正。
7. 同样门下transverseVariance≤库的variance(X)。
8. 对非负w与四个真实HasSum约束，atomicMeasure(w)下variance(X)=q−q²/16。没有全w严格正门。
9. 固定sourceEll<1/30。
10. 对q∈(1,103/100)、非负w、四旧索引权重严格正及sourceEll四HasSum，atomicMeasure(w)的transverseVariance>0、≤q−q²/16，并且 `1/30 < q/(32·transverseVariance)`。
11. 同一门下 `normalVariance/detΔ−32 sourceEll/q>0`。
12. 存在同一p>0、q∈(1,103/100)、eps>0与source矩阵方程，使其后每条正可和且总量<eps的完整r，同时给极限π及全部有限π_J的真概率、normalVariance>0、detΔ>0和第11项的正曲率表达式。p/q/eps先于r/J固定；此最终声明作用于atomicMeasure（π），不是originalMeasure（P）。

盲译阶段尚未将正二次型、实际协方差、σ²与τ²作源对应，也未确认所有多项式实际可积与L²条件。特别不能将transverseVariance误读成τ、以实方差总化toReal值代替真实二阶矩，或把正熵/正曲率升级成全局鞍点唯一性。

## 第二阶段：真实来源及固定 Mathlib 实际定义

盲译落盘后才完整读取scope解释、真实只读R1 238–258，并经指定服务器共享只读通道核对固定Mathlib源码。R1实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。未读作者API/notes/frontier；没有实施U7或运行任何Lean构建。

固定manifest的mathlib revision实测仍为 `807d3836b165983210ee2ecf3cd28f239436949c`。实际读取的两个库源位于该服务器共享mathlib checkout：

- `Mathlib/Probability/Moments/Covariance.lean`，SHA256=`7f261bcecb104697357f2c51f1c66154153236f3266264ba7c5dd7b8519665fd`。
- `Mathlib/Probability/Moments/Variance.lean`，SHA256=`0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e`。

实际 `covariance`（44–45）直接定义为 `∫(X−∫X)(Y−∫Y)dμ`。实际 `evariance`（58）是居中实函数扩展范数平方的lintegral，`variance`（64）为其toReal。`variance_of_not_memLp`（134–136）明确显示不在L²时实方差可被总化成0，确有需要排除的风险。`variance_eq_integral`（157–159）在AE可测门下把该全定义值写为总化实平方积分；这一等式本身也不能替代真实可积性。实际 `covariance_eq_sub`（54–55）要求概率性与两函数MemLp2；实际 `variance_eq_sub`（226–228）同样明确要求MemLp2。

| R1锚点 | 当前定义/目标准确对应 |
| --- | --- |
| 239–241 | Δ是真实倾斜律π下(X,X²)的协方差。第1目标绑定实际居中平方积分与矩阵二次型，第2目标对全非零(a,b)给严格正，合起来表达真实正定性；第3条det>0是后果。 |
| 243–245 | normalVariance=σ²=Var(Y)；transverseVariance=detΔ/σ²=τ²。目标没有把τ²再平方或误作τ，也未冒称已经建立κ的独立对象。 |
| 247 | 目标7/8/10分别给τ²≤Var(X)、原子约束下Var(X)=q−q²/16以及两者组合。 |
| 249–250 | 正确分母是32τ²；目标10保留严格的1/30下界，目标9独立给sourceEll<1/30，常数与源一致。 |
| 252–254 | 目标11正是Λ1=σ²/detΔ−32ℓ/q>0，不缺平方或倒数。 |
| 256–258 | 最终族同时覆盖全部有限阶段与极限的π，使用同一p/q/eps；未新输出v_corr或源第3节全局极小性。 |

## 全部目标的独立数学与边界核查

### 真实可积与 L² 不是可选实现细节

令β=4+√10。概率μ及hb给AE |x|≤β；恒等函数、平方、Y、各个居中线性/二次式及其乘积均连续，在紧区间[−β,β]上有有限界。因此需要的所有次数≤4的多项式实际Bochner可积，X、X²、Y及居中二次式实际属于L²；协方差乘积也真实可积。evariance的相应非负平方积分被有限常数控制，故不是∞，toReal不会从∞塌成0。所有均值和二阶矩均为真实有限期望。

对atomic_id_variance的较弱前提也足够：hm0给HasSum w1，hw≥0给π真概率，既有atomicMeasure_ae_bounds给同一紧界，因而同样取得MemLp2和真实矩。ℓ任意实数没有问题，因为这些可积性只依赖实际支撑及概率质量。

### 实际正二次型、Delta 与 sigma²

记m1=EX、m2=EX²，A=Var(X)、B=Cov(X,X²)、C=Var(X²)。实际定义与上述可积性给

```text
E[(a(X−m1)+b(X²−m2))²] = a²A+2abB+b²C。
```

这里左边是平方的期望，不是均值的平方；中间交叉项是实际库covariance定义。两个非对角元素同时写B，正是实协方差的对称矩阵。因此目标1不是对一个任意矩阵强加代数名字。

为证明目标2，设F(x)=a(x−m1)+b(x²−m2)。F²非负且真实可积；若其积分为0，则F=0几乎处处。每个实际正单点质量使该AE等式在该点精确成立：否则该singleton位于零测异常集，与hbase矛盾。特别在旧点−1、1、2均有F=0；两次相减得

```text
F(1)−F(−1)=2a=0，F(2)−F(1)=a+3b=0，
```

所以a=b=0，矛盾于hne。只用这三个旧点已足够；第四点正质量是与源一致的较强门，不引入缺口。这等价于提升到抛物线上的三点不共线，不能仅以X值不同取代论证。

先用(a,b)=(1,0)得A>0，再用(a,b)=(−B,A)得 `A(AC−B²)>0`，因此D=detΔ=AC−B²>0。每个非零向量的真实二次型正性已在前两项覆盖，不能倒过来把任意det>0当成正定定义。

由于Y=8X−X²且所有项实际可积，EY=8m1−m2，故Y−EY=8(X−m1)−(X²−m2)。实际Var(Y)正是目标1在(8,−1)处的平方积分，给

```text
S=normalVariance=σ²=64A−16B+C>0。
```

由第2项的非零向量(8,−1)得到其严格正性，无需假定源矩或Y的额外概率分布。目标4/5都成立。

### 横向方差、精确常数与 Lambda1

定义t=transverseVariance=D/S=τ²，D>0、S>0使t>0。实际恒等式

```text
A·S−D = A(64A−16B+C)−(AC−B²) = (8A−B)² ≥ 0
```

结合S>0合法除法得到t≤A。恒等式使用上述真实矩阵/σ²绑定，不是另添一个未经证明的假设；目标6/7有足够前提。

对非负原子w的四个真实HasSum，前序接口给EX=q/4、EX²=q及真实可积/L²门，所以实际库的方差减均值平方公式给

```text
A=q−(q/4)²=q−q²/16。
```

对source的1<q<103/100，q>0且1−q/16>0。由0<t≤q(1−q/16)合法比较正分母可得

```text
q/(32t) ≥ 1/[32(1−q/16)] > 1/30，
```

最后的严格号来自q>1使 `32(1−q/16)<30`。这里t本来就是τ²，不能在分母再用t²。实际source定义重新核对为sourceEll=log(31/30)；实对数严格切线界 `log u<u−1` 在u=31/30>1给sourceEll<1/30，是精确有理数比较，不依赖浮点近似。

于是q/(32t)>1/30>sourceEll。以q>0、t>0换形并使用S/D=1/t，得到

```text
S/D−32sourceEll/q = (q−32sourceEll·t)/(q·t)>0。
```

目标9/10/11的符号、严格性、倒数与32系数均与源匹配。

### 实际四旧原子正质量与同一 source 族

一般hbase是μ.real{baseAtom i}>0，真实singleton门没有被简化成任意支撑点或拓扑支撑。对原子w，`fixedAtom(Sum.inl i)=baseAtom i`且fixedAtom单射，已审 `atomicMeasure_real_singleton` 在hw≥0门下精确给μ.real{baseAtom i}=w(Sum.inl i)。所以atomic_transverse_bounds和atomic_curvature_pos中的权重hbase足以建立通用测度hbase；不需要所有无限原子都正。

最终族可一次选择已审U3c `exists_source_finite_and_limit_family` 的同一p/q/eps，之后对任意合格整条r同时取极限和全阶段四HasSum/正性。极限w全正；有限w在旧侧由finiteBase>0给四旧点正，在未来仍为0，所有权重非负。hm0给两类π真概率，实际singleton公式给全部通用hbase，AE界由同一固定原子族继承。因此目标12用的是实际π/π_J，非P/P_J，没有对有限零延拓错误要求全无限正性。

p/q/eps始终在整条r与全部J之前，使用U3c已经统一的有限/极限半径；无需重选参数。J=0只有四旧点，但上述−1、1、2三点论证仍成立，方差/协方差非退化不依赖新增点。泛型μ可有额外连续质量，只要满足hb和实际旧原子正质量，正二次型仍成立。

STATUS: CORRECT

JUSTIFICATION: 三定义与十二目标签名忠实表达R1的真实Δ、σ²和τ²；概率紧支撑足以消除variance.toReal总化风险，实际居中平方积分与协方差绑定、正基点非退化、det/σ²正性、τ²≤Var(X)、精确q/(32τ²)>1/30>ℓ和Λ1正性，以及全finite/limit同一p/q/eps的真实单点门均数学正确。可按原冻结接口实现，无须修订前提。本报告仅为独立声明/source gate，未实施或运行U7 Lean；不将正KL与Λ1正性升级为全局鞍点唯一性。二元累积母函数微分、LLT、尾渐近、曲边界常数、尖点、产品TV和对角未在此证明，根A/B/C/D保持OPEN。
