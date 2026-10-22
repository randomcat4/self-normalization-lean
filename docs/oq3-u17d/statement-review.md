# U17d SourceFarWeightedTail 独立声明/source/API审查

STATUS: CORRECT

唯一reviewer lease1；本票只审未实施冻结声明，仅拥有此新local报告与授权run/statement-review.md。不source/scope/receipt/旧票/shared/cache改动，不spawn/Lean/probe/build/rebuild/commit/rawlogdownload，未读作者candidate/future/实施notes。先仅取fence完整type独立翻译persist，再source/scope/实际数学与API，机械hash/pins/cache最后。

冻结scope SHA256=`bd0850af6664a6be85c5fc9bac90695889afdddc3426e9b8e42f08775023606f`，零新定义/唯一完整target。

## 1. 冻结完整类型（先读）

```lean
theorem exists_source_far_weighted_tail_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H ell delta : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hgap : ell * q < 7 / 200) (hdelta : 0 < delta)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 0 < n →
      Integrable (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z))
        (Measure.pi (fun _ : Fin n => mu)) ∧
      (∫ z : Shao.Path n in {z | z ∈ sourceTail q n ∧
          normalDeviation q z ≤ -delta * (n : ℝ)},
        Real.exp (-ell * normalDeviation q z)
        ∂Measure.pi (fun _ : Fin n => mu)) ≤ C * Real.exp (-c * (n : ℝ))
```

## 2. 独立盲译（先落盘）

固定同一个真实实概率μ及μ-AE |x|≤4+sqrt10，实参数q/H/ell/delta满足1<q<103/100、50<H<51、ell≥0、ell*q<7/200、delta>0；还要求μ-AE 1≤x²≤1+H，且同μ真实二阶矩∫x²=q。

结论存在共同正实C,c，在所有自然n>0上同时成立两件事：真实路径指数权重z↦exp(−ell*normalDeviation q z)对μ的真正n重有限产品P_n Integrable；且在真实事件{z∈sourceTail q n 且normalDeviation q z≤−delta*n}上的实际受限Bochner积分≤C exp(−c*n)。C/c必须在全n外，允许依赖固定μ与参数；结论是对所有正n，不只eventuallyn。n0被显式排除，不能用0除总化推归一化。

此为实际加权远负区积分，不是仅有限标量test cover或未加权事件概率；指数是−ell*M_q而非ell*M_q，负层上权重增大。必须真证全路径权重可积、受限积分有真实意义、同n产品/AE坐标能量门及事件几何/有限测试比較，不能将不可积Bochner积分0当上界。ell0/任意正delta/空事件都保留。

本阶段尚未判断数学/source/API或未来实现。其拟输出是一个真实far概率加权界；当前所有根、generalKL、全17/19/LLT/hW及该D输出仍OPEN。

## 3. 顺序、范围与真实来源

以上完整type与第2节译文已先落盘（35行盲译阶段SHA256=ea128007f0b598d1f5a71d12042d024b6ece9aab0bb5baa3407c56541ba417c3），之后才读冻结scope正文、R1及前置公开接口；未读作者future/candidate/实施notes。此次为尚无实现的声明/source/API门，不把已接受C的proof替代D的未来proof，也没有D的build/Audit/receipt可充作本门证据。

实际R1 lines164–188给1≤X²≤1+H与能量Bernoulli充分gap，224–237给相应严格gap论证及更强全局最优论述；386–391需要负层加权控制和远区指数衰减。此目标以已独立接受A/B/C的标量能量测试和真实样本几何，产出{sourceTail且M≤−delta*n}这一远负法向部分的真实加权积分衰减，是该来源中的充分机制，不是重新证明R1的一般KL/DPI或全局唯一最优。它没有覆盖“法向偏差仍小而切向偏差远”的所有joint外区，不能单凭本目标记整个outside-neighborhood、全(17)/(19)或根已闭合。

7/200=0.035是已接受的充分binary gap阈值；本票不称其为103/3000的数值弱化（7/200反而较大），也不把两者相等。目标保留严格ell*q<7/200，且来源实际ell=log(31/30)不是1/30；本目标更一般地只消费所列ell条件。无新颖性、最优常数、通用KL、唯一全局鞍点等主张。

## 4. 实际前置定义与公开门

已读实际B `SourceEnergyGeometry.lean`、C `FarEnergyExponentialCover.lean`、H `CenteredSampleTilt.lean`及其公开依赖定义，不消费其不可见private作公开API。

实际normalValue(x)=8x−x²，normalDeviation q z=ΣY(z_i)−Nq，energy E=Σz_i²；sourceTail是E>0且sqrt(q)/4*sqrt(NE)≤Σz_i的真实正平方根事件。sourceEnergyRatio R=sqrt(E/(Nq))；sourceFarEnergySet Kfar={R≥0,1≤qR²≤1+H,delta≤q(R−1)²}。

B公开`sourceTail_normalDeviation_energy_lower`在q>0、n>0及真实tail成员下给M≥−Nq(R−1)²；`sourceTail_far_energy_mem`另消费每个实际坐标的能量界与M≤−delta*N，给R∈Kfar、R>0、R≠1。B的`energy_ratio_sq`是private；D必须用公开R定义、E≥0、Nq>0和Real.sq_sqrt重新证明NqR²=E，不能直接调用那个private名字。此重证是直接合法的平方根/正分母代数。

C公开`exists_source_far_energy_exponential_cover`与D的mu/hb/q/H/ell/delta/henergy/hsecond完整假设吻合，先于所有n给c>0及固定有限T⊂ℝ：每个t∈T的真实Z_t=∫exp(t(x²−q))dmu正且指数Integrable，并对每个R∈Kfar有t∈T使ell*q*(R−1)²+c<t(qR²−q)−log Z_t。C不是逐样本预选一个共同t；D必须保留有限和。

H公开`iid_centeredSample_tilt`对任意实q,a,v,s及所有n给真实样本指数Integrable、其实际产品积分=单点normalizer的n次幂、及真实tilt产品恒等式。前提仅mu真概率和hb，不要求q/a真均值，也不受U16d small-ball限制；D只需其可积/normalizer两部分，不需引入新的RN/tilt概率等式。实际centeredNormalProjection=v(Y−q)+s(x−a)，centeredSampleProjection是同n有限和。

D没有EX=q/4、EY=q、正方差/有限原子/离散支持等门，独立核查未发现因此缺口：能量MGF所用H任意中心/参数接口和B确定性样本几何确实不依赖这些额外假设。不能把这个结论倒灌成I/J等旧目标假设被削弱。

## 5. 独立完整数学可行性与真实积分门

固定C给出的同一c,T，令Cconst=(T.card:ℝ)+1>0。它们先于全部n>0；没有eventual阈值，也不在样本z之后选C/c。对每个n>0置N=(n:ℝ)>0、P_n=mu的真实Fin n产品概率。q>1、H>50推出q,H>0。

(1) 原始weight的真全空间可积：H取a=q/4,v=−ell,s=0。有限和精确给centeredSampleProjection=−ell*M。故w=exp(−ell*M)对P_n真正Integrable；先得到该事实再restrict，不能利用不可积Bochner积分总化成0。该调用允许ell=0、任意n，尤其没有除ell。

(2) 每个固定t∈T的真实能量指数：H取a=q/4,v=−t,s=8t。逐点−t(8x−x²−q)+8t(x−q/4)=t(x²−q)；有限和给centeredSampleProjection=t(E−Nq)，均为真实恒等式，不把tangentDeviation的q中心误作任意a。于是F_t=exp(t(E−Nq))对P_n Integrable，且∫F_t=Z_t^n。负t和t=0也成立，无需t正性。

(3) 真normalizer：C已给Z_t>0，故log Z_t合法用于exp_log。定义D_t(z)=exp(t(E−Nq)−N log Z_t)=exp(−N log Z_t)*F_t(z)>0。由常数倍可积得D_t Integrable，再用真实乘常数积分和exp_nat_mul/exp_log得exp(Nlog Z_t)=Z_t^n、∫D_t=exp(−Nlog Z_t)*Z_t^n=1；所有相消量已严格正。没有top.toReal、log0、以形式乘积积分替代真Integrable的问题。

(4) 真产品AE坐标门：对每个i:Fin n，以Measure.tendsto_eval_ae_ae把mu-AE henergy传到真实P_n；再ae_all_iff给P_n-AE所有坐标同时满足能量上下界。Fin n有限/可数，不能从mu-AE直接改成所有路径均满足。

(5) 真实event E_n={z∈sourceTail q n且M≤−delta*N}可测：sourceTail_measurable实际公开，M是连续多项式有限和，闭不等式可测，与tail交仍可测。将产品AE坐标门传至P_n.restrict E_n，并由ae_restrict_mem获得真实成员。只在这些AE好样本上消费B；不是对任意坏坐标路径使用能量几何。

(6) 权重方向及严格gap：对好样本z∈E_n，B给R∈Kfar和−ell*M≤N*ell*q*(R−1)²（ell≥0是乘法方向的必要门）。按该R从固定T选t；乘严格正N，再用NqR²=E，得到

  −ell*M+c*N < t*(E−Nq)−N*log Z_t.

因此w(z)≤exp(−c*N)*D_t(z)。样本相关的t只用于点态比较，不能把它当单一测度后积分。D_t≥0及t∈T给D_t(z)≤S_n(z):=Σ_{u∈T}D_u(z)，故w≤exp(−c*N)*S_n在受限测度下AE成立，符号−c*N正确。

(7) 有限和与积分：每个D_t真正Integrable，故S_n真Integrable且点态非负，真实有限和积分=Σ1=(T.card:ℝ)。w和exp(−c*N)*S_n先全空间可积、再各自restrict可积；setIntegral_mono_ae_restrict要求的两个IntegrableOn及受限AE比较全部有真实来源。随后setIntegral_le_integral消费S_n全空间Integrable和AE非负，给

  ∫_{E_n}w ≤ exp(−c*N)*∫_{E_n}S_n
             ≤ exp(−c*N)*(T.card:ℝ)
             ≤ Cconst*exp(−c*N).

最后乘数exp(−c*N)>0，Cconst>0，结论即冻结type。真实积分存在性先于上述线性/比较，不依靠任何totalization。

(8) 空集/边界：T空不应非法取Nonempty或让C=cardT=0；若好样本属于E_n，cover就提供t∈∅的矛盾，故同一AE有限和majorant论证仍有效，Cconst=1保留正性。空far集合、实际event零质量同样无特例缺口。ell=0时weight=1而能量gap仍给指数衰减；energy端点、delta任意正均保留。n=0不在结论中，仅正n用于Nq分母和平方根几何；不除能量、R、R−1、t、ell，不假设这些量非零。不存在偷偷给全n添加均值条件或让C/c依赖n。

## 6. 固定库实际API与公开导入可见性（静态只读）

已通过指定服务器读取实际固定源码，不作Lean/#check/probe。Mathlib.MeasureTheory.Integral.Bochner.Set为显式拟import；其实际setIntegral_mono_ae_restrict（748–752）包含两项IntegrableOn的section变量，setIntegral_le_integral（738–740）要求全空间Integrable及AE非负。二者前提分别如上满足，不是无需可积的形式比较。

实际Mathlib.MeasureTheory.Integral.Bochner.Basic:248–251名称是`integral_finsetSum`（不是下划线拼写integral_finset_sum），需每项真实Integrable；288–290为`integral_const_mul`。L1Space/Integrable:437–445实际有`integrable_finsetSum'`和`integrable_finsetSum`，以每项Integrable给真有限和；1164–1166的Integrable.restrict给受限可积。可以直接消费这些API或有限归纳，不需新增库/cache。

实际Constructions/Pi:425–426的Measure.tendsto_eval_ae_ae正是坐标AE提升；OuterMeasure/AE:151–153的ae_all_iff需Countable索引，Fin n满足。Measure/Restrict:639–647有ae_restrict_mem，要求event MeasurableSet；ae_restrict_of_ae传全空间AE门至受限测度。均未用未经证明的全路径能量门。

Real.sq_sqrt要求被开方量非负，E=Σz_i²≥0与Nq>0提供；Real.exp_nat_mul及Real.exp_log只在Z_t>0之后相消；exp负参数仍严格正。实际Shao.Path n是Fin n→ℝ，存在标准实Borel/有限产品概率，样本连续性/可测性/有限和实向量实例与既有H/B相同。拟namespace/open MeasureTheory/open scoped BigOperators/noncomputable section足以表达该类型，没有引入额外volume实例或matrix范数歧义。

数学/source/API阶段结论：冻结唯一完整type量词、符号、真实可积/概率门及来源范围均成立，未发现声明阻塞。此为声明批准，不等于未存在的D实现或真实机械proof已完成。下面最后独立核冻结hash、实际import闭包、固定pins与现成cache；缺失时报告而不下载。

## 7. 最后核对的实际冻结与环境事实

scope本地及remote runs/oq3/u17d-20261021/scope.md实测同SHA256=bd0850af6664a6be85c5fc9bac90695889afdddc3426e9b8e42f08775023606f，均5321bytes/35lines。报告所存完整Lean fence与冻结scope按LF文本逐字相等（包含全部类型/量词）；0新定义、1公开目标。实际R1 report.md实测3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，19420bytes/575lines，来源未改。

独立枚举两拟Shao import实际递归闭包，共23个项目源码（含C/H两root，不含未存在D）。逐一实测hash与已接受C的16项前置、H的17项前置之并加C/H实际root完全一致，无冲突/缺项/多项；所有23现成project .olean存在。不是把C/H的依赖数量相加当新闭包，也不把未相关I/J加入D。实际表如下：

| 项目源码（相对worktree） | 实测SHA256 |
| --- | --- |
| Shao/Basic/FinitePath.lean | 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb |
| Shao/OQ3/AtomProjection.lean | 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22 |
| Shao/OQ3/AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| Shao/OQ3/BinaryEntropyBounds.lean | 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228 |
| Shao/OQ3/CenteredLogMGF.lean | 1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4 |
| Shao/OQ3/CenteredSampleTilt.lean | d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501 |
| Shao/OQ3/EnergyBernoulliMGF.lean | e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad |
| Shao/OQ3/FarEnergyExponentialCover.lean | 40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d |
| Shao/OQ3/FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| Shao/OQ3/FiniteNormalSpan.lean | 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de |
| Shao/OQ3/FiniteStageMeasure.lean | 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1 |
| Shao/OQ3/InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| Shao/OQ3/NormalTangentGaussian.lean | d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39 |
| Shao/OQ3/NormalTangentMoments.lean | 8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1 |
| Shao/OQ3/PositiveRate.lean | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |
| Shao/OQ3/RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| Shao/OQ3/ResonanceArithmetic.lean | cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b |
| Shao/OQ3/SampleBoundary.lean | 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2 |
| Shao/OQ3/SourceBinaryEntropyGap.lean | f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9 |
| Shao/OQ3/SourceEnergyGeometry.lean | 3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a |
| Shao/OQ3/SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| Shao/OQ3/SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| Shao/Probability/FiniteIID.lean | d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b |

本地C/H源码hash另与remote actual source各一致，分别4543bytes/108lines与7837bytes/153lines。未重做已接受的A/B/C/H完整proof或已成功target/Audit。本票数学消费的是独立读到的真实公开类型与定义；最后才用上述接受基线核固定源码绑定。

实际23项目文件的34个直接Mathlib imports，加D显式Bochner.Set共35个不同Mathlib模块：全部source与现成.olean存在，未下载或构建cache。相关关键库实测如下：

| Mathlib路径省略Mathlib/前缀 | 实测源码SHA256 |
| --- | --- |
| MeasureTheory/Integral/Bochner/Set.lean | e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75 |
| MeasureTheory/Integral/Bochner/Basic.lean | 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670 |
| MeasureTheory/Function/L1Space/Integrable.lean | d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759 |
| MeasureTheory/Constructions/Pi.lean | bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef |
| MeasureTheory/OuterMeasure/AE.lean | beef84262be5013115b47a93698fb7b1960931dd766dcb6cb8867fe305f22f48 |
| MeasureTheory/Measure/Restrict.lean | a7d15027178c6efab4f942a014c85e298942e9624dbff268e0b13714b0cdc5e6 |
| MeasureTheory/Integral/Pi.lean | 43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9 |
| Analysis/Complex/Exponential.lean | 35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146 |
| Analysis/SpecialFunctions/Log/Basic.lean | 0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97 |
| Analysis/Real/Sqrt.lean | 1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204 |

另外按实际`module`语义只沿public import（旧非module项目文件沿其imports）核公开可见性：Bochner.Set→SumMeasure→Bochner.Basic；Bochner.Set→LocallyIntegrable→IntegrableOn→L1Space.Integrable；CenteredSampleTilt→SampleBoundary→FiniteIID→Independence.Basic→Constructions.Pi；所需OuterMeasure.AE/Measure.Restrict/Exp/Log/Sqrt也均有真实公开路径。不是仅发现磁盘上有源码，就推定未导入API可用。所有上述关键API模块的.olean均存在。

实际toolchain文本leanprover/lean4:v4.36.0-rc1；lean-toolchain实测d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4（29bytes），lake-manifest.json实测40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e（3541bytes），Mathlib实际HEAD807d3836b165983210ee2ecf3cd28f239436949c，与接受前置pins一致。

检查时worktree实际branch=feat/oq3-source-far-weighted-tail，HEAD551f457b67ca485d0044254f5d265e49a656b82f，git status clean；这比C审查时分支推进正常，不构成冻结源改变。localdraft/remote worktree的SourceFarWeightedTail.lean均不存在，remote D run只有scope.md，无D实现/build/Audit/receipt可读。本门没有虚记这些产物PASS。全程只读静态检查及写本owned报告；不运行Lean/#check/APIprobe/重编译，不动cache/CPU0–9任务/全局资源，不下载raw完整日志。

## 8. 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: 冻结唯一完整声明与独立盲译一致。以同一mu的真实二阶矩/AE能量支持及有限样本几何消费已接受C的共同c/T，在全n之外选Cconst=cardT+1；H的任意实参数公开接口给原weight和各测试指数真正Integrable，正Z归一化后的每个固定密度真实积分为1。正确符号的受限AE有限和majorant、真实restricted/full积分比较给全部n>0的指数上界，所有可积/概率/可测/正分母/量词/空T/ell0门均能由当前假设和现成公开API满足。来源相符于远负法向部分的充分加权控制；无声明、导入、环境或API阻塞，准许作者依冻结类型进入实现。

此裁决只批准声明/source/API，不认证尚未创建的D proof。实际D产物须经完整actual-type盲译、source/proof/全部private/generated/TYPE及最后机械独立审查后才能计为已证。全根A/B/C/D、一般KL/唯一全局最优、完整joint外区、全(17)/(19)、LLT/conditional Levy、hW等仍OPEN；不由本声明门提前关闭。
