# U17g StageSourceNegativeTail 独立声明/source/API审查

STATUS: CORRECT

唯一reviewer lease1，仅拥有本新local报告和remote runs/oq3/u17g-20261021/statement-review.md；不独占代码库，不改source/scope/receipt/旧票/shared/cache或撤他人修改。不spawn/Lean/probe/build/rebuild/commit/cachewrite/raw完整log下载，不读作者implementation/future/candidate notes或下一scope；remote项目命令taskset -c 14-17，不用ulimit-v、不碰CPU0–9外部任务。必须先仅拟完整TYPE独立盲译持久化，再scope/来源/actual API数学门，机械hash/pins/cache最后。G尚无源码。

## 1. 冻结唯一完整拟TYPE（先读）

```lean
theorem exists_stage_source_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          negativeNormalLayerTerm mu q sourceEll (dyadicMesh J) theta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          negativeNormalLayerTerm mu q sourceEll (dyadicMesh J) theta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J))
```

## 2. 独立盲译（先持久化）

固定同一真实实概率mu、自然阶段J和q∈(1,103/100)。只假设同mu真实Y均值=q、X均值=q/4，以及mu-AE位于真实stageAtom的四基点与前J个addedAtom范围，每个实际stage单点mu.real质量严格正。

结论是存在共同正gamma/C，先于eventualn及所有theta∈[0,1]/自然K/k；原实际无if负层序列negativeNormalLayerTerm(mu,q,sourceEll,dyadicMesh J,theta,n,k)真正Summable，且每个移位K的真实tsum≤C*rho^K/(1−rho)，rho=exp(−gamma*dyadicMesh J)。sourceEll是实际固定常数，不能按J/n或q更换ell；mu/q/J在n前固定，gamma/C可依赖它们，未宣称任意q存在此概率或全J同一常数。

本TYPE没有hb/H/energy支持/S/det/ellgap额外假设，必须从所列真实stage/正原子/均值门推出F原先全部前提，而非包装成隐含条件或误套仅atomicMeasure版本定理。需要真正可积先做均值积分线性、一般mu的真实二阶方差/协方差及正分母门、实际sourceEll严格不等式；不能用总化variance/integral取巧。J0、theta0/1、k0/K0、empty/off-grid保留。actual phase枚举、双侧零层组合、19/LLT/conditionalLevy/hW/generalKL及所有根仍OPEN。本阶段尚未读scope路线/前置proof/API或作最终判断。

## 3. 审查顺序、来源与本目标新增义务

第1–2节拟完整TYPE与独立译文已先持久化（35行阶段SHA256=2765720ee85bb8acc3744713000b3237e09f5a0f31bc93915bc163f6fdb5668b），之后才读scope路线、真实R1、actual公开API及固定库。未读未来implementation/candidate/notes或下一scope，未用作者路线预设可行。

R1 146–159明确同一q/4均值对各finite stage不变，239–257给实际协方差/方差/横向方差比较与严格kappa gap，并明示同证适用于有限阶段；378–391和421–429分别是负层支配与19的负层截断用途。本G须真实从原stage门消除F额外H/energy/hb/S/det/ellgap，不能只将它们藏进包装假设。本票以下逐项推出，最后才消费F；不等于构造给定q的mu或重做F成功proof。

sourceEll实际定义是Real.log sourceU，sourceU=31/30；公开sourceEll_pos严格正，公开sourceEll_lt_one_div_thirty严格小于1/30。不得把它写成1/30，也不根据J/n重选ell。F输出的negativeNormalLayerTerm与本目标完全同一真实产品/层/权重定义；本目标不引入新公开定义或替代measure。

## 4. 从真实stage范围推出hb与energy门

实际stageAtom x=Sum.elim baseAtom x，fixedAtom=Sum.elim baseAtom addedAtom，AtomicIndex=Fin4⊕ℕ。对hrange的真实见证i做Sum两分支：inl i对应fixedAtom(inl i)，inr j对应fixedAtom(inr j.val)。actual公开fixedAtom_bounds对所有AtomicIndex无额外条件给

  1≤|fixedAtom i| 且 |fixedAtom i|≤4+sqrt10.

所以可直接将这对界提升到同mu-AE x，得到需要的hb及独立lowerabs。J0时inr Fin0无需抽取，四个base仍在；无须给全无限索引建立正权，也没有从一般hb假造下能量界。

设s=sqrt10，B=4+s，H0=25+8s。实际sqrt非负且s²=10；正有理数25/8和13/4满足(25/8)²<10<(13/4)²，故25/8<s<13/4，给真正50<H0<51。B>0，且B²=26+8s=1+H0，均为精确实恒等/有理不等式，无数值近似。

在mu-AE lowerabs≥1及upperabs≤B上，非负两侧平方给1≤x²≤B²=1+H0（|x|²=x²）；得到F所需真实henergy。H0与J/q/mu/n均无关，是固定源最大基点能量常数；不是把H作为新G假设，也不是只用上界hb就推1≤x²。

## 5. 同mu真实S/D/T与VarX，禁止误套atomic版本

hpos对Sum.inl i配合actual stageAtom定义，直接给hbase:∀i:Fin4,0<mu.real{baseAtom i}。此处是同一个实际单点，无需把一般mu转成atomicMeasure或引入未给定weights/HasSum/constraints。mu已真概率，单点real质量是有限真实质量。

已实际读RegularCovariance的四个公开**一般mu**接口，完整共同前提仅为mu真概率、hb及hbase：

- parabolaCovariance_det_pos ⇒ 0<(parabolaCovariance mu).det（109–112）。
- normalVariance_pos ⇒ 0<normalVariance mu（157–160）。
- transverseVariance_pos ⇒ 0<transverseVariance mu（166–170）。
- transverseVariance_le_variance_id ⇒ transverseVariance mu≤ProbabilityTheory.variance id mu（172–180）。

它们确实不是只针对atomicMeasure w。actual S=Var_mu(Y)，Delta是真正Cov_mu(X,X²)矩阵，T=detDelta/S而非sqrt(T)；以上已完整接受的证明在hb下使用真多项式可积/居中二次型及正原子排非零二次式。G给出其精确门，不偷用任意det>0就称正定或用variance.toReal总化论证。

### 5.1 真可积后从均值推出EX²=q

实际InverseTilt公开integrable_continuous_of_fixed_bounds对同mu真概率/hb、任意连续f给Integrable f mu。对id和x²均可先建立真Integrable，8id及8id−id²也可积。actual normalValue=8x−x²，随后才合法用integral_sub/integral_const_mul：

  q=EY=8EX−EX²=8*(q/4)−EX²=2q−EX²，故EX²=q.

没有从不可积Y或X²的总化积分给线性恒等，也未将hsecond隐含成G额外假设。

### 5.2 真MemLp2后计算一般mu VarX

实际MemLp.of_bound（LpSeminorm/Basic:631–633）前提为IsFiniteMeasure mu、AEStronglyMeasurable f和mu-AE norm界；真概率提供有限，连续id提供AEStronglyMeasurable，hb经Real.norm_eq_abs提供|x|≤B。所以得到同mu真正MemLp id 2，而不是凭variance总化默认有限。

实际ProbabilityTheory.variance_eq_sub（Variance:226–228）完整前提为mu概率及MemLp X 2 mu，结论Var X=E[X²]−E[X]²。于是用刚得hsecond与原hmeanX，得到真实

  Var_mu X=q−(q/4)²=q−q²/16.

这里不套atomic_id_variance或atomic_transverse_bounds：其实际域是atomicMeasure w，并有weights/constraints等前提，G未给mu=atomicMeasure w。用一般mu库公式与一般mu比较接口，才合法得到0<T≤q−q²/16。这是真正消除F缺门，不是名称相近就误用原子版本。

## 6. 严格sourceEll间隙与完整F消费

q>1给q>0及q²>q。由T≤q−q²/16有

  32*T≤32q−2q²<30q.

先有T>0，故32T>0；与30>0一起才合法跨正分母，推出

  1/30<q/(32T).

再由实际sourceEll<1/30得F严格hgap。无需将T误当tau或用可能零S/T分母，也不需要Legendre/Hessian假设。这个一般mu实代数是原R1 247–250不等式的实际版本；q>1提供严格性，未将q依stage重选。

sourceEll_pos给ell≥0。正q乘actual ell<1/30，继而用q<103/100及正30，有

  sourceEll*q<q/30<103/3000<7/200.

最后差值是精确1/1500>0，故F的ell*q严格充分gap真实满足；7/200不是103/3000的数值弱化，二者没有混同。所有清分母之前正性明确，sourceEll始终是真log31/30而非1/30。

现可完整调用actual F `exists_source_negative_layer_geometric_tail mu J q H0 sourceEll`，按其原顺序传入：推出的hb、原hq0/hq1、推出的H0严格界、ell非负/ell*q gap、推出henergy、原hmeanY/hmeanX、推出hS/hD、推出ellT gap、原hrange/hpos。每个原显式门都在同mu真实证明，不增G隐藏假设/不删F门。F返回的gamma/C/eventualn后全部theta/K的实际negativeNormalLayerTerm正好就是本目标。

F已完整接受的原/shift真Summable及真实tsum比较无需重做或削弱；当前G仅把先前显式但未从原stage消费的门真正推出。J0/θ0/1/k0/K0/empty/off-grid继承同F定义和界。gamma/C/N仍在全部theta/K/k外，可依赖固定mu/J/q；此条件定理不声称任意q存在该mu或全J同常数。原构造链的同一q/p/eps/P仍须先于未来r/J/n选择，本结论没有按J/n改q权限。

## 7. 实际API与环境门（机械前）

已静态读actual SummableAtoms:214–234 fixedAtom_bounds及SourceStarter:19–20/45–46的sourceU/sourceEll/sourceEll_pos；实际RegularCovariance:200–205以严格log_lt_sub_one_of_pos给ell<1/30；其一般mu四接口的hb/hbase条件已逐项对照。没有调用atomic-only transverse/variance结论。

指定服务器taskset -c 14-17实际读取LpSeminorm/Basic:631–633 MemLp.of_bound和Probability/Moments/Variance:226–228 variance_eq_sub；所需有限性、强AE可测/平方可积均有真来源。连续X/X²积分线性用固定Bochner/Basic的integral_sub/const_mul，和已接受E实际采用的真可积模式相同；不需要未导入的新KL或Levy库，也不需Lean/APIprobe或新缓存。

数学/source/API阶段无声明缺口。下面最后再核完整fence、F实际root/闭包、这些API真实public import可见性与现成olean/pins/hash；无G实现/receipt可读，不以既有作者机械PASS作本门数学证据。

## 8. 最后核实的冻结hash、真实闭包与cache/pins

scope本地fifty-fourth-unit-scope.md及remote runs/oq3/u17g-20261021/scope.md实测同SHA256=f9eed04fd530169ad4c59e0b3acaaa8b194c1f4dbdba96ab1ba0c40ab5af39fa，5024bytes/37lines。报告完整TYPE fence与冻结fence按LF逐字相等，零公开定义/唯一完整目标未变。只读原R1 report.md实测3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，19420bytes/575lines。

F实际source localdraft/remote worktree同SHA256=8077cfb97547c4a8c5b22da6ed17a58168a6ca1f6b2654f6799292a06a8b23f4，4447bytes/92lines；完整独立终票实测7c5c6fa14e46ad10a2daf8fc85a9dc1cd49e71345c4c4a0498b131fb1a538097，26018bytes/256lines，已lead全文读取接受。本票消费该原真实定义和完整API，不重做它已成功proof/build/Audit。

从拟唯一import F实际递归枚举44项Shao闭包（含F，不含未创建G），完整path/hash字典与已接受F的43前置加F root精确相同，无缺项/多项/冲突；全部44现成project .olean存在。实测绑定如下：

| 实际前置源码（相对worktree） | 实测SHA256 |
| --- | --- |
| Shao/Basic/FinitePath.lean | 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb |
| Shao/OQ3/AtomProjection.lean | 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22 |
| Shao/OQ3/AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| Shao/OQ3/BinaryEntropyBounds.lean | 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228 |
| Shao/OQ3/CenteredLogMGF.lean | 1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4 |
| Shao/OQ3/CenteredSampleTilt.lean | d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501 |
| Shao/OQ3/CentralFourierIntegral.lean | 4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93 |
| Shao/OQ3/CharacteristicMeasureDomination.lean | ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb |
| Shao/OQ3/CompactTiltDomination.lean | 6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623 |
| Shao/OQ3/CompactTiltLayerMassBound.lean | 5602fd17ebac0fe40fb789067cea6b9553659dad4c8965ff88aea7e106ef5cc7 |
| Shao/OQ3/EnergyBernoulliMGF.lean | e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad |
| Shao/OQ3/FarEnergyExponentialCover.lean | 40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d |
| Shao/OQ3/FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| Shao/OQ3/FiniteFarArc.lean | 3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71 |
| Shao/OQ3/FiniteNormalSpan.lean | 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de |
| Shao/OQ3/FiniteStageMeasure.lean | 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1 |
| Shao/OQ3/FundamentalFourierAsymptotic.lean | aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1 |
| Shao/OQ3/GlobalNegativeLayerBound.lean | 57b61e6e3bfd184586083e55633a563e4176cbfcf16def62a7d860d92b5c01d8 |
| Shao/OQ3/InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| Shao/OQ3/JointNonlattice.lean | 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559 |
| Shao/OQ3/LocalNegativeLayerControl.lean | e94a5a8e82d2a69a946a12e16f3fb2a58b174fb036becce5632d7c600b796f01 |
| Shao/OQ3/LocalNegativeLayerTail.lean | 049361c77716896922fb1d7cd3e6abf84515b76a99103c597d8d74b63a2f1856 |
| Shao/OQ3/LocalRateMargin.lean | 5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77 |
| Shao/OQ3/NegativeLayerGeometricTail.lean | 8077cfb97547c4a8c5b22da6ed17a58168a6ca1f6b2654f6799292a06a8b23f4 |
| Shao/OQ3/NormalLayerConditionalLaw.lean | 94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a |
| Shao/OQ3/NormalLayerFourier.lean | 063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3 |
| Shao/OQ3/NormalLayerMassBound.lean | 66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1 |
| Shao/OQ3/NormalTangentDomination.lean | b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90 |
| Shao/OQ3/NormalTangentGaussian.lean | d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39 |
| Shao/OQ3/NormalTangentMoments.lean | 8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1 |
| Shao/OQ3/NormalTangentPowerLimit.lean | 819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457 |
| Shao/OQ3/NormalTrialCost.lean | 8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895 |
| Shao/OQ3/PositiveRate.lean | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |
| Shao/OQ3/ProductMeasureDomination.lean | 9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f |
| Shao/OQ3/RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| Shao/OQ3/ResonanceArithmetic.lean | cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b |
| Shao/OQ3/SampleBoundary.lean | 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2 |
| Shao/OQ3/SourceBinaryEntropyGap.lean | f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9 |
| Shao/OQ3/SourceEnergyGeometry.lean | 3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a |
| Shao/OQ3/SourceFarWeightedTail.lean | c9e4c14af297353c5358da6d3e75d72f712649e535102ba18297fc00a0e5261f |
| Shao/OQ3/SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| Shao/OQ3/SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| Shao/OQ3/TiltedMeasureDomination.lean | 5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b |
| Shao/Probability/FiniteIID.lean | d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b |

44项实际project imports直接引用49个不同Mathlib模块，全部source/现成.olean存在。实际承重一般mu API所在RegularCovariance源码0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853、固定bounds所在SummableAtoms源码0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b、sourceEll所在SourceStarter源码0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d、连续可积helper所在InverseTilt源码c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811均与接受冻结hash一致。

关键固定库source hash与现成olean独立核实如下：

| Mathlib源码省略Mathlib/ | 实测源码SHA256 |
| --- | --- |
| Probability/Moments/Variance.lean | 0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e |
| MeasureTheory/Function/LpSeminorm/Basic.lean | 8e7b53565147a97607ebb09d26073084d0e926edbc9349db90f69859990762cd |
| MeasureTheory/Integral/Bochner/Basic.lean | 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670 |
| Analysis/Real/Sqrt.lean | 1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204 |
| Analysis/SpecialFunctions/Log/Basic.lean | 0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97 |

另按actual module/public import语义核真实公开可见性：F→E→D的分支通至SummableAtoms/SourceStarter/InverseTilt；D→CenteredSampleTilt→CenteredLogMGF→NormalTangentMoments→NormalTangentGaussian→RegularCovariance提供一般mu四个比较接口；E→LocalNegativeLayerControl→SampleBoundary→FiniteIID→IdentDistrib→HasLaw→Variance公开链提供variance_eq_sub；CenteredSampleTilt→Integral.Pi→Integral.Prod→LpSeminorm.Prod→LpSeminorm.Basic提供MemLp.of_bound；D→Bochner.Set→SumMeasure→Bochner.Basic提供积分线性。Log/Sqrt均在同固定公开链可达，不是只凭磁盘存在就假定可用。

拟namespace/open MeasureTheory Filter/open scoped BigOperators/noncomputable section可表达全部冻结TYPE；variance和MemLp2所需概率/有限/实Borel/强AE可测门真实满足，没有额外volume/范数实例或新KL/Levy import需要。本轮没有请求/下载cache，不检查任务外U18/未来scope依赖。

指定worktree=/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3；实际toolchain文本leanprover/lean4:v4.36.0-rc1，lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4（29bytes），lake-manifest.json SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e（3541bytes），Mathlib实际HEAD807d3836b165983210ee2ecf3cd28f239436949c，与接受前置pins一致。

检查时branch feat/oq3-stage-source-negative-tail，HEAD bdf206fe5a5a22fcca24d180923c7e2cf05425f8，status clean，属F发布后正常推进，源hash保持。StageSourceNegativeTail.lean在localdraft/remote worktree均不存在，G run只有scope.md；无G implementation/receipt/build/Audit可读或可记PASS。冻结scope中排队及F审查状态是历史文字，不作为实时机械证据。

全程只写owned报告/授权上传，未修改作者源/冻结scope/receipt/旧票/shared/cache或撤他人修改；不spawn/Lean/probe/build/rebuild/commit/raw完整log下载。所有remote项目只读命令均taskset -c 14-17，未用ulimit-v、不触外部CPU0–9任务/全局资源，审查无heavy Lean任务。

## 9. 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 冻结唯一完整TYPE没有将F缺门藏作额外假设。真实stage→fixedAtom_bounds给同mu AE双边绝对界，固定H0=25+8sqrt10严格在(50,51)且B²=1+H0，真正推出hb/henergy；stage正inl质量给一般mu hbase，实际公开一般mu covariance接口给S/D/T正及T≤VarX。连续X/X²先真可积推出EX²=q，MemLp.of_bound先给真MemLp2再variance_eq_sub得VarX=q−q²/16；不误用atomic-only版本或variance/integral总化。正T和q>1给32T<30q，合法正分母后与真实log31/30<1/30接成严格ellgap；正q及q<103/100给ell*q<103/3000<7/200。F所有原显式门于同mu真实推出后完整消费，输出原真实未截断序列/统一theta-K尾，q/ell不随J/n重选。44前置/49直接库cache、实际public API/pins/hash均支持，无声明/source/环境缺口。

此CORRECT只准许G进入实现，尚无G proof可计已证。未来actual完整type/proof/private/generated/TYPE与机械门须完整独立审查；actual全层phase枚举/双侧零层、finite-layer移动阈值/sign尾/conditionalLevy、完整19/generalKL/hW/全局最优及所有根A/B/C/D仍OPEN。本reviewer未实现或发布G。
