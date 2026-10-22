# U17c FarEnergyExponentialCover 独立声明/source/API审查

STATUS: CORRECT

唯一reviewer lease1，本票仅未实现的冻结声明门。只拥有本新报告与授权run/statement-review.md，不spawn、Lean/probe/build/rebuild、sourceedit/cachewrite或下载raw完整log。先仅仅读scope Lean fence完整类型独立翻译落盘，再scope/source/真实前置/数学/API，最后冻结hash/pins/cache；不读作者candidate/future/实施notes，不因A/B完整接受而自动批准C。

scope SHA256=`ea2fe343d95821eedf377ccb0a36d9fdd5f32187165076395cf5b9060e527bc5`。零新公开定义，一完整target。

## 1. 冻结完整类型（先读）

```lean
theorem exists_source_far_energy_exponential_cover (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H ell delta : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hgap : ell * q < 7 / 200) (hdelta : 0 < delta)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : Finset ℝ,
      (∀ t ∈ T, Integrable (fun x : ℝ => Real.exp (t * (x ^ 2 - q))) mu ∧
        0 < (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu)) ∧
      ∀ R ∈ sourceFarEnergySet q H delta, ∃ t ∈ T,
        ell * q * (R - 1) ^ 2 + c < t * (q * R ^ 2 - q) -
          Real.log (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu)
```

## 2. 独立盲译（先持久化）

固定同一个真实实概率μ，μ-AE |x|≤4+sqrt10，固定实q/H/ell/delta，其中1<q<103/100、50<H<51、ell≥0、ell*q<7/200、delta>0；还要求μ-AE 1≤x²≤1+H，且同μ的真实二阶矩∫x²=q。

结论先存在一个共同实c>0，再存在一个实数有限集合T。对T中每个实际t，函数exp(t(x²−q))对同μ真正Integrable，且它的真实积分Z_mu(t)>0。随后对同一个实际sourceFarEnergySet q H delta内全部实R，存在属于同一有限T的t，使严格测试裕量
`ell*q*(R−1)²+c < t*(qR²−q)−log Z_mu(t)`。
c/T可依赖固定μ/q/H/ell/delta及原假设，但必须在全部R之前；不能逐R更换c/T，也不能用无限测试族冒充Finset。t本身是有限实数，可正可负/0，需保留实际积分而非只Bernoulli normalizer。第一项用同q的qR²−q能量偏移；二次惩罚是ell*q而非ell或sourceEll偷换。该目标没有路径n、iid概率事件或概率指数界。

远区集合可能为空：仍要有c>0与某个有限T，其对T的积分条件和全R覆盖需按真量词解释，不能偷偷假设存在R；T可为空并使两后件真。R端点p0/p1是否落在集合须后续由实际能量可行区检查，有限端点指数见证不能用无穷参数。

此时尚不判断数学可行性/严格统一c/有限子覆盖或实际API。所有根、一般KL/globalfar概率/full17/19/LLT/hW仍OPEN。

## 3. 真实来源与actual完整前置接口（盲译之后）

盲译阶段先持久化报告SHA256=`79ead54f32d13011a0a4d4a5a11806b85dede37685f59605078099091fa99072`，2918bytes/36行；此后才读scope正文/原源/实际A、B与gap公开完整类型。没有读作者candidate/future/实施notes或未来C实现。

真实R1 `C:/game/shao/current/oq3/proofs/r1/report.md` SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。164–188的能量区间/边界能量比/纯binary gap与193–237的三段充分比较是标量指数试验的来源；384–391说明完整far概率控制仍需额外步骤。原源一般KL/RN/随机Markov kernel/唯一全局最小陈述并未因本标量有限cover就实现。本候选是一条足够的有限指数测试接口，数值7/200来自已独立接受的U14b refined充分gap，不误称它是103/3000的数值弱化或已完成源Eq9/10。

本轮仅读实际承重公开定义/完整类型，语义沿已接受A/B完整proof，不把作者票当证明：

- actual SourceBinaryEntropyGap的 `binaryRelativeEntropy_source_gap` 在1<q<103/100、50<H<51、R>0且R≠1、p=(qR²−1)/H∈[0,1]时给**严格** `(7/200)(R−1)² < actual binaryRelativeEntropy p ((q−1)/H)`。p闭端点完整保留，未要求p内部。
- actual A第一公开 `exists_binary_exponential_test` 要p∈[0,1]、z∈(0,1)、L<binaryD，给有限实theta/正Btheta和严格测试值>L；A完整proof已独立检查p0/p1有限见证，不用无穷参数或actualKL。
- actual A第二公开 `bounded_energy_logMGF_le_bernoulli` 对同μ/hb、q/H/t、H>0、同henergy与真实二阶矩q，给真exp Integrable/真实Z_mu(t)>0及准确log上界。t任意正负0，无small ball或别的概率族；真矩/可积、AE凸弦、正Z和B先于log都在接受的A全proof中成立。
- actual B定义Kfar={R≥0、1≤qR²≤1+H、delta≤q(R−1)²}；`sourceFarEnergySet_isCompact q H delta hq hH` 对任意实delta、含空集给真实紧性。B完整proof已核闭的四多项式约束和q/H正域上的紧Icc上界，没有隐含非空。

## 4. 严格共同余量及真实有限指数试验

### 4.1 先于所有R的固定正c

固定原μ/q/H/ell/delta，q>1⇒q>0，H>50⇒H>0。令g=7/200−ell*q>0，c0=delta*g/(4*q)>0。它只依赖固定参数，完全先于任何R或测试选择，不用紧集非空或最小值见证。

对任意R∈Kfar，R≥0且1≤qR²推出R≠0，故R>0；delta>0与delta≤q(R−1)²使R≠1。先有q/H正后令p=(qR²−1)/H，z=(q−1)/H。Kfar的能量下/上界给0≤p≤1，q>1给z>0，q<103/100与H>50给q−1<H，故z<1。这里R属于能量端点可给p0/p1，不能随手收紧p∈(0,1)。

令W=(R−1)²。Kfar给delta/q≤W，乘g>0得**4*c0≤gW**，因此2*c0<gW。实际gap给binaryD>(7/200)W=ell*q*W+gW>ell*q*W+2*c0。故统一L_R=ell*q*W+2*c0严格小于实际binaryD，A第一目标适用，给每个R某个有限theta和真Btheta>0。没有从逐R正gap直接错误推出统一c，而是先用delta严格分离和数值g显式构造c0。

hell≥0不是上述正g证明的必要条件，但它保留在完整接口中并符合后续权重用途；没有由未消费某强输入而擅删边界ell0。即使delta大到Kfar空，固定c0仍正，下述forallR cover真，T可空，不用先选R。

### 4.2 Bernoulli试验转为同μ的真实积分测试

令t=theta/H，为有限实数，H>0在所有H取消之前给H≠0。A第二目标用**同一个**μ/hb/q/H/henergy/hsecond和该t，给真正Integrable exp(t(x²−q))、真Z_t>0及
`logZ_t ≤ −t(q−1)+log[1−z+z exp(tH)]`。
先实数H非零才有tH=theta，方可匹配A第一目标的实际Btheta；不能只凭符号名称当两个normalizer相同。A的正Btheta/真Z使log运算处在真实正域，而不是不可积Bochner=0或log0的总化。

因为qR²−q+(q−1)=qR²−1且t(qR²−1)=theta*p，真实环/清分母身份与log上界给
`theta*p−logBtheta ≤ t(qR²−q)−logZ_t`。
这是正确的上界减号方向：logZ越小，实际测试值越大。结合严格A测试得到
`ell*q*W+2*c0 < t(qR²−q)−logZ_t`。
不能把某个t的测试值称为Legendre最优，也没有将纯binaryD等同实际KL；这里只用A两条已接受的实际充分接口。t允许正负/0，q/H不被重选，μ与二阶矩中心q始终相同。

真Integrable和Z>0的结论对**所有固定实t**可由A第二目标独立取得，不只对逐R选择的某个t。因此后续有限子cover即使选择了未在某次显式theta选择中出现的指数，也满足目标要求，不需在开集索引上再偷偷加概率可行条件。

## 5. 紧性取有限T、完整量词和边界

对每个固定实t，记Z_t=∫exp(t(x²−q))dμ，定义
`F_t(R)=t(qR²−q)−logZ_t−ell*q*(R−1)²`，`U_t={R | c0<F_t(R)}`。
Z_t是真积分且正，但就R连续性而言logZ_t只是一个固定实常数；F_t是R上的真实连续多项式加常数。**不需要**证明t↦Z_t连续、对μ联合连续、微分under integral、DCT或Fubini，也不需要一般KL缓存。

实际isOpen_lt给每个U_t开；上节forallR∈Kfar∃t有F_t(R)>2*c0>c0，所以Kfar⊆⋃_(t:ℝ)U_t。B给真实IsCompact Kfar后，实际 `IsCompact.elim_finite_subcover` 对**任意索引类型ℝ**开cover给一个Finsetℝ T，并保持Kfar⊆⋃t∈T U_t。没有Countable索引前提，也不是把countably compact仅可数cover定理误用到实指数族。

对全R∈Kfar，从有限union membership真实提取∃t∈T,F_t(R)>c0，再实代数还原冻结的 `ell*q*(R−1)²+c0 < actual_test_t(R)`。c=c0在T/R前，T同样在全部R前。覆盖集合用阈值c0，而点态生产器留2c0余量，两处严格号都保持；无需再对点态test函数的sup做紧性优化。T可有重复选择经Finset消重，无须依赖每个R构造全局连续选择函数。

对全t∈T的真Integrable/正Z，统一从A第二目标对任意实t得到，并与cover独立同时返回。这里没有“仅∃T覆盖”却漏掉实际积分门。Kfar空时可T=∅，积分全称/覆盖均真；c0仍由原正参数给出。无需Kfar非空，不能从存在有限T反推有测试或有R。

能量端点p0/p1、R远区等号、ell0都保留；delta严格正使R≠1而q>1使z严格内部，其余不需R所在连通分支或测试统一正/负号。没有n、n0、R→1极限、有限阶段J或真实概率事件在本类型中被隐含量化。将来要用同c/T覆盖所有样本还需另证逐坐标AE、真实iid积分与集合概率比较；本票不把未来任务计入完成。

## 6. actual静态API与声明环境

本轮只读固定服务器实际源码，未Lean/API probe：

- `Mathlib/Topology/Compactness/Compact.lean:207–212` actual `IsCompact.elim_finite_subcover {ι:Type v} (hs:IsCompact s) (U:ι→Set X) (hUo:∀i,IsOpen(U i)) (hsU:s⊆⋃i,U i) : ∃t:Finsetι,s⊆⋃i∈t,U i`。原类型无Nonempty s或Countableι条件，正好适用于实t和空K。不能与CountablyCompact版本混淆。
- `Mathlib/Topology/Order/OrderClosed.lean:584–587` actual `isOpen_lt` 从两Continuous函数给严格不等式集合开；固定c0和F_t都是连续实函数，所需OrderClosedTopologyℝ现成。
- A两个实际完整公开type与B紧性完整type已实际读取，不引用错名；`binaryRelativeEntropy_source_gap` exact输入p可行/qH范围/R正非1与候选假设真实一致。A的内部/端点及任意signed t proof接受结论不是作者预期，必要接口参数逐个核对。
- 普通实数正除法、严格线性/多项式序、Set.mem_iUnion/mem_iUnion₂和Finsetℝ可由classical DecidableEq在证明中使用，未要求可计算构造/可测选择；拟noncomputable section合适。无新public定义改变现有F或normalizer语义。
- 拟imports只有EnergyBernoulliMGF与SourceEnergyGeometry，其传递图应公开上述拓扑/连续多项式、积分和log对象。namespace Shao.OQ3、open MeasureTheory足以表达完整目标；类型中无新BigOperators/Matrix scope或默认volume实例。

独立数学/source/API阶段判定支持CORRECT，无发现冻结完整类型缺失假设、量词交换、端点反例或静态API阻塞；下一阶段仅核两端冻结hash、实际source/import闭包、现成cache与pins。尚无C实现可读，本票没有本目标build/Audit/receipt门。

## 7. 最后冻结/actual import闭包/现成cache/pins核对

数学/source/API阶段已先持久化报告SHA256=`04c0d085084e7ee16e576dd80700ac80323f0b71515be9866f11ae26f638b0f4`，11217bytes/101行；最后才核两端scope、actualA/B及既有接受终票hash、真实递归导入图/现成olean/pins。不存在C实现或本目标receipt/build/Audit可声称已读通过，未执行Lean/probe。

| 实际冻结/承重对象 | 实际SHA256 | 字节/行 | 核查 |
|---|---|---|---|
| local forty-ninth-unit-scope.md / remote run scope.md | `ea2fe343d95821eedf377ccb0a36d9fdd5f32187165076395cf5b9060e527bc5` | 4447/32 | 两端相同，完整type已先盲译 |
| actual EnergyBernoulliMGF.lean（localdraft/remote工作树） | `e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad` | 6816/176 | 两端相同，与A接受完整终票绑定 |
| actual SourceEnergyGeometry.lean（localdraft/remote工作树） | `3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a` | 5141/119 | 两端相同，与B接受完整终票绑定 |
| local/remote A完整proof-review | `53e938eb892d62be27cd4c8f7519ac9e266d925d75fb4f425f70ef15c6c08ae4` | 24328/216 | 已接受完整票两端仍一致，末节CORRECT |
| local/remote B完整proof-review | `5a5839a6921c22a6b9c8bc1a3166a67fd6375bfb6b3a6f7cb646ff9227bfaceb` | 26474/266 | 已接受完整票两端仍一致 |

拟imports实际是EnergyBernoulliMGF与SourceEnergyGeometry，两者源码imports递归产生 **16项真实Shao闭包**（含这两根源）。集合和各项重算SHA等于A/B接受闭包的真实并集加两根冻结源；16/16对应olean实际存在。没有C/D未来模块或J/I/H/G概率尾链被当成必要依赖，没有重编任何旧成功目标：

| 实际项目源 | 实际SHA256 |
|---|---|
| Shao/Basic/FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| Shao/OQ3/AtomProjection.lean | `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22` |
| Shao/OQ3/AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| Shao/OQ3/BinaryEntropyBounds.lean | `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228` |
| Shao/OQ3/EnergyBernoulliMGF.lean | `e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad` |
| Shao/OQ3/FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| Shao/OQ3/FiniteNormalSpan.lean | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |
| Shao/OQ3/FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| Shao/OQ3/InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| Shao/OQ3/ResonanceArithmetic.lean | `cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b` |
| Shao/OQ3/SampleBoundary.lean | `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2` |
| Shao/OQ3/SourceBinaryEntropyGap.lean | `f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9` |
| Shao/OQ3/SourceEnergyGeometry.lean | `3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a` |
| Shao/OQ3/SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| Shao/OQ3/SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| Shao/Probability/FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

规范path→SHA字典（JSON sort_keys=True,separators=(',',':')，UTF-8）整体SHA256=`1296b0d612365c18c808507f8d1445185c93a1d4961989924fe3df770d65af86`。这是真实导入闭包/冻结哈希检查，不是C尚未写实现的成功target声明。

实际消费/继承API模块由这两imports的真实源码图可达，均有现成olean；下列源码逐项同真实Mathlib HEAD git对象字节一致：

| 库源（Mathlib前缀省略） | 实际SHA256 |
|---|---|
| Topology/Compactness/Compact.lean | `cdc05494e34ec5d4163211223acf44d4c980629cac5542a52ca6d7360d80754e` |
| Topology/Order/OrderClosed.lean | `011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e` |
| Topology/Order/Compact.lean | `e3d3e63921f09661fc6178857a0a72f28c27d41f7810f66607f24ac5919c7001` |
| Analysis/SpecialFunctions/Log/Basic.lean | `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97` |
| Analysis/Convex/SpecificFunctions/Basic.lean | `809d8e40e5ab931ec4254ae9068e9fb5a4a7c19e95d3fddcc9f4ad81028faef1` |
| MeasureTheory/Integral/Bochner/Basic.lean | `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670` |

真实Mathlib HEAD=`807d3836b165983210ee2ecf3cd28f239436949c`，toolchain=`leanprover/lean4:v4.36.0-rc1`；lean-toolchain SHA256=`d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`（29bytes），lake-manifest.json SHA256=`40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`（3541bytes/117行）。不存在缺cache需要下载/新增安装的声明阻塞。

检查时远端 `Shao/OQ3/FarEnergyExponentialCover.lean` 确未创建。工作树分支可在B发布后推进，声明gate不把旧branch/HEAD误当冻结；本票只绑定scope/实际前置/库pins。共享broker只读成功，host key SHA256=`+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`，未改连接或读凭据。

## 8. 最终独立声明裁决

JUSTIFICATION: **CORRECT。** 冻结完整目标的同μ/真实矩/AE能量条件与已接受A/B实际完整接口相合。严格ell*q<7/200和delta>0能先于全部R给显式共同c0>0；Kfar内p闭端点/z开区间/R正非1门均实际可推出。有限theta转t=theta/H时先H非零，真实logZ上界的减号方向和二次惩罚系数精确，A保证每个实测试真可积/正normalizer。固定t对应R连续开集，只需B真实紧性和实际任意索引有限子cover定理即可得同一Finset T；不错误要求t-积分连续或可数指数集。空K、p0/p1、ell0、far边界及有限T的所有normalizer门均保留，c/T真正位于全部R之外。实际16源闭包与固定API/cache/pins无声明或环境阻塞。

本票仅批准 **U17c声明/source/API门**，不能代替尚不存在实现的完整proof/actualTYPE/最后机械审查。真正标量有限指数覆盖可作为未来概率far估计输入，但当前没有真实iid加权事件积分、AE全坐标提升或概率far界，也未生产一般KL/RN/DPI、source3唯一全局最小/Legendre最优、完整17/19/LLT/hW/WC或根闭合；无最弱/最优/新颖性主张。源sourceEll仍是log(31/30)<1/30，候选使用一般ell及显式ellq gap，没有换成错误相等。根 **A/B/C/D、source3/generalKL/globalfar概率/full17/19/LLT/hW仍OPEN**。

本轮只写拥有的新report与授权run/statement-review.md；未source/scope/receipt/旧票/shared/cache修改，不spawn/Lean/probe/build/rebuild/commit/raw全logdownload，不读作者candidate/future/实施notes，不干预CPU0–9外部任务或启动heavy/ulimit。上传后两端SHA另核并交lead全文读取，批准前不实施C。
