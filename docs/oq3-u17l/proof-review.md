# U17l GaussianBoundaryLaplaceMixture 完整独立证明／来源／实际类型审查

STATUS: CORRECT

## 1. actual 完整公开类型的独立盲译（先行持久化）

本单元声明上下文已存在；本节重新只从actual实现提取唯一完整public TYPE。尚未读取当前scope/R1/primary对照、实现证明体／私有定义与辅助、实际Audit类型或机械收据。0公开DEF，先独立盲译落盘后继续。

```lean
theorem gaussianBoundaryWeight_neg_laplace_mixture
    (kappa x : ℝ) (hk : 0 < kappa) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2))
      (Set.Ioi 0) ∧
    gaussianBoundaryWeight kappa (-x) = (2 / Real.pi) *
      (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2))
```

任意真实κ/x固定，要求κ>0、x≥0。实际f(t)=exp(−[(κ²/2)(1+t²)]x)/(1+t²)在半轴Ioi0上真正IntegrableOn，默认实测度须核实际Lebesgue volume；且既有gaussianBoundaryWeight κ(−x)精确等于2/π乘同一f的半轴积分。这是一个合取公开target，非两个节点。

x0保留：此时核为1/(1+t²)，需要真半轴可积与π/2归一化，使右侧为1。κ严格正，而x无需严格正；不可为简化微分去掉x0，也不能取消√x0或用无限半轴常数1作可积主控。分母1+t²全实严格正，率(κ²/2)(1+t²)正；指数符号／系数κ²/2与2/π、负位移−x、开半轴测度须分别审。

类型没有μ/J/ell、相位、hcont或原模型概率前提；它只连接真实已定义Gaussian边界密度weight与正指数混合，不自证源24精确ζ、源25统一gap、混合后格和交换、hcont/U18a、无条件19、Phi字面CDF、hW、generalKL或任何根闭合。未来实现的参数化选择不是新假设，应完整核私有body、真实可积／导数门与0边界。

本actual独立盲译已先行持久化；下文后附完整来源、全部actual proof及private/generated／类型和最后机械绑定。

## 2. 最终范围、顺序与来源对应

FINAL STATUS: CORRECT。

本终票是完整actual source/proof/TYPE独立审查；不是重发此前声明许可，也不是依据作者机械PASS推定数学正确。最初26行／2050字节检查点SHA256为cbb3e500390fd5fd5688447a2210fa9245d75e9c31bf2317f32b44aecc37c48c。其第1节盲译文字、完整TYPE及随后段落原字节保留；仅首部行政STATUS随完成更新。当前严格完成次序为盲译持久化→冻结scope/R1/primary→全262行actual实现及固定主API→全部28actual DECL/TYPE完整续行→收据、既有日志、源码与依赖／pins绑定。

0公开DEF、1公开合取目标；3私有DEF、14 authored private theorem均已逐体／逐证明读取。全部locals、tactic生成项及其实际一般前提已审。未读作者implementation/candidate/future/cusp笔记；未运行Lean、#check、API探针、重编或写共享cache。仅本新报告写入本地及授权远端报告路径。独立裁决与作者收据的AWAITING_INDEPENDENT_PROOF_REVIEW状态有时间先后，不能混为一张票。

冻结scope59为fifty-ninth-unit-scope.md，完整公开类型与actual源的白空格规范比较相同；4项import、namespace、非计算段和实积分环境均一致。该类型没有额外小κ条件，没有删掉x=0，没有把Gaussian负曲边identity作为假设，也没有加入hcont或形式化erfc公理。虽然已接受声明上下文存在，本次仍先重新翻译actual完整类型再读取证明。

真实R1为current/oq3/proofs/r1/report.md，19420字节／575行，SHA256 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，已只读核对。411–421定义g_J(d)及F_J(d)=exp(−ell*d)g_J(d)；448–455把负半轴写作exp(ell*x)2*GaussianTail(κ_J√x)，包含0端点。475–481的原(25)则是格和相对连续常数的统一正间隙。本模块给其中GaussianTail因子的准确正指数混合，不把该identity误记成原(25)的证明。

已只读核对经典主来源[NIST DLMF 7.7.1](https://dlmf.nist.gov/7.7.E1)：正实轴取z=κ√(x/2)即给相同混合系数及指数。它只说明数学来源经典，绝不充当Lean假设／新公理；实际形式证明完全从真实Gaussian密度、Cauchy积分、参数积分微分和FTC完成。没有新颖性、最优性或最弱假设主张。

原target→消除义务→直接consumer→剩余：原(25)需控制真实负半轴profile的离散减连续差；此前K已把实际stage Gaussian layer weight接到真实密度profile，但尚无可用于正混合分析的精确表示。本L消除“该Gaussian weight是否真等于正Laplace混合且核真可积”的义务。直接consumer是对这同一profile建立格和与积分比较的原(25)证明。真正的混合后格和／积分交换、加上exp(ell*x)后的可积与正率门、统一正下界、原(24)精确ζ系数及余项均仍需单独证明；本票不替它们签收。

## 3. 三个actual私有定义完整体与积分语义

以下body直接来自actual源码13–22行；均为private，不新增公共定义、实例或概率law。

```lean
private def mixtureKernel (b t : ℝ) : ℝ :=
  Real.exp (-(b ^ 2 / 2) * (1 + t ^ 2)) / (1 + t ^ 2)

private def mixtureValue (b : ℝ) : ℝ :=
  (2 / Real.pi) * ∫ t : ℝ in Set.Ioi 0, mixtureKernel b t

private def gaussianPrimitive (b : ℝ) : ℝ :=
  (2 / Real.sqrt (2 * Real.pi)) *
    ((∫ z : ℝ in Set.Ioi 0, Real.exp (-(z ^ 2) / 2)) -
      ∫ z : ℝ in (0 : ℝ)..b, Real.exp (-(z ^ 2) / 2))
```

所有set integral是volume.restrict(Ioi0)的真实实Bochner积分；interval integral采用真实有向Lebesgue积分。Bochner定义本身总化，但下述核、Gaussian和所有使用的微分／尾差门均先取得真正Integrable／IntervalIntegrable。未利用不可积积分默认0制造任何identity。π>0、sqrt(2π)>0；全部1+t²>0。无需人为概率或有限体积Ioi0假设。

## 4. 全部证明与locals的独立语义审查

### 4.1 24–70行：核的非负、Cauchy主控、真实可积与全参数连续

mixtureKernel_nonneg直接从exp正和分母正给非负。mixtureKernel_le令hd:0<1+t²，利用b²≥0推出−(b²/2)(1+t²)≤0，故exp≤1，除以正hd得到核≤(1+t²)⁻¹；这里b任意实，未偷用b>0。核的t连续性用分母处处非零的Continuous.div。

mixtureKernel_integrable调用Integrable.mono'：主函数(1+t²)⁻¹在整条实线上真Integrable，限制到Ioi0仍真可积；实际核连续故AEStronglyMeasurable，范数由核非负转换成核本身再用上述Cauchy界。Ioi0无限体积下从未把常数1当作可积主控。

mixtureValue_continuous使用固定测度volume.restrict(Ioi0)的MeasureTheory.continuous_of_dominated。四门分别是全b的核AEStronglyMeasurable、全b同一Cauchy AE范数界、该Cauchy界真Integrable、每t的b↦核连续。主控同时覆盖全b，尤其b=0及其邻域，非仅逐b界；再乘常数2/π保持连续。

mixtureValue_zero先实际函数外延化kernel0=(1+t²)⁻¹，再用半线反正切积分π/2−arctan0=π/2，得到(2/π)(π/2)=1。π非零为真实库正性。零参数没有调用率0的Gaussian总化积分。

### 4.2 73–111行：Gaussian真可积、primitive连续／零值与FTC

gaussian_half_integrable先把exp(−z²/2)与exp(−(1/2)z²)作真实函数等式，使用率1/2>0的integrable_exp_neg_mul_sq给全实真Integrable。以后Ioi尾积分可积来自这个事实。

gaussianPrimitive_continuous：Gaussian integrand全实连续，其0..b primitive由真实连续函数积分的可微性推出连续；固定半线积分为常数。不存在对任意不可积函数的primitive断言，也不需要b≥0来建立全实连续。

gaussianPrimitive_zero：interval integral0..0=0；真实Gaussian半线积分为sqrt(π/(1/2))/2=sqrt(2π)/2；sqrt(2π)≠0先明确，然后field_simp给归一化1。该Gaussian率确为正1/2，不能借库对非正率的totalization分支。

gaussianPrimitive_hasDerivAt给全部实b的导数−(2/sqrt(2π))*exp(−b²/2)。FTC消费连续Gaussian的intervalIntegrable0b、StronglyMeasurableAtFilter与ContinuousAt；先得0..b积分导数，减去它并乘常数，符号确为负。没有把Gaussian尾函数的形式表达当成无前提FTC。

### 4.3 113–185行：核导数、统一正参数邻域及精确Gaussian系数

mixtureKernel_hasDerivAt的实际链式求导：指数关于b的导数是−u(1+t²)，分母1+t²独立于b且处处非零，因此实际导数是−u*exp(−(u²/2)(1+t²))。使用pow2/div_const2/neg/mul_const/exp/div_const及field_simp/ring；系数2被指数中除2正确消去，未遗留或丢掉1+t²。

mixtureValue_hasDerivAt只要求固定b>0。真实邻域s=Ioo(b/2,2b)包含b，且先于积分变量t选择。真实bound(t)=2b*exp(−(b²/8)t²)，率b²/8>0，乘非负常数2b后在全实、因而Ioi0真Integrable。

hbound对每t、全部u∈s成立：u>0、u<2b以及u²/2≥b²/8。于是

`−(u²/2)(1+t²) ≤ −(u²/2)t² ≤ −(b²/8)t²`，

从exp正及单调、abs(−u)=u得导数范数≤2b exp(−(b²/8)t²)。它不依赖t选择参数邻域，也不要求t有界；因此是真正局部参数一致、积分变量全域的主控。

hasDerivAt_integral_of_dominated_loc_of_deriv_le的所有actual输入逐门成立：Ioo为b邻域；附近每u的核AEStronglyMeasurable；固定b核真Integrable；固定b导数关于t连续故AEStronglyMeasurable；同一hbound及真可积bound；AE全t全u∈s的真实HasDerivAt。库结论同时给导数函数真Integrable与积分函数的HasDerivAt，先于后续积分系数化简。没有只写“可交换导数”而缺少uniform AE门。

heq把导数核确切分解成(−b*exp(−b²/2))*exp(−(b²/2)t²)。正b意味着b²/2>0；半线Gaussian公式给√(π/(b²/2))/2，且此前已经有真正可积。hsqrt把它写成√(2π)/b，仅在b>0下用|b|=b；√2π与π真实非零。hc用(√2π)²=2π得√2π/π=2/√2π。

因此完整导数系数为

`(2/π)(−b exp(−b²/2))(√(2π)/b)/2 = −(2/√(2π))exp(−b²/2)`。

field_simp涉及b的约分均处于hb>0上下文；π／sqrt的非零门明确。这个计算精确核查了两个half因子、外层2/π和负号；不是只比较“比例相同”。没有在b=0消b。

### 4.4 187–223行：仅正半轴常值、真实0连续定常数与尾差

mixtureValue_eq_primitive令D(u)=mixtureValueu−gaussianPrimitiveu。D全实连续，D0=1−1=0。对u>0，两项已证明的真实导数完全相同，差导数为0；借Ioi0开放、凸从而preconnected以及真DifferentiableOn／EqOn deriv=0，得到任意正u/v间D相同。

b=0分支直接用两真实零值。b≥0且b≠0分支得到b>0后，一方面D沿𝓝[>]0趋D0=0；另一方面沿同一右滤子与常数Db最终相等，故趋Db。实数NoMaxOrder／稠序拓扑实例保证该右滤子NeBot，实Hausdorff唯一极限推出Db=0。未在0声称导数为0，也未把空滤子极限当作常值证明。

gaussianPrimitive_eq_tail要求b≥0，消费全实Gaussian真Integrable限制Ioi0，以及0≤b，调用真实integral_Ioi_sub_Ioi：tail0−tailb=interval0b。线性移项给tail0−interval0b=tailb，恰与primitive定义同向。这里没有颠倒尾差符号，也未缺少两端尾积分可积门。

### 4.5 225–258行：公开目标与x=0真实边界

设b=κ√x。hk>0和sqrt非负给b≥0，hx≥0通过sq_sqrt给b²=κ²x。hker完整函数外延把目标exp(−[(κ²/2)(1+t²)]x)/(1+t²)写成mixtureKernel b t，指数括号与x位置由实环恒等式匹配。合取第一项立即消费先前all-b kernel真Integrable，不是由最终等式倒推可积。

第二项消费真实gaussianBoundaryWeight_eq_piecewise κ hk (−x)。若0≤−x，则结合hx得x=0；实际b=0，weight=1与primitive0=1严格匹配。否则保留x>0负位移分支，−(−x)=x，真实下限κ√x正好是b；primitive_eq_tail b hb匹配同一尾积分与2/sqrt2π系数。随后primitive=mixtureValue，再unfold后以hker还原原kernel。

最后只进行sqrt值／平方代入，从未微分x↦√x；不需Real.hasDerivAt_sqrt，也不需改变4import。x=0、任意大x、任意κ>0均覆盖，没有仅对几乎处处x的结论。公共定理没有ell、μ、stage或n参数，不能据本结论修改任何旧源law或均值。

## 5. 固定库实际API、主实现与公开可达

已读取固定源码，不运行#check／Lean／API探针。下面为真正消费的接口及其门；这些门已在第4节逐个映射至actual proof，不以名称近似代替。

| 固定Mathlib文件与行 | 已核实际语义 |
| --- | --- |
| Analysis/SpecialFunctions/ImproperIntegrals.lean274–289 | integrable_inv_one_add_sq给全实真Integrable；integral_Ioi_inv_one_add_sq给π/2−arctani，以真实导数／尾极限和可积证明 |
| Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean115–132,289–301 | Gaussian真Integrable需要正率；half integral对非正率有integral_undef分支，但本源只在已证明正率1/2、b²/8、b²/2上下文消费 |
| MeasureTheory/Function/L1Space/Integrable.lean104–106 | Integrable.mono'要求AEStronglyMeasurable与真实AE范数支配，本核逐门具备 |
| MeasureTheory/Integral/Bochner/Basic.lean474–480 | continuous_of_dominated消费全参数可测、每参数同一可积主控、AE逐点参数连续，经continuous_setToFun_of_dominated实现 |
| Analysis/Calculus/ParametricIntegral.lean284–302 | actual局部主控导数API；先取邻域，再AE变量外统一∀x∈s，返回导数真Integrable及HasDerivAt；实现以同一ball上的导数界导出Lipschitz主控 |
| MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean725–728,931–939 | 真intervalIntegrable、filter强可测及连续点给FTC；continuous primitive可微再连续 |
| Analysis/Calculus/MeanValue.lean767–771 | 实际根namespace IsOpen.is_const_of_deriv_eq_zero；开放且preconnected集合、DifferentiableOn及deriv EqOn0才给两集合内点值相等 |
| MeasureTheory/Integral/IntervalIntegral/Basic.lean1172–1180 | Ioi尾相减是有真IntegrableOn及a≤b门的interval integral，不是无条件总化线性 |
| Topology/Order/DenselyOrdered.lean175–183 | 实NoMaxOrder给nhdsGT_neBot，保证0右极限唯一性可用 |
| Data/Nat/Init.lean425–431 | Nat.AtLeastTwo n是Prop类，唯一field为2≤n；本生成proof是(1+1).AtLeastTwo，闭算术事实 |
| MeasureTheory/Measure/Lebesgue/Basic.lean | 实际real volume是既有Lebesgue实例；所有restriction／interval／Gaussian接口用同一volume |

真实import图词法去除嵌套注释、行注释及字符串后重建；对新module仅沿public import判公开可见性，旧式模块沿实际import传递。当前4import的公开闭包2678模块；以上实际调用所属模块均公开可达。物理缓存闭包中的Mathlib.Analysis.SpecialFunctions.Sqrt仍不在该公开闭包；其hasDerivAt_sqrt不能凭cache存在默用。这项声明阶段已透明报告；当前actual实现彻底避开平方根导数，因此不是本proof环境阻塞，也没有偷偷新增import。

选定主API源码hash：

- ParametricIntegral f0a3c1e155e36b41a4f8ac6cf7adc2a9116e88177726d214e75ab1ad79559739；MeanValue 0f10e5afeb80809192b023486b09e98939d0a6bd0920ab3882bddb41a715d947。
- FundThmCalculus 85ca810c4adc1236fa7d057ff48cf7ae69d2bacf1ac2413b02ba9ac530de1e0b；Bochner.Basic 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670。
- ImproperIntegrals 1527f79047df49f816995ad879a8cfa9e6655f8c8a2c1e0342bf780890a894e7；GaussianIntegral 4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c。
- Lebesgue.Basic 4955d3400a03ba9d525206fcf1cff8592497dfff06674ca13d68d3bdcabb964d；DenselyOrdered 45e23755ea8ca4189b8bbed3274c865201d1ebb30fd734a80c5c2057e5c5fcbe；Data.Nat.Init 806975436869c67d4bd0dddfa042b8eaac3d7309d90a4d6b03d33d7ab5a7edfa。

直接数学承重为已完整独立审查接受的GaussianBoundaryConstant真实weight定义20–22及piecewise52–56：它本身由标准Gaussian真归一化、负曲边集合两半线、反射和端点Lebesgue零建立。当前已只读核其actual定义与完整public类型，源hash保持c44d13d42da6711f9eec44313fb27b363513b7e75aeb83c1df79708157e65f5a。上游K的实际stage接口／profile与完整接受报告保持冻结；不重做旧成功proof或构建。其余55项import链保证真实模块绑定；本L并不在其概率／hcont依赖上增加未声明假设。

## 6. 全部28个actual DECL／完整TYPE的逐项审查

先读完下面全部实际DECL及TYPE长续行，才读取作者receipt／build机械状态。为压缩私有前缀，P严格表示`_private.Shao.OQ3.GaussianBoundaryLaplaceMixture.0.Shao.OQ3.`；所有标P的DECL是该完整前缀加后缀，未省略任何前提。TYPE内✝为Lean打印的同一private常量显示名，不是新增public声明或额外假设。编号按真实Audit输出顺序。

1. DECL PmixtureKernel_hasDerivAt._simp_1_6
```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ), a ≠ 0 → (a ^ n = 0) = False
```
核：有真正GroupWithZero和a≠0门的整数幂非零，包含n负／0，非无条件假设。

2. DECL PmixtureValue；TYPE `ℝ → ℝ`。private DEF，完整积分body已在第3节读取，不能只因此类型接受。

3. DECL PmixtureValue_continuous；TYPE `Continuous Shao.OQ3.mixtureValue✝`。四DCT门已核。

4. DECL PmixtureKernel；TYPE `ℝ → ℝ → ℝ`。private DEF，完整body已核。

5. DECL PmixtureKernel_hasDerivAt
```lean
∀ (u t : ℝ), HasDerivAt (fun b => Shao.OQ3.mixtureKernel✝ b t) (-u * Real.exp (-(u ^ 2 / 2) * (1 + t ^ 2))) u
```
核：全部真实u/t，t分母始终正，真实导数系数正确。

6. DECL PmixtureKernel_hasDerivAt._simp_1_1
```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2], (2 = 0) = False
```
核：保留NeZero2，不把任意Zero类型里的2非零当公理。

7. DECL Pgaussian_half_integrable
```lean
MeasureTheory.Integrable (fun z => Real.exp (-z ^ 2 / 2)) MeasureTheory.volume
```
核：打印−z^2是实平方的负号，匹配实际源exp(−(z²)/2)，真全实Gaussian可积。

8. DECL PgaussianPrimitive_zero；TYPE `Shao.OQ3.gaussianPrimitive✝ 0 = 1`。真实halfGaussian／非零sqrt给值。

9. DECL PmixtureKernel_integrable
```lean
∀ (b : ℝ), MeasureTheory.IntegrableOn (Shao.OQ3.mixtureKernel✝ b) (Set.Ioi 0) MeasureTheory.volume
```
核：包括b0与负b，Cauchy主控，不暗中添加b正前提。

10. DECL PmixtureKernel_le
```lean
∀ (b t : ℝ), Shao.OQ3.mixtureKernel✝ b t ≤ (1 + t ^ 2)⁻¹
```
核：全实b/t，指数非正／正分母真实成立。

11. DECL PmixtureValue_eq_primitive
```lean
∀ (b : ℝ), 0 ≤ b → Shao.OQ3.mixtureValue✝ b = Shao.OQ3.gaussianPrimitive✝ b
```
核：只对b≥0的结论；b0连续与右滤子门真实建立，未错误推广负b。

12. DECL PmixtureKernel_continuous
```lean
∀ (b : ℝ), Continuous (Shao.OQ3.mixtureKernel✝ b)
```
核：分母无零。

13. DECL PmixtureKernel_hasDerivAt._simp_1_4
```lean
∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀] [NoZeroDivisors M₀] {a b : M₀},
  a ≠ 0 → b ≠ 0 → (a * b = 0) = False
```
核：真实NoZeroDivisors及两因子非零，保留完整长续行。

14. DECL PmixtureKernel_hasDerivAt._simp_1_2
```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3], (3 = 0) = False
```
核：数3的明确NeZero门。

15. DECL PgaussianPrimitive；TYPE `ℝ → ℝ`。第3节完整body已核，非抽象Gaussian符号。

16. DECL PmixtureKernel_hasDerivAt._simp_1_3
```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4], (4 = 0) = False
```
核：数4的明确NeZero门。

17. DECL PmixtureValue_hasDerivAt
```lean
∀ (b : ℝ), 0 < b → HasDerivAt Shao.OQ3.mixtureValue✝ (-(2 / √(2 * Real.pi)) * Real.exp (-b ^ 2 / 2)) b
```
核：积分导数限制b>0，系数精确，没要求0处此导数。

18. DECL PgaussianPrimitive_hasDerivAt
```lean
∀ (b : ℝ), HasDerivAt Shao.OQ3.gaussianPrimitive✝ (-(2 / √(2 * Real.pi)) * Real.exp (-b ^ 2 / 2)) b
```
核：全部b的FTC，和上一项在Ioi0相同。

19. DECL PmixtureKernel.eq_1
```lean
∀ (b t : ℝ), Shao.OQ3.mixtureKernel✝ b t = Real.exp (-(b ^ 2 / 2) * (1 + t ^ 2)) / (1 + t ^ 2)
```
核：实际定义展开，无新增分析假设，完整body与第3节一致。

20. DECL PmixtureKernel_hasDerivAt._simp_1_7
```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ), (↑n + 1 = 0) = False
```
核：真正CharZero、Nat强制转换的n+1非零；不是任意环不论特征的结论。

21. DECL PmixtureValue_zero；TYPE `Shao.OQ3.mixtureValue✝ 0 = 1`。Cauchy半质量。

22. DECL Shao.OQ3.gaussianBoundaryWeight_neg_laplace_mixture._simp_1_1
```lean
∀ {α : Type u_1} [inst : Preorder α] (a : α), (a ≤ a) = True
```
核：Preorder反身性生成等式，仅用于0端点分支简化。

23. DECL PmixtureKernel_nonneg
```lean
∀ (b t : ℝ), 0 ≤ Shao.OQ3.mixtureKernel✝ b t
```
核：exp／正分母。

24. DECL PmixtureKernel._proof_1；TYPE `(1 + 1).AtLeastTwo`。actual Nat.AtLeastTwo类仅field2≤n；这是2≤2的闭数值证明，非新axiom或analysis门。

25. DECL PgaussianPrimitive_eq_tail
```lean
∀ (b : ℝ),
  0 ≤ b → Shao.OQ3.gaussianPrimitive✝ b = 2 / √(2 * Real.pi) * ∫ (z : ℝ) in Set.Ioi b, Real.exp (-z ^ 2 / 2)
```
核：完整b≥0长续行、真实尾差与归一化。

26. DECL PgaussianPrimitive_continuous；TYPE `Continuous Shao.OQ3.gaussianPrimitive✝`。真实interval primitive全实连续。

27. DECL PmixtureKernel_hasDerivAt._simp_1_5
```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ), a ≠ 0 → (a ^ n = 0) = False
```
核：保留MonoidWithZero、IsReduced及a≠0门的自然幂非零，覆盖n0，非错误无零幂总化。

28. DECL Shao.OQ3.gaussianBoundaryWeight_neg_laplace_mixture
```lean
∀ (kappa x : ℝ),
  0 < kappa →
    0 ≤ x →
      MeasureTheory.IntegrableOn (fun t => Real.exp (-(kappa ^ 2 / 2 * (1 + t ^ 2)) * x) / (1 + t ^ 2)) (Set.Ioi 0)
          MeasureTheory.volume ∧
        Shao.OQ3.gaussianBoundaryWeight kappa (-x) =
          2 / Real.pi * ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(kappa ^ 2 / 2 * (1 + t ^ 2)) * x) / (1 + t ^ 2)
```
核：完整actual elaborated public TYPE与盲译／scope同一κ>0,x≥0合取；明确volume，未改变任意实参数量词。

清点：2/4/15共3private DEF；其余中14 authored private theorem、1public target、10generated theorem；总28owned、25theorem。generated恰为7个非零通用simp事实、1Preorder反身性、1kernel.eq_1、1Nat.AtLeastTwo。没有推测生成类型、隐藏额外义务或漏掉abstract一般前提。它们没有把分析定理替换成假设，也没有导出共享instance。

## 7. 最后机械绑定：实际源码、既有产物与版本

以下机械检查全部发生于完整proof/API及第6节actual TYPE审查之后。server broker只读执行，项目命令统一taskset -c 14-17；无Lean在途／启动，无ulimit-v、外部CPU0–9／80GiB任务或全局资源动作。未复制原始完整日志到本地，只读server的TYPE选择段、hash／诊断摘要。审查报告中的TYPE摘录是允许的逐项审查证据，并非raw log下载。

2026-10-22 09:32:37 UTC独立实际观察：branch feat/oq3-gaussian-laplace-mixture，HEAD5ffdc89842f49c86102f2bcfb0826589de86f43e；git status仅`?? Shao/OQ3/GaussianBoundaryLaplaceMixture.lean`，无他人变动被撤回。源码localdraft／worktree／run snapshot三端均11528字节／262行，SHA256 fd470e5ffcea5299222a570389ae9603beb1e78b34c065d637e26e08c76dd421。target olean实际存在；本review没有为确认它而重新编译。

- scope local／run同5186字节／28行，a33ee77ea57ce02a2a16002e6b43dc8c3498c5689793e308e0bd1d61381b5bd1。
- 已接受声明票local／run同24988字节／243行，605d0057b5acfb7ce85a9890da35fdb85a4c3c992848371fb4b5a6778ace9bc4，保留历史盲译和公开sqrt API说明；未修改。
- Audit source local／run同1694字节／39行，7f01596b6c1d07405a6f880ba607d7931aeee3b3f601bc711272ae4bc43b0e05。
- Audit.log留server，6206字节／97行，82c7a7bec8d0daa8d653987604f2849885ac921686316d28aa41ff03c1a42133。
- receipt local／run同11537字节／143行，b1daf78ab3e78f8979aaf16bb6c6a32b4e8c1e56d2d572af7b0190cc476a4305。
- prerequisite-hashes local／run同5924字节／57行，37a07ee36fd0b98c816bdff7ece60eef1c9d1bacdc84a96a50c1291fc93ff89c；55项真实源hash逐个一致，排序compact map SHA c5e9824e79c69550d99fe0f093e19f12e85a4c0fbd7ce1fa031b0a5c18e7bb55。

Audit实际源码已读：要求唯一冻结目标存在且是theorem，遍历该target stem及整个private模块前缀，拒新axiom，逐常量Lean.collectAxioms并逐项白名单核对。actual源词法枚举的3private DEF／14private theorem／1public theorem，与全部生成项及28实际输出吻合；不是只按公开target作axiom检查。实际28 AXIOMS行全落在[propext]或[propext,Classical.choice,Quot.sound]，footer实际给0frozen definitions／1frozen theorem／25all theorems／28all declarations／U17L_AXIOM_GATE PASS。types、计数与范围已独立交叉核，非只转述receipt。

build-04首次当前完整源成功的历史exit0由保存的receipt记录；review只读原产物及诊断，不伪称自己重执行。其实际2187字节／34行，SHA de1cf4e25ef30f589c832f09b933cc3d00403e3812772d6110389bc35d6ca8ed，非空：11个真正诊断warning、0error，包括未使用／未执行tactic sequence和deprecated if_neg。不能写成空日志或零warning。警告没有改变任何数学假设／证明强度，review不得为清理风格而改冻源重编。

历史完整changed source01/02/03分别失败、不是partial success：01日志4904字节／83行，2a17af81f692cbde615055f8136b61b1bfec0f9c6915de4dc13b25204f156275；02为2863字节／43行，7e206865f1af2263ac36aab6ad2d3adc185a033b2b3ab7ddc2cecb5dd9296753；03为2267字节／35行，2975903c50106d7c707385697be070a58519582ff2654a802e8f762ebb258850。所选实际诊断含simp／rewrite／强类型转换／已无goal／多余end等表达式问题，03仍有1error；04当前源首完整成功后没有重复同一成功target或Audit。保存历史不能作为当前源码有漏洞，也不能删去失败记录。

保存build／Audit命令明确taskset -c 14-17、lake env lean -M8192 -j4 -DautoImplicit=false。无降低autoImplicit或数学检查、无ulimit虚拟内存限制、无新增公理／sorry等规避。Lean版本文件实际leanprover/lean4:v4.36.0-rc1，29字节／1行，SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4。lake-manifest实际3541字节／117行，SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e；mathlib实际git HEAD807d3836b165983210ee2ecf3cd28f239436949c，与receipt同pin。没有执行Lean版本探针。

独立去注释／字符串静态扫描：actual公共完整签名白空格匹配scope；精确4imports不变；CR0、无尾空白；sorry/admit/axiom/unsafe/native_decide/implemented_by禁用词无匹配。源码全读补足词法扫描局限；无本模块新共享instance、隐藏公理或对旧source修改。

## 8. 实际55项目前置绑定与缓存闭包

按actual4import重新递归解析，得到55 Shao／2905 Mathlib源；所有对应源及现成olean均实际存在，缺项0。公开图与物理图分开核：cached Sqrt模块不可公开调用的问题如第5节所述，当前proof不消费它。递归图和逐源hash既与run prerequisite-hashes.json一致，也与receipt的imported_project_sources_sha256一致；未读取作者candidate cache metadata或为闭包写cache。

下列为从真实worktree读取并逐个比对成功的完整55项SHA256。前置计数不包含当前L本身；保持历史已接受源与作者head，未重做任何旧成功构建。

```text
Shao/Basic/FinitePath.lean 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb
Shao/OQ3/AtomProjection.lean 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22
Shao/OQ3/AtomicMeasure.lean 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39
Shao/OQ3/AtomicProductControl.lean 6f886635f2201e04d1004a4f4b3b4058d406be3a283f716b70f1ce1cfaa5775f
Shao/OQ3/AtomicTailControl.lean ec528d9af8b475f1db8a78c93ab917d754365d280027a86be2823825b19c2f79
Shao/OQ3/BinaryEntropyBounds.lean 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228
Shao/OQ3/CenteredLogMGF.lean 1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4
Shao/OQ3/CenteredSampleTilt.lean d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501
Shao/OQ3/CentralFourierIntegral.lean 4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93
Shao/OQ3/CharacteristicMeasureDomination.lean ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb
Shao/OQ3/CompactTiltDomination.lean 6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623
Shao/OQ3/CompactTiltLayerMassBound.lean 5602fd17ebac0fe40fb789067cea6b9553659dad4c8965ff88aea7e106ef5cc7
Shao/OQ3/CorrectedScaleContinuity.lean b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8
Shao/OQ3/EnergyBernoulliMGF.lean e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad
Shao/OQ3/FarEnergyExponentialCover.lean 40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d
Shao/OQ3/FiniteConstraints.lean 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0
Shao/OQ3/FiniteFarArc.lean 3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71
Shao/OQ3/FiniteNormalSpan.lean 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de
Shao/OQ3/FiniteStageMeasure.lean 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1
Shao/OQ3/FundamentalFourierAsymptotic.lean aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1
Shao/OQ3/GaussianBoundaryConstant.lean c44d13d42da6711f9eec44313fb27b363513b7e75aeb83c1df79708157e65f5a
Shao/OQ3/GlobalNegativeLayerBound.lean 57b61e6e3bfd184586083e55633a563e4176cbfcf16def62a7d860d92b5c01d8
Shao/OQ3/InverseTilt.lean c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811
Shao/OQ3/JointNonlattice.lean 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559
Shao/OQ3/LocalNegativeLayerControl.lean e94a5a8e82d2a69a946a12e16f3fb2a58b174fb036becce5632d7c600b796f01
Shao/OQ3/LocalNegativeLayerTail.lean 049361c77716896922fb1d7cd3e6abf84515b76a99103c597d8d74b63a2f1856
Shao/OQ3/LocalRateMargin.lean 5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77
Shao/OQ3/NegativeLayerGeometricTail.lean 8077cfb97547c4a8c5b22da6ed17a58168a6ca1f6b2654f6799292a06a8b23f4
Shao/OQ3/NormalLayerConditionalLaw.lean 94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a
Shao/OQ3/NormalLayerFourier.lean 063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3
Shao/OQ3/NormalLayerMassBound.lean 66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1
Shao/OQ3/NormalTangentDomination.lean b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90
Shao/OQ3/NormalTangentGaussian.lean d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39
Shao/OQ3/NormalTangentMoments.lean 8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1
Shao/OQ3/NormalTangentPowerLimit.lean 819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457
Shao/OQ3/NormalTrialCost.lean 8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895
Shao/OQ3/PositiveLayerTail.lean ebcef2d9ada2df9973a16ab8f1c9806c304dbaf1d01731c9de5ffcfd9d12172a
Shao/OQ3/PositiveRate.lean 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b
Shao/OQ3/ProductMeasureDomination.lean 9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f
Shao/OQ3/RegularCovariance.lean 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853
Shao/OQ3/ResonanceArithmetic.lean cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b
Shao/OQ3/SampleBoundary.lean 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2
Shao/OQ3/SampleChangeOfMeasure.lean d6259e330afca7b95e2e206c7021a44836e32cc0add596d14a6af8bdbda25134
Shao/OQ3/SourceBinaryEntropyGap.lean f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9
Shao/OQ3/SourceEnergyGeometry.lean 3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a
Shao/OQ3/SourceFarWeightedTail.lean c9e4c14af297353c5358da6d3e75d72f712649e535102ba18297fc00a0e5261f
Shao/OQ3/SourceGaussianBoundaryProfile.lean 22df4806e0179c5dc1ea70f759895bdd6a8610ae1f212c3e16b38d0bf6282515
Shao/OQ3/SourceStarter.lean 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d
Shao/OQ3/StageCurvedLayerLimit.lean 71c85b128101af074034f454f40d25405b6898624989d464a69a73cc19db4d60
Shao/OQ3/StageLayerDecomposition.lean b6204bbbc39d029e221e473c76e8ebe34a42cf4765f4c3f7ccbd657d6311a8de
Shao/OQ3/StageLayerSeriesLimit.lean 4c797f9f5f9b47c0f62764c0b62396b9679172782d144fca29a091b83a52e02d
Shao/OQ3/StageSourceNegativeTail.lean 8b2e2eee60a9725e02653b58741cd63ba497fd5e5c5baaa0dca228fbda3ea8a0
Shao/OQ3/SummableAtoms.lean 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b
Shao/OQ3/TiltedMeasureDomination.lean 5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b
Shao/Probability/FiniteIID.lean d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b
```

## 9. 最终独立裁决与剩余义务

STATUS: CORRECT。

JUSTIFICATION: actual完整公开合取target忠实于冻结scope与真实Gaussian负半轴函数；262行全部实现、3private完整body、14private证明及全部locals已独立逐门审查。真实all-b Cauchy可积先于积分连续，正b同一邻域Gaussian可积主控先于参数积分微分，正率及非零分母先于精确halfGaussian系数化简；真实Gaussian primitive的FTC、Ioi0常值和0右连续共同给准确常数，最后只作b=κ√x的值代入，x0真实保留。全部28actual TYPE含10生成项的完整一般前提／eq_1／AtLeastTwo已核；实际Audit全owned传递公理白名单、4imports公开可达、55真实项目前置／2905Mathlib缓存及源hash、pins、历史build04非空11warning首成功与receipt绑定均一致。未发现数学、来源、类型或环境实质缺口。

此CORRECT是独立full proof判定，不把作者成功门当作证明，不接受收据叙述替代分析。无BLOCKED项、无要求改源码／增import／重编的必要修复；11style/deprecation warnings透明保留为非实质限制。作者check时review pending／未commitPR的nonclaims属历史正确状态；本报告完成不自动发布或改变旧证据。

本单元完成原25分析前置的真实Gaussian正混合身份及核IntegrableOn，直接服务随后格和－连续积分的正间隙证明。它没有证明混合格和交换、完整原24/25uniformgap、Phi字面CDF／cusp EM、U18a/hcont生产者、无条件15/19、rotation/hW/generalKL或任何根。所有root A/B/C/D仍OPEN；此前显式hcont的下游结论仍保留其条件。无commit／PR／merge／发布操作由reviewer执行。交付只限本终票及授权remote proof-review.md，lead需全文读取再决定发布。
