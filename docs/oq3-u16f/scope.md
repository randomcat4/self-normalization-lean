# OQ3-U16f：真实测度小化下的特征函数模量与紧倾斜族共同系数

冻结v1，DECLARATION_REVIEW_QUEUED，尚未批准或实现。拟Shao/OQ3/CharacteristicMeasureDomination.lean。imports Shao.OQ3.FiniteFarArc、Shao.OQ3.CompactTiltDomination、Mathlib.MeasureTheory.Measure.Sub；namespace Shao.OQ3、open MeasureTheory、noncomputable section。零新公开定义、两个公开目标。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，356–360的紧倾斜参数族共同Fourier常数所需统一模量生产者。采用真实残差测度的凸分解，直接比较本lane既有actual jointCharacteristic，不复制root公共quadraticChar/cosine恒等式或修改root所有的定义。它本身尚未给中央/远弧积分C/sqrt n或Chernoff概率。

```lean
theorem jointCharacteristic_norm_le_of_measure_lower (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ) (hm : 0 ≤ m)
    (hlower : ENNReal.ofReal m • mu ≤ nu) :
    m ≤ 1 ∧ ∀ xi eta : ℝ,
      ‖jointCharacteristic nu xi eta‖ ≤
        1 - m * (1 - ‖jointCharacteristic mu xi eta‖)

theorem exists_compact_tilted_characteristic_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ p ∈ K, ∀ xi eta : ℝ,
      ‖jointCharacteristic (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
        1 - m * (1 -
          ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖)
```

actual jointPhase=Complex.exp(((xi*x+eta*x²:ℝ):ℂ)*I)，jointCharacteristic是真Bochner复积分。它是已有公开定义，不另复制别名。首目标不假设hb或mu/nu原子性，频率任意实且整个频域有效；真实两概率、m≥0和真实measure下界不可省略。m可以0或1，m≤1是从真实总质量下界推出的输出，不预设m≤1隐藏掉边界。第二目标真有界基准mu，任意compact K含空集、参考(u0,v0)不必属于K；同一正m≤1先于全部p/xi/eta。

首目标数学路线：令a=ENNReal.ofReal m，etaMeasure=nu−a•mu。因为a有限、mu概率，小measure a•mu真有限；hlower使真实Measure.sub_apply/measurable univ合法，Measure.sub_add_cancel_of_le给etaMeasure+a•mu=nu。etaMeasure真有限（实际Measure.Sub已有isFiniteMeasure_sub）。以univ总质量比较和真实概率先得m≤1。etaMeasure.real univ=1−m的实等式须先核各测度有限、ofReal.toReal m=m、真实sub_apply与ENNReal.toReal_sub，不能用无条件带符号measure减法或top.toReal。

对同一个actual phase在etaMeasure、a•mu及mu均用连续/可测和全局norm=1建立真Integrable，不能仅借totalized积分。integral_add_measure在这两个真可积门后拆nu积分，integral_smul_measure给a.toReal=m的真实标量乘mu积分。剩余复积分模≤etaMeasure.real univ=1−m（norm_integral_le_of_norm_le_const）。复三角与m≥0得到norm(phi_nu)≤(1−m)+m*norm(phi_mu)，重排为目标。m0/m1均不除m或1−m；首目标也不需要相位有非零频率或参考law非退化。

第二目标先用已完整接受U15c exists_compact_quadratic_tilted_domination得到共同m0>0。其公开接口未给m0≤1，且K可能空，不能从选择p∈K推m0≤1。可取m=min m0 1>0并以标量单调把同一measure下界缩小，保留forall p；m≤1由min直接。每个真实quadratic tilt的概率实例必须来自U15a quadratic_exp_integrable_of_ae_abs_le，再isProbabilityMeasure_tilted，不使用Measure.tilted不可积时zero的总化。参考tilt也用同一hb/真exp可积，不需参考点属于K。对每个p的真实两个prob/measure下界应用首目标；共同m早于所有频率和p。

指定服务器只读核：Mathlib.MeasureTheory.Measure.Sub.lean源码SHA7255179e0ec6689998e84bb02b660d7499d67aeb71ee758a80914fc3142b5172，olean真实存在。72–73行sub_apply要求小measure有限、measurableSet和下界；100–102行sub_add_cancel_of_le；145–146行isFiniteMeasure_sub。Bochner.Basic 1002–1006行norm_integral_le_of_norm_le_const、1010–1015行integral_add_measure需真可积、1047–1048行integral_smul_measure；所有实转换非top门和复标量范数需在实现中明确核对。无需新缓存或root公共源码。

该线性m模量比较不同于先前U15b的产品m²/cosine积分传递。它是对实际characteristic的另一条标准充分证明，不能据此声称复制/完成root公共quadraticChar连接。后续可经已公开centeredNormalTangentCharacteristic_factor及相位模1转本lane中心特征函数；基准中央二次缺口和fararc rho<1经共同m给统一小球/远弧gap，再真积分得到紧族C/N。当前两个目标不包含这些未证明解析步骤，也不将固定mu U16a逐点常数提升为compact共同常数。

不证明紧族完整质量界、Chernoff(16)/(17)、正尾全局唯一性或远区gap、完整层和19/LLT/hW/WC/KL、根闭合或最优/新颖性。根ABCD全部OPEN。当前U16e声明审查中；本单元只冻结排队，待lead全文读完U16e最终proof票后再派唯一reviewer。review必须先盲译两个完整类型并落盘，再scope/source/真实API/数学门；批准前不实施或Leanprobe。不cachewrite/copyroot源/rebase/merge。
