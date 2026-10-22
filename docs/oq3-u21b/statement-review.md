# U21b AffineWeakCramer 独立声明／来源／API审查

STATUS: IN_PROGRESS

本段为不可改写的先行盲译前缀。只读取冻结 scope78 的两个 Lean fence 与 namespace/open/header；尚未读取其路线说明、原始来源、实际库 API 或行政 readiness/candidate metadata。它不是实现或内核验收。审查范围为零公开定义、两个完整公开定理。

## 先行完整环境与类型保全

模块拟为 Shao.OQ3.AffineWeakCramer；namespace Shao.OQ3；open MeasureTheory；open scoped Matrix BigOperators；noncomputable section。四个显式 imports 原文：

```lean
import Shao.OQ3.JointNonlattice
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
```

两个完整目标原文：

```lean
theorem affine_parabola_characteristic_factor (mu : Measure ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (xi eta : ℝ) :
    let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - b)
    let nu : Measure (Fin 2 → ℝ) := mu.map Y
    let xiA : ℝ := xi * A 0 0 + eta * A 1 0
    let etaA : ℝ := xi * A 0 1 + eta * A 1 1
    let phi : ℂ := ∫ y : Fin 2 → ℝ,
      Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu
    phi = Complex.exp (((-(xiA * b 0 + etaA * b 1) : ℝ) : ℂ) * Complex.I) *
      jointCharacteristic mu xiA etaA ∧
      ‖phi‖ = ‖jointCharacteristic mu xiA etaA‖

theorem uniform_weakCramer_of_affine_frequency_bounds
    {ι : Type*} (K : Set ι) (mu : ι → Measure ℝ)
    (hprob : ∀ p ∈ K, IsProbabilityMeasure (mu p))
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (b : ι → (Fin 2 → ℝ))
    (L U beta c R : ℝ) (hL : 0 < L) (hU : 0 < U) (hbeta : 0 ≤ beta)
    (hc : 0 < c) (hR : 0 ≤ R)
    (hfreq : ∀ p ∈ K, ∀ xi eta : ℝ,
      L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
            (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
        Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
            (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
          U * Real.sqrt (xi ^ 2 + eta ^ 2))
    (hWC : ∀ p ∈ K, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu p) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let Y : ι → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - b p)
    let nu : ι → Measure (Fin 2 → ℝ) := fun p => (mu p).map (Y p)
    let Phi : ι → ℝ → ℝ → ℂ := fun p xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
    let cA : ℝ := c * Real.rpow U (-beta)
    let RA : ℝ := R / L
    0 < cA ∧ 0 ≤ RA ∧
      ∀ p ∈ K, IsProbabilityMeasure (nu p) ∧
        ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖Phi p xi eta‖ ≤
            1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

## 独立量词与数学盲译

1. 第一定理对任意实数轴上的测度 mu、任意实二阶矩阵 A、任意实二维向量 b 及任意实频率 xi、eta 成立。
2. 此处没有 mu 概率、有限、sigma-finite、矩可积、A 可逆、A 对称或 b 是均值等前提。
3. 向量空间是 Fin 2 → ℝ；测度及统计量由下列 let 唯一固定，不能由调用者另选。
4. Y(x)=A·((x,x²)−b)；nu 是同一 mu 在 Y 下的真实推送测度。
5. xiA=xi*A00+eta*A10；etaA=xi*A01+eta*A11，按坐标这应为 A 的转置作用于频率 (xi,eta)。
6. phi 是 nu 上 exp(i(xi*y0+eta*y1)) 的实际复 Bochner 积分，不是自由复数变量。
7. 第一合取断言 phi=exp(−i(xiA*b0+etaA*b1))*jointCharacteristic mu xiA etaA。
8. 第二合取断言上述真实 phi 的复模等于原测度 jointCharacteristic 在变换频率的复模。
9. 盲审疑点：任意无限测度下相位不必可积；须核 unconditional integral_map 与复常数乘法的总化积分语义是否足以精确保证此声明，而不能默加 mu 有限。
10. 盲审疑点：必须核 Y 及相位的实际可测门，矩阵两坐标展开、转置方向及负常数相位，不能把中心 b 当成实际矩。
11. 第二定理对任意类型 ι、任意集合 K、任意测度族 mu、任意逐参数矩阵 A 和向量 b 成立。
12. 只在 p∈K 时要求 mu p 是真实概率；不要求 K 非空、参数有拓扑或任何 p 联合可测性。
13. L、U、beta、c、R 都是在全部 p 和全部频率之前固定的实数。
14. 假设 L>0、U>0、beta≥0、c>0、R≥0；没有 beta>0 或 R>0 的额外门。
15. 对每个 p∈K、每个实频率 (xi,eta)，hfreq 提供两条真欧氏频率比较。
16. 记 rho=sqrt(xi²+eta²)，rhoA=sqrt((xi*A00+eta*A10)²+(xi*A01+eta*A11)²)。
17. hfreq 明确假设 L*rho≤rhoA≤U*rho；rho 是欧氏长度，不是 Fin 2 Pi 空间默认最大值范数。
18. hWC 明确假设同一 mu p 在所有 rho>R 的频率满足模≤1−c*rho^(−beta)。
19. hWC 只管原始族；没有把变换后族的期望结论预先作为前提。
20. 结论的 Y p、nu p 和 Phi p 全由同一个 mu p、A p、b p 固定，实际推送不能替换为代理概率律。
21. 结论常数是 cA=c*U^(−beta)、RA=R/L，不是重新存在选择的常数。
22. 输出 cA>0、RA≥0，并对每个 p∈K 输出 nu p 真概率及其全部 rho>RA 频率上的同 beta 弱 Cramér 界。
23. 所有 cA、RA、beta 不依赖 p、xi、eta；中心 b 对模只应产生单位相位，不应影响常数。
24. 盲审疑点：下界 L 用于将 rho>R/L 严格推到 rhoA>R；上界 U 配合负指数用于给出减项下界，方向须逐项核对。
25. 盲审疑点：负幂比较和乘法公式使用前要有 rho、rhoA、U*rho 的真正正性；不能靠 rpow 在 0 的总化。
26. beta=0、R=0、K=∅、任意 b 均须保留。无须在 p∉K 生产概率或频率界。
27. 本声明显式输入频率双界，并未生产实际协方差逆平方根及其共同谱界；后续标准化消费者须另行绑定这些实对象。
28. 两条声明本身不提供新的源律、一般无界族稳定性、完整根 C 或其他原根闭合。

--- END IMMUTABLE BLIND PREFIX ---

## 后续独立来源与声明审查

以下内容在上述完整盲译已落盘之后形成。此前 IN_PROGRESS 是保留的历史检查点；最终状态见本报告末尾。未读取作者 c-next-affine-standardization-notes、candidate/scanner JSON 正文或未来实现笔记，未参与实现。

### 来源的实际范围与直接承重用途

R2 原件 report.md 的 SHA256 为 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。本地实际读到 523 行／20102 字节，并核对了原件 38–60、83–92、343–373 行。

R2 40–43 的 W=(X,X²)、真实指数倾斜 P_theta，与本节点输入的抛物线统计量和任意实测度完全兼容。其 50–60 的谱界和标准化矩是假设；本声明没有伪造这些生产者。
R2 86–92 的 Y_theta=Delta(theta)^(-1/2)(W−m(theta))、平移只改变相位、标准化保持 beta，正是两条拟定理所分解的数学义务。
R2 343–369 先从真实密度下界获得未标准化族 WC，随后要求标准化只按谱界改变常数。本声明诚实输入已获原律 WC 和统一 L/U，不把它们包装成由仿射恒等式自行证明。
实际 root-contract.md 66–72 仍要求标准化倾斜族的矩、谱和 B 的 Fourier/Edgeworth 等其他义务；76–78 的有界族稳定性也不单由本节点完成。

第一目标覆盖准确的统计量／转置频率／中心相位身份；第二目标从明确的统一频率双界传递实际像律的 WC。直接消费者是已接受 PR159 未标准化紧倾斜族 WC 之后的真实协方差标准化。后续必须把 A p 绑定实际 Delta(p)^(-1/2) 或已证明等价的白化，并从实际谱界产生 L/U。不能以本门批准代替这些生产者或完整根 C。

### 第一目标：任意测度下的真实积分身份

1. 按实际 Mathlib/Data/Matrix/Mul.lean 719–729，(A*ᵥv)i 是第 i 行的有限 dotProduct；dotProduct 在 76–77 定义为有限乘积和。Matrix 不是这里的协方差或自伴矩阵假设。
2. Fin 2 的两项展开给 Y0=A00*(x−b0)+A01*(x²−b1)，Y1=A10*(x−b0)+A11*(x²−b1)。
3. 因而 xi*Y0+eta*Y1=(xi*A00+eta*A10)*x+(xi*A01+eta*A11)*x²−[(xi*A00+eta*A10)*b0+(xi*A01+eta*A11)*b1]。
4. 所以冻结 xiA/etaA 的确是 Aᵀu，而非 Au。若 A 非对称仍成立；不需要修改类型或增加 A 对称假设。
5. 每个 Y 坐标是实多项式和常数的组合。有限 Pi 的坐标连续判据直接给 Continuous Y；这里不需要新导入矩阵拓扑或矩阵范数模块，也不需要 A 可逆。
6. 实数／有限实 Pi 使用标准 Borel 可测结构。实际 BorelSpace/Basic.lean 494–501 的 Continuous.measurable/aemeasurable 适用于这个 Y。
7. 实际目标相位 F(y)=exp(i(xi*y0+eta*y1)) 连续；强可测性来自复数伪度量、第二可数性质及实际 StronglyMeasurable/Basic.lean 723–726 的 Continuous.stronglyMeasurable，或 AEStronglyMeasurable.lean 240–243 的对应桥。对任何 nu 都可形成所需强可测／AE 强可测证据。
8. Bochner/Basic.lean 1065–1074 的 integral_map_of_stronglyMeasurable 要求 Measurable Y 与 StronglyMeasurable F，没有 Integrable 或有限测度前提。其证明显式分 Integrable 与非 Integrable 两支；后一支通过 integrable_map_measure 等价及 integral_undef 同步两边，不能把这个分支误报为缺口。
9. 同文件 1076–1086 的 integral_map 接收 AEMeasurable Y mu 与 AEStronglyMeasurable F (mu.map Y)，同样没有概率或可积前提。因此冻结第一目标的任意 mu 范围有实际库语义支持，不应为了使用概率版 integrable_jointPhase 而擅自缩窄声明。
10. 将第 3 项恒等式复嵌入、乘 I，再用 Complex.exp_add，逐点得到 F(Yx)=exp(−i(xiA*b0+etaA*b1))*jointPhase xiA etaA x。常数相位符号是负，且 b 在 A 的内侧；不能换成未经转置的频率与 b 的点积。
11. 实际 Bochner/Basic.lean 288–290 integral_const_mul 对任意复常数和函数无可积前提成立；它由同文件 275–278 的 integral_smul 给出。故可以在刚建立的 map 积分身份后精确提出这个固定复因子，不依赖虚假的积分加法或无限测度总质量有限。
12. 实际 JointNonlattice.lean 20–24 明确定义 jointPhase 与 jointCharacteristic：后者就是同一 mu 上 exp(i(xiA*x+etaA*x²)) 的实际复积分。结论未用代理 characteristic family。
13. 该文件 26–27 公开 jointPhase_norm，实际消费 Complex.norm_exp_ofReal_mul_I。任意实相位的复指数模等于 1；结合 norm_mul 即得第二合取，不需除相位或除积分。
14. 若 mu 真无限、相位不可积，第一目标描述的是固定库的总化 Bochner 积分。此时相应非可积身份由第 8–11 项 API 保证；本目标没有虚称这些相位“真可积”。在随后概率消费者中，相位才有真正可积性。

边界逐项成立：mu=0、任意无限测度、A=0／奇异／非对称、b 任意、xi=eta=0 都没有非法除法、对数或负幂。第一目标没有任何隐藏概率或矩门。

### 第二目标：实际推送概率与精确统一常数

固定任意 p∈K 后才局部使用 hprob p hp。上一节的同一 Y p 连续可测，所以 nu p 是真正的可测像律；不是 Measure.map 对不可测映射的兜底定义。
实际 Probability.lean 124–131 的 map 概率 instance 本身还有总化分支，因此“infer_instance 成功”单独不能证明本声明的真实统计量含义。本门已另外建立 Y p 可测，并可用其 AEMeasurable 证据和 map_apply_of_aemeasurable 对 univ 的精确等式验证 nu p(univ)=mu p(univ)=1。
目标相位连续且模恒为 1，在真概率 nu p 下以常数 1 支配，从而真正 Integrable。原律的变换频率相位也可用 JointNonlattice.lean 29–35 的公开 integrable_jointPhase。这些真可积门不从第一目标的总化语义偷换而来。

以下令 r=sqrt(xi²+eta²)，rA=sqrt(xiA²+etaA²)，z=−beta。r 与 rA 均为非负实数；这里全程不使用 Fin 2 Pi 默认最大值范数作为频率半径。

1. 先由 R≥0、L>0 得 RA=R/L≥0；由 U>0 和实际 Real.rpow_pos_of_pos（Pow/Real.lean 116–117），得 U^z>0，因此 cA=c*U^z>0。
2. 对任意 r>RA，由 RA≥0 得 r>0；以正 L 跨乘 R/L<r，精确得 R<L*r。没有除 r、R 或 beta。
3. hfreq 的下界 L*r≤rA 给 R<rA。由于 R≥0，rA 真正严格为正，允许在原 hWC 的严格外区实例化 (xiA,etaA)。
4. hfreq 的上界给 rA≤U*r；U*r>0。由 hbeta 得 z≤0。
5. 实际 Pow/Real.lean 565–569 的 rpow_le_rpow_of_nonpos 原型为 hx:0<x、hxy:x≤y、hz:z≤0，结论 y^z≤x^z。取 x=rA、y=U*r，得到 (U*r)^z≤rA^z。这个方向给所需减项下界，而非上界。
6. 实际同文件 476–483 的 mul_rpow 需要两底数非负。现在 U>0、r>0 已真实获得，所以 (U*r)^z=U^z*r^z；不使用 0 的负幂总化。
7. 乘正 c，得 cA*r^z=c*(U*r)^z≤c*rA^z，进而 1−c*rA^z≤1−cA*r^z。
8. 第一目标模身份与 hWC 给 ‖Phi p xi eta‖=‖jointCharacteristic (mu p) xiA etaA‖≤1−c*rA^z≤1−cA*r^z，精确为冻结结论。
9. cA、RA 均在全部 p、xi、eta 之前由同一个 L/U/beta/c/R 固定，没有逐参数、逐频率或 n 依赖选择。

K 为空时 p∈K 部分真空，但 cA>0、RA≥0 仍由实际标量门交付，无 Nonempty K 输入。任意中心 b p 只贡献模为 1 的相位。没有 p 的积分或极限，故不需要索引类型的可测空间、K 可测、A/b 关于 p 连续或联合可测。
beta=0 时 z=0、U^0=r^0=1，结论正是原常数 c 的传递；不把 source 的 0<beta<2/5 擅加到这个更一般代数目标。R=0 时只使用严格 r>0 外区。第一目标允许奇异矩阵，第二目标对非空 K 的正 L 全频率下界已诚实排除频率坍缩，不需要额外逆矩阵接口。

### 固定环境与公开可达性判断

四个 imports 的符号与 header 一致；Matrix scope 实际在 Mul.lean 722–723 绑定 *ᵥ；完整 Matrix 定义和 dotProduct 均位于公开 section（55）。BigOperators 支持有限和；本类型不用 Topology 的 nhds 记号或 ContDiff ∞ 等额外 scoped notation，不存在此前不同单元的同类环境缺口。
Bochner/Basic.lean 132 为 expose public section，其两个 integral_map、integral_const_mul 是实际公开声明，不涉及外模块 private helper。Pow/Real.lean 17 为 expose public section，所需 rpow API 实际公开。没有依赖 Mathlib 中不在本 imports 下的新矩阵谱或逆平方根模块。
JointNonlattice 实际公开 20–43 的 phase/characteristic/真概率相位可积及范数上界可以直接消费；其 45 行私有严格凸辅助和后续原子非格点证明不是本节点接口需求。
公开可测／强可测桥已经由上述实际固定源码核实；JointNonlattice 29–35 也真实使用了相同连续相位的 AE 强可测与 Integrable.of_bound API。有限实 Pi、复数的标准 Borel／第二可数实例满足已读原型，不需自建可测结构或拓扑。
本门只判数学与静态实现环境可行，没有本模块 Lean elaboration、source build、module-owner Audit 或新生成常量可供验证，也没有预报其内核 PASS。

## 数学完成后才执行的轻量行政绑定

冻结 scope 两端均 71 行／7379 字节，SHA256 均为 57f5eaf02d4c5b36aded5bff04b33ea57cd85d36dc4b671baac619cfebee101e。完整 0DEF／2THM 类型与四个 imports 已原样保存在先行前缀；本报告没有改写 scope。
实际只读 Shao-only 导入头链为 JointNonlattice→AtomProjection→SummableAtoms→SourceStarter→FiniteConstraints，止于这五个项目模块。没有递归重扫已通过的 Mathlib 全图，也不声称本次得到一份新的 public/physical Mathlib 节点总数。
五个正式接受源的绑定从已核 RootA74 prerequisite-hashes.json 提取，而非作者 candidate JSON。canonical 紧凑路径键字典 SHA 为 bc48253cce1ae61632e2f1c21945b41c6f7839c681075d8b9814140e54e3587f，独立复现与冻结声明相同：

| canonical source-relative key | 正式已接受 SHA256 |
|---|---|
| Shao/OQ3/AtomProjection.lean | 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22 |
| Shao/OQ3/FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| Shao/OQ3/JointNonlattice.lean | 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559 |
| Shao/OQ3/SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| Shao/OQ3/SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |

定向只读检查实际八个 olean 路径均存在：上述五个 own .lake/build/lib/lean/Shao/OQ3 对象，以及 mathlib build 下 Data/Matrix/Mul、MeasureTheory/Integral/Bochner/Basic、Analysis/SpecialFunctions/Pow/Real 三个显式对象。此检查只核文件存在性，没有重新编译、重哈希旧稳定对象、复制缓存或改 LEAN_PATH。
旧闭图与 pins 使用既有已验收证据：Joint 旧接受链；Matrix.Mul 在接受的真实 mulVec 消费链；Bochner.Basic 为已用积分 API 的公开根；Pow.Real 是 PR159 已通过的直接种子。本门不把文件存在或复用图标签当作数学证明；真正可用性已由前文实际 API/body/条件读验支持。
实际观察的工作树仍为 feat/oq3-source-smooth-mean-map，HEAD d4a9ffc332fe8247b121dc3298c322c52ac1d26b，git status --porcelain 为空；本模块 AffineWeakCramer.lean 两端均不存在。尚无本模块 source/Audit/probe/build/newbranch。本声明门没有任何新 Lean 检查记录或需要宣称通过的内核公理审计。
所有远端读取均经 tools/server.py，并在 taskset -c 14-17 内执行；没有占用 heavy Lean、触及外部 CPU0–9/80GiB、增加资源或运行 smoke。写入范围只限本报告与授权 remote statement-review.md。未改 scope/源/旧票/receipt/pins/cache/任何 frozen head。

## 最终裁决与未完成义务

STATUS: CORRECT
VERDICT_SCOPE: U21b DECLARATION / SOURCE / STATIC API GATE ONLY；不是完整证明或内核验收。
JUSTIFICATION: 两个完整类型都指向实际抛物线统计量的可测仿射推送；第一目标在真实公开无条件积分换元与常数乘法语义下对任意 mu 成立，转置坐标和负相位精确；第二目标对真概率像律按显式 L/U 双界传递，同一 beta、cA=c*U^(−beta)、RA=R/L 的符号、严格区域与 rpow 条件均满足，空 K／beta0／R0／任意中心边界保留。没有发现须改冻结类型或 imports 的实质缺口。

原始义务→本声明消除的门→直接消费者→剩余：R2 90–92／368 的仿射标准化→精确真实特征积分相位与 Aᵀ 频率身份、统一负幂常数与概率转移→未标准化紧倾斜族 WC 后的实际协方差白化→仍须生产 actualCov 逆平方根／等价白化和实际谱双界、标准化矩及完整根 C/B 分析。hfreq 与 hWC 依旧是明确 caller 输入，不是本节点已经消去的假设；本门不引入任意代理特征族，不改 law，不声称一般无界 tilt 稳定或最优常数。

审查期间收到根协调正式 v40 更新：PR164 已验收整合 159/161/162/163，原 OQ3 A 状态为 CLOSED_INTEGRATED_KERNEL_CHECKED；B/C/D 仍 OPEN。这是晚于冻结 scope78／盲译前缀的行政更新，不改历史字节，也不将本 U21b 声明当成 C 的完成。
更新绑定为 main5591a25ddc767e6edfd618a88855075c2af7e375、accepted dc1604d8e9c88781166a0c797f45b84ff013673a、finaltree237f22e49ab4af8e80484cbe312fdbbdb10ed3ab、receipt-v40 2ef611852d796dd446c21479c2f023d320a7333eddd75863d059f65db3d76108；本门未重跑 root 成功 gate 或旧对象检查。早期 gatecode/tree 不与最终 accepted/finaltree 混同。
冻结 scope 计划以后从已接受 v39 59a531b89eff7c11e4fc53583067f2cd3b53a517 正常新建独立分支仍不改变数学；本门没有修改分支。最终实现、全部 owner TYPE、公理与 proof gate 均须后续独立完成。

不可改写盲前缀：94 行／6227 字节，SHA256 fc4de4aaad986009ed890f76783679d946f29cec018bf8038240d2f94720c9ca。最终追加后独立重核其原字节未变。
