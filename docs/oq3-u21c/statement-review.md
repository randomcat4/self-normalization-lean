# U21c CovarianceWhitening 独立声明／来源／API审查

STATUS: IN_PROGRESS

本段是先行不可改写盲译前缀。只读取冻结 scope79 两个 Lean fence 中的三个 imports、两个完整公开 TYPE 及 header；尚未读取说明、原来源、作者路线／候选 metadata 或实际生产者证明。此门为声明／来源／静态 API 审查，不是实现审查。

## 冻结环境与全部类型原文

拟模块 Shao.OQ3.CovarianceWhitening；namespace Shao.OQ3；open MeasureTheory；open scoped Matrix BigOperators；noncomputable section。零公开定义、两个公开定理。

```lean
import Shao.OQ3.AffineWeakCramer
import Shao.OQ3.RegularCovariance
import Mathlib.Probability.Moments.Covariance
```

```lean
theorem centered_affine_parabola_mean_covariance
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (h1 : MemLp (fun x : ℝ => x) 2 mu)
    (h2 : MemLp (fun x : ℝ => x ^ 2) 2 mu)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    let m : Fin 2 → ℝ := ![∫ x, x ∂mu, ∫ x, x ^ 2 ∂mu]
    let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - m)
    let nu : Measure (Fin 2 → ℝ) := mu.map Y
    IsProbabilityMeasure nu ∧
      (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 nu ∧
        (∫ y : Fin 2 → ℝ, y i ∂nu) = 0) ∧
      ∀ i j : Fin 2,
        ProbabilityTheory.covariance (fun y : Fin 2 → ℝ => y i)
          (fun y : Fin 2 → ℝ => y j) nu =
            (A * parabolaCovariance mu * Aᵀ) i j

theorem uniform_covariance_whitened_moments_weakCramer
    {ι : Type*} (K : Set ι) (mu : ι → Measure ℝ)
    (hprob : ∀ p ∈ K, IsProbabilityMeasure (mu p))
    (M lambdaMin lambdaMax beta c R : ℝ)
    (hM : 0 ≤ M) (hmin : 0 < lambdaMin) (hmax : 0 < lambdaMax)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hbound : ∀ p ∈ K, ∀ᵐ x ∂mu p, |x| ≤ M)
    (hspec : ∀ p ∈ K, ∀ xi eta : ℝ,
      lambdaMin * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * parabolaCovariance (mu p) 0 0 +
            2 * xi * eta * parabolaCovariance (mu p) 0 1 +
            eta ^ 2 * parabolaCovariance (mu p) 1 1 ∧
        xi ^ 2 * parabolaCovariance (mu p) 0 0 +
            2 * xi * eta * parabolaCovariance (mu p) 0 1 +
            eta ^ 2 * parabolaCovariance (mu p) 1 1 ≤
          lambdaMax * (xi ^ 2 + eta ^ 2))
    (hWC : ∀ p ∈ K, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu p) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let D : ι → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (mu p)
    let s : ι → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : ι → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : ι → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    let m : ι → (Fin 2 → ℝ) := fun p => ![∫ x, x ∂mu p, ∫ x, x ^ 2 ∂mu p]
    let Y : ι → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - m p)
    let nu : ι → Measure (Fin 2 → ℝ) := fun p => (mu p).map (Y p)
    let Phi : ι → ℝ → ℝ → ℂ := fun p xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
    let L : ℝ := 1 / Real.sqrt lambdaMax
    let U : ℝ := 1 / Real.sqrt lambdaMin
    let Q : ℝ := 4 * U * (M + M ^ 2)
    let cA : ℝ := c * Real.rpow U (-beta)
    let RA : ℝ := R / L
    0 < L ∧ 0 < U ∧ 0 ≤ Q ∧ 0 < cA ∧ 0 ≤ RA ∧
      ∀ p ∈ K,
        0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
        (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
          0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
        IsProbabilityMeasure (nu p) ∧
        (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (nu p) ∧
          (∫ y : Fin 2 → ℝ, y i ∂nu p) = 0) ∧
        (∀ i j : Fin 2,
          ProbabilityTheory.covariance (fun y : Fin 2 → ℝ => y i)
            (fun y : Fin 2 → ℝ => y j) (nu p) = if i = j then 1 else 0) ∧
        (∀ᵐ y : Fin 2 → ℝ ∂nu p, Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) ≤ Q) ∧
        (∀ k : ℕ,
          Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k)
            (nu p) ∧
          (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂nu p) ≤ Q ^ k) ∧
        ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖Phi p xi eta‖ ≤
            1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)
```

## 独立量词与数学盲译

1. 第一目标以同一个实概率测度 mu 为对象，假设实际 id(x)=x 与 x² 各属于真实 L²(mu)；没有非退化或 A 可逆假设。
2. A 是任意实2×2矩阵；m=(∫x,∫x²) 是该同 mu 的实际两个均值，非外部任意中心。
3. Y(x)=A((x,x²)−m)，nu=mu.map Y；没有另选像律或输入手工概率。
4. 第一合取输出 nu 真概率；第二合取对每个实际像坐标给真 MemLp2 和均值0。
5. 第三合取对所有 i/j 精确给 cov_nu(y_i,y_j)=(A*parabolaCovariance mu*Aᵀ)ij；顺序必须是 A D Aᵀ，不能偷换成 Aᵀ D A。
6. 需要核 parabolaCovariance 的实际四项确是同 mu 的 x/x² 协方差，而非任意抽象矩阵；真实 L² 须先支持积分线性、居中和平移不变性。
7. 任意 A 可奇异或为零，第一目标不能强加输入不包含的正定性；其坐标 L²/零均值仍应成立。
8. 第二目标对任意类型 ι、任意 K、任意实测度族 mu；只在 p∈K 给 mu p 真概率，K 可空，未给参数可测／连续结构。
9. M、lambdaMin、lambdaMax、beta、c、R 同时在所有 p、频率、自然阶数之前固定；M≥0，lambdaMin/lambdaMax/c>0，beta/R≥0。
10. hbound 是同族实样本的逐p真AE绝对值界 |x|≤M，没有伪称全点支撑或只针对代理律。
11. hspec 对所有 p∈K、所有实 xi/eta 给实际 D=parabolaCovariance(mu p) 的二维对称二次型上下界 λmin(xi²+eta²)≤D00xi²+2D01xi eta+D11eta²≤λmax(xi²+eta²)。
12. 这是真实谱约束的显式caller输入；目标没有输入任意白化矩阵或频率比较，须由 D 自行生产。
13. hWC 是原 mu p 的实际抛物线 jointCharacteristic 在 sqrt(xi²+eta²)>R 上≤1−c*rho^(−beta)。
14. 所有结论 let 由这些输入唯一固定：D p 为实际协方差矩阵，s p=sqrt(D00D11−D01²)，t p=sqrt(D00+D11+2s)。
15. A p 明确为 [[D11+s,−D01],[−D01,D00+s]]/(s*t)；不是存在选择的矩阵。须核这恰为正定对称 D 的逆平方根且两分母真非零。
16. m p 是各 mu p 的真实均值，Y/nu/Phi 是对应真实居中仿射统计量、像律及其实际复相位积分。
17. L=1/sqrt(lambdaMax)、U=1/sqrt(lambdaMin)、Q=4U(M+M²)、cA=c*U^(−beta)、RA=R/L，全部是固定显式常数。
18. 目标首先输出 L/U/cA 严格正、Q/RA非负；即使 K 为空也必须交付这些数值性质。
19. 对每 p∈K 输出 s/t严格正、Aᵀ=A、A D A=I。
20. 还输出每个非零频率向量 u 的 u·A u>0；不能把 A D A=I 单独当成 A 正定的证明，因为负平方根也可能白化。
21. 对同 nu p 输出真概率、各坐标真 L²且均值0、完整实际协方差矩阵为单位阵的逐项等式。
22. 对 nu p 真AE输出字面欧氏半径 sqrt(y0²+y1²)≤Q；不是 Pi 最大值范数界。
23. 对每个自然 k，实际 rho(y)^k 真可积且其真积分≤Q^k；k=0和Q=0须按自然幂语义保留。
24. k=9 可服务原来源8+δ（δ=1）的矩门，但类型只写所有自然阶，不自动声称非整数阶或原B所有分析已完成。
25. 最后在同真实像律及同 beta 上输出统一 WC 常数 cA和RA；不允许重新选择 mu、A或中心来证明模界。
26. 必须从白化及真实谱门推出全频率 L*rho(u)≤rho(Aᵀu)≤U*rho(u)，然后才可消费既有仿射WC定理；此双界没有被偷偷输入本类型。
27. 盲审疑点：covariance.map／居中线性性和 MemLp.map 需要实际可测与可积门；不能依 covariance 总化或积分总为0绕过L²。
28. 盲审疑点：2×2显式A的代数白化、正定性与频率谱界必须在det和s/t真正性之后，不能在奇异情形靠inv/sqrt总化成立。
29. 盲审疑点：Q数值是否足以统一控制真实中心m及全像律欧氏半径；积分换元／AE支持转移须用同Y，不能把pointwise bound在不支持处误用。
30. M=0、beta=0、R=0、K空、原均值不为0都应不额外排除；非空族若M0与正谱矛盾，须由真实假设处理而非除M。
31. 所有 k/freq 的结论在同 p 和同一组全局常数之下，不允许逐p/逐阶重选Q/cA/RA。
32. 本门不输出紧倾斜族谱的来源、不建立Hessian等于实际covariance或均值逆；完整C/B仍另有承重义务。

--- END IMMUTABLE BLIND PREFIX ---

## 盲译之后的独立来源与实际API审查

上述前缀已经先行持久化；以下才对照完整 scope79、实际 R2 原件、已接受生产源和固定 Mathlib 公开 API。没有读取作者候选/scanner JSON 正文、未来或 implementation 笔记，没有以 scope 路线或作者标签替代数学论证。最初 IN_PROGRESS 是保留的历史检查点，最终状态见末节。

### 来源与声明的实际强度

实际原件 current/oq3/proofs/r2/report.md 的冻结 SHA 为 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。本门读验 38–60、83–92、343–373 行，并核 root-contract.md 64–78 的根 B/C/D 范围。
R2 41–45 使用真实抛物线统计量 W=(X,X²)、真实倾斜律及其均值／协方差；本两个目标没有引入代理随机向量或自由协方差矩阵。
R2 50–60 的实际谱(2)和标准化矩、86–92 的 Y=Delta^(-1/2)(W−m)、368 的标准化仅调整统一常数，是本节点直接承担的义务。hspec 忠实保留谱作为源假设，未声称由 bounded 或概率本身自动推出非退化。
第一目标是实际居中仿射像律的矩／协方差通用生产者；第二目标把真实 D、显式正对称白化、统一矩界和已接受仿射 WC 组合，实质消除上一节点仍需手工 A／hfreq 的门。
本节点不生产完整紧倾斜族的实际统一谱，未把实际 covariance 与倾斜 Hessian 的一般绑定、均值局部逆、远域概率／Edgeworth 等义务伪装为完成。B/C/D 仍 OPEN；A 的 v40 正式完成不为此门提供证明捷径。

## 第一目标：同一mu的真实均值、L²和协方差

实际 RegularCovariance.lean 20–24 定义 parabolaCovariance(mu) 为 [[Var_mu X,Cov_mu(X,X²)],[Cov_mu(X,X²),Var_mu X²]]。两个非对角元素按定义相同，D10=D01 不依赖额外对称性假设；但对 Var/Cov 的真实有限解释仍须前置 L²。

1. 真概率给有限测度。输入 h1/h2 已是真 MemLp2；在有限测度下可降至 L¹，所以两个 m 坐标的实际积分都有限。不是先用总化积分为零制造“均值”。
2. 常数属于 L²（实际 LpSeminorm/Basic.lean 273–274 memLp_const），因此 Z0=X−m0、Z1=X²−m1 真属于 L²；再经两项常数倍和得到每个 Yi=Ai0*Z0+Ai1*Z1 真 L²。
3. 这些 L² 前提也给各居中乘积 Zr*Zs 的真可积性。实际 Covariance.lean 113–122 的 covariance_add_left 证明明确使用 centered MemLp 与 integrable_mul，这不是无条件形式线性。
4. Y 是有限实 Pi 中的两坐标多项式组合，连续可测。不能跨模块调用 U21b 的 private affine_parabola_continuous；新模块可以如公开矩阵定义那样逐坐标展开有限和，局部诚实证明连续性，所需 continuous_pi、实多项式和有限和 API 已可见。
5. 同 mu 真概率和实际 Y.aemeasurable 给 nu 真概率；可用公开 Measure.isProbabilityMeasure_map_iff。这个证据确保 nu 是可测真实统计量像律，不依非可测 map 的兜底定义。
6. 对坐标 f_i(y)=y_i，连续性给 AEStronglyMeasurable f_i nu。实际 LpSeminorm/Basic.lean 1031–1033 memLp_map_measure_iff 接收这个证据与 Y 的 AEMeasurable，把像坐标 L² 精确等价为已建立的 Yi 真 L²。
7. 实际 Bochner/Basic.lean 1076 integral_map 给 ∫nu y_i=∫mu Yi。先有两项 L¹ 与常数 L¹，再用 integral_sub（261–268）、integral_add、integral_const_mul 和概率下常数积分，得 ∫Z0=∫Z1=0、进而 ∫Yi=0。
8. 实际 Covariance.lean 309–320 covariance_map/covariance_map_fun 需要两个目标坐标 AE 强可测及 Y 的 AE 可测，精确给 Cov_nu(f_i,f_j)=Cov_mu(Yi,Yj)，没有要求未输入的逆映射。
9. 对 Yi/Yj 使用实际 covariance_add_left/right（113–127）与 const_mul/smul（129–140），所有加法先有第2–3项真 L²／可积门；展开成四个有限协方差项。
10. 实际 covariance_sub_const_left/right（208–220）只在输入对应真实 L¹ 后去掉中心；covariance_comm（75–78）处理交叉项反序。
11. 实际 Variance.lean 197–201 covariance_self 接收 AEMeasurable X，联系 Var 与自协方差。这里 X 和 X² 连续，且已经有真实 L²／有限居中平方积分，故不是借 Var 的 ENNReal.toReal 总化绕过真实方差。
12. 最终四项为 Ai0*Aj0*D00 + Ai0*Aj1*D01 + Ai1*Aj0*D10 + Ai1*Aj1*D11，按实际有限矩阵乘法恰为 (A D Aᵀ)ij；不是 Aᵀ D A。

此目标允许退化 mu、奇异或零 A。它从不需 s/t/det 正性，不可以借第二目标的谱前提来偷偷强化第一目标。均值 m 是同一 mu 的两个积分，没有调用者自由中心或另选 law。

## 第二目标：全部显式参数的独立数学核算

以下固定任意 p∈K。先局部使用 hprob，再由实际 hbound、M≥0 与多项式连续性得 |X²|≤M² 真AE；实际 MemLp.of_bound（LpSeminorm/Basic.lean 631–633）在有限测度和 AE 强可测前提下给 X/X² 真 L²。故第一目标可用于同 mu p、同 m p 和稍后实际 A p。
在这些真有限矩门之后，记实际 D=[[a,b],[b,d]]，δ=ad−b²；D 的 b 是 Cov(X,X²)，不是任意拟合系数。

### 真正分母正性与显式正对称白化

1. 将 hspec 分别代入 (1,0) 和 (0,1)，得 a≥lambdaMin>0、d≥lambdaMin>0。
2. 将 hspec 下界代入 (−b,a)，得到 aδ≥lambdaMin*(b²+a²)>0。右端严格正由 a>0、lambdaMin>0 及 b²≥0 给出；不需任何原子正性或特殊固定支撑。
3. 由于 a>0，推出 δ>0。因此 s=sqrtδ>0 且 s²=δ。
4. a+d+2s>0，因此 t=sqrt(a+d+2s)>0 且 t²=a+d+2s；所有清分母操作都可先获得 s*t>0／非零，而非借 Real.sqrt 或除法零点总化。
5. 定义 N=[[d+s,−b],[−b,a+s]]=adj(D)+sI。冻结的 A 精确是 N/(s*t)，每个条目和负号都一致；不是另选一个存在白化矩阵。
6. 直接有限二维代数给 D*N=N*D=s*(D+sI)、N*(D+sI)=s*t²*I，因此 N*D*N=s²*t²*I。
7. 以第4项正分母归一化即 A*D*A=I。A 的两个非对角条目相同，直接得 Aᵀ=A。
8. 单有 ADA=I 不足以排除负平方根；冻结类型另外输出 A 正定是必要且可实现的。
9. 对 u=(xi,eta)≠0，A 的二次型分子为 s*(xi²+eta²)+q_D(−eta,xi)。hspec 给后项≥lambdaMin*(xi²+eta²)>0；s>0、分母s*t>0，故 u·A u>0。
10. 全部操作只需实数正性、sqrt平方、有限 Fin2 矩阵展开／ring 恒等式；不依赖新的谱函数／矩阵平方根模块或未证明的库命名等价。输出的是已验证的显式正对称白化及其完整性质，足以作本型消费者。

这一步真正从实际谱推出 det/s/t/A 的性质，不把任何手工 detpos／basepositive／A/hfreq 输入补进第二类型。对 K 外的 p，公式作为总函数可以总化；冻结结论从未对 K 外要求白化或正性，不会把这种总化当作证据。

### 从实际谱到全频率双界

令 u=(xi,eta)，v=Aᵀu=A u。由 A 对称与 ADA=I，真实二次型 q_D(v)=uᵀADAu=xi²+eta²。
以 hspec 的完整上下界用于 v 得 lambdaMin*(v0²+v1²)≤xi²+eta²≤lambdaMax*(v0²+v1²)。
记 r=sqrt(xi²+eta²)、rA=sqrt(v0²+v1²)，均非负。分别先比较非负平方，得到 sqrt(lambdaMin)*rA≤r≤sqrt(lambdaMax)*rA。
两 λ 严格正，故它们的 sqrt 严格正；合法跨乘／除法给 (1/sqrt(lambdaMax))*r≤rA≤(1/sqrt(lambdaMin))*r，正是冻结 L/U。
这里对零频率也有效，从未除 r 或 rA；上一 U21b 所需 hfreq 是对全部频率的双界，因此不能只证非零频率后遗漏零向量。
实际 Matrix/Mul.lean 1133–1135 的 dotProduct_transpose_mulVec 给正确转置双线性身份；亦可有限两坐标直接展开。没有以 Fin2 Pi 默认范数代替字面欧氏半径。
全局不需另外假设 lambdaMin≤lambdaMax：若 K 非空，hspec 已有相容性；K 空时不能从无元素抽取这一不等式，但本证明的全局 L/U 正性根本不需它。

### 真实像律／单位协方差／统一矩常数

第一目标适用于已独立建立的同 mu p 真 L² 与实际 A p。它真实给 nu p 概率、各像坐标 L²／均值0，以及 Cov_nu=A D Aᵀ。由 Aᵀ=A 和 ADA=I，每项恰为 if i=j then 1 else 0；这里单位协方差是实际 covariance 积分值。
原 m 坐标界不依赖白化结论循环推出：实际 Bochner/Basic.lean 1002–1006 norm_integral_le_of_norm_le_const，在已知有限概率下给 |m0|≤M、|m1|≤M²；本处同时已经另有真 L²／L¹，故这些实际均值不是总化替身。
对源 AE 点，|X−m0|≤2M、|X²−m1|≤2M²。不存在对支持之外点强加的全点边界。
将已证明的频率上界用于两个基向量 e0/e1，得到 Aᵀe_i（即 A 第 i 行）的欧氏长度≤U，每个真实条目 |Aij|≤U。
故每个 |Yi|≤|Ai0|*2M+|Ai1|*2M²≤2U(M+M²)。再由 rho(Y)≤|Y0|+|Y1|，精确得 rho(Y)≤4U(M+M²)=Q。Q 是保守但充分的共同常数，无缺失 sqrt2 或矩阵范数转换因子。
目标像空间谓词 {y | sqrt(y0²+y1²)≤Q} 为连续函数的闭次水平集，真可测；用实际 Map.lean 249–251 ae_map_iff 和 Y 真 AEMeasurable，将源 AE 界传到同 nu 的真 AE 欧氏界。
不可以只用 ae_of_ae_map 的反向蕴含替代这里需要的推送方向；已核 API 实际是带可测谓词的双向等价，足以支持正确方向。

对每个自然 k，g_k(y)=rho(y)^k 连续可测、非负，真AE 0≤g_k≤Q^k（先有 rho/Q 非负）。在真概率 nu 下，公开 Integrable.of_bound 给真 Integrable g_k。
在得到这条真可积性后，才能用积分单调与真常数积分 ∫nu Q^k=Q^k 给冻结积分上界；不得以不可积 Bochner 默认0伪造全阶矩。
k=0 时 g_0=1 且 Q^0=1，即使 Q=0 也适用，积分为真实概率质量1；无非法除 Q 或借 0^0 抹掉零阶矩。k=9 对应有界应用的8+δ、δ=1，可作后续 B 的矩输入，但本节点不据此宣称 B 其余分析完成。

### 真实标准化特征积分与同一beta

上述 A、真实 m、同 nu/Phi 和刚生产的 L/U 频率双界可直接实例化已完整独立接受的 U21b uniform_weakCramer_of_affine_frequency_bounds；没有跨模块 private 调用。
L/U>0 由两 λ 的真 sqrt 正性；Q≥0 来自 M≥0 和 U>0。cA=c*U^(−beta)>0、RA=R/L≥0 与 U21b 的显式常数完全一致。
U21b 消费同 hprob、hWC、A、m 和 hfreq，输出实际 nu 上的 Phi 积分模界；不是把另一个自由复数族叫作标准化特征函数。
其负幂方向与严格外区门已由真实公开已接受实现处理，含 beta=0、R=0。这里不重新选择 p、law、center、beta 或频率依赖的常数，也未依赖未验收 future lemma。

## 边界与静态环境完整性

第一目标的退化 mu／奇异 A 由真 L² 与概率足够支持；第二目标的严格谱只对 p∈K 使用。K 空时仍能全局输出 L/U/cA 正与Q/RA非负，不假设 Nonempty K。
M=0 从不作为分母；若 K 非空，该样本界与严格正谱不相容，但不需要偷加 M>0，形式推导可以在原假设下进行。K 空／M0 的全局常数输出依旧成立。
原样保留任意实际均值而非假定 X 中心0；beta0/R0、频率0、自然阶0都已分别说明。没有参数空间拓扑或联合可测门，也没有 p、k、频率外重新选择数据。
三个 imports 与 header 足够表达完整 TYPE。Matrix 1 是 Fin2 方阵单位阵；Aᵀ、*ᵥ 通过已接受 Affine 的 Matrix.Mul 公开符号；MemLp 的2与自然幂k按各自实有类型解释，没有新的∞／ContDiff scoped notation 问题。
实际 Covariance.lean 34 是 expose public section，其 add/subconst/map/comm API 皆为公开。Variance.lean 8 public import Covariance，42 为 expose public section；RegularCovariance 直接导入 Variance，提供实际 covariance_self 等可见语义。
LpSeminorm/Basic 的 memLp_map_measure_iff、MemLp.of_bound、memLp_const 以及 Bochner/Map API 已按上文真实原型逐项读验。Finite real Pi 坐标连续及复相位 AE 强可测桥沿已接受 Affine 实际环境可用。
实际实现仍需在本模块内证明/组织有限二维代数、真实矩与可测门，不能调用 U21b 私有连续性或 RegularCovariance 私有原子helper。本声明路线完全不需要这些跨 private API，也不需要新增矩阵谱／sqrt import。
这里的正确性是完整声明数学与静态可实现性判断，不预报未来 Lean elaboration、owner TYPE／公理或 proof gate PASS。

## 数学完成后才执行的轻量绑定

scope79 两端实际均103行／9256字节，SHA256 0952e68e7cc354ebc1e6fd379f68caf8a27fd75b52ed9865dbac4576caecbfc8；完整两TYPE与三个 imports 已原样留在先行前缀，未改冻结文件。
实际 small Shao-only header DFS 是11节点：AffineWeakCramer、AtomProjection、AtomicMeasure、FiniteConstraints、FiniteStageMeasure、InverseTilt、JointNonlattice、PositiveRate、RegularCovariance、SourceStarter、SummableAtoms。
直接两条承重链为 AffineWeakCramer→JointNonlattice→AtomProjection→SummableAtoms→SourceStarter→FiniteConstraints，以及 RegularCovariance→FiniteStageMeasure/PositiveRate→InverseTilt→AtomicMeasure→SummableAtoms；没有读取作者 candidate JSON 代替这个实际头图。
从已核 RootA74 正式 path-key 字典的旧10项，加独立完整接受 PR166 源29457076f283c08b093949d3c12cfb020ea0bb496e51573ad74554114e94031f，独立复现 canonical11=1218f35137fd25486e259b6a192747642d68edbfeadc63fa44fcbb0b0b45f59a。
这个正式旧源子字典绑定包括实际 RegularCovariance 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853；无须重哈希旧源／稳定对象或再做 Mathlib 全图。
本次只定向核上列11个 own项目 olean，加 Mathlib.Probability.Moments.Covariance 对象，共12路径全部实际存在。没有新 physical/public Mathlib 总计数，没有重复 pins、smoke、编译、Audit、缓存hash或对象复制。
观察到 branch feat/oq3-affine-weak-cramer，HEADb3362fcb26bda08f5027ef3118ad6c759f0f5138，git status 空；CovarianceWhitening.lean 两端均不存在，尚无本模块 source/probe/Audit/build/newbranch。
未来计划从这个冻结166head正常新建 child branch 不改变已接受源；本审查未创建分支、移动ref或修改任何旧head、scope、receipt、metadata、shared/cache/pins。
所有远端实际命令通过 tools/server.py，在 taskset -c 14-17 内轻量读取；未占用 heavy Lean、没有触及外部 CPU0–9/80GiB 或全局资源。唯一写入是本新报告与授权 remote statement-review.md。

## 最终声明裁决与剩余义务

STATUS: CORRECT
GATE: COMPLETE DECLARATION / SOURCE / STATIC ACTUAL API REVIEW ONLY；未实现、未做本模块内核 proof 验收。
JUSTIFICATION: 两个完整目标在真概率和真实L²／bounded前提下能够生产同一居中像律的真实均值／协方差；实际谱正性充分保证冻结显式A的正对称白化、合法分母及真实频率双界；Q的全部因子足以统一控制欧氏AE半径和每个自然阶真积分；同律同常数与U21b公开生产者精确匹配，边界和环境门均无发现缺口。第二目标确已消去手工任意A/hfreq输入，保留的实际hspec是源原假设而非偷换输出。

原目标→本节点消除→直接consumer→仍缺：R2(2)、86–92及368标准化→实际covariance下显式正对称白化、真实nu中心化／单位cov／全自然阶欧氏矩和统一标准化WC→紧倾斜族单点WC稳定性之后的完整C及B标准化输入→实际compact-tilt共同谱生产与159组合、一般Hessian/covariance绑定与均值逆、Edgeworth/远域概率和原B余下分析。并不消除caller实际hspec，也不证明一般无界族自动稳定。
根A按v40为 CLOSED_INTEGRATED_KERNEL_CHECKED，B/C/D OPEN。没有因本声明CORRECT而把完整C或B记为完成；未来完整源码、全部owner TYPE／公理及proof终审仍必须独立验收。

不可改写盲前缀保留126行／8989字节，SHA256 25f1185db69608b260d441c8ae69a913846a1b65ee4541825ec7b579b04e6316；最终追加后已逐字节复核未改。
