# U21c 冻结：实际协方差白化、真实像律矩与一致弱Cramér

状态：FROZEN_FOR_INDEPENDENT_STATEMENT_REVIEW。上一U21b完整220行CORRECT终票全读并核89行盲前缀后PR166发布，当前feat/oq3-affine-weak-cramer/head b3362fcb26bda08f5027ef3118ad6c759f0f5138 clean；没有CovarianceWhitening源/probe/Audit/newbranch/build。v40正式关闭原A，B/C/D OPEN。

来源：R2 report.md38–60谱假设(2)、83–92真实Y=Delta^(-1/2)(W-m)及343–373有界紧倾斜稳定性。R2 SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55。U21b/PR166消除一般仿射phase/transpose频率/统一负幂常数步骤，但hfreq尚为输入；本单元从实际parabolaCovariance(mu)和实际谱(2)生产正对称白化、真实推送均值0/covI/有界全阶矩，消除任意A和caller hfreq。原始uniform实际谱仍是明确源假设，未伪装成由bounded/tilt自动生产；后续完整C须生产实际紧倾斜谱并接159，原B仍缺一般导数/均值逆和分析链。

模块Shao.OQ3.CovarianceWhitening，0公开DEF/2公开THM；namespace Shao.OQ3，open MeasureTheory，open scoped Matrix BigOperators，noncomputable section。精确imports：

```lean
import Shao.OQ3.AffineWeakCramer
import Shao.OQ3.RegularCovariance
import Mathlib.Probability.Moments.Covariance
```

完整TYPE（不得静默加强假设）：

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

真实对象/可积门：type1任意A，但中心m为同mu的真实两个积分；输入X和X²真MemLp2及真概率，得到nu每坐标真MemLp2及实际均值0、实际covariance=(A D Aᵀ)ij。Y为有限Pi实多项式连续可测；公开memLp_map_measure_iff（LpSeminorm/Basic1031–1033）、covariance_map_fun（Covariance309–320）、integral_map与实际概率map_iff完成真正推送。中心化/加法使用真实L2和概率；不得用总化零积分伪造协方差，或跨模块private helper。

白化门：type2实际D用既有parabolaCovariance定义，是[[VarX,CovXX²],[CovXX²,VarX²]]，不是任意caller矩阵。hspec取(1,0)/(0,1)得a,d>=lambdaMin>0；取(-b,a)得a*(ad-b²)>=lambdaMin*(b²+a²)>0，故delta>0，s>0,t>0，所有分母非零。精确有限代数给A对称/A D A=I；vᵀA v的分子=s||v||²+q_D(-v1,v0)>0，故输出正对称白化。这里只称已验证正对称白化及明确输出性质，不依赖一个未证等价的库逆平方根命名。

频率门：令v=Aᵀu，对称及A D A=I精确给q_D(v)=||u||²。真实hspec产生lambdaMin||v||²<=||u||²<=lambdaMax||v||²，正平方根得L*rho(u)<=rho(Aᵀu)<=U*rho(u)。这是本单元生产并喂给U21b的hfreq，不再作为第二TYPE输入；cA/RA保持与U21b精确相同，same beta。全部半径与矩字面使用Euclidean sqrt，不是Fin2 Pi max norm。

一致矩门：真实bounded给L2及|m1|<=M、|m2|<=M²。实际频率上界于e0/e1给|Aij|<=U，于是|Yi|<=2U(M+M²)，rho(Y)<=|Y0|+|Y1|<=Q=4U(M+M²)。实际AE map传递后，连续rho^k及真概率给每个自然k的真Integrable和积分<=Q^k；含k=0与k=9=8+1，后者可满足有界情形所需的一个正delta，不外推为已证一般无界8+delta。0≤Q全局交付；K空/M0/beta0/R0均保留。没有参数拓扑/联合可测要求，因为不对p积分；常数lambdaMin/lambdaMax/M/beta/c/R/L/U/Q/cA/RA全部在p、k、频率外同一固定。

承重/剩余：消除真实协方差白化、实际推送中心化与单位cov、一致bounded全阶矩及从真实谱到频率双界/标准化WC的门；直接consumer为159紧倾斜WC后完整C和原B标准化输入。未生产一般倾斜均值=gradient/covariance=Hessian、均值局部逆、compact-tilt实际统一谱或原始单点WC稳定性（159另有）、Edgeworth/远域概率/细胞与Laplace分析。必须后续实际compose159和实际谱生产者，不能据本单元关闭C/B/D；A已正式v40 CLOSED。

环境：仅small Shao import-header DFS得到11项目源，正式hash来自RootA74/v39 accepted字典+完整独立接受PR166源29457076；canonical11=1218f35137fd25486e259b6a192747642d68edbfeadc63fa44fcbb0b0b45f59a。Mathlib Covariance直接seed已在接受RegularCovariance/Variance闭图，Affine完整成功seed已通过；不重扫全Mathlib/不新造全图计数。11项目对象+1明确Covariance对象定向共12路径全存在，仅做一次，不重hash稳定缓存/旧源/跑smoke/改pins。普通Lake/own单Shao-root，非U20c view。

执行：整份CORRECT声明终票lead全读并核hash后才从冻结PR166 head b3362fcb26bda08f5027ef3118ad6c759f0f5138正常新建feat/oq3-covariance-whitening；计划PR base feat/oq3-affine-weak-cramer保持六文件一提交，若166被root整合由root处理retarget，不自行merge/reset/rebase。保持全部77旧owned refs不变。全Lean仅serverCPU14–17/native8192MiB/j4/autoImplicitfalse/单heavy；首成功不重复；首次module-owner全部TYPE/公理审计含private/generated，随后完整独立proof终票全读才接受/commit/PR。白名单propext/Classical.choice/Quot.sound；禁sorry/admit/newaxiom/unsafe/native_decide/implemented_by/证明设置弱化。root独占common/cache/pins/integration，外部CPU0–9/80GiB不动；不新agent/chat/goal，复用sole reviewer lease1。
