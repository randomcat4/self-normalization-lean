# OQ3 U21e 独立声明、来源与公开接口组合审查

## 不可改写的先行盲译前缀 BEGIN

角色：全新独立声明审查者。本段在读取冻结 scope 的说明段、原来源、root-contract、两条 public seed、任何作者证明与任何旧审查之前写成。此前只读取项目行政约束、math-theorem 技能及必要角色/机械核验边界参考，以及 scope 第1行标题和两个 Lean fence。这里只记录类型本身的独立解释，不承诺已完成来源或接口匹配。

冻结题面标题：U21e 冻结：完整有界紧倾斜族的实际白化、统一矩与弱Cramér装配。
冻结 scope：drafts/oq3/eighty-first-unit-scope.md；93行，8682字节，SHA256 dbd4392151790ce2a9e86cc84f8fe26fe6e116c84444d79fa31847fb53fd9d99。
目标：Shao.OQ3.exists_compact_tilted_whitened_family；0 DEF / 1 THM。

### 完整原始导入与 TYPE（仅复制两个 fence）
```lean
import Shao.OQ3.CovarianceWhitening
import Shao.OQ3.CompactTiltCovarianceSpectrum
```

```lean
theorem exists_compact_tilted_whitened_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    let D0 : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance mu0
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      let lo : ℝ := m * D0.det / (D0 0 0 + D0 1 1)
      let hi : ℝ := 2 * (M ^ 2 + M ^ 4) + 1 + lo
      let c0 : ℝ := m ^ 2 * c / 2
      let mup : (ℝ × ℝ) → Measure ℝ := fun p =>
        mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
      let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (mup p)
      let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
      let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
      let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
        ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
          ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
      let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
        ![∫ x, x ∂mup p, ∫ x, x ^ 2 ∂mup p]
      let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x =>
        A p *ᵥ (![x, x ^ 2] - means p)
      let nu : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (mup p).map (Y p)
      let Phi : (ℝ × ℝ) → ℝ → ℝ → ℂ := fun p xi eta =>
        ∫ y : Fin 2 → ℝ,
          Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
      let L : ℝ := 1 / Real.sqrt hi
      let U : ℝ := 1 / Real.sqrt lo
      let Q : ℝ := 4 * U * (M + M ^ 2)
      let cA : ℝ := c0 * Real.rpow U (-beta)
      let RA : ℝ := R / L
      0 < lo ∧ lo < hi ∧ 0 < c0 ∧
        0 < L ∧ 0 < U ∧ 0 ≤ Q ∧ 0 < cA ∧ 0 ≤ RA ∧
        ∀ p ∈ K,
          IsProbabilityMeasure (mup p) ∧ (∀ᵐ x ∂mup p, |x| ≤ M) ∧
          MemLp (fun x : ℝ => x) 2 (mup p) ∧
          MemLp (fun x : ℝ => x ^ 2) 2 (mup p) ∧
          (ENNReal.ofReal m • mu0 ≤ mup p) ∧
          (∀ xi eta : ℝ,
            lo * (xi ^ 2 + eta ^ 2) ≤
                xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ∧
              xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ≤
                hi * (xi ^ 2 + eta ^ 2)) ∧
          (∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
            ‖jointCharacteristic (mup p) xi eta‖ ≤
              1 - c0 * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) ∧
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
### 独立盲译：全部量词与真实对象

1. 输入是实数轴上的一个测度 mu，并带 IsProbabilityMeasure mu 实例。给定实数 M≥0 及 mu-几乎处处 |x|≤M；给定实参数对集合 K⊆ℝ×ℝ 及 IsCompact K，不要求 K 非空。u0、v0、beta、c、R 都是实数，只有 beta≥0、c>0、R≥0 三个符号限制。
2. 唯一弱 Cramér 输入只针对同一实际参考倾斜律 mu0=mu.tilted(x↦u0*x+v0*x²)：对每个实频率 xi、eta，只要 R<sqrt(xi²+eta²)，其 jointCharacteristic 的复模至多 1−c*rpow(sqrt(xi²+eta²),−beta)。没有调用者提供的族弱 Cramér、族概率、谱上下界、频率双边界或白化矩阵前提。此盲译尚未展开 jointCharacteristic 的定义；之后必须核对它确为实际 (x,x²) 的特征函数。
3. 在结论中先以 let 固定 mu0 及 D0=parabolaCovariance mu0，再存在一个实数 m，满足 0<m 且 m≤1。该同一个 m 先于所有 p、k、xi、eta 量词选定。parabolaCovariance 在盲译中只按类型中真实定义名记录；其积分/协方差含义待随后公开定义核对。
4. 其余全部对象都是字面的 let 绑定，没有额外存在选择：lo=m*det(D0)/(D0[0,0]+D0[1,1])；hi=2*(M²+M⁴)+1+lo；c0=m²*c/2。对每个 p=(p.1,p.2)，mup(p)=mu.tilted(x↦p.1*x+p.2*x²)，D(p)=parabolaCovariance(mup(p))。
5. s(p)=sqrt(D00(p)*D11(p)−D01(p)²)，t(p)=sqrt(D00(p)+D11(p)+2*s(p))。A(p) 是类型中完整写出的对称2×2矩阵，分母同为 s(p)*t(p)：第一行 ((D11+s)/(s*t), −D01/(s*t))，第二行 (−D01/(s*t), (D00+s)/(s*t))。没有让调用者任给等价白化矩阵。
6. means(p) 是在同一 mup(p) 下的实际积分向量 [∫x, x；∫x, x²]；Y(p)(x)=A(p)*ᵥ([x,x²]−means(p))；nu(p) 是同一 mup(p) 经 Y(p) 的 map。Phi(p,xi,eta) 是在该实际 nu(p) 上对 exp(((xi*y0+eta*y1):ℂ)*I) 的积分，不是抽象提供的函数。
7. 频率/支撑常数全局固定为 L=1/sqrt(hi)、U=1/sqrt(lo)、Q=4*U*(M+M²)、cA=c0*rpow(U,−beta)、RA=R/L；同一个 m 同时参与测度下界、lo、c0，进而也参与 cA。所有这些常数都在 p、自然数 k 及频率量词之外。

### 独立盲译：全部输出

8. 首先输出 0<lo、lo<hi、0<c0、0<L、0<U、0≤Q、0<cA、0≤RA。除 m≤1 外，没有另外声明 hi 或 L/U 的大小排序，但上述正性隐含 hi>0。参考点 (u0,v0) 不要求属于 K。
9. 对每个 p∈K，同时输出：mup(p) 为概率测度；同一支撑界 |x|≤M 几乎处处成立；x 和 x² 在 mup(p) 下均属于 MemLp 2；ENNReal.ofReal(m) 标量乘 mu0 的测度不大于同一 mup(p)。
10. 对每个 p∈K 及每个实 xi、eta，真实 D(p) 的二次型 q=xi²*D00+2*xi*eta*D01+eta²*D11 同时满足 lo*(xi²+eta²)≤q≤hi*(xi²+eta²)。同一 p 的未白化 jointCharacteristic 在原阈值 R 之外满足系数 c0、同一 beta 的弱 Cramér 界。
11. 对每个 p∈K，s(p)>0、t(p)>0、A(p)ᵀ=A(p)、A(p)*D(p)*A(p)=1；对每个非零频率向量（xi≠0 或 eta≠0），xi*(A(p)*ᵥ[xi,eta])0+eta*(A(p)*ᵥ[xi,eta])1>0。因此 A 的正定要求也是真实输出，不是前提。
12. 对每个 p∈K，实际 nu(p) 为概率测度；每个坐标 i∈Fin 2 在 nu(p) 下属于 MemLp 2 且实际积分为0；每对坐标 i、j 的 ProbabilityTheory.covariance 恰为 Kronecker delta（i=j 时1，否则0）。
13. 对每个 p∈K，nu(p)-几乎处处 sqrt(y0²+y1²)≤Q；对每个自然数 k，欧氏半径的 k 次幂在同一 nu(p) 下可积，且实际积分≤Q^k。量词含 k=0，也含 k=9，没有把 k 限成正数或限定某个矩阶。
14. 对每个 p∈K 及实频率 xi、eta，只要 RA<sqrt(xi²+eta²)，字面实际 Phi 的复模≤1−cA*rpow(sqrt(xi²+eta²),−beta)。

### 独立盲译：边界及尚待核对的风险

15. 类型没有要求 M>0、beta>0、R>0、K 非空或参考点属于 K。M=0、beta=0、R=0 都必须在随后审查中诚实处理，不能偷加排除条件。K=∅ 时族断言真空，但全局 m、lo、c0 等正性仍有义务。频率0不被末尾严格阈值与 RA≥0纳入；谱双边界仍量化频率0，非零正定性明确排除频率0。
16. 范围明确使用 sqrt(y0²+y1²) 与 sqrt(xi²+eta²) 作为二维欧氏半径。载体 Fin 2→ℝ 的默认范数可能不是该半径；后续匹配不得把默认 Pi 范数与这里的欧氏表达式直接等同。
17. 实数除法、sqrt、rpow、积分和 covariance 在 Lean 中是总函数；类型本身的 let 绑定不保证分母非零或积分真实可积。随后必须核对公开接口确实给出 det/trace 正性、s*t 非零、参考与族的概率及所需可积性，才能排除总化漏洞。
18. 本先行段只做完整类型盲译，没有运行 Lean、probe、公理审计或远程命令。它不认定任何种子已经进入 main，不认定 C 或 B/D 原根已闭合。

## 不可改写的先行盲译前缀 END

## 后续审查范围与精确材料

这是声明静态组合可行性门。下列判断不使用作者或旧审查者的结论作为证明，也不重新审查两条 seed 的实现证明；它检查给定精确 public TYPE 对本新声明的逐项蕴含、真实对象语义及来源范围。角色、资源和只写本文件的权限已由 AGENTS.md、SERVER.md、TEAM.md、REGISTRY.json 与 TAKEOVER.md 核对。本轮不启用 math-ultra，不派生子实例。

先行前缀已先于后续材料落盘，完整保留本文件第1–114行、前9927字节；SHA256 为 5f151e787112eaf3349b30eb047e317531f61b058e69844ebb70240001bcd812。其字节哈希在继续读取材料前、追加前均重新确认。本段及以后仅为追加。

| 材料 | 实读范围与身份 |
|---|---|
| eighty-first-unit-scope.md | 先读第1行与第11–85行的两个 Lean fence，盲译落盘后读完整93行；8682B；SHA256 dbd4392151790ce2a9e86cc84f8fe26fe6e116c84444d79fa31847fb53fd9d99 |
| C:/game/shao/current/oq3/proofs/r2/report.md | 完整523行；重点38–60、74–76、83–92、343–373；实核 SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55 |
| drafts/oq3/root-contract.md | 完整82行，重点第5节；历史行政状态按当前 A 已闭合、B/C/D 仍开放解释 |
| drafts/oq3/CovarianceWhitening.lean | 精确 SHA256 d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8；公开类型212–226、291–345 |
| drafts/oq3/CompactTiltCovarianceSpectrum.lean | 精确 SHA256 99b8b9b20f1860ddd7890d8b4d317825ce76572e1c0d209d6843340a33b0c634；公开类型99–112、182–214 |
| 必要已有公开定义/API | curated library/Shao/OQ3/RegularCovariance.lean 20–24；JointNonlattice.lean 20–24、29–30的可积性类型；CompactTiltWeakCramer.lean 17–37；CompactTiltDomination.lean 15–16、30–42 |

当前正式接受基线按任务和 REGISTRY 为 v42/main 4cae9790a5d21e126ffdd7b4b6adbc836aa185e9；169/170 仍作为精确待整合 seed 使用，不因两张既有独立票而推断它们已经进入 main。本报告没有修改或刷新这些行政状态，也没有读取任何旧 statement/proof review 全文、U21e 作者 proof-plan/未来 notes 或 scanner/candidate 元数据。

## 独立来源与语义核对

| 来源精确位置 | 新声明的对应位置及判断 |
|---|---|
| R2 40–43，root-contract 28、37 | W=(X,X²)；mu0、mup 都是同一 mu 对 p.1*x+p.2*x² 的实际二次指数倾斜（scope 26、32–34）。没有换成自由二维向量、三角阵律或其他参考律。 |
| R2 45、50–60 | 原文的标准化基于真实倾斜均值和协方差。scope 34、40–44 使用实际 covariance/variance 矩阵、实际积分均值及实际推前律；scope 60–64 给共同谱，77–81给统一欧氏自然阶矩。以 k=9 可供原文8+delta条件中的 delta=1。这里没有宣称任意非整数矩已成 Lean 输出。 |
| R2 74–76 | 有界时从一个参考倾斜的实际 WC 传到紧参数族。scope 18–25仅输入 base probability、AE boundedness、compactness及该单点WC，概率、L²、谱和族WC均在输出。参考点无需在K，与密度比较的数学含义相容。 |
| R2 83–92 | Y_theta=Delta^(-1/2)(W−mean)，平移只改变相位，线性变换保持beta。scope 35–47和68–84固定真实正对称白化矩阵、中心化像律及其实际特征积分，beta保持不变，只有c与R变为同一族的cA与RA。 |
| R2 343–369，root-contract 76 | 同一密度下界m产生m²倍平方模缺口，再给c0=m²c/2。scope 28–31、59、65–67、51用同一m，测度下界和WC没有各自另选常数。 |
| R2 371–373，root-contract 66–72、78 | 本声明限于有界mu，未扩展单点WC稳定性到无界情形，也未输出原B尾展开、Song/Edgeworth、均值逆、胞重建、Laplace或远区概率结论，更没有原D十六原子丢番图见证。 |

必要公开定义消除了名称歧义：RegularCovariance 20–24 的 parabolaCovariance 真的是 Var_mu(x)、Cov_mu(x,x²)、Var_mu(x²) 组成的对称2×2矩阵；JointNonlattice 20–24 的 jointCharacteristic 真的是 ∫ exp(i*(xi*x+eta*x²)) dmu。候选没有把这两个真实对象替换为自由矩阵或抽象函数。原文以 Hessian 表示同一协方差；本门只确认候选确实使用 covariance，不把“对任意相关mu证明实际 log-partition Hessian等于该矩阵”算作本单元已输出的额外结论，原B的对应接口仍须按正式冻结范围核验。

## 两条完整公开 TYPE 的逐项组合

记 seed 170 为 T=exists_compact_tilted_covariance_spectral_bounds（182–214），seed 169 为 W=uniform_covariance_whitened_moments_weakCramer（291–345）。以下每个条件都来自它们的完整真实类型，而非 scope 89行的作者接口说明。

第一步的类型替换是 T(mu,M,hM,hb,K,hK,u0,v0,beta,c,R,hc,hWC)。T 183–189与候选18–25的对应输入字面相同；T本身不要求hbeta、hR，它们在候选中明确保留以供第二步使用。T 190–194的mu0、D0、存在m、lambdaMin、lambdaMax分别与候选26–30的mu0、D0、m、lo、hi完全一致。这里从T的一次存在消去固定唯一使用的那个m，之后不另选m。

T 195直接给0<lo、lo<hi、0<c0；由0<lo<hi严格传递即得0<hi。这已经充分满足W 295的hmax:0<lambdaMax；W不要求独立的trace/determinant假设，也不要求调用者证明任何lambdaMin/lambdaMax之外的矩阵正定前提。

| W 291–309的输入槽 | 来自候选或同一次T输出 |
|---|---|
| ι、K、mu（292） | ι=ℝ×ℝ；K就是原K；W的族mu取候选mup，不取参考mu0 |
| hprob（293） | T 196–198的每个p∈K的实际mup概率性 |
| M、lambdaMin、lambdaMax、beta、c、R（294） | M、lo、hi、beta、c0、R；其中W的c必须取c0=m²c/2，不能误用原参考c |
| hM、hmin、hmax（295） | 原hM；T的0<lo；0<lo<hi推出0<hi |
| hbeta、hc、hR（296） | 原hbeta；T的0<c0；原hR；不增强为严格正beta或R |
| hbound（297） | T 198的同一mup在同一M内的AE界 |
| hspec（298–306） | T 202–210的真实parabolaCovariance(mup p)双边二次型界，与候选D p同义展开 |
| hWC（307–309） | T 211–214的原阈值R、同beta、系数c0的实际族jointCharacteristic界 |

W无需调用者提供hfreq；候选也没有增设它。W调用所需hspec、hprob及族hWC均是T的输出，不是新声明输入。T 199–201额外给出的两个MemLp 2及measure lower在组合中保留为最终输出，没有丢弃。

| W输出与候选let/输出的精确对齐 | 核对 |
|---|---|
| W 310–315 ↔ scope 34–39 | D、s、t及A的每一个条目和分母s*t相同；没有换转置、负号、对角位置或平方根分支 |
| W 316–318 ↔ scope 40–44 | W内部名m在这里仅重命名为means，避免与密度下界标量m混淆；两个积分、中心化向量Y、nu=(mup p).map(Y p)逐字绑定同一law |
| W 319–321 ↔ scope 45–47 | Phi同为实际nu上的exp(i*(xi*y0+eta*y1))积分；没有以仅满足某些性质的函数替代 |
| W 322–326 ↔ scope 48–52 | L=1/sqrt hi，U=1/sqrt lo，Q=4U(M+M²)，cA=c0*rpow U(−beta)，RA=R/L；所有参数均为上述一次调用的值 |
| W 327 ↔ scope 54 | L、U、Q、cA、RA的五个符号结论完全相同 |
| W 328–331 ↔ scope 55、68–70 | 同一p∈K下s>0、t>0、A对称、A*D*A=1及非零向量对A二次型严格为正，全部直接输出 |
| W 332–337 ↔ scope 71–76 | 实际nu概率、坐标L²/均值0、所有坐标对协方差为if i=j then 1 else 0，完全相同 |
| W 338–342 ↔ scope 77–81 | AE欧氏半径界及每个自然k的可积性/积分≤Q^k完全相同，没有替换为默认Pi范数 |
| W 343–345 ↔ scope 82–84 | 同RA、cA、beta及实际Phi的统一WC结论完全相同 |

T在每个p后使用局部let mup，候选提前定义函数mup；在固定p处beta展开/let展开后是同一个mu.tilted表达式。T的lambdaMin/lambdaMax改名lo/hi、W内部积分均值m改名means也只是绑定变量改名。最终需要的操作只有从一次T输出选定m，从其每点合取中取各分量，进行上述一次W应用，再按候选顺序合取回填。没有交换“对每个p存在m”和“存在m对所有p”的顺序；两个public seed在类型中已分别给出所需全局常数和所有p的输出，无需选择新的概率族、中心、矩阵或频率常数。

## 同m、量词、退化情形与总化风险复核

1. 同m链完整：T的同一个m出现在ENNReal.ofReal m • mu0≤mup p、lo=m*detD0/traceD0、c0=m²c/2；W使用该lo和该c0，故cA=(m²c/2)*rpow(1/sqrt(lo),−beta)。没有把m换成另一密度比较见证或先后两次存在调用产生的值。cA不可以写为原c*rpow U(−beta)，当前冻结类型没有这个错误。
2. 所有m、lo、hi、c0、L、U、Q、cA、RA都在全部p∈K、k及xi/eta量词之外。它们可依赖mu、M、K、参考u0/v0和原WC参数，不能依赖p、频率或矩阶。K仅需compact，W甚至不另外要求compact，故没有加入K非空、参数联合可测性或参考点∈K。
3. K=∅时，T仍承诺全局m和lo/c0正性；这来自单点参考WC，不能只说所有结论真空。随后W的族输入在空K上真空成立，其五个全局常数符号仍由正lo/hi、c0、非负M/R保证。全局存在量词没有被省略。
4. 参考点不在K时，T 186–189和候选21–25都只使用任意u0/v0，没有成员关系前提。参考law自身不是任意测度：在|x|≤M上，令B=|u0|M+|v0|M²，则exp(−B)≤exp(u0*x+v0*x²)≤exp(B)。base概率性保证归一化积分有限且严格正；参考倾斜仍是概率、有同一支撑界和x/x²的L²。因此D0的variance/covariance具有真实可积含义，不能靠不可积时总化为0成立。T的公开结论另已明确给出0<lo，全局分母风险不需要调用者另加假设。
5. 对每个p∈K，同一有界指数论证适用；更直接地，T 198–200明确输出实际mup概率性及x、x²的L²，故means的两积分、D的方差/协方差不是不可积总化值。W 329输出s>0、t>0，A的分母s*t在适用点非零；W 332–342输出实际nu概率、坐标L²及欧氏各阶可积性，排除了nu、均值和矩的总化漏洞。Y对x是固定矩阵作用于多项式的连续函数，实际map也没有不可测推前的漏洞。所有这些只在p∈K主张，let定义域扩展到K外不造成额外正性要求。
6. M=0没有被偷偷排除：此时base概率集中在x=0，参考倾斜的jointCharacteristic恒为1。取xi=R+1、eta=0（R≥0），半径为R+1>R且正，c*rpow(R+1,−beta)>0，与hWC矛盾。因此该边界的全部输入不能同时成立；结论不依赖偷加M>0，也不通过Q=0和identity covariance伪造退化白化。
7. beta=0诚实保留：W明确只要求beta≥0，U>0时rpow U(−0)=1，故cA=c0，频率正半径上的rpow因子也为1。R=0同样保留，L>0给RA=0；没有暗中使用R>0来满足W接口，也没有更换严格阈值。
8. 频率0处，谱界两端及中间二次型均为0；A正定输出明确要求非零频率。原WC前件R<0与R≥0矛盾，最终WC前件RA<0与RA≥0矛盾，所以没有在0频率强迫|Phi(0)|<1。对阈值等号点也没有越过严格大于号。
9. k=0与所有自然矩一起输出：nu概率使∫1=1，Q^0=1，即便Q=0也没有把0^0误读成0；可积性是概率测度上的常数可积性。k=9则直接给统一九阶欧氏绝对矩，足供有界来源的8+delta且delta=1；未把整数结论说成任意实数矩或无界情形。
10. Fin 2→ℝ虽使用默认Pi空间结构，谱、AE支撑矩、频率阈值和全部矩在T、W及候选中都是字面sqrt(a²+b²)，三者完全同式。本次组合不需要任何默认范数等于欧氏范数的转换，也没有把坐标L²误当作已给某个错误范数的矩界。

## 裁决与权限边界

STATUS: CORRECT

JUSTIFICATION: 在所列精确两条public seed的完整真实类型作为接口前提时，冻结候选全部输入已覆盖所需条件；同一次T输出的m给出measure lower、lo、c0和族谱/rawWC，0<lo<hi给W所需hmax，W按(mu族=mup,lambdaMin=lo,lambdaMax=hi,c=c0)的一次实例化给出候选的同一D/means/A/Y/nu/Phi及全局L/U/Q/cA/RA。剩余只是let展开、绑定改名及合取重排，没有发现隐藏前提、量词移动、同m错配、错误范数或真实积分/方差漏洞。来源上的有界单点到紧族稳定性及实际标准化/统一矩范围相符。

本结论严格限于声明静态组合可行性；没有提交U21e实现，也没有Lean elaboration、kernel proof、构建或传递公理审计的成功声明。后续完整实现仍须新鲜独立证明审查和指定服务器的正式门；不能用本票提前关闭原C，也不能关闭B或D。原A按当前修正vCorr/fixed x0正式状态保留，不外推其范围。

实际执行限制：只轻量读取指定本地文件、必要curated公开定义/API，核对三份新冻结对象及R2原来源的SHA256，唯一写入本报告。未运行任何Lean/probe/Audit、任何远程命令、工具链探测、缓存扫描或旧稳定库重复哈希；未改生产源、冻结scope、REGISTRY/TEAM、状态/inventory、版本、历史票、缓存或源历史；未发跨线程消息、未spawn子实例。后续检查确认先行9927字节保持原哈希；完整文件最终行数/字节数/SHA256在交付回复中报告，避免文件自引用哈希。
