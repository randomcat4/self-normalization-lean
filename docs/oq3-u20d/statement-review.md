# U20d SourceCanonicalSaddle 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 不可改写完整TYPE盲审前缀

本前缀仅根据scope75两个完整Lean代码块生成，尚未读取本轮scope说明、原文或新增生产者／几何API正文及环境元数据。
本轮是声明门：0公开DEF、1公开合取THM，尚无本模块实现验收。已知先前节点不替代本TYPE的独立审查。

```lean
import Shao.OQ3.SourceCanonicalRate
import Shao.OQ3.SourceLogPartitionDerivatives
import Shao.OQ3.SourceGeometricScale
import Shao.OQ3.PositiveRate
```

```lean
theorem source_canonical_saddle_hessian_and_scale
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    let P : Measure ℝ := originalMeasure sourceEll w
    letI : IsProbabilityMeasure P := originalMeasure_isProbabilityMeasure sourceEll w
      (fun i => (hw i).le)
      (by simpa only [constraintFeature, constraintTarget, Matrix.cons_val_zero, mul_one]
        using hm 0)
    let W : ℝ → ℝ × ℝ := fun x => (x, x ^ 2)
    ∃ lift : (Fin 2 → ℝ) → bivariateMGFDomain P W,
      (∀ theta, (lift theta : ℝ × ℝ) = (theta 0, theta 1)) ∧
      let K : (Fin 2 → ℝ) → ℝ := fun theta => bivariateLogMGF P W (lift theta)
      let theta0 : Fin 2 → ℝ := ![8 * sourceEll, -sourceEll]
      let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (atomicMeasure w)
      let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
      let gradient : (Fin 2 → ℝ) →L[ℝ] ℝ :=
        (pr 0).smulRight (q / 4) + (pr 1).smulRight q
      let hessian : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
        ∑ i : Fin 2, ∑ j : Fin 2, (pr i).smulRight ((pr j).smulRight (D i j))
      let x0 : ℝ := Real.sqrt q / 4
      let a0 : ℝ := q / 4
      let s0 : ℝ := 8 * sourceEll
      let t0 : ℝ := -sourceEll
      let v : Fin 2 → ℝ := ![1, 2 * a0 / x0 ^ 2]
      let lambda0 : ℝ := s0 * a0 + t0 * q - K theta0
      let lambda1 : ℝ := 2 * t0 / x0 ^ 2 + dotProduct v (D⁻¹ *ᵥ v)
      let vCorr : ℝ := (-t0) * Real.sqrt D.det * Real.sqrt lambda1
      (∀ theta, K theta =
        Real.log (∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P)) ∧
      HasFDerivAt K gradient theta0 ∧
      HasFDerivAt (fun theta => fderiv ℝ K theta) hessian theta0 ∧
      (∀ u : Fin 2 → ℝ, u ≠ 0 → 0 < dotProduct u (D *ᵥ u)) ∧
      0 < x0 ∧ q = a0 ^ 2 / x0 ^ 2 ∧ s0 = -2 * a0 * t0 / x0 ^ 2 ∧ t0 < 0 ∧
      lambda0 = saddleRate sourceEll q w ∧ 0 < lambda0 ∧
      0 < D.det ∧ 0 < lambda1 ∧ 0 < vCorr ∧
      correctedInverseScale sourceEll q (atomicMeasure w) = vCorr⁻¹
```

### 独立逐项翻译、真实对象与待核门

1. 调用者任给同一个q，严格满足1<q<103/100。
2. 调用者任给同一个w，所有AtomicIndex上的权重严格正；这比前节点非负门强，但这里是明确前提。
3. 对全部Fin4索引要求实际权重乘fixedAtom特征的真HasSum到constraintTarget q，不用总化tsum冒充。
4. P固定为originalMeasure sourceEll w，此后没有再选择law。
5. 目标内部letI用hw的非负化和hm0生产P真概率实例，不新增caller概率。
6. W是(x,x²)，canonical域为此同一P／W的实际指数可积域。
7. 结论先存在lift，把整个ambient Fin2→ℝ空间映入真实canonical domain subtype。
8. 对每个theta，lift的底层对必须恰为(theta 0,theta 1)，不能换成重参数化或只定义局部窗口。
9. K是canonical bivariateLogMGF在这个lift上的拉回，不是另立自由logMGF。
10. K须在整个ambient参数空间逐点等于真实P的字面log指数积分。
11. 不能因lift有证明参数就对一个不明的subtype拓扑求导；应由底层坐标身份绑定真实ambient函数。
12. theta0为实际Fin2向量![8sourceEll,−sourceEll]。
13. D是同w的atomicMeasure下真实parabolaCovariance矩阵，不是原P的未倾斜协方差，也不是任意正定矩阵。
14. pr_i是有完整连续线性映射类型的坐标投影。
15. gradient映射为h↦(q/4)h₀+qh₁。
16. hessian是外层i／内层j的双重Fin2和，形式为h↦[k↦Σij h_i·k_j·D_ij]。
17. 它的类型是真正嵌套连续线性映射，不只是若干坐标二阶偏导数。
18. 第一导数结论为HasFDerivAt K gradient theta0。
19. 第二导数结论为HasFDerivAt(θ↦fderiv ℝ K θ) hessian theta0，要求实际导函数的Fréchet导数。
20. 若从literal K接口转移，需整个K函数恒等及相应fderiv函数恒等，只有theta0处值相等不够。
21. D正定性完整表述为任意非零u都有u·(D*u)>0，不能只把det>0当定义。
22. x0固定为sqrt q/4，a0=q/4，s0=8sourceEll，t0=−sourceEll。
23. 标量鞍点方程为x0>0、q=a0²/x0²、s0=−2a0t0/x0²、t0<0。
24. 所有x0²分母必须先由正q证明非零；不能利用实除法总化得到虚假方程。
25. v真实定义为![1,2a0/x0²]，第二分量预计为8，但须合法清分母证明。
26. lambda0是同一canonical K(theta0)形成的实际测试值，必须等于同q/w的saddleRate且严格正。
27. 正率前提需由明确all-w严格正和非零sourceEll生产，不可假借前一节点只要求非负权重的比较结论。
28. lambda1是实际2t0/x0²+v·D⁻¹v；需要真实det>0排除矩阵逆总化的奇异捷径。
29. 结论同时生产D.det>0与lambda1>0，不能由调用者输入这两个正性。
30. vCorr=(-t0)·sqrt(detD)·sqrt(lambda1)，需三因子各严格正。
31. 最后把已存在的correctedInverseScale sourceEll q (atomicMeasure w)精确绑定为这个vCorr的逆。
32. 该等式需要实际平方根乘法／非零域及负号系数32，不能只展示类似形式的常数。
33. 所有let都位于原同q/w／P／存在lift之内，没有另选的协方差或校正尺度。
34. 待核公开API：canonical全域给lift成员，actual literal导数定理给整个ambient梯度／真实fderiv二阶，且参数坐标方向一致。
35. 待核公开API：strict原子质量、真概率与真实L2矩是否能生产一般协方差严格二次型，不跨模块引用private helper。
36. 待核公开API：已有几何尺度恒等是否完整交付这里的D／v／lambda1／vCorr表达式，而不是不同自变量或转置。
37. 待核固定环境：四imports在已验证单Shao根视图下可达；不重跑稳定完整图或Lean。
38. 类型未提供均值映射局部逆、邻域C2或完整根A组装；即使这里正确，这些义务仍分别待闭。
39. 全部原A/B/C/D仍OPEN，本前缀不预报proof／kernel验收。

--- END IMMUTABLE BLIND PREFIX ---

## 来源与实际公开API的独立数学审查

上述101行6821B盲前缀先于scope说明／R1／生产者正文持久化，SHA256 `801a32c3a72b6f4c53148b488042d990fcec57faefc1c583714df7a47287b072`。随后实读scope75完整内容、R1 141–159／239–257／431–443、root-contract 26–35及46–57，并读实际SourceCanonicalRate、SourceLogPartitionDerivatives、SourceGeometricScale、PositiveRate公共完整类型以及关键生产体、RegularCovariance和AtomicMeasure必要定义／公共API。没有使用作者candidate／proposal／implementation路线当作数学证明。本轮仍是声明门，无本模块proof／kernel验收。

### 原始对象和同律要求

R1 141–159给P中心化、反倾斜后回到π、a=q/4、x0=√q/4、参数(8ell,−ell)及正Lambda0；239–257给Δ=Covπ(X,X²)严格正定、真实Varπ(Y)和Lambda1>0；431–443的式(20)给校正常数与连续常数身份。root-contract 28–34要求同P的真实K梯度／Hessian、几何鞍点方程和v_corr=(-t0)√detD√Lambda1。当前TYPE精确对应这些对象，但未声称给出R1连续积分本身的求值或均值映射逆。

本TYPE的w是全严格正，清楚区别U20c仅非负版本。令hw0 i=(hw i).le，hm0按冻结证明体给真HasSum w 1，公开originalMeasure_isProbabilityMeasure生产P真概率；atomicMeasure_isProbabilityMeasure也给同w的π真概率。没有另选全正存在族来代替调用者w，也不把P／π混成一个测度。D只在π下定义，这是实际P于theta0倾斜后的同一π，符合R1。

### 全域lift和整个canonical ambient K

已接受U20c公开source_canonical_rate_unique_minimizer对同q/w/hw0/hm给bivariateMGFDomain P W=univ及每个域成员的真实正配分／literal log。由此可明确构造lift(theta)=⟨(theta 0,theta 1),真实domain成员证明⟩；coercion坐标身份是rfl。lift无需具备另一个子类型拓扑或先假设可微，也没有只覆盖theta0附近。

将bivariateLogMGF的真实定义及这个底层坐标身份展开，对全部theta得到K(theta)=log∫exp(theta0·x+theta1·x²)dP。这里theta0／theta1指坐标，不是把固定鞍点替代变量。funext给整个ambient函数等式；可在HasFDerivAt和fun theta=>fderiv K theta内部统一重写。仅证明鞍点值相等确实不足以转移导数，但当前有全函数等式并能构造它。

正配分／可积性来自同P下任意实二次exp的真实Integrable，已由U20c／PR146产生。没有域外log0／零倾斜捷径。全域univ还确保该有限维ambient表达式确有全参数输入，不在这里假借局部均值逆来定义K。

### 梯度与真正fderiv二阶

实际SourceLogPartitionDerivatives.lean161–177公开source_log_partition_first_and_second_derivatives要求同q/w/hw0/full4hm；它的P、literal K、Fin2 theta0、actual D、pr、gradient、hessian与本TYPE逐表达式一致。输出两个真实HasFDerivAt，包括HasFDerivAt(fun theta=>fderiv ℝ K theta) hessian theta0，非仅Peano展开或方向二阶。用前述全函数K等式可整体转移这两个结论，没有新增C2或Hessian假设。

我实读其公开生产体178–250：真实P和π概率先建立，normalizedMoment在theta0还原为同π的真实矩；193–219先MemLp x／x²再variance_eq_sub与covariance_eq_sub，交叉项D10=D01为真实构造恒等；238–250先有全参数第一导数和整个fderiv函数等式，再求真实导函数的导数。不是利用单点gradient数值来冒充二阶。

hessian实际双和的外层pr_i和内层pr_j作用为h_i·k_j·D_ij；转置或行列反向不能默默更换。这里与已接受公开类型逐字同结构，其生产体230–237实际对两向量ext后用Fin.sum_univ_two、投影／smulRight展开，再代同π一至四阶矩。故同一actual D确实代表这条嵌套CLM二阶。

### 实际D的完整二次型正定

严格hw给hbase i=hw(Sum.inl i)。AtomicMeasure.lean34–42和51–55公开API分别给真实singleton质量=w_i、真概率和固定AE界；fixedAtom(Sum.inl i)=baseAtom i。故可生产hbp i:0<π.real{baseAtom i}，不把权重正性未经绑定直接当测度正质量。

RegularCovariance.lean20–24的D为[[Var X,Cov(X,X²)],[同一Cov(X,X²),Var X²]]，所以D10=D01为定义性相等。32–36公开centered_parabola_integral_eq把真实中心二次式平方积分绑定为a²D00+2abD01+b²D11；80–84公开centered_parabola_integral_pos在同π真概率、AE界、四个实际正singleton门下，对(a,b)非零给严格正积分。两项全是public，不需跨模块引用其private ae_zero_at_positive_atom。

对任意u≠0，用Fin2的全部两个坐标可知u0≠0或u1≠0（否则逐坐标funext即u=0）。实例化a=u0,b=u1，再展开dotProduct和mulVec的两个有限和，利用D10=D01得到u·D u等于上述严格正积分。因此TYPE的完整∀u≠0二次型结论有公开生产路径，非把det>0误当正定定义。该路径不依赖一般概率矩阵det正的错误推断。

这些积分不是variance.toReal总化制造的数：RegularCovariance实际生产体39–66先给中心平方／交叉项真Integrable再作积分线性；正性证明85–107也先平方真可积，再从积分零推出AE零，并在真实正单点−1、1、2上消去二次式系数。声明调用只用公开两个定理，无隐藏原子／L2门。

### 标量鞍点方程和真实正Lambda0

q>1给q>0及sqrt q>0，因而x0=sqrt q/4>0，x0²=q/16>0且非零；a0=q/4。合法清分母后a0²/x0²=q，−2a0t0/x0²=8sourceEll=s0；sourceEll_pos给t0=−sourceEll<0。没有把q=0或x0=0的总化除法用于等式。

U20c同law实际theta-domain witness底层为(8sourceEll,−sourceEll)，在候选(q/4,q)达到saddleRate。当前lift(Fin2 theta0)也有精确同底层对；由Subtype.ext或直接展开canonical log的底层坐标，可把达到等式转为当前K theta0形成的lambda0=saddleRate。不存在一个新opaque参数或不同lift值造成法则／率漂移。

PositiveRate.lean142–154公开saddleRate_pos要求ell≠0、全权重严格正及全部hm；sourceEll_pos确实给ell≠0，这些正是当前前提。其生产先真inverseNormalizer正再比较真实log，不能由U20c有限率恒等式单独推正。故lambda0>0有真实公开来源，不是手给正率或KL身份。

### Lambda1、vCorr及correctedInverseScale

实际SourceGeometricScale.lean21–36公开source_corrected_scale_geometric_identity接受同q窗口、hw0、hbase、full4hm；其D/x0/a0/v/curvature表达式与本TYPE的D/x0/a0/v/lambda1完全一致。t0=−sourceEll，所以curvature就是lambda1，且−t0=sourceEll；该public合取同时给detD>0、lambda1>0、vCorr>0和实际correctedInverseScale=vCorr⁻¹，不调用其中private inverse_tangent_quadratic。

实读其生产37–99确认：先真实base单点质量和parabolaCovariance_det_pos；q正后证明x0²=q/16、v第二分量8、2(−ell)/x0²=−32ell/q；由实际normalVariance_eq_covariance和已验收矩阵逆公式得lambda1=S/detD−32ell/q。实际正曲率API来自同q窗口与真实矩界，绝不是奇异矩阵总化逆的假结论。detD·lambda1=S−(32ell/q)detD，再用正det的sqrt_mul给精确乘积根式。

CorrectedScaleContinuity.lean20–22的真实定义正是(ell·sqrt(S−(32ell/q)detD))⁻¹。公开几何接口已经在正域生产全部非零门并识别为同一个vCorr倒数；R1 438–443系数32、负t0和根式乘积均相符。这里不需要另一个自由矩阵、任意手工radicand或单独假设det／lambda1正。

数学／来源／公开API阶段裁定：完整冻结TYPE存在不增加假设、不调用外部private helper且保持同q/w/P/D的真实公开生产路径。它承担canonical坐标／导数／正定／鞍点和几何身份适配，尚未给均值映射邻域逆或全C2邻域；这些剩余没有藏入本声明。下一步仅做必要元数据／环境绑定，不运行Lean或重复完整导入图。

## 最后元数据／环境绑定（非proof凭据）

本地scope75为70行6940B，SHA256 `d38dd216682cb45f1bffe2641c441d6e4ca08affa320c272e77740821a516c5f`，remote run/scope.md实际同hash。只存在0公开DEF／1完整THM的冻结声明；没有SourceCanonicalSaddle.lean、target build或Audit。当前gate不是已实现证明的验收。

实际当前lane为`feat/oq3-source-canonical-rate`，HEAD `7dcf60695c046d0d89e96b92ccd25604e444cfe9`，tree `0acb4f35dc49de4f27250df50bfd32838eb51d01`，status干净。它是已接受PR156现有分支，不是尚未创建的U20d分支；不为本声明rebase／reset／merge／fetch／retarget或更改任何冻结head。

### 直接公共生产者精确绑定

| 本轮实际读取公共API的源 | 当前行数／字节 | SHA256 |
|---|---:|---|
| SourceCanonicalRate.lean | 99／4662 | `fc492cbacca9a8df208b9a20ea47d7e84e71c1c48e1f87448adbd925f5378d92` |
| SourceLogPartitionDerivatives.lean | 253／13173 | `18c42fc0bea7cdaf1fb69acba96caf452a35eddc9819e29d211fe94a4aa32f07` |
| SourceGeometricScale.lean | 102／4365 | `6361d54e22501bf85a6c683a7e85d9df05082bd6190cad73a8d03dc00f3e7470` |
| PositiveRate.lean | 189／9294 | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |

本轮不重跑已完成的完整physical／public图。为避免把作者candidate正文当独立证据，我从已接受U19b的17项、U19c的8项、U20c的13项正式prerequisite-hashes.json作并集，再加四个实际seed源码的当前hash；公共接口可见性则直接核生产源的public theorem类型和普通转导imports。三个正式旧字典SHA分别为`9f579be17ffa72b4b08b449e427d16b928d6b5f9206cf7ef92abd809792ab7f9`、`c90c1ebd9d25345ff17457101e14be62995788ebf49a596027fd0b43e6f31536`、`73d47bbf6d015aa4a478496a58cd4c95e8de1dc89746101f5a4dac12ae1007cf`。

并集独立得到25个canonical相对源路径，无hash冲突；逐项当前源hash不符0，compact SHA256独立重算`a2bc1daeb0e36fb2393964fd1e113b073b30ddf3419439097c29d2c7915a4867`。这是接受依赖字典并集及必要新source绑定，不是重新扫描整个Mathlib图。scope的2783 Mathlib及既有public大图统计在本门沿用已完成证据，本门不另宣称重算其分列／总节点计数。

25路径为：Shao/Basic/FinitePath；OQ3的AtomProjection、AtomicMeasure、AtomicProductControl、AtomicTailControl、BinaryEntropyBounds、CorrectedScaleContinuity、EnergyBernoulliMGF、FiniteConstraints、FiniteNormalSpan、FiniteStageMeasure、InverseTilt、PositiveRate、RegularCovariance、ResonanceArithmetic、SampleBoundary、SourceBinaryEntropyGap、SourceCanonicalRate、SourceGeometricScale、SourceGlobalExponentialTests、SourceLogPartitionDerivatives、SourceStarter、SummableAtoms；Probability的BivariateLegendre、FiniteIID（均为对应.lean相对路径）。全部为既有接受源，不消费尚未实现的U21a或未来mean-map模块。

### 已接受单Shao-root环境的针对性沿用

只对该25项既有并集做必要路径元数据检查：经U20c已核`runs/oq3/u20c-20261021/import-view`对应.olean路径缺项0，没有重算二进制hash或重跑导入／smoke。该视图OQ3指own lane现有build目录，Probability指接受v38 build目录；这正确适配固定Lean按package根首选缓存的查找规则。U20c的actual fc492cba源和新目标对象已在同一own OQ3目录可消费，不退回v1无效的并列Shao-root逐模块fallback。

本轮没有重验稳定pins、51对象或缓存目录hash，也没有复制cache。既有Lean v4.36.0-rc1、Mathlib807d3836b165983210ee2ecf3cd28f239436949c及root唯一cache／shareddefs／integration所有权沿用不变。未来目标仍须最终Lean进程view首Shao-root且保留其余Lake／Mathlib路径，实际elaboration和首个owner Audit要在实现后完成，本静态门不预报其PASS。

remote run当前仅scope.md及作者candidate-cache.py／json元数据文件；未读其正文或运行scanner。仅最后hash绑定candidate-cache.json为4268B，SHA256 `2cb1d88b595345f6594f95cff9ce803a005c7140acfcdfac1de05072e2db3a89`，它不提供本报告数学或独立并集的依据。首次作者图transport timeout及未重放属于保留的行政历史，本轮没有因此重扫完整图或执行Lean。

所有服务器项目读取均taskset -c 14-17，未启动任何heavy任务，未触外部CPU0–9／80GiB或全局资源。只写本新声明报告及授权远端副本，不改source／scope／旧票／Audit／receipt／pins／view／cache／他人文件，不新agent／chat／commit／PR。

## 独立最终裁决与准确剩余

STATUS: CORRECT

绑定scope75精确SHA及完整TYPE，当前声明数学正确、原文匹配、量词／同law／真实域／二阶／正定和全部几何正域门均有公开可消费的实际生产路径；未发现CRITICAL GAPS。该裁决是声明／来源／API／静态环境批准，绝不是本模块proof或kernel已验收。

原target→本节点拟消除：同一源P上的canonical全域ambient坐标lift、整个K literal函数身份、真实Fréchet梯度和fderiv二阶、同π协方差完整正定、实际标量鞍点方程、正lambda0、正lambda1／vCorr及correctedInverseScale精确倒数。直接consumer是root A在U20b一次取得的同w/q/P上同时消费U20c全局率结论与本鞍点／常数适配；不重新选择法则或输入手工全局最小／Hessian。

剩余：本模块尚未实施；完整实际proof、所有owner TYPE／公理和首strict target／Audit以及独立proof终票仍须逐门完成。当前只给theta0处的一阶／真实二阶，不声称邻域C2、均值映射邻域逆、统一远域率间隙／概率估计、标准化WC或Edgeworth。原B/C/D、一般KL9/10、最终A装配及全部原A/B/C/D仍OPEN；U21a仍仅声明正确且DEFERRED_UNIMPLEMENTED，不记proof接受计数。

101行6821B盲前缀SHA256 `801a32c3a72b6f4c53148b488042d990fcec57faefc1c583714df7a47287b072`原字节保留。首部IN_PROGRESS是初始落盘历史，本节CORRECT为本次完整声明终裁。lead整份报告全文读完前不得把本门当作源实现／发布许可已执行。
