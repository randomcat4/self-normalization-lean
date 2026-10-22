# OQ3-U17c：真实远区能量的有限指数覆盖

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U17B_FULL_FINAL；未批准/未实现。拟Shao/OQ3/FarEnergyExponentialCover.lean。imports Shao.OQ3.EnergyBernoulliMGF、Shao.OQ3.SourceEnergyGeometry；namespace Shao.OQ3，open MeasureTheory，noncomputable section。零公开定义、一个完整公开目标。U17a已完整独立审查接受/PR110，U17b已作者门核验、完整proof审查运行；只有B完整终票由lead全文读完接受后才派本声明门，批准前不写本源/Lean probe，不改变任何冻结前置源。

来源current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，164–237实际能量支持/充分binary gap及386–391远区控制。本单元构造真实同一mu的有限实指数试验覆盖，仍不含样本iid/加权概率积分；不冒称一般KL数据处理、任意rho的唯一全局最小或Legendre最优。

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

目标中mu是真概率，hb固定AE绝对有界，actual二阶矩=q，actualAE平方区间[1,1+H]；q/H限制来自已接受source gap的充分常数，不优化或宣称最弱。ell≥0且ell*q<7/200、delta>0，真实c>0和有限T均先于所有R（未来先于所有n/样本）。T允许空；far集合可能空，不能先取一点或要求非空。所有R包括energy端点p0/p1和far不等式等号；t可任意正/负/0，非假定所有t同号。

数学可行路线（审查须先完整type独立翻译再读本段）：令g=7/200−ell*q>0，c0=delta*g/(4*q)>0。集合内R≥0、1≤qR²≤1+H和delta≤q(R−1)²给R>0、R≠1与4*c0≤g*(R−1)²；q>0先于所有约分。p=(qR²−1)/H在[0,1]，z=(q−1)/H在(0,1)。真实SourceBinaryEntropyGap严格binaryD>(7/200)*(R−1)²，故L=ell*q*(R−1)²+2*c0<binaryD。

用U17a第一目标给有限实theta及真实正normalizer；令t=theta/H，先H>0才取消H。U17a第二目标对actual同一mu/q/H/t给真exp可积、正Zt及logZt≤−t(q−1)+log(1−z+zexp(tH))。实际纯实环等式 t*(qR²−q)+t*(q−1)=t*(qR²−1)=theta*p，得到L<t*(qR²−q)−logZt。没有把纯binaryD等同于actual KL，或把某个试验值误当Legendre最优。

对每个固定实t，F_t(R)=t*(qR²−q)−logZt−ell*q*(R−1)²是连续实多项式（真实积分logZt仅为固定实常数）。U_t={R|c0<F_t(R)}实际开。上段F_t(R)>2*c0且c0>0给forallR∈Kfar存在真实t覆盖。已接受B的真实IsCompact Kfar后，用actual IsCompact.elim_finite_subcover对全部实t索引开集取固定有限T；不存在R相关无限试验交换。每个t∈T的可积/正Zt属性由A第二目标对任意实t直接给，完整目标不能只返回有限集合覆盖而漏掉真实normalizer门。T空只在far空时可行，c0仍独立严格正。

actual compact API来自B import图；无新cache安装/公共源改动。后续真正远区weighted sample set integral须另冻目标并证明真iid积分、AE全坐标提升、固定finite正density sum与集合积分比较；本票不将本标量有限覆盖计为该概率门完成。root A/B/C/D、source3/generalKL/globalfar/full17/19/LLT/hW均OPEN。固定p/q/eps/P先于r/J/n，beta<2/5仅充分修复，无最优/新颖性主张。

检查资源：后续作者Lean仅CPU14–17、同时1个heavy、常规单进程8GiB；审查声明只读，无Lean/probe/rebuild/cachewrite/spawn。所有完整types和actualsource映射优先，机械hash/pins/cache最后。标准传递axiom白名单propext/Classical.choice/Quot.sound，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。声明批准之后实施，完整proof独立审查另行执行。
