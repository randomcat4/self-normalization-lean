# OQ3-U17f：无局部截断的真实负层级数与统一几何尾

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U17E_COMPLETE_FINAL；未批准/未实施，不计接受。拟 Shao/OQ3/NegativeLayerGeometricTail.lean，唯一import Shao.OQ3.GlobalNegativeLayerBound；namespace Shao.OQ3，open MeasureTheory Filter，open scoped BigOperators，noncomputable section。一完整公开定义、一完整公开目标。E作者严格首次空build01/3实际owned三axiom门已完成，完整proof独立审查运行；必须等E完整final由lead全文读取后才派本声明门，批准前不写F源/Leanprobe。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，378–391真实负层权重与指数衰减、421–429层尾控制。此处消费E的全实非负负层界，定义没有if/局部delta，不能以旧J cutoff false分支的形式零替代真实概率。仍保留E所有同mu原始均值、能量/参数、协方差、finite stage/positive atom门。

```lean
def negativeNormalLayerTerm (mu : Measure ℝ) (q ell h theta : ℝ)
    (n k : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.exp (ell * (h * ((k : ℝ) + theta))) *
    (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = -(h * ((k : ℝ) + theta)) ∧
        z ∈ sourceTail q n}

theorem exists_source_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q H ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hellq : ell * q < 7 / 200)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J))
```

独立审查先读/盲译完整DEF与完整type并持久化，再读路线/source/API，机械最后。gamma/C/N置于全部theta∈[0,1]和K/k之前。theta=0/1、k=0、K=0、ell=0、J=0均保留，mesh=dyadicMesh J始终真正正。定义在实际负层和sourceTail上直接取同mu的Fin n产品real质量，没有局部if、没有改成sup或替代measure，也没有隐含n依赖mu/常数。

E给同gamma/C/eventualn后，h=dyadicMesh J>0，rho=exp(-gamma*h)满足0<rho<1。任意k/theta≥0有t=h*(k+theta)≥0；E全实k界可直接实例t。theta≥0及gamma/h正使exp(-gamma*t)≤rho^k，得到真term非负且≤C*rho^k。使用真实summable_geometric_of_abs_lt_one与Summable.of_nonneg_of_le先证原序列Summable。对K+k同样逐点≤(C*rho^K)*rho^k，另先证shift真Summable及majorant真Summable，再tsum_le_tsum/tsum_mul_left/tsum_geometric给完整冻结tail。分母1-rho>0先保留；不能用不可和tsum默认零。可复用J已审几何proof结构，但须删除整个if和delta，不能改动既有模块。

只读实际数学库接口和现成cache，不下载/重建依赖、不改root公共源/import/pins/整合。禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by，传递仅propext/Classical.choice/Quot.sound。所有新target/Audit在指定server严格-DautoImplicit=false、CPU14–17/native-M8192-j4、lane1heavy；禁止ulimit-v/改心跳语义/干预外部CPU0–9任务。唯一reviewer只读noLean/probe/rebuild/spawn/cachewrite/raw完整日志下载。

此目标proof经完整门后仅完成全部真实负层的真Summable/统一phase-index几何尾。有限层真实条件弱收敛/全LLT、整个正负层求和极限(19)、单侧rotation/cuspEM/hW以及一般KL/source3/全局最优/根ABCD仍OPEN。未来合正负层时须实际处理零层与phase索引，不能重复两次零层。p/q/eps/P固定先于未来r/J/n，beta<2/5仅充分修复，无最弱/最优/新颖性主张。
