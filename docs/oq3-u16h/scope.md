# OQ3-U16h：实际中心投影的iid产品倾斜与事件指数比较

冻结v1，DECLARATION_REVIEW_QUEUED，尚未批准或实现。拟Shao/OQ3/CenteredSampleTilt.lean。imports Shao.OQ3.CenteredLogMGF、Shao.OQ3.SampleBoundary、Mathlib.MeasureTheory.Measure.Tilted、Mathlib.MeasureTheory.Integral.Pi；namespace Shao.OQ3、open MeasureTheory、open scoped BigOperators、noncomputable section。一个公开定义、三个公开目标。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，350–365实际中心二元倾斜、iid换测度及尾事件指数比较。已有本lane SampleChangeOfMeasure.lean 29–86对原子inverse tilt给实际同类finite-product证明；这里改编其已接受标准API模式到任意真实有界mu的中心二元投影，不复制/修改root公共源码，也不把已有证明模式声称新颖。

```lean
def centeredSampleProjection (q a v s : ℝ) (n : ℕ) (z : Shao.Path n) : ℝ :=
  ∑ i : Fin n, centeredNormalProjection q a v s (z i)

theorem iid_centeredSample_tilt (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) (n : ℕ) :
    Integrable (fun z : Shao.Path n => Real.exp (centeredSampleProjection q a v s n z))
      (Measure.pi (fun _ : Fin n => mu)) ∧
      (∫ z : Shao.Path n, Real.exp (centeredSampleProjection q a v s n z)
        ∂Measure.pi (fun _ : Fin n => mu)) =
        (∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu) ^ n ∧
      (Measure.pi (fun _ : Fin n => mu)).tilted (centeredSampleProjection q a v s n) =
        Measure.pi (fun _ : Fin n => mu.tilted (centeredNormalProjection q a v s))

theorem centeredProjection_tilt_eq_quadratic (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) :
    mu.tilted (centeredNormalProjection q a v s) =
      mu.tilted (fun x : ℝ => (8 * v + s) * x + (-v) * x ^ 2)

theorem iid_centeredSample_event_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) (n : ℕ)
    (E : Set (Shao.Path n)) (hE : MeasurableSet E) (c : ℝ)
    (hlower : ∀ z ∈ E, c ≤ centeredSampleProjection q a v s n z) :
    (Measure.pi (fun _ : Fin n => mu)).real E ≤
      Real.exp ((n : ℝ) * centeredNormalLogMGF mu q a v s - c) *
        (Measure.pi (fun _ : Fin n =>
          mu.tilted (centeredNormalProjection q a v s))).real E
```

定义完整体是真实有限sample上所有单点投影之和，Shao.Path n=Fin n→ℝ，不另引入随机变量或任意率。投影actual定义是v(Y−q)+s(X−a)。本单元q/a是任意实平移中心，不要求实际均值；仅在真实均值门后才解释其均值0。它不偷加q>0/ell、方差正定、阶段/原子性或小参数球门。hb和mu真实概率保证所有固定实v/s的实指数真可积，所有n包括0；不把U16d的小球结论误扩大，而直接以连续有界支撑真证明单点指数可积。

首目标真可积和normalizer及measure等式绑定同一个mu/q/a/v/s/n。路线：single exp真实连续，integrable_continuous_of_fixed_bounds mu hb给真Integrable，integral_exp_pos给Z>0；exp(sum projection)=prod_i exp(projection_i)由Real.exp_sum。实际Integrable.fintype_prod (fun _=>singleExpIntegrable)给sample exp真Integrable，integral_fintype_prod_eq_pow给实际normalizer Z^n。不能只用总化Fubini等式声称sample可积。n0的empty product=1和empty sum=0必须保留，sample product测度是真概率。

真实iid测度等式可改编SampleChangeOfMeasure原证明：Measure.pi_eq对可测矩形，tilted_apply'与真实normalizer、prod_div_distrib把实际密度写成坐标密度之积；Measure.restrict_pi_pi将矩形限制转坐标限制测度；single exp的真IntegrableOn.div_const与Integrable.fintype_prod给密度乘积真可积；ofReal_integral_eq_lintegral_ofReal先消费真可积和非负；integral_fintype_prod_eq_prod及ENNReal.ofReal_prod_of_nonneg后逐坐标用tilted_apply_eq_ofReal_integral'。两端真实概率须由single/sample真exp可积先建立；不许把不可积tilted=0或top.toReal视作证明。所有Z、Z^n均严格正，不丢normalizer。

第二目标由真实投影恒等式 f(x)=(8v+s)x−v*x²−(vq+sa)。可选g(x)=(8v+s)x−v*x²，常数b=−vq−sa，g真exp可积；真mu.tilted g概率下tilted_const给再倾斜常数不变，而实际tilted_tilted hf给(mu.tilted g).tilted b=mu.tilted(g+b)。再tilted_congr/逐点环等式与f绑定。该证明必须真正先给g exp可积和mu.tilted g概率，不能只用“倾斜忽略常数”口号。所有系数任意有符号，v=s0正常，无除v/s/q/a。

第三目标E是明确可测事件，c是任意实点态下界；不假设它已是tail或层事件。single真exp可积给Z>0，首目标给sample真可积/normalizer Z^n>0及真实产品tilt等式。由实际tilted_apply_eq_ofReal_integral'和有限真概率实质量转换，P_nu(E)=∫_E exp(sampleProjection)/Z^n dP_mu；密度真IntegrableOn由首目标及正Z提供。hlower先给E上exp(c)≤exp(sampleProjection)，真常数与密度可积后积分比较，得到exp(c)*P_mu(E)≤Z^n*P_nu(E)。exp(c)>0，且真实exp((n:ℝ)*log Z)=Z^n只在Z>0后使用，由exp_sub等式重排得到完整目标。真实centeredNormalLogMGF定义体内积分正性在这里明确证明，不能log0/负值总化。E空、c正负/零和n0均不除n或P(E)。

后续应用时，sampleProjection逐点环展开应为v*normalDeviation q z+s*((sum_i z_i)−(n:ℝ)*a)。实际tangentDeviation q的中心是n*q/4，不能把tangentDeviation a误当n*a；只有source a=q/4后再绑定。正尾事件M=d,R≥r需s≥0才给lower v*d+s*r，负尾需s≤0，必须单独证明真实trial s的符号；本单元只给明确hlower下的真事件概率比较，不偷偷生产这些sign门。再把第二目标的quadratic tilt经真实线性参数映射送入compact K，未来才可消费U16g层质量同C/N与U16e实际cost。

实际已读固定库Tilted.lean101–124提供tilted_apply'/tilted_apply_eq_ofReal_integral'，126–136真exp可积推出概率，251–252 tilted_tilted要求原exp真Integrable，74–75 tilted_const要求真实概率。Integral.Pi106–108和119–122给实际有限积积分；Constructions.Pi279–283的pi_eq、418–421的restrict_pi_pi；这些API已在U9b的真实已接受源中使用，不需猜测不存在的pi_tilted helper或新增缓存。首目标的真可积仍是本新实现必须核的义务，不借旧原子w前提代替一般mu。

当前U16g完整声明审查中，U16h只冻结排队，待lead全文读完G终票后才派本声明门；批准前不实施或Leanprobe。唯一reviewer先盲译完整定义体/三个完整types并持久化，再source/实际库/可积/正normalizer/真实measure等式/量词与边界门。所有Lean/重计算只在指定服务器。

不证明trial尾符号、紧倾斜族质量界（由G另证）、负层(16)/(17)、全局远区gap、完整19/LLT/hW/WC/KL、Legendre最优性或根闭合，无最弱/最优/新颖性主张。根ABCD全部OPEN，不cachewrite/copyroot源码/rebase/merge。
