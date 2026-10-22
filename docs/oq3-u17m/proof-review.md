# U17m SourceGaussianLatticeGap 完整独立证明／来源／实际类型审查

STATUS: CORRECT

## 1. actual完整公开类型独立盲译（先行持久化）

此前完整声明票的上下文存在，但本节重新只从actual实现提取public声明；尚未读取当前实现证明／private body、scope对照或作者receipt／build／Audit证据。本实际模块无public DEF，唯一完整public合取target如下。

```lean
theorem stage_sourceGaussianLayerWeight_lattice_gap
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight mu q sourceEll
      ((k : ℝ) * dyadicMesh J)) ∧
    correctedInverseScale sourceEll q mu +
      (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (4096 * Real.pi) ≤
      (dyadicMesh J / Real.sqrt (normalVariance mu)) *
        ∑' k : ℤ, sourceGaussianLayerWeight mu q sourceEll
          ((k : ℝ) * dyadicMesh J)
```

固定任意同一真实概率μ、J:ℕ及q:ℝ，要求1<q<103/100。同μ有真实EY=q和EX=q/4；μ-AE值在实际Fin4⊕FinJ阶段原子值域，且每个实际阶段singleton的mu.real严格正。结论首先要求整数k↦sourceGaussianLayerWeight μ q sourceEll (k*h)真正Summable；其次(h/√S)乘同一整数格和至少为actual correctedInverseScale sourceEll q μ加h√h/(4096π)，其中h=dyadicMesh J，S=normalVariance μ。

全J包括J0；不是只对J充分大。常数4096π固定，μ/q不能在格和／连续常数／参数证明之间替换。类型没有手工κ/S/D/T/gap/H或Summable输入，也没有hcont/EM/ζ输入。所需方差／sqrt／rate正性、真实可积与可和、整数零层一次、混合换序与显式常数必须由实际证明全部生产，不能继承“声明CORRECT”作证。

这是0新公开DEF、1完整合取目标。若实现终审通过，拟完成原25的充分正间隙；不同时证明原24精确ζ、hcont／无条件19、rotation／diagonal或任何根。本节actual盲译已先行持久化，随后才进入scope/R1、全部实现及TYPE，机械证据最后。

## 2. 终审范围、来源及完整类型对应

本票独立审查当前685行实现，而非把此前254行声明CORRECT当proof。最初actual盲译检查点为2460字节／32行，SHA256 e12e5ffe7ec66970f0461b24ee339cb76f1fcffd1230fa880e1e7f5cfd1fddd6；第1节完整盲译与TYPE原字节保留，仅首部行政STATUS在最终完成时更新。冻结scope／R1上下文在本次盲译后对照，随后全读actual实现和真实API，再全50actual TYPE，最后才读receipt／build／Audit机械状态。

actual public完整type与scope60唯一Lean fence白空格规范相同，5imports不变，0publicDEF／1合取目标。当前scope SHA1db7c32e02a40cd2973366f5328208a68fe87f4c67d7702d2c64ea08614a3195；此前statement票071221160cd299ad910bc261f0608ef64e691c30c1419dbcfe85f47346e23bf7保留，未覆写。作者implementation/future/cusp/next notes与candidatecache JSON均未读取。

真实R1 current/oq3/proofs/r1/report.md为19420字节／575行，SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，原件只读。411–426的F_J是同μ Gaussian layer weight并以h/σ归一化；431–443的连续积分是真corrected逆尺度；448–481的原(25)是正h^(3/2)格差；486–494的原(26)还要相位回返与19极限。当前实现不借EM／ζ，而真正证明全J的显式充分原25下界；不声称原24精确渐近或后续26已经成立。

原target→已消除义务→直接consumer→remaining：原25所需“同一实际stage模型的整数格和真Summable、端点抵消和统一正差”由本实现直接完成，公开下界可供原25取b=1/(8192π)>0、J0=0。直接consumer是原26对实际相位返回子列的选择；hcont真实生产者／无条件19、rotation／实际diagonal n_J仍待完成。不能把本静态及proof终审的原25充分结论扩大成完整LLT、hW、generalKL或根闭合。

## 3. 四个actual私有DEF完整body

```lean
private def quadratureR (s h : ℝ) : ℝ :=
  h / (Real.exp (s * h) - 1) + h / 2 - 1 / s

private def cauchyWeight (t : ℝ) : ℝ :=
  (2 / Real.pi) * (1 + t ^ 2)⁻¹

private def decayRate (ell a t : ℝ) : ℝ := a * (1 + t ^ 2) - ell

private def mixedKernel (ell a x t : ℝ) : ℝ :=
  cauchyWeight t * Real.exp (-decayRate ell a t * x)
```

全部积分是实际实Lebesgue volume／其Ioi0 restriction，prod同样是这两个真实restriction。DEF本身总化；后续每次使用1/s、exp(sh)−1和无穷积分的线性／交换，均由真正正域／Integrable／Summable辅助门支撑，不依赖默认积分0／tsum0。没有新public DEF、shared instance或输入概率law替换。

## 4. 全部685行proof、37私有定理与locals

### 4.1 17–72：R的三个真实不等式

quadratureR_nonneg令φ(u)=(u−2)exp(u)+u+2，用真实HasDerivAt规则逐项微分得φ'=(u−1)exp(u)+1。Real.add_one_le_exp(−u)乘正exp(u)，再exp(−u)exp(u)=1，给所有实u的φ'≥0。故真正满足全实monotone_of_hasDerivAt_nonneg；不是只在u≥0证明后非法升级全实。φ0=0，s,h>0使φ(sh)≥0。actual代数identity是R_s(h)=φ(sh)/[2s(exp(sh)−1)]，分母先正，和R/h的等价公式一致，没有漏掉h。

quadratureR_le_half先exp(sh)−1>0，再由exp(sh)≥1+sh正分母跨乘得到h/(exp(sh)−1)≤1/s，故R≤h/2。quadratureR_ge_quarter在sh≥4与s>0后得1/s≤h/4，第一分式非负，故R≥h/4。三者只在各自真实门下消费，未从R的总化定义推出无条件正性。

### 4.2 74–137：Cauchy权与mixedKernel的真实L1

cauchyWeight_nonneg、continuous由π>0与1+t²>0；cauchyWeight_integrable消费真实inv_one_add_sq全实Integrable再限制Ioi0、乘2/π。integral_cauchyWeight用实际半线反正切积分给准确质量1。没有无限半轴常数1可积的伪门。

decayRate_lower在a≥0给s(t)≥a−ell。mixedKernel_nonneg对任意ell/a/x/t成立，指数恒正；mixedKernel_continuous只陈述固定ell/a/x对t连续，不把任意负x的指数增长误记可积。mixedKernel_le在a≥0,x≥0时由下界乘x及exp单调给核≤w(t)exp(−(a−ell)x)；hgap在该纯点态比较未显式引用是冗余假设，非逻辑漏洞。

mixedKernel_integrable明确消费连续可测及Cauchy真L1乘有限实常数作范数主控；integral_mixedKernel_le在两边真Integrable后使用integral_mono、再质量1得到∫核≤exp(−(a−ell)x)。其需要的a−ell>0保证以后几何衰减，不是总化积分比较。

### 4.3 139–238：实际profile、真正几何可和与整数重组

profile_pos消费真实gaussianBoundaryWeight_eq_piecewise的x≥0分支，得到F(x)=exp(−ell*x)，含x0时F0=1。profile_neg_mixture对κ>0,x≥0获得L的真实核Integrable与identity，乘有限常数exp(ell*x)，在同一t上准确指数相加为mixedKernel ell(κ²/2)x。虽然该证明只显式使用hm.2改写，hm.1已由同一公开定理取得；常数乘真实核确实L1，不能把这个恒等式误解释成允许无条件Fubini。

exp_nat_summable／exp_nat_tsum分别在r>0后明确|exp(−r)|<1，利用真几何Summable／tsum并以exp_nat_mul做完整函数外延。exp_succ_summable从真Nat列的injective succ重索引；exp_succ_tsum先真tsum_eq_zero_add，再使用正1−exp(−r)、exp(r)−1及exp(−r)exp(r)=1清分母，得到负列从n+1开始的1/(exp(r)−1)。

profile_nat_summable以r=ell*h>0匹配正列；profile_neg_summable先证明实际负项非负并被r=(κ²/2−ell)h>0的真exp-succ列支配，才由Summable.of_nonneg_of_le给可和。profile_integer_summable消费这两个真正Nat子列，经Summable.of_nat_of_neg_add_one覆盖ℤ；非负索引与−(n+1)不交，0仅属于前者。没有先用tsum默认0去制造恒等式。

### 4.4 240–303：倒率L1、联合L1与真正Fubini

decayRate_pos由s≥a−ell>0严格成立。weighted_inv_integrable证明w/s连续且范数≤w/(a−ell)，主控真Cauchy L1。integral_mixedKernel_x使用正确负指数系数−s(t)<0的integral_exp_mul_Ioi给w(t)/s(t)；其x切片真Integrable来自同一严格负率。

mixedKernel_joint_integrable的actual函数是p=(t,x)↦mixedKernel ell a p.2 p.1，坐标顺序已核。先给joint连续／AEStronglyMeasurable；每t的x切片真exp L1；内层范数积分由核非负恰为w/s，再由weighted_inv_integrable给外L1，最后integrable_prod_iff产生实际prod Integrable。两个restricted volume均σ-finite，库SFinite门真实满足。

integral_profile_negative先在Ioi0的实际x≥0门下用profile_neg_mixture，随后才用上述joint真Integrable的integral_integral_swap.symm，把x外t内换为t外x内，最后逐t消费integral_mixedKernel_x。没有先交换再证明联合可积。

### 4.5 305–411：积分范数列Summable先于交换，所有线性项各自L1

tsum_profile_negative先用核非负给真实hnorm等式，再以积分上界和exp-succ几何主控证明n↦∫‖mixedKernel(n)‖真正Summable。每n的核真Integrable由mixedKernel_integrable给，才调用integral_tsum_of_summable_integral_norm。之后逐t的s(t)h>0给真实几何sum；tsum_mul_left并非用来跳过可和门，内层exp列的真可和也由已证正率几何事实支持。

weighted_geom_integrable明确exp(s(t)h)−1>0，且以exp tangent给w/(exp(sh)−1)≤w/(s*h)，主控是weighted_inv_integrable除正h。weightedR_continuous在s与exp(sh)−1全实非零门后成立。weightedR_integrable用0≤R≤h/2把范数支配于w*h/2，证明真正L1；实现从未声称裸R在无限半轴可积。

integral_weightedR的函数外延是wR=h*w/(exp(sh)−1)+(h/2)w−w/s。其两加项和被减项均先由weighted_geom／Cauchy／weighted_inv给真实Integrable，再消费integral_add/sub和常数乘积分，最后∫w=1。得到准确的+h/2项；不存在不合法∞−∞或总化积分线性。

### 4.6 413–466：实际负反射、零层一次与精确端点抵消

integral_profile_split先从公开Gaussian profile定理给全实真Integrable，κ²>2ell由hgap清算。正半轴实际profile等于exp(−ell*x)，真负率积分为1/ell。integral_comp_neg_Ioi把x>0的F(−x)积分映射到原Iic0侧；这是Lebesgue端点零性质处理的积分恒等式，不能误写成Ioi的精确集合反射就是Iic。两侧真Integrable后intervalIntegral.integral_Iic_add_Ioi给全实积分。

profile_positive_tsum先真Summable后拆0项，得到1+1/(exp(ell*h)−1)。profile_quadrature_identity分别建立hpos/hneg真Summable，NatInt重索引明确传递实际f，随后才重排ℤ sum、代入负列混合sum、真实全积分分拆及integral_weightedR。实环化简给

`hΣ_Z F(kh)−∫_ℝF = R_ell(h)+∫_{t>0} w(t) R_{s(t)}(h)`。

正列包含k0、负列从n+1开始，零层准确计一次；∫w=1保证正侧+h/2与负侧−h/2准确抵消。actual NatInt的显式f处理的是elaboration参数，不更改数学或heartbeat设置。

### 4.7 468–548：真实有限区间、raw常数6/(577π)及profile正差

integral_weightedR_lower要求a>1/30、ell<1/30、0<h≤1，先得到a≥0、a−ell>0。令u=√h>0、u²=h、r=12/u>0，A=Icc r(2r)。完整locals hbounds先由真实正u跨乘得到12≤tu≤24，再平方得到144≤h*t²≤576；t≥r>0与u>0的门在平方／约分前均明确。

hpoint中s(t)h=ah*t²+(a−ell)h≥144a>24/5>4，因此R≥h/4。由h(1+t²)≤577与π、1+t²、577π严格正，实际w=2/[π(1+t²)]≥2h/(577π)。mul_le_mul保留各因子非负门，得到wR≥[2h/(577π)](h/4)。

hfinite用真实连续函数在Icc上的IntegrableOn；setIntegral_ge_of_const_le_real显式消费measurableSet_Icc、volume_Icc=ofReal(r)≠∞、逐点下界和hfinite。真实volume.real(Icc r2r)=r由r≤2r先建立；没有对无穷体积toReal。hsub再消费全Ioi0上的weightedR真L1、AE非负和A⊂Ioi0的AE子集门，扩大积分上界。hsqrt≠0后准确清分母，把常数乘真实长度化为6h√h/(577π)。端点平方、分母正与测度有限门均实际出现。

profile_lattice_gap结合准确quadrature identity、这个raw lower及R_ell≥0，得到∫F+6h√h/(577π)≤hΣF。无需未证EM／ζ或“h充分小”，所有0<h≤1均成立。

### 4.8 550–682：实际同μ stage门、L2与最终4096π归一化

hb从hrange按Fin4／FinJ映射公开fixedAtom_bounds；hbase只取实际hpos的inl分支。同μ normalVariance_pos和transverseVariance_pos给S,T真正正，不使用atomic-only版本。hX/hX2真Integrable在积分线性前建立，EY=8EX−EX²代两实际均值给EX²=q；hLp是真MemLp2，variance_eq_sub先消费它，再得VarX=q−q²/16。

transverseVariance_le_variance_id给T≤该真VarX；正T后hfrac真实跨乘出1/30<q/(32T)。可独立核算30q−32T≥2q(q−1)>0，q>1足够，hq1在冻结接口中保持。κ=√q/(4√T)>0，hksq使用真实sqrt平方给κ²/2=q/(32T)，故a>1/30>sourceEll；ell始终是真log(31/30)，绝非等于1/30。

hY先同stage fixedAtom_normalValue_lower给Y≥−9，再用全球恒等式Y=16−(x−4)²给Y≤16，因此|Y|≤16。hYlp先真MemLp2，hY2由真实紧界连续多项式给L1；平方上界256经integral_mono_ae和概率常数真可积给E(Y²)≤256。variance_eq_sub消费hYlp后得S≤256，Spos再给0<σ=√S≤16。没有从仅|X|界省略真实Y界，也没用variance.toReal总化冒充二阶矩。

hmesh正与≤1从公开dyadicMesh定义重证，未调用其他模块private helper。公开K恰以同μ/J/q／均值／范围／单点门给所有d的actual profile identity及(1/σ)∫同F=actual correctedInverseScale。用函数外延hfunext转移整数真Summable，raw profile gap同一函数／law转移，乘1/σ≥0。

最终hmargin先σ≤16，随后正分母4096π与577π跨乘核16/4096≤6/577（16*577=9232<24576=6*4096）。σ>0才除σ。该步与独立证书raw归一化至少3/(4616π)>1/(4096π)一致。乘积分的continuous exact K identity把第一项换成同law corrected值，最后环恒等式(1/σ)(hΣF)=(h/σ)ΣF匹配完整公开target。全部J含0=h1，无n依赖参数或q重选。

## 5. 实际固定库与已接受继承语义

读取了当前固定源码中实际主API类型及实现；不凭编译日志或只凭名称猜测。

| 主API实际来源 | 实际消费门／实现核对 |
| --- | --- |
| Deriv.MeanValue437–440 | 全实HasDerivAt与全实导数非负才给Monotone，源码经deriv版本／凸域平均值定理实现；R的φ满足全称门 |
| Complex.Exponential的add_one_le_exp／exp_add／exp_nat_mul | 全实exp tangent和真实指数相乘，生成R符号与ratio，不引入数值exp近似 |
| InfiniteSum.ENNReal532–537 | Summable.of_nonneg_of_le先真majorant Summable、逐项非负与比较，lift NNReal后生产实Summable |
| SpecificLimits.Normed493–497 | 真|ratio|<1的几何可和／sum；actual proof的r>0先给ratio域 |
| NatInt349–374 | 真实不交Nat／negSucc分区生成additive HasSum／Summable／tsum，重排需两子列真Summable |
| Integral.DominatedConvergence97–115 | 先各项Integrable和积分norm列Summable，底层证明ENNR norm积分总和≠∞再生产积分HasSum，非总化无条件交换 |
| Integral.Prod230–242,481–483 | joint AEStronglyMeasurable＋AE真sections＋真实norm-integral L1得到prod Integrable；Fubini再消费该joint门 |
| ImproperIntegrals77–80,102–107 | exp积分Ioi要求实际系数<0；本源传−s(t)、−ell，真可积同时建立 |
| Bochner.Set733–736 | setIntegral_mono_set需全目标集合真实IntegrableOn、AE非负与AE子集；代码hsub实际都给出 |
| Bochner.Set794–797 | 常数下界积分还需MeasurableSet、μs≠∞及真实函数IntegrableOn，返回c*μ.real s≤∫s f；有限Icc门完整 |
| Lebesgue.Basic87–94／Lebesgue.Integral89–91 | 实区间有限长度与真实反射／端点零质量，current volume非人为实例 |
| IntervalIntegral.Basic1210–1214 | 真Iic/Ioi两侧可积后分拆全实积分 |
| Probability.Moments.Variance226–228 | variance_eq_sub要求真概率和MemLp2，本public proof对X/Y分别先生产 |

公开K的一般stage完整接口、L的真实负曲边混合接口及GaussianBoundaryConstant的真实density／profile／piecewise在此前完整独立终票已接受，本次消费其实际同law语义并最后重核源码hash，不重编旧目标。Cauchy主控质量来自真实ImproperIntegrals，不是新增假设。T=detΔ/S是τ²，κ分母是4√T，normalVariance是σ²；整个证明未混淆三者。

## 6. 全部50 actual DECL／完整TYPE审查

在任何作者receipt／build机械状态之前，已经读取首Audit全部50个DECL／TYPE及所有续行。下列逐项保存允许选择的类型证据（不是raw完整日志下载）；✝为Lean私有显示名。每个private DEF除TYPE外，其完整body已在第3节核；每个定理的证明语义已对应第4节，而非仅按数量通过。

### TYPE 01 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.integral_weightedR_lower

```lean
∀ (ell a h : ℝ),
  1 / 30 < a →
    ell < 1 / 30 →
      0 < h →
        h ≤ 1 →
          6 * h * √h / (577 * Real.pi) ≤
            ∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.cauchyWeight✝ t * Shao.OQ3.quadratureR✝ (Shao.OQ3.decayRate✝ ell a t) h
```

核：actual条件a>1/30,ell<1/30,0<h≤1；真有限区间给raw6/(577π)。

### TYPE 02 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_le_half

```lean
∀ (s h : ℝ), 0 < s → 0 < h → Shao.OQ3.quadratureR✝ s h ≤ h / 2
```

核：exp tangent比较的两分母先正，不能无hs/hh使用。

### TYPE 03 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.mixedKernel_le

```lean
∀ (ell a x t : ℝ),
  0 ≤ a → ell < a → 0 ≤ x → Shao.OQ3.mixedKernel✝ ell a x t ≤ Shao.OQ3.cauchyWeight✝ t * Real.exp (-(a - ell) * x)
```

核：保留x非负、a非负和hgap；hgap对纯比较冗余，不削弱结论。

### TYPE 04 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.weightedR_integrable

```lean
∀ (ell a h : ℝ),
  0 ≤ a →
    ell < a →
      0 < h →
        MeasureTheory.IntegrableOn
          (fun t => Shao.OQ3.cauchyWeight✝ t * Shao.OQ3.quadratureR✝ (Shao.OQ3.decayRate✝ ell a t) h) (Set.Ioi 0)
          MeasureTheory.volume
```

核：真正被w*h/2主控的是weightedR，绝非裸R。

### TYPE 05 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.cauchyWeight

```lean
ℝ → ℝ
```

核：private DEF；完整body是2/π乘Cauchy核，第3节已核。

### TYPE 06 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.cauchyWeight_nonneg

```lean
∀ (t : ℝ), 0 ≤ Shao.OQ3.cauchyWeight✝ t
```

核：全部实t成立，π及1+t²正。

### TYPE 07 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.profile_positive_tsum

```lean
∀ (ell kappa h : ℝ),
  0 < ell →
    0 < kappa →
      0 < h → ∑' (n : ℕ), Shao.OQ3.gaussianBoundaryProfile ell kappa (↑n * h) = 1 + 1 / (Real.exp (ell * h) - 1)
```

核：正列含0，sum为1+负移几何分式，先真可和。

### TYPE 08 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.exp_succ_summable

```lean
∀ (r : ℝ), 0 < r → Summable fun n => Real.exp (-r * (↑n + 1))
```

核：真实succ注入重索引；n是Nat，不重复0。

### TYPE 09 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.mixedKernel_joint_integrable

```lean
∀ (ell a : ℝ),
  0 ≤ a →
    ell < a →
      MeasureTheory.Integrable (fun p => Shao.OQ3.mixedKernel✝ ell a p.2 p.1)
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict (Set.Ioi 0)))
```

核：实际p=(t,x)、kernel(p.2,p.1)，真实prod restrictions及norm-section门。

### TYPE 10 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.cauchyWeight_integrable

```lean
MeasureTheory.IntegrableOn Shao.OQ3.cauchyWeight✝ (Set.Ioi 0) MeasureTheory.volume
```

核：真实volume.restrict Ioi0的Cauchy L1。

### TYPE 11 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.tsum_profile_negative

```lean
∀ (ell kappa h : ℝ),
  0 < kappa →
    ell < kappa ^ 2 / 2 →
      0 < h →
        ∑' (n : ℕ), Shao.OQ3.gaussianBoundaryProfile ell kappa (-((↑n + 1) * h)) =
          ∫ (t : ℝ) in Set.Ioi 0,
            Shao.OQ3.cauchyWeight✝ t / (Real.exp (Shao.OQ3.decayRate✝ ell (kappa ^ 2 / 2) t * h) - 1)
```

核：负列从n+1起，积分norm列真Summable先交换；完整长续行已核。

### TYPE 12 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.profile_integer_summable

```lean
∀ (ell kappa h : ℝ),
  0 < ell →
    0 < kappa → ell < kappa ^ 2 / 2 → 0 < h → Summable fun k => Shao.OQ3.gaussianBoundaryProfile ell kappa (↑k * h)
```

核：源k:ℤ，正Nat与−(n+1)各自真Summable后不交覆盖。

### TYPE 13 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.decayRate

```lean
ℝ → ℝ → ℝ → ℝ
```

核：private DEF；完整body a(1+t²)−ell，第3节已核。

### TYPE 14 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_nonneg._simp_1_3

```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4], (4 = 0) = False
```

核：生成通用非零事实；完整实际前提保留：NeZero4。不是新增分析假设／axiom。

### TYPE 15 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.mixedKernel_nonneg

```lean
∀ (ell a x t : ℝ), 0 ≤ Shao.OQ3.mixedKernel✝ ell a x t
```

核：任意实参数只给点态非负，不声称任意x时L1。

### TYPE 16 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.profile_neg_mixture

```lean
∀ (ell kappa x : ℝ),
  0 < kappa →
    0 ≤ x →
      Shao.OQ3.gaussianBoundaryProfile ell kappa (-x) =
        ∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.mixedKernel✝ ell (kappa ^ 2 / 2) x t
```

核：ell任意实，但κ正／x非负；L真核可积，不自动全x积分换序。

### TYPE 17 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.integral_mixedKernel_x

```lean
∀ (ell a t : ℝ),
  0 ≤ a →
    ell < a →
      ∫ (x : ℝ) in Set.Ioi 0, Shao.OQ3.mixedKernel✝ ell a x t = Shao.OQ3.cauchyWeight✝ t / Shao.OQ3.decayRate✝ ell a t
```

核：积分变量是x，正确负指数系数−s，先真正率可积。

### TYPE 18 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.mixedKernel

```lean
ℝ → ℝ → ℝ → ℝ → ℝ
```

核：private DEF；完整body w(t)exp(−s(t)x)，实际参数次序已核。

### TYPE 19 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR._proof_1

```lean
(1 + 1).AtLeastTwo
```

核：实际Nat (1+1).AtLeastTwo，类field仅2≤n，即闭算术2≤2；非隐含额外前提。

### TYPE 20 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.exp_nat_summable

```lean
∀ (r : ℝ), 0 < r → Summable fun n => Real.exp (-r * ↑n)
```

核：r>0给真ratio∈(0,1)，源指定n:ℕ。

### TYPE 21 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.mixedKernel_continuous

```lean
∀ (ell a x : ℝ), Continuous (Shao.OQ3.mixedKernel✝ ell a x)
```

核：固定ell/a/x、对t连续，全部实参数无错误L1推广。

### TYPE 22 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.mixedKernel_integrable

```lean
∀ (ell a x : ℝ),
  0 ≤ a → ell < a → 0 ≤ x → MeasureTheory.IntegrableOn (Shao.OQ3.mixedKernel✝ ell a x) (Set.Ioi 0) MeasureTheory.volume
```

核：真Cauchy常数主控及可测门，限定x≥0。

### TYPE 23 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR

```lean
ℝ → ℝ → ℝ
```

核：private DEF；完整body为第3节真实梯形余量，类型本身不提供无条件正域。

### TYPE 24 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.exp_nat_tsum

```lean
∀ (r : ℝ), 0 < r → ∑' (n : ℕ), Real.exp (-r * ↑n) = 1 / (1 - Real.exp (-r))
```

核：严格r域、真几何可和，分母1−exp(−r)>0。

### TYPE 25 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.integral_mixedKernel_le

```lean
∀ (ell a x : ℝ),
  0 ≤ a → ell < a → 0 ≤ x → ∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.mixedKernel✝ ell a x t ≤ Real.exp (-(a - ell) * x)
```

核：先两边真实Integrable后integral_mono，质量1。

### TYPE 26 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_nonneg._simp_1_7

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ), (↑n + 1 = 0) = False
```

核：生成通用非零事实；完整实际前提保留：AddMonoidWithOne、CharZero及n:ℕ强制转换。不是新增分析假设／axiom。

### TYPE 27 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.profile_nat_summable

```lean
∀ (ell kappa h : ℝ),
  0 < ell → 0 < kappa → 0 < h → Summable fun n => Shao.OQ3.gaussianBoundaryProfile ell kappa (↑n * h)
```

核：ell/κ/h全正给正列真Summable，含n0。

### TYPE 28 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_nonneg._simp_1_5

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ), a ≠ 0 → (a ^ n = 0) = False
```

核：生成通用非零事实；完整实际前提保留：MonoidWithZero、IsReduced、a非零及n:ℕ。不是新增分析假设／axiom。

### TYPE 29 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_ge_quarter

```lean
∀ (s h : ℝ), 0 < s → 0 < h → 4 ≤ s * h → h / 4 ≤ Shao.OQ3.quadratureR✝ s h
```

核：保留4≤s*h及s/h正域，来自1/s≤h/4和几何项非负。

### TYPE 30 — Shao.OQ3.stage_sourceGaussianLayerWeight_lattice_gap

```lean
∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (J : ℕ) (q : ℝ),
  1 < q →
    q < 103 / 100 →
      ∫ (x : ℝ), Shao.OQ3.normalValue x ∂mu = q →
        ∫ (x : ℝ), x ∂mu = q / 4 →
          (∀ᵐ (x : ℝ) ∂mu, x ∈ Set.range fun i => Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i) →
            (∀ (i : Fin 4 ⊕ Fin J), 0 < mu.real {Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i}) →
              (Summable fun k =>
                  Shao.OQ3.sourceGaussianLayerWeight mu q Shao.OQ3.sourceEll (↑k * Shao.OQ3.dyadicMesh J)) ∧
                Shao.OQ3.correctedInverseScale Shao.OQ3.sourceEll q mu +
                    Shao.OQ3.dyadicMesh J * √(Shao.OQ3.dyadicMesh J) / (4096 * Real.pi) ≤
                  Shao.OQ3.dyadicMesh J / √(Shao.OQ3.normalVariance mu) *
                    ∑' (k : ℤ), Shao.OQ3.sourceGaussianLayerWeight mu q Shao.OQ3.sourceEll (↑k * Shao.OQ3.dyadicMesh J)
```

核：完整actual elaborated public TYPE与第1节／scope同一μ/J/q及全部门；无手工S/T/gap输入。

### TYPE 31 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_nonneg._simp_1_6

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ), a ≠ 0 → (a ^ n = 0) = False
```

核：生成通用非零事实；完整实际前提保留：GroupWithZero、a非零及n:ℤ。不是新增分析假设／axiom。

### TYPE 32 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_nonneg._simp_1_2

```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3], (3 = 0) = False
```

核：生成通用非零事实；完整实际前提保留：NeZero3。不是新增分析假设／axiom。

### TYPE 33 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.integral_weightedR

```lean
∀ (ell a h : ℝ),
  0 ≤ a →
    ell < a →
      0 < h →
        ∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.cauchyWeight✝ t * Shao.OQ3.quadratureR✝ (Shao.OQ3.decayRate✝ ell a t) h =
          (h * ∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.cauchyWeight✝ t / (Real.exp (Shao.OQ3.decayRate✝ ell a t * h) - 1)) +
              h / 2 -
            ∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.cauchyWeight✝ t / Shao.OQ3.decayRate✝ ell a t
```

核：三项分别真L1后线性及质量1，h/2符号精确；完整续行已核。

### TYPE 34 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.weightedR_continuous

```lean
∀ (ell a h : ℝ),
  0 ≤ a →
    ell < a →
      0 < h → Continuous fun t => Shao.OQ3.cauchyWeight✝ t * Shao.OQ3.quadratureR✝ (Shao.OQ3.decayRate✝ ell a t) h
```

核：仅weightedR连续；分母s与exp(sh)−1处处正。

### TYPE 35 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.integral_profile_split

```lean
∀ (ell kappa : ℝ),
  0 < ell →
    0 < kappa →
      ell < kappa ^ 2 / 2 →
        ∫ (d : ℝ), Shao.OQ3.gaussianBoundaryProfile ell kappa d =
          1 / ell + ∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.cauchyWeight✝ t / Shao.OQ3.decayRate✝ ell (kappa ^ 2 / 2) t
```

核：full profile真Integrable后真实Iic/Ioi与反射，得到正侧1/ell。

### TYPE 36 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.integral_cauchyWeight

```lean
∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.cauchyWeight✝ t = 1
```

核：真Cauchy半线质量准确1，是端点抵消承重事实。

### TYPE 37 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.profile_quadrature_identity

```lean
∀ (ell kappa h : ℝ),
  0 < ell →
    0 < kappa →
      ell < kappa ^ 2 / 2 →
        0 < h →
          h * ∑' (k : ℤ), Shao.OQ3.gaussianBoundaryProfile ell kappa (↑k * h) -
              ∫ (d : ℝ), Shao.OQ3.gaussianBoundaryProfile ell kappa d =
            Shao.OQ3.quadratureR✝ ell h +
              ∫ (t : ℝ) in Set.Ioi 0,
                Shao.OQ3.cauchyWeight✝ t * Shao.OQ3.quadratureR✝ (Shao.OQ3.decayRate✝ ell (kappa ^ 2 / 2) t) h
```

核：两Nat列先真Summable，0层只计一次，准确Rell+∫wR，不借EM。

### TYPE 38 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_nonneg._simp_1_4

```lean
∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀] [NoZeroDivisors M₀] {a b : M₀},
  a ≠ 0 → b ≠ 0 → (a * b = 0) = False
```

核：生成通用非零事实；完整实际前提保留：NoZeroDivisors和a/b分别非零。不是新增分析假设／axiom。

### TYPE 39 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.profile_neg_summable

```lean
∀ (ell kappa h : ℝ),
  0 < kappa →
    ell < kappa ^ 2 / 2 → 0 < h → Summable fun n => Shao.OQ3.gaussianBoundaryProfile ell kappa (-((↑n + 1) * h))
```

核：只需κ正／ell<κ²/2／h正；ell无需正，因为仅负列。

### TYPE 40 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_nonneg

```lean
∀ (s h : ℝ), 0 < s → 0 < h → 0 ≤ Shao.OQ3.quadratureR✝ s h
```

核：第4.1节全实φ导数／正分母证明；s/h严格正。

### TYPE 41 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.weighted_inv_integrable

```lean
∀ (ell a : ℝ),
  0 ≤ a →
    ell < a →
      MeasureTheory.IntegrableOn (fun t => Shao.OQ3.cauchyWeight✝ t / Shao.OQ3.decayRate✝ ell a t) (Set.Ioi 0)
        MeasureTheory.volume
```

核：s≥a−ell>0及w/(a−ell)真L1主控；明确volume。

### TYPE 42 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.weighted_geom_integrable

```lean
∀ (ell a h : ℝ),
  0 ≤ a →
    ell < a →
      0 < h →
        MeasureTheory.IntegrableOn
          (fun t => Shao.OQ3.cauchyWeight✝ t / (Real.exp (Shao.OQ3.decayRate✝ ell a t * h) - 1)) (Set.Ioi 0)
          MeasureTheory.volume
```

核：正exp(s*h)−1及倒率/h L1主控，非无条件几何分母。

### TYPE 43 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.exp_succ_tsum

```lean
∀ (r : ℝ), 0 < r → ∑' (n : ℕ), Real.exp (-r * (↑n + 1)) = 1 / (Real.exp r - 1)
```

核：先真序列tsum拆0，再exp(r)−1正域约分。

### TYPE 44 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.quadratureR_nonneg._simp_1_1

```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2], (2 = 0) = False
```

核：生成通用非零事实；完整实际前提保留：NeZero2。不是新增分析假设／axiom。

### TYPE 45 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.decayRate_pos

```lean
∀ (ell a t : ℝ), 0 ≤ a → ell < a → 0 < Shao.OQ3.decayRate✝ ell a t
```

核：明确a非负及ell<a，严格正率先于求和／积分。

### TYPE 46 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.decayRate_lower

```lean
∀ (ell a t : ℝ), 0 ≤ a → a - ell ≤ Shao.OQ3.decayRate✝ ell a t
```

核：只需a非负；不把t界作为隐藏条件。

### TYPE 47 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.profile_lattice_gap

```lean
∀ (ell kappa h : ℝ),
  0 < ell →
    ell < 1 / 30 →
      0 < kappa →
        1 / 30 < kappa ^ 2 / 2 →
          0 < h →
            h ≤ 1 →
              (∫ (d : ℝ), Shao.OQ3.gaussianBoundaryProfile ell kappa d) + 6 * h * √h / (577 * Real.pi) ≤
                h * ∑' (k : ℤ), Shao.OQ3.gaussianBoundaryProfile ell kappa (↑k * h)
```

核：ell正及严格source式阈值、全部h∈(0,1]，raw真实profile差。

### TYPE 48 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.cauchyWeight_continuous

```lean
Continuous Shao.OQ3.cauchyWeight✝
```

核：实际分母处处非零；与积分主控同一weight。

### TYPE 49 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.profile_pos

```lean
∀ (ell kappa x : ℝ), 0 < kappa → 0 ≤ x → Shao.OQ3.gaussianBoundaryProfile ell kappa x = Real.exp (-ell * x)
```

核：κ>0、x≥0，包括0层；原Gaussian全质量真实1。

### TYPE 50 — _private.Shao.OQ3.SourceGaussianLatticeGap.0.Shao.OQ3.integral_profile_negative

```lean
∀ (ell kappa : ℝ),
  0 < kappa →
    ell < kappa ^ 2 / 2 →
      ∫ (x : ℝ) in Set.Ioi 0, Shao.OQ3.gaussianBoundaryProfile ell kappa (-x) =
        ∫ (t : ℝ) in Set.Ioi 0, Shao.OQ3.cauchyWeight✝ t / Shao.OQ3.decayRate✝ ell (kappa ^ 2 / 2) t
```

核：κ正／gap保证真实联合L1后才Fubini；ell可任意实。

实际合计4private DEF＋37authored private theorem＋1public target＋8generated theorem＝50owned／46theorem；生成项恰7个真实一般非零simp事实和1个Nat.AtLeastTwo，不臆测存在eq_1或其他helpers。已读每项全部TYPE续行，无省略号／截断接受。

## 7. 机械证据最后：源码、现有首完整成功与公理门

本节只在685行proof、实际主API及50全TYPE独立审查之后读取。作者receipt的AWAITING_INDEPENDENT_PROOF_REVIEW是作者check时历史状态，本票最终独立CORRECT是后来的判断；不能混成作者自己已做独立终审。没有以receipt的implementation_environment_note替代第4节数学核验。

10:23:23 UTC实际只读观察：worktree为/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3，branch feat/oq3-source-gaussian-lattice-gap，HEAD f879f4d2c7b768b938b32f08826963254fabc9d1；git status仅`?? Shao/OQ3/SourceGaussianLatticeGap.lean`。L正常PR128的head推进已经冻结，不是前置源漂移。没有reviewer commit／PR／pub或源修改。

以下local／worktree／run对应项已实际只读hash，非只按brief引用：

| 证据 | 字节／行 | SHA256 |
| --- | --- | --- |
| actual M源码，local／worktree／run snapshot三端 | 33728／685 | d211fa4e676fbb76e81ff59008fb654c6b4fdc51c78a1bccd7adf4b1f5b419bd |
| frozen scope60，local／run | 7141／40 | 1db7c32e02a40cd2973366f5328208a68fe87f4c67d7702d2c64ea08614a3195 |
| 声明终票，local／run | 27776／254 | 071221160cd299ad910bc261f0608ef64e691c30c1419dbcfe85f47346e23bf7 |
| Audit源，local／run | 1683／39 | f2728896f88e57a9503c3a0fb0196e097cfcba78e5cc7f23bbe8ce3f1d3a9a21 |
| Audit.log，留server | 14464／254 | 2fbfbb239232b5569b22bc5924c716402136cac1ff15647bfa130f95a2f7b8b2 |
| receipt，local／run | 23145／502 | 06b6b7a85287949e6dfbc5caf24b1e1d2e6a44ebd86cd19927ff194ff83b784e |
| build-history.json，server | 10070／376 | 6df4bb5bfca10a7cfa14d1875a5a060cd2a9a7b577aba1ccd7f873f0088462bf |
| prerequisite-hashes.json，local／run | 6042／58 | 549c7178e433e802ed84d052be989eb9c8e53710278ee55da2ebd3293b2cad11 |

Audit实际源已读：冻结唯一target要求存在且为theorem；枚举公开target stem和整个_private.Shao.OQ3.SourceGaussianLatticeGap前缀，拒newaxiom并逐常量Lean.collectAxioms检查白名单。actual source词法／全文清点42个authored声明加8generated与50输出一致，未漏别名或额外private。实际50DECL／50TYPE／50AXIOMS行；axiom集合只有[propext]或[propext,Classical.choice,Quot.sound]。实际footer为0 frozen defs、1 frozen theorem、46 all theorem、50 all declarations、U17M_AXIOM_GATE PASS。当前target olean存在，但本审查没有为此重编。

build17是当前完整685行源首次complete success，保存历史exit0，实际日志4054字节，SHA916d5de1763b0563ac76a9cb3f7937e9bc0c32d2bbb053750a348d1a97307634。它非空，有19个真正warning诊断、0error；主要为tactic sequencing、未显式引用hgap／未使用simp参数、deprecated if_pos等。不能写成空build／零warning。未为清理这些非实质风格项而修改或重复成功source。

实际build-history与receipt.incremental_history17条逐字段相等；17个记录source SHA全部不同，每个现有build log的实际hash及字节数均与相应记录匹配。下表严格区分partial与complete；04不能作为完整frozen target验收，也不能把所有01–16统称失败。

| attempt | 当时源码行／完整性／exit | 记录source SHA256 | 实际server log SHA256 |
| --- | --- | --- | --- |
| 01 | 134／PARTIAL_FAILURE／1 | ae01611bc055b05007fc2ca9d11d36f3c6f12d09e698d5633b801e33a5b8d0d6 | 6dacc9f5ff5ec1054c9afd3311834246cb5513f9a0bf042d170364226d6f84f6 |
| 02 | 136／PARTIAL_FAILURE／1 | 32239db5e09c79217f7ccb3d3deb5b0c52a607df89f43f05ea5441ed16a2b19f | 098c1233a815fce34c320e2195643aef08c82ab095989f36889b28e122185623 |
| 03 | 138／PARTIAL_FAILURE／1 | 248eace61d8a27cecc12b8b4de5c341a862844ca32c19524219ff719f8ea2e56 | 1683d4263ee9e8f9ccf030688a45c18ca2708bcc9d74ac2aec783fa62df64c0d |
| 04 | 140／PARTIAL_SUCCESS／0 | bd5111412db15d26b1690f4a76f227b918cf33c9c45c6f255145886ed9a13477 | 954f0e4df9d55a5017fd95676a491ea430b5d5c1a5174a832bed53219cf1cfce |
| 05 | 240／PARTIAL_FAILURE／1 | 690e20fb0e5d0b7ff35f2d2148c151d8676c3caa24f41f8c0a91afdb5114d478 | 318cc3cf5f5591e40bcfdec1684dc967e870653d51823780afda6c1e1ddc550f |
| 06 | 242／PARTIAL_FAILURE／1 | a6e63f38f8841b6dea192072384203919d29e9d46b63342b01e4c47c41ab5ecf | bc873524bc0ce004e66afc04802b8e1465cff450679a8105f9c02902666def88 |
| 07 | 240／PARTIAL_FAILURE／1 | 67c8a7fc86aef3ef73493ac2fd9efddff0a3aeb7d744bda4546fe2d451ce1fd8 | abba74472b51b22bd114031d6b5407fc310c34123ddfa9417be79f6ab10e7fd4 |
| 08 | 350／PARTIAL_FAILURE／1 | f3b08886f0537a5a7eca8cf5a5844dc393abbc0ab6f5bd4797e36eb8c661b8dc | 69edd06d254ca4d3d7a8b5f9d9a5674e064a24cf227f86938dff48334f602eda |
| 09 | 351／PARTIAL_FAILURE／1 | afbb25cba6018dd1a4e7103b1741d6a063afe2f127e5a95b7071a6d70796a97b | 51d2323b1cfe34d75374e471660824b3ac0bc59c308b8b9268ccd4cae6c9cd89 |
| 10 | 467／PARTIAL_FAILURE／1 | b17d080f8622fe423dbf2b5a7903190687a9b77e797481cbc56c6fd4433d4a3e | 8c03039f520ae7ef7f344e88f21a54b7ab137acd8b31df84d63f6fbfe976402b |
| 11 | 468／PARTIAL_FAILURE／1 | 92663d230c7bb40bfc967ff1c3e8544762e25e4a9347897e0bd603e6d07154ca | d3fc72ac82c4969bd214050f737409c632683a11f8140cf6a0c7b31a8521adc0 |
| 12 | 548／PARTIAL_FAILURE／1 | 6174fcae4e4acfa9996e3dd27156d1556144daf88108f62eb9114bd3b33b04e6 | f5b3aa41b3f57cad70ed48692ca05ccebf2dad333f42de8d9a1c2ed562ae618d |
| 13 | 550／PARTIAL_FAILURE／1 | 582ca5f9957c43c07a95fa7952bc483e15b12398518b5763ff97919dab572dc6 | 8a5d1ff368daf7f67b6f09729143a056a93b795db6a990556a060c9903b4b4d8 |
| 14 | 675／COMPLETE_FAILURE／1 | 9dbea8317966932f525effe58ddfe6f4df28d613abdad76e128dc4135c0dbdc9 | 0431be5c4a5697962fcc032cc7b57df6240f71ee68e80438b270553043d5f9fe |
| 15 | 678／COMPLETE_FAILURE／1 | 8676f63c5782921fb95b387dfbd9d241353f404dc8d9faae4ca08ca26dbd82a7 | 17130aa9c5b7bc8a90b6b0c4878a680cc1c3ebde0f81c5f3102f5ee97f86dce9 |
| 16 | 681／COMPLETE_FAILURE／1 | 4c6e9cb8620480747c34e7f8afaabcd2a36a2251d17ca92d5173125887413d74 | 530a615cff3f8f02da424e5d4ee34a40dadac8df43d6890455a9121271f01cdf |
| 17 | 685／COMPLETE_SUCCESS／0 | d211fa4e676fbb76e81ff59008fb654c6b4fdc51c78a1bccd7adf4b1f5b419bd | 916d5de1763b0563ac76a9cb3f7937e9bc0c32d2bbb053750a348d1a97307634 |

01–03和05–13为changed partial失败；04是真正140行private部分成功；14–16是changed完整版本失败；17是当前完整版本首次成功。10／11实际选取诊断均显示默认200000heartbeat在whnf耗尽；当前NatInt调用明确传真实f，源码没有set_option或heartbeat／maxRecDepth设置，保存命令也无该类弱化。当前完整冻结type／imports始终未改；历史partial不是承诺完整目标已过。

关于local put路径误写及随后重复尝试：作者保存receipt将其明确记录为Python sourcehash guard在任何Lean启动前拒绝，未计入17条实际build。本次独立可核事实是17历史条目各sourcehash不同、build04 partial／build17 complete分类及对应log hash匹配，没有重复相同成功source或Audit的保存记录；reviewer未重演transfer／guard或启动Lean来验证历史。透明保留这一区别，不把guard拒绝捏造成第18次Lean失败或成功。

保存target／Audit命令都为taskset -c 14-17 lake env lean -M8192 -j4 -DautoImplicit=false，17条历史记录的affinity均[14,15,16,17]、native_memory_mib8192／jobs4／autoImplicit false。reviewer所有server项目只读命令同样taskset -c 14-17，未启动heavy Lean，未用ulimit-v，未触CPU0–9外部80GiB任务／全局资源，未改心跳或证明强度。

lean-toolchain真实29字节／1行、内容leanprover/lean4:v4.36.0-rc1、SHAd581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4。lake-manifest真实3541字节／117行、SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e；mathlib实际git HEAD807d3836b165983210ee2ecf3cd28f239436949c，与receipt匹配。没有运行Lean版本探针或更新pin。

独立actual源扫描：完整publicTYPE与冻结scope白空格匹配；5imports恰为L、Deriv.MeanValue、Integral.Prod、Integral.DominatedConvergence、InfiniteSum.NatInt；CR0、无尾空白，sorry／admit／axiom／unsafe／native_decide／implemented_by／set_option均无匹配。全文审查补足扫描局限。没有新public DEF、shared instance或隐式新增概率假设。

## 8. 实际public图、56项目前置与cache绑定

从actual5import重新进行剥嵌套注释／行注释／字符串的词法闭包核对；新module只沿public import检查公开可见性、旧式模块沿真实import。得到56Shao／2905Mathlib物理源依赖，所有对应源／现成olean实际齐，missing0；公开图2679模块。第5节所有实际主API与K/L一般stage／真实profile接口都公开可达。Pi.Bounds不在物理或公开依赖，其olean仍缺，但本证明只消费cached Trigonometric.Basic的π正性，无需补cache。

actual56项源hash map与run prerequisite及receipt的imported_project_sources_sha256逐项一致，compact排序SHAa0882f1323c3678065d15727dca14fcee92da8a9df770c7b0550e4b19b5ea582。当前M自身不计入前置56。以下完整map直接绑定已读取实际worktree源，而不是只把receipt重复一遍；所有旧成功proof／构建未重做。

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
Shao/OQ3/GaussianBoundaryLaplaceMixture.lean fd470e5ffcea5299222a570389ae9603beb1e78b34c065d637e26e08c76dd421
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

实际关键库文件hash也与先前声明门保持：Bochner.Set e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75；InfiniteSum.ENNReal 88ef56c969006630d0066b7af2c74e75dd060608f3c42f0ef288ad1c6da908cc；Integral.Prod 8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05；DCT56394aacfe591230d26a1d93641f2a1d3e3a3eae4fcfe772775533a1da295833；NatInt4dc1dffbdb6a0b0157e8810b20dfc0051bedf7f449b6d1fa5b8a9a47fa47f645；Lebesgue.Integral8fa19186f554100cee2b450ba3faef3e84c0407734a3068e442093d2b9ff4ea4；Deriv.MeanValueb6f3e52c283bdd2c3eb01173c8ac32b82dff0efdfc1890c361f8eed63359edb8；Complex.Exponential35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146；SpecificLimits.Normedeee44dfd62feb67bdf3ccc6cf57e8e101f38a7408dbb9c6347e0978ce2010d41；Variance0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e。没有读取作者candidatecache metadata或implementation／future notes；没有任何cache写入。

## 9. 最终独立裁决、原25与剩余

STATUS: CORRECT。

JUSTIFICATION: actual完整frozen public TYPE忠实于scope60与R1同一真实stage模型。全部685行／4private完整DEF／37private证明／所有locals已独立审；正率、真正各项／joint Integrable与积分norm真Summable在所有无穷交换前建立。真实Iic/Ioi反射、整数Nat/negSucc覆盖及Cauchy质量1保证零层一次和h/2精确抵消；R全实φ导数非负与正确正分母证明三个不等式。真实有限Icc长度／逐点平方界／setIntegral门给raw6h√h/(577π)，同μ X/Y真L2与实际stage范围生产a>1/30>log(31/30)>0及0<σ≤16，最后严格正σ下归一化得到公开h√h/(4096π)，全J含0。全部50actual TYPE及8generated真实通用前提已核，50owned全传递公理白名单／首完整build17非空19warning／source三端／56真实前置／pins／公开API绑定一致。未发现实质数学、来源、类型或环境缺口。

本CORRECT为完整独立proof verdict，不是作者机械PASS的转述。当前实现完成原(25)所需的一条充分显式uniform gap及实际整数Summable：b=1/(8192π)>0、J0=0对这同一实际source finite family可用；不声称原(24)精确ζ系数或最优常数。lead需全文读本票后再进行接受计数／提交／发布，reviewer不自行commit或提前修改协调状态。

直接consumer仍为原(26)：要接真实hcont生产者至无条件19、相位回返与实际diagonal n_J选择。U18a／hcont、无条件15/19、rotation／diagonal、Phi字面CDF／完整LLT、hW、generalKL及root A/B/C/D均仍OPEN。没有把充分β修复当最优／最弱或把经典正混合称新颖结论。19style warnings透明保留为非实质限制；无重编、源／旧票／scope／receipt／共享文件／cache修改、spawn或发布动作。
