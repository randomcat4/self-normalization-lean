# U17d SourceFarWeightedTail 完整独立proof/source/actualTYPE审查

STATUS: CORRECT

唯一reviewer lease1。仅拥有此新报告及remote runs/oq3/u17d-20261021/proof-review.md；不独占代码库，不修改作者source/scope/receipt/旧票/shared/cache，不spawn/Lean/probe/build/rebuild/commit/raw完整log下载，不读作者future/candidate/实施notes。已知此前声明审查上下文，但本次先仅提取actual完整公开type，重新独立翻译并持久化，再读实际proof和机械证据。

## 1. 实际唯一公开完整type（先读）

```lean
theorem exists_source_far_weighted_tail_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H ell delta : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hgap : ell * q < 7 / 200) (hdelta : 0 < delta)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 0 < n →
      Integrable (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z))
        (Measure.pi (fun _ : Fin n => mu)) ∧
      (∫ z : Shao.Path n in {z | z ∈ sourceTail q n ∧
          normalDeviation q z ≤ -delta * (n : ℝ)},
        Real.exp (-ell * normalDeviation q z)
        ∂Measure.pi (fun _ : Fin n => mu)) ≤ C * Real.exp (-c * (n : ℝ))
```

## 2. 独立数学盲译（先持久化）

取同一真实实概率mu；mu-AE |x|≤4+sqrt10。固定实q,H,ell,delta：1<q<103/100，50<H<51，ell≥0，ell*q<7/200，delta>0；mu-AE每个原子值/实坐标满足1≤x²≤1+H，同mu真实二阶矩∫x²=q。这里没有EX=q/4或EY=q、正协方差、有限支持假设。

须存在同一对正实C,c，在所有自然n>0之外固定，使每个n的真实Fin n产品mu^n上，完整权重w(z)=exp(−ell*M_q(z))真正Integrable；且在真实{sourceTail q n 且M_q(z)≤−delta*n}事件上w的受限Bochner积分≤C*exp(−c*n)。C/c可依赖所有固定输入，不能依赖n或样本z；全n>0成立而非仅eventually。n=0明确不在结论中。

这是远负法向部分真实加权积分；负M时−ell*M≥0，权重增长，因此必须正确利用gap抵消。不能把不可积Bochner积分总化为0当作证明；不能用逐样本选择的测试当固定概率密度直接积分。要求真可积、可测/AE转移、正单点normalizer和有限和积分均有真实门。ell=0、空事件/空有限测试、能量端点/任意正delta保留，不得非法除ell或假定测试正。

此阶段尚未审实现、private/generated、TYPE或receipt/build/Audit；本票尚无最终判定。所有根、generalKL、全joint外区/full17/19/LLT/hW仍OPEN。

## 3. Scope、来源与实际声明对应

第1–2节先独立落盘（33行阶段SHA256=5a6eedb224b8eda0ef89822abcc08591f01c64e443554e6901c7cc181becaaac），之后才读冻结scope、R1与全实现；此前完整声明票存在的上下文已明示，不伪称对项目全无先验。此次重新审actual类型与proof，不把旧声明批准或作者绿灯当证明。

actual source的公开type与scope唯一type保留同mu、全部q/H/ell/delta假设、真实产品Integrable、真实受限积分及全n>0量词。没有新增公开定义或隐含均值/方差/离散支持假设；最终机械阶段将逐字核冻结全文与imports/hash。

R1 lines164–188的能量支持/Bernoulli充分gap、224–237的率gap论述、386–391的加权负层和远区控制是实际来源。目标实现只到{sourceTail且M≤−delta*n}的远负法向部分真实加权积分指数衰减；不自动覆盖法向偏差小但切向远的全部joint外区，不等于全(17)/(19)。7/200=0.035是实际消费的充分gap，不能称103/3000的数值弱化或与其相等；源ell=log(31/30)不是1/30。没有证明通用KL/DPI/RN、Legendre最优、唯一全局鞍点、新颖性或最优常数。

## 4. 逐段完整实现与承重语义审查

已逐行读取全部158行actual source，含2个authored private及所有主证明locals；还未读取作者receipt/build/Audit绿灯。无源编辑/Lean/probe。

### 4.1 两个private辅助（lines10–40）

sample_projection_linear（10–16）：实际centeredSampleProjection是Σ[v(Y_i−q)+s(X_i−a)]，normalDeviation是ΣY_i−Nq。证明仅展开真实定义并用有限和加减/常数乘法/Fin n基数=N，得v*M+s*(ΣX_i−Na)。无均值、n正性或概率门，故n0也是真恒等式；没有将tangentDeviation(q)=ΣX−Nq/4偷换成任意a。

sample_energy_mgf（18–40）：先逐点函数外延及真实normalValue=8x−x²给−t(Y−q)+8t(x−q/4)=t(x²−q)。再用前一private和normalDeviation_eq_sum_energy给实际sample指数恒等。最后消费已接受H iid_centeredSample_tilt在同mu/hb/q/a=q/4/v=−t/s=8t的公开完整类型，其.1为真产品exp Integrable、.2.1为真实积分=单点normalizer^n。这不是仅对t小或t正的接口；两辅助保留任意实q/t和所有n含0。

H的承重语义已按真实公开类型及实际定义复核：单点exp由hb和连续紧界真Integrable；H在任何乘积积分/归一化之前有Integrable.fintype_prod给真实联合可积，然后actual product integral=Z^n。D未调用不可积tilt=0总化分支，也未把任意中心q/a宣称mu均值。H既有完整独立终票已接受，本次绑定实际源码公开语义，不重做其成功构建。

### 4.2 常数与原weight可积（42–78）

主证明先由q>1、H>50得q,H>0（56–57）；58–59完整传递D的同mu/hb/q/H/ell/delta/真henergy/hsecond给C的公开finite-cover定理。C返回同一c>0及有限T，每个t∈T真单点exp可积且Z_t>0，且全部R∈Kfar有严格测试gap。60行就在intro n之前选Cconst=cardT+1与c，正性明确，不能依赖n、z或R。

61–70才固定n>0，N=(n:ℝ)>0、Nq>0，nu实际定义为mu的Fin n产品，Z_t为同mu真实能量normalizer，rho_t=exp(t(E−Nq))/Z_t^n，S=Σ_{t∈T}rho_t，Eevent为真正sourceTail∩{M≤−delta*N}。rho是局部函数，不是新公开任意“概率律”定义。

71–78对q/4,v=−ell,s=0用sample_projection_linear精确得到sampleProjection=−ell*M，再从H.1得完整weight对同nu真正Integrable。无小球扩大全参数、无EX/EY门、无用不可积Bochner积分0制造上界，先可积后restrict。

### 4.3 正normalizer、有限正密度与真积分（79–96）

hrho（79–85）只对t∈T建立密度事实：先从hT得Z_t>0，再由private sample_energy_mgf得F_t真Integrable及∫F_t=Z_t^n。hf.div_const给rho真Integrable；integral_div与实际hint改写后，pow_ne_zero n hZ.ne'使div_self合法，得到∫rho_t=1。不是先写formal normalizer公式再假定积分存在，也没有log0/top.toReal。

hrho0（86–87）由exp非负与正Z的n次幂非负给rho_t≥0，只要求t∈T；不对T外可能总化的rho擅作正质量断言。hS（88）以每项Integrable消费真实integrable_finsetSum；hS0（89–90）是逐点有限非负和。hSint（91–96）先用每项真可积满足integral_finsetSum，再用显式Finset.sum_congr将每项真实积分改为1，有限常数和给cardT。未把逐样本t视为一个固定密度；没有遗漏有限和线性前提。

### 4.4 同n产品AE坐标与真事件可测（97–110）

hcoords对每个Fin n坐标用Measure.tendsto_eval_ae_ae.eventually henergy，再ae_all_iff组合成nu-AE全坐标能量门。Fin n有限/可数，真实mu是概率故产品的标准有限/SigmaFinite条件满足；没有把AE原子界改成所有路径界。

hM展开真实normalDeviation/normalValue，用连续有限和给真实路径M连续；hE由已接受sourceTail_measurable和闭不等式的measurableSet_le相交，保留sourceTail中的正energy/sqrt阈值。hlarge在比较之前由S真Integrable常数倍得到。110行同时使用ae_restrict_of_ae hcoords及ae_restrict_mem hE，因此只对受限测度下AE真正成员/好坐标消费几何，而非对任意坏路径。

### 4.5 样本几何、符号与有限和majorant（111–141）

111消费B实际sourceTail_far_energy_mem，假设逐一为q,H,delta>0、n>0、实际坐标henergy、真实tail成员、真实M上界，给R∈Kfar。112只对该R从固定T选择t。113另取sourceTail_normalDeviation_energy_lower：M≥−Nq(R−1)²。

114–117重证公开定义下NqR²=Eenergy：Eenergy=Σz_i²≥0且Nq>0，所以Real.sq_sqrt的被开方量非负；正N/q允许清分母。不调用B不可见private energy_ratio_sq。118–121以该真等式推N*t(qR²−q)=t(Eenergy−Nq)，不假定E、t或R−1非零。

122以严格正N乘C的严格gap；123以ell≥0乘几何下界，方向正确。把两式相加移项得124–129的

  −ell*M ≤ −c*N + t(Eenergy−Nq) − N log Z_t.

这是恰能补偿负M增长权重的符号。使用弱≤舍弃严格性合法；未反转ell乘法，且不除ell/k/R−1。原htestN所有系数是同n、同q、同c。

130–135再次先得Z_t>0，再用实际Real.exp_nat_mul及exp_log得exp(Nlog Z_t)=Z_t^n，exp_sub给能量对数表达的exp恰等于实际rho_t商。137–139由exp单调和exp_add得w≤exp(−cN)*rho_t；140的Finset.single_le_sum要求其他所有u∈T的rho_u非负，hrho0已提供。141乘exp(−cN)≥0，得到受限AE的w≤exp(−cN)*S。样本选择t只进入点态比较，随后被同一个有限S消去，真正积分前没有样本相关测度。

### 4.6 真受限积分比较及全n结论（142–155）

返回hw后，将冻结event积分改写为nu.restrict Eevent。147直接用实际integral_mono_ae而不是仅形式setIntegral：hw.integrableOn及hlarge.integrableOn分别满足两函数对同受限测度的真实Integrable，hbound正是该限制测度的AE比较。149–150的setIntegral_le_integral要求majorant全空间Integrable和AE非负，hlarge及exp_nonneg*hS0均先于调用成立。

151–152最后才以integral_const_mul和hSint算全空间积分exp(−cN)*cardT。153–155只乘exp(−cN)≥0，把cardT改大为cardT+1；无需除exp、无complex cancellation，所得C/c正并在全部n外。所有线性/比较均有真正可积门，不以积分总化替代。

### 4.7 所有边界、范围与继承来源

空T：没有Nonempty提取，cardT+1=1仍正；若受限AE好样本存在，hcover会给t∈∅的矛盾，因此同一hbound合法，空有限和和真实积分=0照常。空far集合/零event质量也不需假定不存在路径。ell=0允许，Z测试t=0或负数允许；energy端点/任意正delta均未被排除。n=0只在public结论被hn排除，辅助恒等和产品MGF仍真n0；Nq、sqrt等清分母始终在hnR/hq后。结论对所有n≥1，没有隐藏eventual阈值。

没有使用真正均值EX=q/4/EY=q、S/det正、原子单点质量或stage/J；因此也未虚称这些在无门时成立。此一般mu界可用于满足额外门的实际来源族，但不会自动完成固定p/q/eps的全局构造、全joint外区/概率层求和、generalKL/全LLT/hW/根闭合。

## 5. 实际固定库API审查（在TYPE/receipt之前）

已通过指定服务器静态只读核实际Mathlib源码：Bochner/Basic:662–667 integral_mono_ae必须两侧真实Integrable；Set:738–740 setIntegral_le_integral必须全空间Integrable及AE非负，源码147与149的前提确实不同且均满足。integral_div（295–297）是实/复RCLike总化积分公式，但D在调用前有hf真可积、相消时有Z_t^n≠0，未滥用总化。

Bochner/Basic:248–251的实际名为integral_finsetSum（不是integral_finset_sum），源码93确用其真Integrable参数；L1Space/Integrable:443–445 integrable_finsetSum由每项真可积给有限和，1086–1087 Integrable.div_const、1028–1030 Integrable.const_mul给实际商/倍函数可积，integrableOn/restrict是以restrict_le_self保持真实可积。

Constructions/Pi:425–426的Measure.tendsto_eval_ae_ae及OuterMeasure/AE:151–153的ae_all_iff给同产品坐标AE，Measure/Restrict:642–643的ae_restrict_mem要求真实MeasurableSet。源码均精确消费。实际Real.exp_nat_mul在Analysis/Complex/Exponential:234–235，exp_log在Log/Basic:59–61需正实Z；Sqrt:177的sq_sqrt需被开方量非负。源码相应hZ、hnq、energy_nonneg先建立，不调用负参数下错误exp_log或sqrt平方消去。

此时完整proof/source阶段未发现数学缺口；下面先读所有实际DECL/TYPE及长续行，随后才读取作者receipt/build/Audit机械结论与hash/pins。

## 6. 全部实际DECL/TYPE独立审查（机械绿灯之前）

从指定服务器现有Audit.log只提取DECL/TYPE及完整续行，未先读AXIOMS/PASS/receipt。实测11个DECL/11个完整TYPE，全部是theorem：1public+2authored private+8generated；无新definition/axiom，也没有只检查1个目标。以下按actual输出顺序逐项核，不按命名猜测遗漏项。

1. `Shao.OQ3.exists_source_far_weighted_tail_bound._simp_1_3`：
```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3], (3 = 0) = False
```
有显式NeZero 3前提，非零常数3的等式命题归False；不是给任意OfNat无条件断言3≠0。

2. `Shao.OQ3.exists_source_far_weighted_tail_bound._simp_1_5`：
```lean
∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀] [NoZeroDivisors M₀] {a b : M₀},
  a ≠ 0 → b ≠ 0 → (a * b = 0) = False
```
真实NoZeroDivisors及两因子非零给乘积非零，吻合field_simp清分母义务；未默消Nq=0。

3. `Shao.OQ3.exists_source_far_weighted_tail_bound._simp_1_6`：
```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ),
  a ≠ 0 → (a ^ n = 0) = False
```
保留IsReduced和a非零，排除非零幂零元；n0也由非零门有效，不是任意MonoidWithZero都无条件非零。

4. `Shao.OQ3.exists_source_far_weighted_tail_bound`：actual完整TYPE如下，与第1节actual公开source type全部假设、实产品、Integrable/受限事件积分、C/c及n量词一致：
```lean
∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (q H ell delta : ℝ),
      1 < q →
        q < 103 / 100 →
          50 < H →
            H < 51 →
              0 ≤ ell →
                ell * q < 7 / 200 →
                  0 < delta →
                    (∀ᵐ (x : ℝ) ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H) →
                      ∫ (x : ℝ), x ^ 2 ∂mu = q →
                        ∃ C c,
                          0 < C ∧
                            0 < c ∧
                              ∀ (n : ℕ),
                                0 < n →
                                  MeasureTheory.Integrable (fun z => Real.exp (-ell * Shao.OQ3.normalDeviation q z))
                                      (MeasureTheory.Measure.pi fun x => mu) ∧
                                    (∫ (z : Shao.Path n) in
                                        {z | z ∈ Shao.OQ3.sourceTail q n ∧ Shao.OQ3.normalDeviation q z ≤ -delta * ↑n},
                                        Real.exp
                                          (-ell * Shao.OQ3.normalDeviation q z) ∂MeasureTheory.Measure.pi fun x => mu) ≤
                                      C * Real.exp (-c * ↑n)
```
pretty-printer的pi索引类型由同一Shao.Path n被积函数确定为Fin n，没有额外隐含law或n-dependent mu。

5. `_private.Shao.OQ3.SourceFarWeightedTail.0.Shao.OQ3.sample_energy_mgf`：
```lean
∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu],
  (∀ᵐ (x : ℝ) ∂mu, |x| ≤ 4 + √10) →
    ∀ (q t : ℝ) (n : ℕ),
      MeasureTheory.Integrable (fun z => Real.exp (t * (Shao.energy z - ↑n * q)))
          (MeasureTheory.Measure.pi fun x => mu) ∧
        (∫ (z : Shao.Path n), Real.exp (t * (Shao.energy z - ↑n * q)) ∂MeasureTheory.Measure.pi fun x => mu) =
          (∫ (x : ℝ), Real.exp (t * (x ^ 2 - q)) ∂mu) ^ n
```
明确是同mu真实产品Integral+Integrable，不消费q是均值、t正或n正；与实际H实例化一致。

6. `_private.Shao.OQ3.SourceFarWeightedTail.0.Shao.OQ3.sample_projection_linear._simp_1_3`：
```lean
∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonAssocSemiring R]
  (s : Finset ι) (f : ι → R) (a : R),
  ∑ i ∈ s, a * f i = a * ∑ i ∈ s, f i
```
这是真实有限和左乘分配，NonUnitalNonAssocSemiring已有分配律；不需要交换/结合/单位或任何概率，可包括空s。

7. `Shao.OQ3.exists_source_far_weighted_tail_bound._simp_1_8`：
```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ), (↑n + 1 = 0) = False
```
CharZero下n+1自然数cast非零，n为自然数；没有把任意实n+1无条件视为非零。

8. `Shao.OQ3.exists_source_far_weighted_tail_bound._simp_1_2`：
```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2], (2 = 0) = False
```
显式NeZero 2，常数归False的标准非零helper。

9. `Shao.OQ3.exists_source_far_weighted_tail_bound._simp_1_7`：
```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ),
  a ≠ 0 → (a ^ n = 0) = False
```
GroupWithZero的非零基底整数幂非零，负n的逆数门由a≠0保留，不是假设逆0非零。

10. `_private.Shao.OQ3.SourceFarWeightedTail.0.Shao.OQ3.sample_projection_linear`：
```lean
∀ (q a v s : ℝ) (n : ℕ) (z : Shao.Path n),
  Shao.OQ3.centeredSampleProjection q a v s n z =
    v * Shao.OQ3.normalDeviation q z + s * (∑ i, z i - ↑n * a)
```
完整type的括号是真正sum减Na，真实任意a线性展开；与private证明/样本定义一致，无tangent中心偷换。

11. `Shao.OQ3.exists_source_far_weighted_tail_bound._simp_1_4`：
```lean
∀ {α : Type u_2} [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4], (4 = 0) = False
```
显式NeZero 4，合法常数非零归False。

actual枚举确为公开stem生成7项（_simp_1_2到_8）及private有限和生成1项；并不存在本票漏读的_simp_1_1。全部actual类型均已核数学前提及与source消费对应，尚未用作者axiom gate充当语义判断。下一节最后才读取机械证据。

## 7. 最后读取并独立核实的机械证据

作者receipt现在才全文读取；它是机械记录，不作为第4–6节数学正确性的前提。本轮没有Lean/#check/probe/build/rebuild。指定remote run=/root/rivermind-data/shao-lean-20261021/runs/oq3/u17d-20261021，worktree=/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3。

| 冻结文件/现有产物 | 本轮实际SHA256 | 大小/行数 |
| --- | --- | --- |
| localdraft、remote worktree及run快照SourceFarWeightedTail.lean | c9e4c14af297353c5358da6d3e75d72f712649e535102ba18297fc00a0e5261f | 8175bytes/158lines，各相同 |
| local fiftieth-unit-scope.md / remote scope.md | bd0850af6664a6be85c5fc9bac90695889afdddc3426e9b8e42f08775023606f | 5321bytes/35lines，各相同 |
| local u17d-statement-review.md / remote statement-review.md | 5a1e087d192602a7afe0fb5e2b804eec0b7e0283bc4ed4c3aa589862a780836f | 19072bytes/162lines，各相同 |
| local U17d-receipt.json / remote receipt.json | ca39802ccbe7720a947b55cebf221d8d379fd69e978c090d0c99b69f39b6e19a | 6339bytes/82lines，各相同 |
| local U17d-Audit.lean / remote Audit.lean | a2cfe9921eaf0d54900c120c6d9475c325c7542464262d1f89d2d36f0c76bab1 | 1621bytes/38lines，各相同 |
| remote Audit.log | 7a0c14e804ac88f0e22b8bfa69bd0ada0af15950f58b1310f3640655a501b672 | 4018bytes/69lines |
| remote build-02.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 | 实际0bytes/0lines |
| local u17d-prerequisite-hashes.json / remote prerequisite-hashes.json | 522ba4ca25a441e3d5c9f44192df8b5afa3ad807ff5a604342acbe4ef5521b0c | 2410bytes/25lines，各相同 |
| actual只读R1 report.md | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 | 19420bytes/575lines |

actual公开type与scope完整fence做LF逐字比较相同（比作者收据WHITESPACE_NORMALIZED更直接）；三imports与scope所列完全相同。实际源原始bytes无CR、末尾LF、无尾空白；实际源码扫描无sorry/admit/axiom/unsafe/native_decide/implemented_by。没有新增公开定义，2private均为theorem，TYPE已完整核11项。

作者收据记录成功命令为`taskset -c 14-17 lake env lean -M8192 -j4 -DautoImplicit=false -o .lake/build/lib/lean/Shao/OQ3/SourceFarWeightedTail.olean Shao/OQ3/SourceFarWeightedTail.lean`，exit_code=0；Audit同CPU/原生内存线程/strict autoImplicit参数，exit_code=0。本轮真实读取现有空build-02和Audit输出/hash，目标现成.olean确实存在；空log本身不编码退出码，退出码来自冻结作者机械记录，本轮未声称重新执行得到0。build01修复历史未当成功最终凭据，也未重跑。

Audit.lean实际源码已全文读38行：defs=[]、目标唯一public；遍历env.constants，对目标stem和整个_private.Shao.OQ3.SourceFarWeightedTail前缀逐项排新axiom并Lean.collectAxioms检查传递依赖，不只是#print axioms一个目标；实际11个owned均已在第6节逐项读完整TYPE。最后真实log摘要是U17D_FROZEN_THEOREMS 1、U17D_ALL_THEOREMS 11、U17D_ALL_DECLARATIONS 11、U17D_AXIOM_GATE PASS，与独立枚举一致。

实际每项AXIOMS也最后核读：public主定理、sample_energy_mgf、sample_projection_linear及_simp_1_7均为[propext, Classical.choice, Quot.sound]；private有限和生成项为[propext, Quot.sound]；其余_simp_1_2/_3/_4/_5/_6/_8为[propext]。全部在标准三公理白名单内，没有新project axiom或遗漏private/generated。作者门因此确实与此冻结源码/目标覆盖相符，但完整独立CORRECT依据仍是上述实际proof/source/TYPE审查。

receipt当前标签均为U17d；“final independent proof review pending”“No U17d commit/PR/merge”明示at author-check time，与当时pending/未提交事实吻合，不把它当本轮final之后仍pending的实时状态；未发现复制上一单元标签的元数据错误。root_status四项OPEN且nonclaims只称本远负normal加权积分，没有声称整个joint外区/全17/19或KL等，范围正确。

## 8. 实际23项目前置、库与pins（机械最后）

从actual D source递归读取真实Shao imports，自行枚举23项，不含D自身；与receipt.imported_project_sources_sha256及独立prerequisite-hashes.json的完整字典逐字/逐hash相同，无缺项/多项/冲突。所有23前置现成.olean均存在，未构建或下载。具体实测如下：

| 实际前置源码（相对worktree） | 实测SHA256 |
| --- | --- |
| Shao/Basic/FinitePath.lean | 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb |
| Shao/OQ3/AtomProjection.lean | 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22 |
| Shao/OQ3/AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| Shao/OQ3/BinaryEntropyBounds.lean | 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228 |
| Shao/OQ3/CenteredLogMGF.lean | 1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4 |
| Shao/OQ3/CenteredSampleTilt.lean | d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501 |
| Shao/OQ3/EnergyBernoulliMGF.lean | e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad |
| Shao/OQ3/FarEnergyExponentialCover.lean | 40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d |
| Shao/OQ3/FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| Shao/OQ3/FiniteNormalSpan.lean | 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de |
| Shao/OQ3/FiniteStageMeasure.lean | 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1 |
| Shao/OQ3/InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| Shao/OQ3/NormalTangentGaussian.lean | d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39 |
| Shao/OQ3/NormalTangentMoments.lean | 8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1 |
| Shao/OQ3/PositiveRate.lean | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |
| Shao/OQ3/RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| Shao/OQ3/ResonanceArithmetic.lean | cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b |
| Shao/OQ3/SampleBoundary.lean | 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2 |
| Shao/OQ3/SourceBinaryEntropyGap.lean | f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9 |
| Shao/OQ3/SourceEnergyGeometry.lean | 3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a |
| Shao/OQ3/SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| Shao/OQ3/SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| Shao/Probability/FiniteIID.lean | d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b |

这些固定源与此前已完整独立接受的C/H数学语义绑定一致；C提供真实finite test/Zpositive/共同gap，H提供任意实参数的真样本可积及product normalizer，B提供确定性几何与实际R定义；不把无关I/J或root新公共模块混入此闭包，也不重复编译旧成功目标。

本轮静态读到的关键固定库source hash/现成olean如下（全部olean存在）：

| Mathlib源码（省略Mathlib/） | 实测SHA256 |
| --- | --- |
| MeasureTheory/Integral/Bochner/Basic.lean | 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670 |
| MeasureTheory/Integral/Bochner/Set.lean | e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75 |
| MeasureTheory/Function/L1Space/Integrable.lean | d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759 |
| MeasureTheory/Constructions/Pi.lean | bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef |
| MeasureTheory/OuterMeasure/AE.lean | beef84262be5013115b47a93698fb7b1960931dd766dcb6cb8867fe305f22f48 |
| MeasureTheory/Measure/Restrict.lean | a7d15027178c6efab4f942a014c85e298942e9624dbff268e0b13714b0cdc5e6 |
| Analysis/Complex/Exponential.lean | 35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146 |
| Analysis/SpecialFunctions/Log/Basic.lean | 0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97 |
| Analysis/Real/Sqrt.lean | 1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204 |

三实际imports与声明门完全相同；前置及固定库未变，所以已静态核实的公开import路径与类型实例仍成立。实际Shao.Path n是Fin n→ℝ，nu显式mu产品，不依赖未指定的默认volume或matrix norm。工具链实际文本leanprover/lean4:v4.36.0-rc1，lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4（29bytes），lake-manifest.json SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e（3541bytes），Mathlib实际HEAD807d3836b165983210ee2ecf3cd28f239436949c。

机械检查时branch feat/oq3-source-far-weighted-tail，HEAD551f457b67ca485d0044254f5d265e49a656b82f，status仅?? Shao/OQ3/SourceFarWeightedTail.lean，符合冻结作者检查阶段；未commit/PR或把D提前算入root整合数。其他旧PR integrated/关闭与否不影响本冻结源数学绑定。未读run中api-publish.py/receipt.py或作者candidate/future/实施notes。

本轮仅写owned local/remote报告，静态只读现有源和选择性TYPE/机械输出；未下载raw完整日志、未Lean/probe/build/rebuild/spawn/cachewrite/sourceedit或kill任务，未动CPU0–9外部任务/全局资源，也未使用ulimit-v。既有作者命令遵循CPU14–17、oneheavy及Lean原生-M8192-j4，审查本身不占heavy。

## 9. 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: actual唯一公开完整type与冻结scope一致；全158行实现、2authored private、全部8generated及11实际完整TYPE均已按独立顺序审完。真实任意参数H接口先给原weight和能量测试exp可积；正Z下rho商的全积分恰1；同nu产品AE坐标及可测restricted event支持B实际正平方根几何。共同finite-cover严格gap在N>0/ell≥0门后以正确符号控制负层增长权重，再以固定有限正密度和支配，所有真可积/受限AE/有限和线性/全空间非负积分比较门明确满足，C=cardT+1和c在全部n>0外。空T/空事件/ell0/端点与n0排除均正确。最后机械证据、23前置、pins/hash和全传递三公理白名单与实际证明绑定一致，未发现数学/声明/source/API/TYPE或机械阻塞。

此为U17d的完整独立CORRECT，支持其“sourceTail且远负法向M≤−delta*n”的真实加权积分充分producer。它不是一般KL/RN/DPI/Legendre/globalminimizer或完整joint外区、全17/19、LLT/conditional Levy、hW；全部根A/B/C/D仍OPEN。最终票交付后由lead全文读取再决定commit/pub，本审查未执行发布。
