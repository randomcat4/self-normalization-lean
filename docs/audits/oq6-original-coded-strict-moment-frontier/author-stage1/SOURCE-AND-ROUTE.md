# 来源、单一 witness 路线和精确接口

STATUS: STAGE1 DESIGN ONLY. 数学路线已给出；未实现、未 elaboration、未运行 Lean、未冻结。

主候选选择直接226路线。已完整读取p51的355LF、exact226公开声明16–384、exact228完整源文件及其冻结/独立来源 intake、229完整源及201LF实际公开TYPE、230完整源及391LF全部实际TYPE。旧合格producer的完整独审/机器证据按精确字节复用；本件不重新审旧证明、不重跑旧检查。当前选中定理不使用228的weighted证明或其sourceCost极限。未选的较强设计在CANDIDATE-via228-NOT-SELECTED.md保留，明确依赖未qualified228。

## 题意与占位范围

p51是UNCERTIFIED_REPAIR_CANDIDATE；原源外部概率引擎及相关陈述归Shao–Zhou。本单元是对来源S19、S20–S25与S4最后截断预算段的机械化接口设计，不宣称数学新颖性。没有联网或新增文献状态断言，没有把原源的外部依赖说成从零证明。

| 原源位置 | 本候选位置 | 精确含义与界限 |
|---|---|---|
| S19 | P18/P20及cWindow | 原μ的p阶矩推出原P的L0上界；cWindow^p=min(1/2,cBudget)/2，z≥1窗口给两个严格原始余量。cBudget任意正，未识别为cSZ。 |
| S20 | ε/Y/a/s/η及P06–P09 | 规范εk=1/(8√n(k+1))，均值和尺度由实际积分定义；同一个226 m0，ν与q均不随k变化。 |
| S21 | P07/P08与generic解析接口 | 使用真实L2/均值0/总能量1和全样本ε误差；未假设原g无原子。 |
| S22/S23 | Qε/Dη/P10 | signed阈值恒等式逐样本成立，真实D1和剪裁D2保持参数1。没有CDF或概率闭尾结论。 |
| S24/S25 | H/Hdelete/M/Mdelete/Anew/AdeleteNew，P10–P14/P20 | 真实完整/删除包络、可测标量因子化及Qε的L1小量；删除量不含被删坐标，所有系数仍用原n。 |
| S4末段F连续预算 | Fz与P05/P16–P20 | Fz(t)=(zt)^2min(abs(zt),1)，原P/P0/ν积分精确运输，同η的δ/L极限保留严格预算。未以1+z替换。 |

## 推荐路线：一次226，原μ上230，同序列229

1. 在原mΩ上，以现有actual_quadratic_source_moments的n=3、x=0实例提取`Measurable[mΩ,borel ℝ] g`及`MemLp g 2 μ`。这是已存在的确定性原投影事实接口；不调用新的存在性模型。n=3/x=0仅用于提取这两个原μ事实，不把该n替代主目标n。原始hgp、β始终使用原μ。
2. 原mΩ还在作用域时，把230显式实例化为`@...actual_iid_source_z_strict_moment_budgets Ω mΩ μ <original probability instance> g hg hg2 p hp2 hp3 hgp cBudget hcBudget`。得到cWindow、原μ下标量预算及所有n,z的原P产品预算；这一步没有μ0或ν的p阶矩输入。
3. 只调用一次qualified226的`actual_original_literal_remainder_envelope μ h hh hh2 hhsymm hcenter hprojectionsecond`，取m0/hm0/hcg。以后只用该返回包的forall部分，绝不再次调用221/224/226或228来“挑一个相同模型”。先证规范ε的正、小及趋零，用明确ε0实例取固定法则；每个εk的normalization/factorization取同一forall包当前实例。K=4√n不随k。
4. 226公开给出原约化gcoord的可测性、坐标测度保持和均值0；后缀给出增广ξ的可测性/L2/能量。原ξ0均值与q律给增广ξ均值0。Ylocal的可测性及全样本ε误差由qualified scalar-code+quantized_observation_spec实际接口取得，输入ξlocal的可测性由gcoord可测性复合fst取得。不存在caller Y可测性回调。
5. 每个εk的226当前包直接给P09、signed恒等式和完整/删除因子化P12/P13/P14。P10的Q/包络界、P11的真实可积性及积分界用独立已有`actual_normalized_remainder_envelope_spec`，不消费228任何proof。其ρ=4εk√n与Kεk环等式一致；由非负积分和εk→0夹逼得Qε-L1→0。A/B/D1/D2的可测性、可积性、非负/绝对控制全在226实际公开包，不加假设。
6. generic `actual_projection_tilt_and_truncated_cost_limits`在增广空间显式mAug、参数x=z、当前规范ξ/Y/ε上给Fz真实可积性、逐坐标δη→δν和Lη→Lν。它只要求2阶矩，不要求p阶矩。
7. 精确运输不是caller callback。令zeroSection ζ i=(ζi,0)，用下面的固定pi/prod可测API证明mN0→mAug可测。ξi∘zeroSection=ξ0i逐点定义相等，故从增广ξi可测得到P05；这也直接核实激活指出的228公开接口薄弱处可被现有固定API消除。该截面不要求Ω中默认值、不要求0属于U支持、不声称它保持测度。
8. 用hm0构造原到约化的id可测（measurable_id''及measurable_pi_iff），结合226的P0=map id P构造MeasurePreserving id P P0。对每个具体`fun ζ => Fz(ξ0 i ζ)`，沿q与id分别用下面完整`integral_map_of_stronglyMeasurable`/`integral_map`，得δνi=∫P0 Fzξ0=δ0i。可积性先由generic增广结果、q.integrable_comp向P0返回，再由id.integrable_comp_of_integrable向原P返回。无未导出的g-m0假设，无任意f的caller hIntEq参数。
9. 230的δ/L与这里δ0/L0通过`Shao.truncationF (z*t)=Fz t`的定义等式匹配，P的measurable space显式固定mΩ。由此取得P18/P20的原始严格余量；再运输到δν/Lν，用229同一ξ/Y/ε/ν实例取得严格矩预算尾段。P19无条件极限来自第6步，不依赖窗口成立。
10. 任给τ>0，把229的有限坐标/总预算尾段与Q-L1→0的尾段相交，提取一个k0。P09/P10/P12/P13/P14对所有k原本成立，故同一k≥k0保留独立中心化/总方差1、非零分母、signed恒等式以及完整/删除标量可测因子化。没有跨n,z的统一k0，也不新增显式原始余量假设。

## Derived proof-local Prop interfaces

以下均是现有输入/包的推论，非caller假设。新增proof-local普通数据为zeroSection，以及严格预算尾阈值kb、Q-L1尾阈值kq取出的tailIndex=max kb kq；其类型、RHS与witness作用域已列于清单。API返回的完整Prop类型在本件后半全文保留。

### hProjection

Scope: original mΩ before m0.

```lean
Measurable[mΩ, borel ℝ] g ∧ MemLp g 2 μ
```

### hn1

Scope: fixed n.

```lean
1 ≤ n
```

### hNpos

Scope: fixed n.

```lean
0 < Real.sqrt (n : ℝ)
```

### hK

Scope: fixed n.

```lean
0 ≤ K
```

### hEpsilon

Scope: fixed n, before all k.

```lean
(∀ k : ℕ, 0 < ε k ∧ ε k < 1 / (4 * Real.sqrt (n : ℝ))) ∧ Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ))
```

### hFixedLaw

Scope: same226 m0, fixed n; explicit epsilon0 packet.

```lean
@IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧ P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧ IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀
```

### hξ0mean

Scope: same226 current fixed n.

```lean
∀ i : Fin n, (∫ ζ, ξ0 i ζ ∂P₀) = 0
```

### hξmean

Scope: fixed augmented ν.

```lean
∀ i : Fin n, (∫ x, ξ i x ∂ν) = 0
```

### hξlocalMeas

Scope: fixed m0,n.

```lean
∀ i : Fin n, Measurable[mAugLocal, borel ℝ] (ξlocal i)
```

### hYspec

Scope: fixed same sequence.

```lean
∀ (k : ℕ) (i : Fin n), Measurable[mAugLocal, borel ℝ] (Ylocal k i) ∧ Measurable[mAug, borel ℝ] (Y k i) ∧ ∀ x : Fin n → Ω × ℝ, |Y k i x - ξ i x| ≤ ε k
```

### hCurrent

Scope: for each k, same226 forall packet at epsilon(k).

```lean
(∀ k : ℕ, (1 / 2 : ℝ) < s k ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η k i x = ηlocal k i (x i)) ∧
          iIndepFun (η k) ν ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (η k i) ∧ MemLp (η k i) 2 ν ∧
            (∫ x, η k i x ∂ν) = 0) ∧
          (∑ i : Fin n, ∫ x, (η k i x) ^ 2 ∂ν) = 1 ∧
          ν {x : Fin n → Ω × ℝ | Vη k x = 0} = 0 ∧
          (∀ᵐ x ∂ν, 0 < Vη k x ∧ 0 < b x ∧ 0 < Vη k x * b x)) ∧
(∀ (k : ℕ) (x : Fin n → Ω × ℝ), Wη k x + Dη k x - z * Vη k x * b x = W x + D1 (q x) - z * V x * b x) ∧
(∀ k : ℕ, ∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
          Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
          ∀ x : Fin n → Ω × ℝ, (M k x, Anew k x, B x) = Ffull (C k x)) ∧
(∀ (k : ℕ) (i : Fin n), ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
          Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
          ∀ x : Fin n → Ω × ℝ,
            (Mdelete k i x, AdeleteNew k i x, Bdelete i x) =
              Fdelete (fun j : {j : Fin n // j ≠ i} => η k j.val x)) ∧
(∀ k : ℕ, ∃ G1 G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          ∀ x : Fin n → Ω × ℝ, Dη k x = G1 (C k x) ∧ D2 (q x) = G2 (C k x))
```

### hEnvelopeInputs

Scope: fixed n,C0,z; same226.

```lean
Measurable[mAug,borel ℝ] (fun x => D1 (q x)) ∧ Measurable[mAug,borel ℝ] (fun x => D2 (q x)) ∧ Measurable[mAug,borel ℝ] A ∧ Measurable[mAug,borel ℝ] B ∧ (∀ x, 0 ≤ A x) ∧ (∀ x, 0 ≤ B x) ∧ (∀ x, |D1(q x)| ≤ A x) ∧ (∀ x, |D2(q x)| ≤ B x) ∧ Integrable[mAug] A ν ∧ Integrable[mAug] B ν
```

### hQDifference

Scope: fixed same sequence.

```lean
∀ (k : ℕ) (x : Fin n → Ω × ℝ), Dη k x - D1 (q x) = Qε k x
```

### hQIntegralBound

Scope: fixed n,C0,z; ∀k.

```lean
∀ k : ℕ, Integrable[mAug] (fun x => |Qε k x|) ν ∧ (∫ x, |Qε k x| ∂ν) ≤ K * ε k * (∫ x, H x ∂ν)
```

### hQlimit

Scope: fixed n,C0,z.

```lean
Filter.Tendsto (fun k => ∫ x, |Qε k x| ∂ν) Filter.atTop (nhds (0 : ℝ))
```

### hZeroSection

Scope: same m0,n, independent of law support.

```lean
Measurable[mN₀,mAug] zeroSection
```

### hSectionIdentity

Scope: same m0,n.

```lean
∀ (i : Fin n) (ζ : Fin n → Ω), ξ i (zeroSection ζ) = ξ0 i ζ
```

### hξ0m

Scope: same m0,n.

```lean
∀ i : Fin n, Measurable[mN₀,borel ℝ] (ξ0 i)
```

### hidN

Scope: original product to reduced product.

```lean
Measurable[mN,mN₀] (id : (Fin n → Ω) → (Fin n → Ω))
```

### hId

Scope: original product to reduced product.

```lean
@MeasurePreserving (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀
```

### hF0m

Scope: same m0,n,z.

```lean
∀ i : Fin n, Measurable[mN₀,borel ℝ] (fun ζ => Fz (ξ0 i ζ))
```

### hFzTransport

Scope: same m0,n,z.

```lean
∀ i : Fin n, (∫ x, Fz (ξ i x) ∂ν) = (∫ ζ, Fz (ξ0 i ζ) ∂P₀) ∧ (∫ ζ, Fz (ξ0 i ζ) ∂P₀) = (∫ ζ, Fz (ξ0 i ζ) ∂P)
```

### hFzIntTransport

Scope: same m0,n,z.

```lean
∀ i : Fin n, Integrable[mN₀] (fun ζ => Fz (ξ0 i ζ)) P₀ ∧ Integrable[mN] (fun ζ => Fz (ξ0 i ζ)) P
```

### hOriginalStrict

Scope: only under exact original230 window.

```lean
(∀ i : Fin n, δ0 i < (1/2 : ℝ)) ∧ L0 < cBudget * z ^ 2
```

### hAugmentedStrict

Scope: same window after exact source transport.

```lean
(∀ i : Fin n, δν i < (1/2 : ℝ)) ∧ Lν < cBudget * z ^ 2
```

### hMomentTail

Scope: same229 instantiated ξ/Y/ε/ν.

```lean
∃ kb : ℕ, ∀ k : ℕ, kb ≤ k → (∀ i : Fin n, δη k i < (1/2 : ℝ)) ∧ Lη k < cBudget * z ^ 2
```

### hQTolerance

Scope: fixed τ>0.

```lean
∀ᶠ k : ℕ in Filter.atTop, (∫ x, |Qε k x| ∂ν) < τ
```

## p阶矩与没有隐藏接口的核对

唯一p阶矩假设hgp在原μ上，β也在原μ上。230使用原μ，generic229/解析极限只用226已给出的增广L2，故主路线根本没有“必须先假定约化/增广p阶矩”的步骤。P16/P18仍逐项导出真正Fz可积性，Bochner未定义积分的默认0不能充当成本证据。

若后续消费者实际需要归一化p阶函数在P0/ν上的可积性，具体可用原hgp缩放、原产品eval测度保持得到P上的可积性；`fun ζ => Real.rpow |ξ0 i ζ| p`由P05与连续rpow(abs,p)给mN0可测；hId.integrable_comp返回P0可积性，hq.integrable_comp_of_integrable给ν可积性。这个可导出的接口不需要新caller premise，但主候选没有额外许诺η的p阶矩，也不使用它。

## 已验证的228比较与精确剩余范围

原激活指出的228未显式公开g-m0或hIntEq问题，是“公开形式较薄”，不是反例：公开增广ξ可测 + 固定可测zeroSection足以恢复目标ξ0可测；P0 map-law/q律足以运输具体Fz。主候选直接226甚至还有gcoord可测性可用，因此没有最小数学接口缺失要偷偷补成callback。226抽取同一m0后，对规范εk逐项调用其forall接口是同一witness；不能对228和226两次独立存在性应用声称m0相等。

未选较强版本加入sourceCostη→sourceCost0并共用τ尾段。这个极限属于228/227实际weighted消费者内容，因此它确实依赖exact228资格；不能由226的无权L1包络或本主候选直接升级。主候选删除该整块和14个相应数据let，保留文件作为可审查设计比较；没有重写/绕过228证明。

形式层尚未运行，可能仍需常规的显式instance/definitional-equality整理；不能把这里的手工接口核对称为Lean通过。没有已知需要新数学假设的阻塞。所有新代码实现、声明冻结、服务器native/AX与独立完整最终review仍由lead依相应阶段执行。OQ56与原root范围均未闭合。

## 完整实际必需API声明

下列从绑定的现有精确源字节提取，仅声明，不含证明体；有别于候选中的新定理。API返回的普通let/RHS和所有Prop/回调由完整段落逐字界定，不能用缩略说明默增参数。旧producer证明没有重审。

### One common original model 226

Path: C:\game\shao lean\library\Shao\OQ6\OriginalLiteralRemainderEnvelope.lean

```lean
theorem actual_original_literal_remainder_envelope
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun t : Ω × Ω => h t.1 t.2))
    (hh2 : MemLp (fun t : Ω × Ω => h t.1 t.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ t : Ω × Ω, h t.1 t.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1) :
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ :=
      ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
        (hcg : @MeasurableSpace.CountablyGenerated Ω m₀),
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      IsProbabilityMeasure μ₀ ∧
      ∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
          (z : ℝ) (hz : 0 ≤ z) (K : ℝ) (hK : 0 ≤ K),
        let mFixedLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mFixed : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mFixedLocal)
        let νFixedLocal : Fin n → @Measure (Ω × ℝ) mFixedLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀
            ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))
        let νFixed : @Measure (Fin n → Ω × ℝ) mFixed :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mFixedLocal) νFixedLocal
        let ξFixed : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun (i : Fin n) (x : Fin n → Ω × ℝ) => g (x i).1 / Real.sqrt (n : ℝ)
        let VFixed : (Fin n → Ω × ℝ) → ℝ :=
          fun x : Fin n → Ω × ℝ => Real.sqrt (∑ j : Fin n, (ξFixed j x) ^ 2)
        let VdeleteFixed : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
            Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξFixed j x) ^ 2)
        let BFixed : (Fin n → Ω × ℝ) → ℝ :=
          fun x : Fin n → Ω × ℝ => studentizerClipBudget n r C0 rho 1 (fun j : Fin n => (x j).1)
        let BdeleteFixed : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
            studentizerClipBudgetDeleted n r C0 rho 1 (fun j : Fin n => (x j).1) i
        let HFixed : (Fin n → Ω × ℝ) → ℝ :=
          fun x : Fin n → Ω × ℝ =>
            (1 + VFixed x) * (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + BFixed x))
        let HdeleteFixed : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
            (1 + VdeleteFixed i x) *
              (Real.sqrt (n : ℝ) + z * Real.sqrt (1 + BdeleteFixed i x))
        let payment : Fin n → ℝ :=
          fun i : Fin n => K *
            ((∫ x, HFixed x ∂νFixed) + (∫ x, HdeleteFixed i x ∂νFixed))
        let paymentTotal : ℝ := ∑ i : Fin n, payment i
        ∀ (ε : ℝ) (hε : 0 < ε)
            (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))),
          let mN : MeasurableSpace (Fin n → Ω) :=
            @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
          let mN₀ : MeasurableSpace (Fin n → Ω) :=
            @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
          let P : @Measure (Fin n → Ω) mN :=
            @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
              (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
          let P₀ : @Measure (Fin n → Ω) mN₀ :=
            @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
              (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
          let N : ℝ := Real.sqrt (n : ℝ)
          let O : Fin n → (Fin n → Ω) → Ω := fun i ξ => ξ i
          let gcoord : Fin n → Ω → ℝ := fun _ o => g o / N
          let Q : (Fin n → Ω) → (Fin n → Ω) := fun ξ i => O i ξ
          let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
          let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r C0 rho 1
          let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r C0 rho 1
          let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
          let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
          let B1del : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r C0 rho 1
          let κ : (Fin n → Ω) → ℝ := fun _ => 0
          let W0 : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
          let V0 : (Fin n → Ω) → ℝ :=
            fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
          let T0 : (Fin n → Ω) → ℝ := fun ξ =>
            if V0 ξ = 0 then κ ξ else
              (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
          let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
          let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
          let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
            @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
              (fun _ : Fin n => mAugLocal)
          let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
            fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
          let ν : @Measure (Fin n → Ω × ℝ) mAug :=
            @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
              (inferInstance : Fintype (Fin n))
              (fun _ : Fin n => mAugLocal) νlocal
          let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
          let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
            Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
              (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
          let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => gcoord i t.1
          let Ylocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
            Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
          let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => gcoord i (x i).1
          let Y : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => Ylocal i (x i)
          let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
          let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
          let ηlocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
            Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
          let η : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
          let C : (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun x i => η i x
          let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
          let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
          let Wη : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, η i x
          let Vη : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
          let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
          let Dη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
            fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
          let Tη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
            fun z x => (Wη x + Dη z x) / (Vη x * b x)
          let Z0 : Set (Fin n → Ω) := {ξ | projectionV n g ξ = 0}
          let Z : Set (Fin n → Ω × ℝ) := {x | V x = 0}
          let p0 : ℝ := P.real Z0
          let comparisons : Set (ℝ → ℝ → Prop) :=
            {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
              R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
              R = (fun a b : ℝ => a = b)}
          let F0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) := fun R z =>
            {ξ | R (projectionW n g ξ + D1 ξ)
              (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
          let A0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) :=
            fun R z => {ξ | R (Tclip ξ) z}
          let Eη : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ) :=
            fun R z => {x | R (Tη z x) z}
          let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
          let A : (Fin n → Ω) → ℝ := fun ξ : Fin n → Ω => |D1 ξ|
          let Adel : (Fin n → Ω) → Fin n → ℝ :=
            fun (ξ : Fin n → Ω) (i : Fin n) => |Ddel ξ i|
          let B1 : (Fin n → Ω) → ℝ := studentizerClipBudget n r C0 rho 1
          let deletionMass : (Fin n → Ω) → Fin n → ℝ :=
            fun (ξ : Fin n → Ω) (i : Fin n) =>
              |A ξ - Adel ξ i| + |B1 ξ - B1del ξ i|
          let deletionTotal : (Fin n → Ω) → ℝ :=
            fun ξ : Fin n → Ω => ∑ i : Fin n, deletionMass ξ i
          @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
          P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
          (∀ i : Fin n, Measurable (O i) ∧ MeasurePreserving (O i) P₀ μ₀) ∧
          iIndepFun O P₀ ∧
          (∀ i : Fin n, Measurable (gcoord i) ∧
            MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ ∧
            (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 ∧
            (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ)) ∧
          (∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 ∧
          Q = id ∧ W0 = projectionW n g ∧ V0 = projectionV n g ∧ T0 = Tclip ∧
          Measurable D1 ∧ Measurable D2 ∧
          (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ) ∧
          Measurable[mN₀, borel ℝ] Tclip ∧ Measurable[mN, borel ℝ] Tclip ∧
          @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
            @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P ∧
          IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
          (1 / 2 : ℝ) < s ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i)) ∧
          iIndepFun η ν ∧
          (∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν) ∧
          (∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν) ∧
          (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
          (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
          (∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0) ∧
          ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0 ∧
          (∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x) ∧
          Measurable[mAug, borel (Fin n → ℝ)] C ∧
          MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug ∧
          (∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
            ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
              ∀ x : Fin n → Ω × ℝ, H x = F (C x)) ∧
          (∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
            ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
              Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
              (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
                d y = F (fun j => ηlocal j.val (y j))) ∧
              Measurable[borel (Fin n → ℝ), borel ℝ]
                (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
              ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x)) ∧
          (∃ G2 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
            (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
            ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
              Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
              ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x)) ∧
          (∀ i : Fin n,
            ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
              Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
              ∀ x : Fin n → Ω × ℝ,
                (Ddel (q x) i, Jdel (q x) i, B1del (q x) i) =
                  Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
          (∀ z : ℝ, Measurable (Dη z) ∧ Measurable (Tη z)) ∧
          MeasurableSet[mN₀] Z0 ∧ MeasurableSet[mN] Z0 ∧ MeasurableSet Z ∧
          ν Z = P₀ Z0 ∧ P₀ Z0 = P Z0 ∧ ν.real Z = p0 ∧
          (∀ (z : ℝ) (x : Fin n → Ω × ℝ),
            Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x) ∧
          (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
            MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN] (A0 R z) ∧
            MeasurableSet[mN₀] (F0 R z) ∧ MeasurableSet[mN] (F0 R z) ∧
            MeasurableSet (Eη R z) ∧
            ν (Eη R z) = P₀ (F0 R z) ∧ P₀ (F0 R z) = P (F0 R z) ∧
            (∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
            P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
            |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0) ∧
          (∀ ξ : Fin n → Ω, 0 ≤ A ξ ∧ 0 ≤ B1 ξ ∧ |D2 ξ| ≤ B1 ξ) ∧
          (∀ (i : Fin n) (ξ : Fin n → Ω), 0 ≤ Adel ξ i ∧ 0 ≤ B1del ξ i) ∧
          Measurable[mN₀, borel ℝ] J ∧
          Measurable[mN₀, borel ℝ] A ∧ Measurable[mN₀, borel ℝ] B1 ∧
          (∀ i : Fin n,
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Ddel ξ i) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Jdel ξ i) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => Adel ξ i) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => B1del ξ i)) ∧
          Integrable A P₀ ∧ Integrable B1 P₀ ∧ Integrable D2 P₀ ∧
          (∀ i : Fin n,
            Integrable (fun ξ : Fin n → Ω => Adel ξ i) P₀ ∧
            Integrable (fun ξ : Fin n → Ω => B1del ξ i) P₀ ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => |A ξ - Adel ξ i|) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => |B1 ξ - B1del ξ i|) ∧
            Measurable[mN₀, borel ℝ] (fun ξ : Fin n → Ω => deletionMass ξ i) ∧
            Integrable (fun ξ : Fin n → Ω => |A ξ - Adel ξ i|) P₀ ∧
            Integrable (fun ξ : Fin n → Ω => |B1 ξ - B1del ξ i|) P₀ ∧
            Integrable (fun ξ : Fin n → Ω => deletionMass ξ i) P₀) ∧
          Measurable[mN₀, borel ℝ] deletionTotal ∧ Integrable deletionTotal P₀ ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => A (q x)) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => B1 (q x)) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => D2 (q x)) ∧
          Integrable (fun x : Fin n → Ω × ℝ => A (q x)) ν ∧
          Integrable (fun x : Fin n → Ω × ℝ => B1 (q x)) ν ∧
          Integrable (fun x : Fin n → Ω × ℝ => D2 (q x)) ν ∧
          (∀ i : Fin n,
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Adel (q x) i) ∧
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => B1del (q x) i) ∧
            Integrable (fun x : Fin n → Ω × ℝ => Adel (q x) i) ν ∧
            Integrable (fun x : Fin n → Ω × ℝ => B1del (q x) i) ν ∧
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ∧
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |B1 (q x) - B1del (q x) i|) ∧
            Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ∧
            Integrable (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ν ∧
            Integrable (fun x : Fin n → Ω × ℝ => |B1 (q x) - B1del (q x) i|) ν ∧
            Integrable (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ν) ∧
          Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionTotal (q x)) ∧
          Integrable (fun x : Fin n → Ω × ℝ => deletionTotal (q x)) ν ∧
          let Afull : (Fin n → Ω × ℝ) → ℝ := fun x : Fin n → Ω × ℝ => A (q x)
          let Adelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) => Adel (q x) i
          let B : (Fin n → Ω × ℝ) → ℝ := fun x : Fin n → Ω × ℝ => B1 (q x)
          let Bdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) => B1del (q x) i
          let Vdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
              Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ j x) ^ 2)
          let Cbudget : (Fin n → Ω × ℝ) → ℝ :=
            fun x : Fin n → Ω × ℝ => Real.sqrt (1 + B x)
          let CbudgetDelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) => Real.sqrt (1 + Bdelete i x)
          let H : (Fin n → Ω × ℝ) → ℝ :=
            fun x : Fin n → Ω × ℝ => (1 + V x) * (Real.sqrt (n : ℝ) + z * Cbudget x)
          let Hdelete : Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (i : Fin n) (x : Fin n → Ω × ℝ) =>
              (1 + Vdelete i x) * (Real.sqrt (n : ℝ) + z * CbudgetDelete i x)
          let M : ℝ → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (x : Fin n → Ω × ℝ) => K * θ * H x
          let Mdelete : ℝ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ) => K * θ * Hdelete i x
          let Aenvelope : ℝ → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (x : Fin n → Ω × ℝ) => Afull x + M θ x
          let AenvelopeDelete : ℝ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ) => Adelete i x + Mdelete θ i x
          let Δ : ℝ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ) =>
              (Aenvelope θ x - AenvelopeDelete θ i x) - (Afull x - Adelete i x)
          let fee : ℝ → Fin n → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ) =>
              |Aenvelope θ x - AenvelopeDelete θ i x| + |B x - Bdelete i x|
          let feeTotal : ℝ → (Fin n → Ω × ℝ) → ℝ :=
            fun (θ : ℝ) (x : Fin n → Ω × ℝ) => ∑ i : Fin n, fee θ i x
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (ξ i) ∧ MemLp (ξ i) 2 ν) ∧
          (∀ i : Fin n, (∫ x, (ξ i x) ^ 2 ∂ν) = 1 / (n : ℝ)) ∧
          (∑ i : Fin n, ∫ x, (ξ i x) ^ 2 ∂ν) = 1 ∧
          Measurable[mAug, borel ℝ] V ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (Vdelete i)) ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 0 ≤ Vdelete i x ∧ Vdelete i x ≤ V x) ∧
          Measurable[mAug, borel ℝ] Cbudget ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (CbudgetDelete i)) ∧
          (∀ x : Fin n → Ω × ℝ, 1 ≤ Cbudget x) ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 1 ≤ CbudgetDelete i x) ∧
          Measurable[mAug, borel ℝ] H ∧ Integrable[mAug] H ν ∧
          (∀ i : Fin n, Measurable[mAug, borel ℝ] (Hdelete i) ∧ Integrable[mAug] (Hdelete i) ν) ∧
          (∀ x : Fin n → Ω × ℝ, 0 < H x) ∧
          (∀ (i : Fin n) (x : Fin n → Ω × ℝ), 0 < Hdelete i x) ∧
          (∀ θ : ℝ, Measurable[mAug, borel ℝ] (M θ) ∧
            ∀ i : Fin n, Measurable[mAug, borel ℝ] (Mdelete θ i)) ∧
          (∀ θ : ℝ, Integrable[mAug] (M θ) ν ∧
            ∀ i : Fin n, Integrable[mAug] (Mdelete θ i) ν) ∧
          (∀ θ : ℝ, Integrable[mAug] (fun x : Fin n → Ω × ℝ => |M θ x|) ν ∧
            ∀ i : Fin n, Integrable[mAug] (fun x : Fin n → Ω × ℝ => |Mdelete θ i x|) ν) ∧
          (∀ θ : ℝ, 0 ≤ θ → ∀ x : Fin n → Ω × ℝ,
            0 ≤ M θ x ∧ ∀ i : Fin n, 0 ≤ Mdelete θ i x) ∧
          (∀ θ : ℝ, (∫ x, M θ x ∂ν) = K * θ * (∫ x, H x ∂ν)) ∧
          (∀ (θ : ℝ) (i : Fin n),
            (∫ x, Mdelete θ i x ∂ν) = K * θ * (∫ x, Hdelete i x ∂ν)) ∧
          (∀ θ : ℝ, (∫ x, |M θ x| ∂ν) = K * |θ| * (∫ x, H x ∂ν)) ∧
          (∀ (θ : ℝ) (i : Fin n),
            (∫ x, |Mdelete θ i x| ∂ν) = K * |θ| * (∫ x, Hdelete i x ∂ν)) ∧
          (∀ i : Fin n, payment i = K * ((∫ x, H x ∂ν) + (∫ x, Hdelete i x ∂ν))) ∧
          (∀ i : Fin n, 0 ≤ payment i) ∧
          0 ≤ paymentTotal ∧
          (∀ (θ : ℝ) (i : Fin n),
            (∫ x, M θ x ∂ν) + (∫ x, Mdelete θ i x ∂ν) = θ * payment i) ∧
          (∀ (θ : ℝ) (i : Fin n),
            (∫ x, |M θ x| ∂ν) + (∫ x, |Mdelete θ i x| ∂ν) = |θ| * payment i) ∧
          (∀ θ : ℝ,
            (∑ i : Fin n, ((∫ x, M θ x ∂ν) + (∫ x, Mdelete θ i x ∂ν))) = θ * paymentTotal) ∧
          (∀ θ : ℝ,
            (∑ i : Fin n, ((∫ x, |M θ x| ∂ν) + (∫ x, |Mdelete θ i x| ∂ν))) = |θ| * paymentTotal) ∧
          Filter.Tendsto (fun θ : ℝ => ∫ x, M θ x ∂ν) (nhds (0 : ℝ)) (nhds (0 : ℝ)) ∧
          Filter.Tendsto (fun θ : ℝ => ∫ x, |M θ x| ∂ν) (nhds (0 : ℝ)) (nhds (0 : ℝ)) ∧
          (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, Mdelete θ i x ∂ν)
            (nhds (0 : ℝ)) (nhds (0 : ℝ))) ∧
          (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, |Mdelete θ i x| ∂ν)
            (nhds (0 : ℝ)) (nhds (0 : ℝ))) ∧
          (∀ θ : ℝ, Measurable[mAug, borel ℝ] (Aenvelope θ) ∧ Integrable[mAug] (Aenvelope θ) ν) ∧
          (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (AenvelopeDelete θ i) ∧
            Integrable[mAug] (AenvelopeDelete θ i) ν) ∧
          (∀ θ : ℝ, 0 ≤ θ → ∀ x : Fin n → Ω × ℝ,
            0 ≤ Aenvelope θ x ∧ ∀ i : Fin n, 0 ≤ AenvelopeDelete θ i x) ∧
          (∀ θ : ℝ, ∃ Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel (Fin n → ℝ), borel (ℝ × ℝ × ℝ)] Ffull ∧
            ∀ x : Fin n → Ω × ℝ,
              (M θ x, Aenvelope θ x, B x) = Ffull (C x)) ∧
          (∀ (θ : ℝ) (i : Fin n),
            ∃ Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
              Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdelete ∧
              ∀ x : Fin n → Ω × ℝ,
                (Mdelete θ i x, AenvelopeDelete θ i x, Bdelete i x) =
                  Fdelete (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
          (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
            Δ θ i x = M θ x - Mdelete θ i x) ∧
          (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
            |Δ θ i x| ≤ |M θ x| + |Mdelete θ i x|) ∧
          (∀ θ : ℝ, 0 ≤ θ → ∀ (i : Fin n) (x : Fin n → Ω × ℝ),
            |Δ θ i x| ≤ M θ x + Mdelete θ i x) ∧
          (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (Δ θ i) ∧
            Integrable[mAug] (Δ θ i) ν ∧
            Integrable[mAug] (fun x : Fin n → Ω × ℝ => |Δ θ i x|) ν) ∧
          (∀ (θ : ℝ) (i : Fin n), (∫ x, |Δ θ i x| ∂ν) ≤ |θ| * payment i) ∧
          (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, |Δ θ i x| ∂ν)
            (nhds (0 : ℝ)) (nhds (0 : ℝ))) ∧
          (∀ (θ : ℝ) (i : Fin n), Measurable[mAug, borel ℝ] (fee θ i) ∧
            Integrable[mAug] (fee θ i) ν) ∧
          (∀ θ : ℝ, Measurable[mAug, borel ℝ] (feeTotal θ) ∧ Integrable[mAug] (feeTotal θ) ν) ∧
          (∀ (θ : ℝ) (i : Fin n) (x : Fin n → Ω × ℝ),
            |fee θ i x - deletionMass (q x) i| ≤ |M θ x| + |Mdelete θ i x|) ∧
          (∀ (θ : ℝ) (i : Fin n),
            |(∫ x, fee θ i x ∂ν) - (∫ x, deletionMass (q x) i ∂ν)| ≤ |θ| * payment i) ∧
          (∀ θ : ℝ,
            |(∫ x, feeTotal θ x ∂ν) - (∫ x, deletionTotal (q x) ∂ν)| ≤ |θ| * paymentTotal) ∧
          (∀ i : Fin n, Filter.Tendsto (fun θ : ℝ => ∫ x, fee θ i x ∂ν)
            (nhds (0 : ℝ)) (nhds (∫ x, deletionMass (q x) i ∂ν))) ∧
          Filter.Tendsto (fun θ : ℝ => ∫ x, feeTotal θ x ∂ν)
            (nhds (0 : ℝ)) (nhds (∫ x, deletionTotal (q x) ∂ν))
```

### Generic exact source-z limits

Path: C:\game\shao lean\library\Shao\OQ6\NormalizedAnalyticCostLimits.lean

```lean
theorem actual_projection_tilt_and_truncated_cost_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (x : ℝ) :
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let ℓ : Fin n → Ω → ℝ := fun i ω => x * ξ i ω - (x * ξ i ω) ^ 2 / 2
    let ℓη : ℕ → Fin n → Ω → ℝ := fun k i ω => x * η k i ω - (x * η k i ω) ^ 2 / 2
    let S : Ω → ℝ := fun ω => ∑ i : Fin n, ℓ i ω
    let Sη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, ℓη k i ω
    let Sminus : Fin n → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, ℓ j ω
    let Sηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
    let m : Fin n → ℝ := fun i => ∫ ω, Real.exp (ℓ i ω) ∂ν
    let mη : ℕ → Fin n → ℝ := fun k i => ∫ ω, Real.exp (ℓη k i ω) ∂ν
    let I : ℝ := ∫ ω, Real.exp (S ω) ∂ν
    let Iη : ℕ → ℝ := fun k => ∫ ω, Real.exp (Sη k ω) ∂ν
    let J : Fin n → ℝ := fun i => ∫ ω, Real.exp (Sminus i ω) ∂ν
    let Jη : ℕ → Fin n → ℝ := fun k i => ∫ ω, Real.exp (Sηminus k i ω) ∂ν
    let δ : Fin n → ℝ := fun i => ∫ ω, (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1 ∂ν
    let δη : ℕ → Fin n → ℝ := fun k i => ∫ ω, (x * η k i ω) ^ 2 * min |x * η k i ω| 1 ∂ν
    let L : ℝ := ∑ i : Fin n, δ i
    let Lη : ℕ → ℝ := fun k => ∑ i : Fin n, δη k i
    let q : Ω → ℝ := fun ω => Real.exp (S ω) / I
    let qη : ℕ → Ω → ℝ := fun k ω => Real.exp (Sη k ω) / Iη k
    let qminus : Fin n → Ω → ℝ := fun i ω => Real.exp (Sminus i ω) / I
    let qηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => Real.exp (Sηminus k i ω) / Iη k
    let pminus : Fin n → Ω → ℝ := fun i ω => Real.exp (Sminus i ω) / J i
    let pηminus : ℕ → Fin n → Ω → ℝ := fun k i ω => Real.exp (Sηminus k i ω) / Jη k i
    (∀ i : Fin n, Integrable (fun ω => Real.exp (ℓ i ω)) ν ∧ 0 < m i) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => Real.exp (ℓη k i ω)) ν ∧ 0 < mη k i) ∧
    Integrable (fun ω => Real.exp (S ω)) ν ∧ 0 < I ∧
    (∀ k : ℕ, Integrable (fun ω => Real.exp (Sη k ω)) ν ∧ 0 < Iη k) ∧
    (∀ i : Fin n, Integrable (fun ω => Real.exp (Sminus i ω)) ν ∧ 0 < J i) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => Real.exp (Sηminus k i ω)) ν ∧ 0 < Jη k i) ∧
    (∀ ω : Ω, Real.exp (S ω) ≤ Real.exp ((n : ℝ) / 2)) ∧
    (∀ (k : ℕ) (ω : Ω), Real.exp (Sη k ω) ≤ Real.exp ((n : ℝ) / 2)) ∧
    (∀ (i : Fin n) (ω : Ω), Real.exp (Sminus i ω) ≤ Real.exp (((n - 1 : ℕ) : ℝ) / 2)) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω), Real.exp (Sηminus k i ω) ≤ Real.exp (((n - 1 : ℕ) : ℝ) / 2)) ∧
    (∀ i : Fin n, Integrable (fun ω => (x * ξ i ω) ^ 2 * min |x * ξ i ω| 1) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun ω => (x * η k i ω) ^ 2 * min |x * η k i ω| 1) ν) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |(x * η k i ω) ^ 2 * min |x * η k i ω| 1| ≤ x ^ 2 * (8 * (ξ i ω) ^ 2 + 2)) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => mη k i) Filter.atTop (nhds (m i))) ∧
    Filter.Tendsto Iη Filter.atTop (nhds I) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => Jη k i) Filter.atTop (nhds (J i))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => δη k i) Filter.atTop (nhds (δ i))) ∧
    Filter.Tendsto Lη Filter.atTop (nhds L) ∧
    Integrable q ν ∧ (∫ ω, q ω ∂ν) = 1 ∧
    (∀ k : ℕ, Integrable (qη k) ν ∧ (∫ ω, qη k ω ∂ν) = 1) ∧
    (∀ i : Fin n, Integrable (qminus i) ν ∧ (∫ ω, qminus i ω ∂ν) = J i / I) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (qηminus k i) ν ∧ (∫ ω, qηminus k i ω ∂ν) = Jη k i / Iη k) ∧
    (∀ i : Fin n, Integrable (pminus i) ν ∧ (∫ ω, pminus i ω ∂ν) = 1) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (pηminus k i) ν ∧ (∫ ω, pηminus k i ω ∂ν) = 1) ∧
    (∀ (i : Fin n) (ω : Ω), qminus i ω = (J i / I) * pminus i ω) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω), qηminus k i ω = (Jη k i / Iη k) * pηminus k i ω) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => qη k ω) Filter.atTop (nhds (q ω))) ∧
    (∀ (i : Fin n) (ω : Ω), Filter.Tendsto (fun k : ℕ => qηminus k i ω) Filter.atTop (nhds (qminus i ω))) ∧
    (∀ (i : Fin n) (ω : Ω), Filter.Tendsto (fun k : ℕ => pηminus k i ω) Filter.atTop (nhds (pminus i ω))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => Jη k i / Iη k) Filter.atTop (nhds (J i / I)))
```

### Qualified229 exact strict tails

Path: C:\game\shao lean\drafts\oq56\unit229\author-01\NormalizedStrictMomentBudgets.lean

```lean
theorem actual_source_z_strict_truncated_moment_budgets
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω : Ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω : Ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (z : ℝ) (hz : 1 ≤ z)
    (cBudget : ℝ) (hcBudget : 0 < cBudget) :
    let η : ℕ → Fin n → Ω → ℝ := fun (k : ℕ) =>
      Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let Fz : ℝ → ℝ := fun (t : ℝ) => (z * t) ^ 2 * min |z * t| 1
    let δ0 : Fin n → ℝ := fun (i : Fin n) => ∫ ω : Ω, Fz (ξ i ω) ∂ν
    let δη : ℕ → Fin n → ℝ := fun (k : ℕ) (i : Fin n) =>
      ∫ ω : Ω, Fz (η k i ω) ∂ν
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let Lη : ℕ → ℝ := fun (k : ℕ) => ∑ i : Fin n, δη k i
    (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) →
    L0 < cBudget * z ^ 2 →
    (∀ i : Fin n, Integrable (fun (ω : Ω) => Fz (ξ i ω)) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun (ω : Ω) => Fz (η k i ω)) ν) ∧
    (∀ i : Fin n,
      Filter.Tendsto (fun (k : ℕ) => δη k i) Filter.atTop (nhds (δ0 i))) ∧
    Filter.Tendsto Lη Filter.atTop (nhds L0) ∧
    (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2)
```

### Qualified230 original IID quantitative window

Path: C:\game\shao lean\drafts\oq56\unit230\author-01\repair-01\IIDSourceStrictMomentBudgets.lean

```lean
theorem actual_iid_source_z_strict_moment_budgets
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (p : ℝ) (hp2 : 2 < p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o : Ω => Real.rpow |g o| p) μ)
    (cBudget : ℝ) (hcBudget : 0 < cBudget) :
    let β : ℝ := ∫ o : Ω, Real.rpow |g o| p ∂μ
    let c : ℝ :=
      Real.rpow (min (1 / 2 : ℝ) cBudget / 2) (1 / p)
    0 ≤ β ∧
      0 < c ∧
      Real.rpow c p = min (1 / 2 : ℝ) cBudget / 2 ∧
      Real.rpow c p < min (1 / 2 : ℝ) cBudget ∧
      (∀ (n : ℕ) (_hn : 1 ≤ n) (z : ℝ) (_hz : 1 ≤ z),
        let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
        let N : ℝ := Real.sqrt (n : ℝ)
        let ξ : Fin n → (Fin n → Ω) → ℝ :=
          fun i ω => g (ω i) / N
        let projectionTest : (Fin n → Ω) → Fin n → ℝ :=
          fun ω i => Shao.truncationF (z * ξ i ω)
        let δ : Fin n → ℝ :=
          fun i => ∫ ω : Fin n → Ω, projectionTest ω i ∂P
        let L : ℝ := ∑ i : Fin n, δ i
        let scalarBudget : ℝ :=
          ∫ o : Ω, Shao.truncationF (z * (g o / N)) ∂μ
        IsProbabilityMeasure P ∧
          Integrable (fun o : Ω => Shao.truncationF (z * (g o / N))) μ ∧
          (∀ i : Fin n, Integrable (fun ω : Fin n → Ω =>
            projectionTest ω i) P) ∧
          (∀ i : Fin n, δ i = scalarBudget) ∧
          L = (n : ℝ) * scalarBudget ∧
          (∀ i : Fin n, L = (n : ℝ) * δ i) ∧
          (∀ i : Fin n, 0 ≤ δ i) ∧
          0 ≤ L ∧
          L ≤ β * Real.rpow z p /
            Real.rpow (n : ℝ) ((p - 2) / 2) ∧
          (β = 0 → L = 0 ∧ (∀ i : Fin n, δ i = 0)) ∧
          ((β = 0 ∨
              (0 < β ∧ z ≤ c * Real.rpow β (-1 / p) *
                Real.rpow (n : ℝ) ((p - 2) / (2 * p)))) →
            L ≤ Real.rpow c p ∧
              (∀ i : Fin n, δ i < (1 / 2 : ℝ)) ∧
              L < cBudget * z ^ 2))
```

### Original projection facts; only first pair consumed

Path: C:\game\shao lean\library\Shao\OQ6\ActualQuadraticTiltMoments.lean

```lean
theorem actual_quadratic_source_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => μ)
    let S : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, φ (ξ j)
    let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun j k => r (ξ j) (ξ k)) i
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, ψ ξ i ^ 2
    let A : ℝ :=
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ :=
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))
    let D : ℝ :=
      ∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))
    Measurable g ∧ MemLp g 2 μ ∧ (∫ o, g o ∂μ) = 0 ∧
      (∫ o, g o ^ 2 ∂μ) = 1 ∧
      Measurable (fun z : Ω × Ω => r z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) ∧
      (∀ o y, r o y = r y o) ∧
      (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) ∧
      0 ≤ v ∧ 1 ≤ s ∧ v ≤ s ^ 2 ∧
      Integrable w μ ∧ (1 / 2 : ℝ) ≤ m ∧ m ≤ (3 / 2 : ℝ) ∧
      Measurable L ∧ Integrable L μ ∧
      (∀ o, 0 < L o ∧ L o ≤ 2 * C) ∧
      (∫ o, L o ∂μ) = 1 ∧
      Integrable (fun o => (L o - 1) ^ 2) μ ∧
      (∫ o, (L o - 1) ^ 2 ∂μ) ≤ 4 * C ^ 2 * a ^ 2 ∧
      μ.tilted φ = ρ ∧ IsProbabilityMeasure ρ ∧
      Integrable (fun ξ => Real.exp (S ξ)) P₀ ∧
      (∫ ξ, Real.exp (S ξ) ∂P₀) = m ^ n ∧ 0 < m ^ n ∧
      (∀ ξ, Real.exp (S ξ) / m ^ n =
        ∏ j : Fin n, L (ξ j)) ∧
      Pₐ = P₀.withDensity
        (fun ξ => ENNReal.ofReal (∏ j : Fin n, L (ξ j))) ∧
      Pₐ = Measure.pi (fun _ : Fin n => ρ) ∧
      IsProbabilityMeasure Pₐ ∧
      MemLp F 2 Pₐ ∧ Integrable (fun ξ => F ξ ^ 2) Pₐ ∧
      (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 Pₐ) ∧
      Integrable Λsq Pₐ ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) =
        (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B +
          6 * (n.choose 4 : ℝ) * D ∧
      (∫ ξ, Λsq ξ ∂Pₐ) =
        2 * (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 *
        (4 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
          96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 *
        (8 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
        (2 * C ^ 2 + 8 * C ^ 3 * x ^ 2 + 4 * C ^ 4 * x ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
        (4 * C ^ 2 + 8 * C ^ 3 * x ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
        14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤
        14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 2)
```

### Independent normalized Q envelope

Path: C:\game\shao lean\library\Shao\OQ6\NormalizedRemainderEnvelope.lean

```lean
theorem actual_normalized_remainder_envelope_spec
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ Y : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (D1 D2 A B : Ω → ℝ)
    (Adelete Bdelete : Fin n → Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (hA : Measurable A) (hB : Measurable B)
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hD1A : ∀ ω : Ω, |D1 ω| ≤ A ω)
    (hD2B : ∀ ω : Ω, |D2 ω| ≤ B ω)
    (hAint : Integrable A ν) (hBint : Integrable B ν)
    (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ)))
    (herr : ∀ (i : Fin n) (ω : Ω), |Y i ω - ξ i ω| ≤ ε)
    (z : ℝ) (hz : 0 ≤ z) :
    let η : Fin n → Ω → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let C : Ω → ℝ := fun ω => Real.sqrt (1 + B ω)
    let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + z * C ω)
    let ρ : ℝ := 4 * ε * Real.sqrt (n : ℝ)
    let Dη : Ω → ℝ := fun ω => D1 ω + W ω - Wη ω + z * b ω * (Vη ω - V ω)
    let Aε : Ω → ℝ := fun ω => A ω + ρ * H ω
    let Bε : Ω → ℝ := B
    let Aεdelete : Fin n → Ω → ℝ := Adelete
    let Bεdelete : Fin n → Ω → ℝ := Bdelete
    (∀ i : Fin n, Measurable (η i)) ∧
    Measurable W ∧ Measurable Wη ∧ Measurable V ∧ Measurable Vη ∧
    Measurable b ∧ Measurable C ∧ Measurable H ∧ Measurable Dη ∧
    Measurable Aε ∧ Measurable Bε ∧
    (∀ ω : Ω, 0 ≤ b ω ∧ b ω ≤ C ω) ∧
    (∀ ω : Ω, 0 < H ω) ∧
    0 < ρ ∧ ρ < 1 ∧
    Integrable H ν ∧
    Integrable D1 ν ∧
    Integrable Dη ν ∧
    Integrable Aε ν ∧
    Integrable (fun ω => Dη ω - D1 ω) ν ∧
    Integrable (fun ω => |Dη ω - D1 ω|) ν ∧
    Integrable (fun ω => ρ * H ω) ν ∧
    Integrable (fun ω => A ω + H ω) ν ∧
    (∀ ω : Ω, |Dη ω - D1 ω| ≤ ρ * H ω) ∧
    (∀ ω : Ω, |Dη ω| ≤ Aε ω) ∧
    (∀ ω : Ω, 0 ≤ Aε ω) ∧
    (∀ ω : Ω, Aε ω ≤ A ω + H ω) ∧
    (∀ ω : Ω, 0 ≤ Bε ω ∧ |D2 ω| ≤ Bε ω) ∧
    Bε = B ∧ Aεdelete = Adelete ∧ Bεdelete = Bdelete ∧
    (∀ (i : Fin n) (ω : Ω),
      |Aε ω - Aεdelete i ω| ≤ |A ω - Adelete i ω| + ρ * H ω) ∧
    (∀ (i : Fin n) (ω : Ω),
      |Bε ω - Bεdelete i ω| = |B ω - Bdelete i ω|) ∧
    (∫ ω, |Dη ω - D1 ω| ∂ν) ≤ ρ * (∫ ω, H ω ∂ν) ∧
    (∫ ω, |Aε ω - A ω| ∂ν) = ρ * (∫ ω, H ω ∂ν) ∧
    (∫ ω, Aε ω ∂ν) = (∫ ω, A ω ∂ν) + ρ * (∫ ω, H ω ∂ν)
```

### Canonical scalar code

Path: C:\game\shao lean\library\Shao\OQ6\ScalarObservationCoding.lean

```lean
theorem countable_uniform_augmented_base_four_code
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    let H : ℕ → Set (Ω × ℝ) :=
      MeasurableSpace.natGeneratingSequence (Ω × ℝ)
    let c : (Ω × ℝ) → ℝ := baseFourIndicatorCode H
    let lambda01 : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
    let ν : Measure (Ω × ℝ) := μ.prod lambda01
    IsProbabilityMeasure lambda01 ∧
    IsProbabilityMeasure ν ∧
    (∀ z : Ω × ℝ,
      Summable (fun k : ℕ =>
        (if z ∈ H k then (2 : ℝ) else 1) / (4 : ℝ) ^ (k + 1))) ∧
    (∀ z : Ω × ℝ, (1 / 3 : ℝ) ≤ c z ∧ c z ≤ (2 / 3 : ℝ)) ∧
    Measurable c ∧
    (∀ k : ℕ, MeasurableSet (baseFourOneSet k)) ∧
    (∀ k : ℕ, H k = c ⁻¹' baseFourOneSet k) ∧
    MeasurableSpace.comap c (borel ℝ) =
      (inferInstance : MeasurableSpace (Ω × ℝ)) ∧
    (∀ z z' : Ω × ℝ, c z = c z' → z.2 = z'.2) ∧
    (∀ t : ℝ, ν ({z : Ω × ℝ | c z = t}) = 0)
```

### Canonical quantization

Path: C:\game\shao lean\library\Shao\OQ6\QuantizedObservationCoding.lean

```lean
theorem quantized_observation_spec
    {X : Type*} [mX : MeasurableSpace X]
    (ξ c : X → ℝ) (hξ : Measurable ξ) (hc : Measurable c)
    (hrange : ∀ x : X, (1 / 3 : ℝ) ≤ c x ∧ c x ≤ (2 / 3 : ℝ))
    (hcomap : MeasurableSpace.comap c (borel ℝ) = mX)
    (ε : ℝ) (hε : 0 < ε) :
    let Y : X → ℝ := quantizedObservation ε ξ c
    let D : ℝ → ℝ := fun y : ℝ => y / ε - (Int.floor (y / ε) : ℝ)
    Measurable Y ∧
    Measurable D ∧
    (∀ x : X, |Y x - ξ x| ≤ ε) ∧
    (∀ x : X, Int.floor (Y x / ε) = Int.floor (ξ x / ε)) ∧
    (∀ x : X, D (Y x) = c x) ∧
    MeasurableSpace.comap Y (borel ℝ) = mX ∧
    (∀ (ν : Measure X),
      (∀ t : ℝ, ν ({x : X | c x = t}) = 0) →
      ∀ t : ℝ, ν ({x : X | Y x = t}) = 0)
```

## 固定Pi/Prod/积分运输API

Path: C:\game\shao lean\coordination\pinned-api-20261026\Mathlib\MeasureTheory\MeasurableSpace\Constructions.lean, lines 376–426.

```lean
    MeasurableSpace (α × β) :=
  m₁.prod m₂

theorem measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.fst : α × β → α) :=
  Measurable.of_comap_le le_sup_left

theorem measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.snd : α × β → β) :=
  Measurable.of_comap_le le_sup_right

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[fun_prop]
theorem Measurable.fst {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).1 :=
  measurable_fst.comp hf

@[fun_prop]
theorem Measurable.snd {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).2 :=
  measurable_snd.comp hf

theorem Measurable.prod {f : α → β × γ} (hf₁ : Measurable fun a => (f a).1)
    (hf₂ : Measurable fun a => (f a).2) : Measurable f :=
  Measurable.of_le_map <|
    sup_le
      (by
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp]
        exact hf₁)
      (by
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp]
        exact hf₂)

@[fun_prop]
theorem Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : α → β}
    {g : α → γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a : α => (f a, g a) :=
  Measurable.prod hf hg

@[fun_prop]
theorem Measurable.prodMap [MeasurableSpace δ] {f : α → β} {g : γ → δ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Prod.map f g) :=
  (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)

theorem measurable_prodMk_left {x : α} : Measurable (@Prod.mk _ β x) :=
  measurable_const.prodMk measurable_id

theorem measurable_prodMk_right {y : β} : Measurable fun x : α => (x, y) :=
  measurable_id.prodMk measurable_const

@[fun_prop]
theorem measurable_diag : @Measurable α (α × α) m (m.prod m) Function.diag :=
  measurable_id.prodMk measurable_id
```

Path: C:\game\shao lean\coordination\pinned-api-20261026\Mathlib\MeasureTheory\MeasurableSpace\Constructions.lean, lines 571–599.

```lean

variable {X : δ → Type*} [MeasurableSpace α]

instance MeasurableSpace.pi [m : ∀ a, MeasurableSpace (X a)] : MeasurableSpace (∀ a, X a) :=
  ⨆ a, (m a).comap fun b => b a

variable [∀ a, MeasurableSpace (X a)] [MeasurableSpace γ]

theorem measurable_pi_iff {g : α → ∀ a, X a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, X a => f a :=
  measurable_pi_iff.1 measurable_id a

theorem MeasurableSpace.comap_le_comap_pi {g : (a : δ) → β → X a} (a : δ) :
    .comap (g a) inferInstance ≤ pi.comap (fun b c ↦ g c b) := by
  simpa only [pi, comap_iSup] using le_iSup_of_le a <| by measurability

theorem Measurable.eval {a : δ} {g : α → ∀ a, X a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg

@[fun_prop]
theorem Measurable.of_eval {f : α → ∀ a, X a} (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf

```

Path: C:\game\shao lean\coordination\pinned-api-20261026\Mathlib\MeasureTheory\Integral\Bochner\Basic.lean, lines 1065–1085.

```lean
theorem integral_map_of_stronglyMeasurable {β} [MeasurableSpace β] {φ : α → β} (hφ : Measurable φ)
    {f : β → G} (hfm : StronglyMeasurable f) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ := by
  by_cases hfi : Integrable f (Measure.map φ μ); swap
  · rw [integral_undef hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  simp only [integral_eq_setToFun]
  apply setToFun_of_le_map_of_stronglyMeasurable _ _
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).1 hfi) hfm hφ le_rfl
  intro s x hs
  simp [weightedSMul_apply, map_measureReal_apply, hs, hφ]

theorem integral_map {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → G}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  let g := hfm.mk f
  calc
    ∫ y, f y ∂Measure.map φ μ = ∫ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ x, g (hφ.mk φ x) ∂μ :=
      (integral_map_of_stronglyMeasurable hφ.measurable_mk hfm.stronglyMeasurable_mk)
    _ = ∫ x, g (φ x) ∂μ := integral_congr_ae (hφ.ae_eq_mk.symm.fun_comp _)
```

Path: C:\game\shao lean\coordination\pinned-api-20261026\Mathlib\MeasureTheory\Constructions\Pi.lean, lines 401–407.

```lean
omit [∀ i, SigmaFinite (μ i)] in
lemma _root_.MeasureTheory.measurePreserving_eval [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  classical
  rw [Measure.pi_map_eval, Finset.prod_eq_one, one_smul]
  exact fun _ _ ↦ measure_univ
```

上述`integrable_comp`及`integrable_comp_of_integrable`的调用形状已在curated qualified OriginalClippedCanonicalCostPacket.lean 383–406与449–464以及exact228的transport段核对；本地没有另存其Mathlib原声明的完整单文件副本，故不伪称此件新读了缺失副本。其数学类型是对可测目标f的可积复合等价/向源拉回；完整实际已用模式与map积分API足够界定本候选的具体Fz运输，实施若发现具体固定API差异应记录真实错误而非新增caller callback。
