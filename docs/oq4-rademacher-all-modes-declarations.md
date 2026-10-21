# RademacherAllModes 完整规范声明清单

STATUS: AUTHOR_CANONICAL_READY；独立最终审查待完成。

实际规范模块: Shao.OQ4.RademacherAllModes。Source 原字节固定，完整原文实际模块 --stdin 无产物审计及唯一新目标 olean 编译均通过。

Source SHA256: 04cd5a52a40398586908a42682724c357daf0e0c8bbf25a049bbd620d27ee8aa；7720B。

Sole olean SHA256: 93ac5657481fb7555620730e3ceaf9adcacc9ba0979451541dd4e6cc3cd017cf；183592B。

原始 imports: Shao.OQ4.RademacherFiniteBasis, Shao.OQ4.RademacherIteration, Shao.OQ4.KilledPathLaw。

编译器 imports: ['Init', 'Init', 'Shao.OQ4.RademacherFiniteBasis', 'Shao.OQ4.RademacherIteration', 'Shao.OQ4.KilledPathLaw']。

完整源选取规则: 全部 getModuleIdxFor? = none，无 name/namespace 过滤；raw Name/Expr、原始日志和二进制仅服务器保存。全部17项与私有Source及actual import-only target环境逐字段一致，包括完整原名/kind/universes/raw Expr类型/传递公理/定义体/实例标记。

计数: {"all_definition_kind": 1, "all_nonprivate_names": 13, "all_private_names": 4, "all_theorem_kind": 16, "complete_source_owned": 17, "explicit_private_theorems": 4, "explicit_public_definitions": 1, "explicit_public_theorems": 8, "generated_helpers": 4, "import_only_actual_target_owned": 17, "outside_AllModes_namespace": 3, "registered_instances": 0}。

all41 的实际owner OR raw/user namespace选取为863项、99defs；old847/98defs所有字段保持一致。新目标在import-only环境拥有17项，在all41中实际owner为16项、新增distinct名称16项。共享项 Shao.OQ4.killedAction.congr_simp 已存在于old847，all41中保留原owner Shao.OQ4.KernelRecurrence；其完整字段与新Source同项一致。所有17项均在all41中逐字段核对，没有按预期数删选。

实例注册表按导入范围分别完整核对：原Source三imports与direct-target单import各23147项；无额外Lean的all40/all41各23329项；完整审计工具额外import Lean的old40/all41各25020项。每个对应范围中的全部entry字段及erased registry均exact，没有混计不同范围。标准三公理、所有isUnsafe=false、注册新实例0；旧40/92/97组字节保持，私有编译产物0、自有live Lean进程0。

实际证据路径（均在服务器 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-all-modes）：

- 原Source完整原文/all-none17：original-source-registry-raw.json。
- actual direct-target owner17：direct-target-registry-raw.json。
- 完整工具 old40 owner OR namespace847：all40-complete-tool-raw.json。
- 完整工具 all41 owner OR namespace863、target owner16：all41-complete-tool-raw.json。
- 共享helper的source/direct/old40/all41完整raw字段：overlap-raw-exact.json；旧owner为Shao.OQ4.KernelRecurrence。


## Shao.OQ4.RademacherAllModes.closedStrip_probability_spectrum

- 分类: public explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (n : Nat),
  @Eq.{1} Real
    (@MeasureTheory.Measure.real.{0} ((i : Fin n) → Real)
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.measurableSpace)
      (@MeasureTheory.Measure.pi.{0, 0} (Fin n) (fun (x : Fin n) => Real) (Fin.fintype n)
        (fun (i : Fin n) => Real.measurableSpace) fun (x : Fin n) => Shao.OQ4.RademacherCosine.law)
      (@Shao.closedStrip n h))
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherAllModes.survivalCoefficient m j)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherFiniteBasis.mu m j) n))
        (Shao.OQ4.RademacherFiniteBasis.vector m j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
```

## Shao.OQ4.RademacherAllModes.killedAction_eq_pow

- 分类: public explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (j : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j)
  (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r)
  (n : Nat),
  @Eq.{1} Real
    (@Shao.OQ4.killedAction Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h n
      (Shao.OQ4.RademacherFiniteBasis.phi m j) (@Int.cast.{0} Real Real.instIntCast r))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherFiniteBasis.mu m j) n)
      (Shao.OQ4.RademacherFiniteBasis.vector m j r))
```

## Shao.OQ4.RademacherAllModes.killedIterKernel_integrable

- 分类: public explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (_hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (_hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (_hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (j : Nat)
  (_hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j)
  (r : Int)
  (_hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r)
  (n : Nat),
  @MeasureTheory.Integrable.{0, 0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
        (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
    Real Real.measurableSpace (Shao.OQ4.RademacherFiniteBasis.phi m j)
    (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace) Real
      (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
      (@Shao.OQ4.killedIterKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h n)
      (@Int.cast.{0} Real Real.instIntCast r))
```

## Shao.OQ4.RademacherAllModes.killedIterKernel_integral

- 分类: public explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (j : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j)
  (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r)
  (n : Nat),
  @Eq.{1} Real
    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      Real.measurableSpace
      (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        Real (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        (@Shao.OQ4.killedIterKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h
          n)
        (@Int.cast.{0} Real Real.instIntCast r))
      fun (w : Real) => Shao.OQ4.RademacherFiniteBasis.phi m j w)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherFiniteBasis.mu m j) n)
      (Shao.OQ4.RademacherFiniteBasis.vector m j r))
```

## Shao.OQ4.RademacherAllModes.killedIterKernel_real_univ_spectrum

- 分类: public explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r)
  (n : Nat),
  @Eq.{1} Real
    (@MeasureTheory.Measure.real.{0} Real Real.measurableSpace
      (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        Real (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        (@Shao.OQ4.killedIterKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h
          n)
        (@Int.cast.{0} Real Real.instIntCast r))
      (@Set.univ.{0} Real))
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherAllModes.survivalCoefficient m j)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherFiniteBasis.mu m j) n))
        (Shao.OQ4.RademacherFiniteBasis.vector m j r))
```

## Shao.OQ4.RademacherAllModes.killedMass_spectrum

- 分类: public explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r)
  (n : Nat),
  @Eq.{1} Real
    (@Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h n
      (@Int.cast.{0} Real Real.instIntCast r))
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherAllModes.survivalCoefficient m j)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherFiniteBasis.mu m j) n))
        (Shao.OQ4.RademacherFiniteBasis.vector m j r))
```

## Shao.OQ4.RademacherAllModes.shiftedClosedSurvival_probability_spectrum

- 分类: public explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r)
  (n : Nat),
  @Eq.{1} Real
    (@MeasureTheory.Measure.real.{0} ((i : Fin n) → Real)
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.measurableSpace)
      (@MeasureTheory.Measure.pi.{0, 0} (Fin n) (fun (x : Fin n) => Real) (Fin.fintype n)
        (fun (i : Fin n) => Real.measurableSpace) fun (x : Fin n) => Shao.OQ4.RademacherCosine.law)
      (@Shao.OQ4.shiftedClosedSurvival n h (@Int.cast.{0} Real Real.instIntCast r)))
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherAllModes.survivalCoefficient m j)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherFiniteBasis.mu m j) n))
        (Shao.OQ4.RademacherFiniteBasis.vector m j r))
```

## Shao.OQ4.RademacherAllModes.survivalCoefficient

- 分类: public explicit definition
- kind: definition
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
(m j : Nat) → Real
```

完整 definition value（pp.all）:

```lean
fun (m j : Nat) =>
  Shao.OQ4.RademacherFiniteBasis.coefficient m j fun (x : Int) =>
    @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)
```

## Shao.OQ4.RademacherAllModes.survivalCoefficient.eq_1

- 分类: generated helper
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m j : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherAllModes.survivalCoefficient m j)
    (Shao.OQ4.RademacherFiniteBasis.coefficient m j fun (x : Int) =>
      @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherAllModes.survivalCoefficient_eq

- 分类: public explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m j : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherAllModes.survivalCoefficient m j)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) =>
        Shao.OQ4.RademacherFiniteBasis.vector m j s))
```

## Shao.OQ4.RademacherFiniteBasis.coefficient.eq_1

- 分类: generated helper
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m j : Nat) (F : Int → Real),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.coefficient m j F)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (F s)
          (Shao.OQ4.RademacherFiniteBasis.vector m j s)))
```

## Shao.OQ4.RademacherFiniteBasis.vector.eq_1

- 分类: generated helper
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m j : Nat) (s : Int),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.vector m j s)
    (Shao.OQ4.RademacherFiniteBasis.phi m j (@Int.cast.{0} Real Real.instIntCast s))
```

## Shao.OQ4.killedAction.congr_simp

- 分类: generated helper
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.KernelRecurrence
- already in old847: true
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (ν ν_1 : @MeasureTheory.Measure.{0} Real Real.measurableSpace)
  (e_ν : @Eq.{1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace) ν ν_1)
  [inst : @MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace ν] (h h_1 : Real) (e_h : @Eq.{1} Real h h_1)
  (n n_1 : Nat) (e_n : @Eq.{1} Nat n n_1) (f f_1 : Real → Real) (e_f : @Eq.{1} (Real → Real) f f_1) (z z_1 : Real)
  (e_z : @Eq.{1} Real z z_1),
  @Eq.{1} Real (@Shao.OQ4.killedAction ν inst h n f z)
    (@Shao.OQ4.killedAction ν_1
      (@Eq.ndrec.{0, 1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace) ν
        (fun (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace) =>
          @MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace ν)
        inst ν_1 e_ν)
      h_1 n_1 f_1 z_1)
```

## _private.Shao.OQ4.RademacherAllModes.0.Shao.OQ4.RademacherAllModes.action_one_on_grid

- 分类: private explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (j : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j)
  (w : Real)
  (hw :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) (Shao.OQ4.RademacherIteration.grid m) w),
  @Eq.{1} Real
    (@Shao.OQ4.killedAction Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Shao.OQ4.RademacherFiniteBasis.phi m j) w)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherFiniteBasis.mu m j)
      (Shao.OQ4.RademacherFiniteBasis.phi m j w))
```

## _private.Shao.OQ4.RademacherAllModes.0.Shao.OQ4.RademacherAllModes.constant_reconstruction_ae

- 分类: private explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r)
  (n : Nat),
  @Filter.EventuallyEq.{0, 0} Real Real
    (@MeasureTheory.ae.{0, 0} Real (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.instFunLike.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.instOuterMeasureClass.{0} Real Real.measurableSpace)
      (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        Real (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        (@Shao.OQ4.killedIterKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h
          n)
        (@Int.cast.{0} Real Real.instIntCast r)))
    (fun (x : Real) => @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) fun (w : Real) =>
    @Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherAllModes.survivalCoefficient m j) (Shao.OQ4.RademacherFiniteBasis.phi m j w)
```

## _private.Shao.OQ4.RademacherAllModes.0.Shao.OQ4.RademacherAllModes.phi_bound

- 分类: private explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m j : Nat) (w : Real),
  @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (Shao.OQ4.RademacherFiniteBasis.phi m j w))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## _private.Shao.OQ4.RademacherAllModes.0.Shao.OQ4.RademacherAllModes.phi_measurable

- 分类: private explicit theorem
- kind: theorem
- universes: []
- instance: false
- unsafe: false
- all41 actual owner: Shao.OQ4.RademacherAllModes
- already in old847: false
- transitive axioms: Classical.choice, Quot.sound, propext

完整类型（pp.all）:

```lean
∀ (m j : Nat),
  @Measurable.{0, 0} Real Real Real.measurableSpace Real.measurableSpace (Shao.OQ4.RademacherFiniteBasis.phi m j)
```
