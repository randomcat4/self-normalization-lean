# 本模块完整声明清单

STATUS: AUTHOR_AUDITED_AWAITING_INDEPENDENT_REVIEW

以下来自真实 canonical 模块所有权审计，未按名称过滤。所有34个新声明逐一列出完整名称、kind、实例状态、完整 pp.all 签名及传递公理依赖。

源码 SHA256：`c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861`；8414 字节。

实测：4个定义、9个显式公开定理、1个命名实例、6个显式私有 helper、14个生成 helper；总计34个，Lean kind 为4个 definition、30个 theorem，注册实例数1。

## Shao.OQ4.RademacherCosine.Kcos_principal

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hrlo : @LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r)
  (hrhi : @LE.le.{0} Int Int.instLEInt r (@Nat.cast.{0} Int instNatCastInt m)),
  @Eq.{1} Real
    (Shao.OQ4.Kcos Shao.OQ4.RademacherCosine.law (Shao.OQ4.RademacherCosine.angle m) h
      (@Int.cast.{0} Real Real.instIntCast r))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.rho m)
      (Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m)
          (@Int.cast.{0} Real Real.instIntCast r))))
```

## Shao.OQ4.RademacherCosine.Kcos_principal._proof_1_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Quot.sound`

```lean
∀ (m : Nat) (r : Int)
  (hrlo : @LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r),
  Not
      (@LE.le.{0} Int
        (@Preorder.toLE.{0} Int
          (@PartialOrder.toPreorder.{0} Int
            (@SemilatticeInf.toPartialOrder.{0} Int
              (@Lattice.toSemilatticeInf.{0} Int
                (@DistribLattice.toLattice.{0} Int (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder))))))
        (@Neg.neg.{0} Int
          (@NegZeroClass.toNeg.{0} Int
            (@SubNegZeroMonoid.toNegZeroClass.{0} Int
              (@SubtractionMonoid.toSubNegZeroMonoid.{0} Int
                (@SubtractionCommMonoid.toSubtractionMonoid.{0} Int
                  (@AddCommGroup.toDivisionAddCommMonoid.{0} Int Int.instAddCommGroup)))))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) r
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherCosine.Kcos_principal._proof_1_2

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Quot.sound`

```lean
∀ (m : Nat) (r : Int) (hrhi : @LE.le.{0} Int Int.instLEInt r (@Nat.cast.{0} Int instNatCastInt m)),
  Not
      (@LE.le.{0} Int
        (@Preorder.toLE.{0} Int
          (@PartialOrder.toPreorder.{0} Int
            (@SemilatticeInf.toPartialOrder.{0} Int
              (@Lattice.toSemilatticeInf.{0} Int
                (@DistribLattice.toLattice.{0} Int (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder))))))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) r
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherCosine.Kcos_principal._proof_1_3

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Quot.sound`

```lean
∀ (m : Nat) (r : Int)
  (hrlo : @LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r),
  Not
      (@LE.le.{0} Int
        (@Preorder.toLE.{0} Int
          (@PartialOrder.toPreorder.{0} Int
            (@SemilatticeInf.toPartialOrder.{0} Int
              (@Lattice.toSemilatticeInf.{0} Int
                (@DistribLattice.toLattice.{0} Int (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder))))))
        (@Neg.neg.{0} Int
          (@NegZeroClass.toNeg.{0} Int
            (@SubNegZeroMonoid.toNegZeroClass.{0} Int
              (@SubtractionMonoid.toSubNegZeroMonoid.{0} Int
                (@SubtractionCommMonoid.toSubtractionMonoid.{0} Int
                  (@AddCommGroup.toDivisionAddCommMonoid.{0} Int Int.instAddCommGroup)))))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) r
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherCosine.Kcos_principal._proof_1_4

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Quot.sound`

```lean
∀ (m : Nat) (r : Int) (hrhi : @LE.le.{0} Int Int.instLEInt r (@Nat.cast.{0} Int instNatCastInt m)),
  Not
      (@LE.le.{0} Int
        (@Preorder.toLE.{0} Int
          (@PartialOrder.toPreorder.{0} Int
            (@SemilatticeInf.toPartialOrder.{0} Int
              (@Lattice.toSemilatticeInf.{0} Int
                (@DistribLattice.toLattice.{0} Int (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder))))))
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) r
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherCosine.angle

- 分类：definition
- kind：`definition`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
(m : Nat) → Real
```

## Shao.OQ4.RademacherCosine.angle.eq_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherCosine.angle m)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Real.pi
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast Shao.OQ4.RademacherCosine.halfENNReal._proof_1))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## Shao.OQ4.RademacherCosine.angle_lt_pi_div_two

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherCosine.angle m)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Real.pi
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
```

## Shao.OQ4.RademacherCosine.angle_pos

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherCosine.angle m)
```

## Shao.OQ4.RademacherCosine.halfENNReal

- 分类：definition
- kind：`definition`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
ENNReal
```

## Shao.OQ4.RademacherCosine.halfENNReal._proof_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherCosine.halfENNReal.eq_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
@Eq.{1} ENNReal Shao.OQ4.RademacherCosine.halfENNReal
  (@HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal
    (@instHDiv.{0} ENNReal (@DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoid))
    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        Shao.OQ4.RademacherCosine.halfENNReal._proof_1)))
```

## Shao.OQ4.RademacherCosine.integer_closed_iff

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (h : Real) (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (s : Int),
  Iff
    (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (@Int.cast.{0} Real Real.instIntCast s))
      h)
    (@LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup s) (@Nat.cast.{0} Int instNatCastInt m))
```

## Shao.OQ4.RademacherCosine.integer_closed_iff._proof_1_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Quot.sound`

```lean
∀ (m : Nat) (s : Int)
  (hint :
    Not
      (@LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup s)
        (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (@LE.le.{0} Int Int.instLEInt
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@abs.{0} Int instLatticeInt Int.instAddGroup s)) →
    False
```

## Shao.OQ4.RademacherCosine.killedKernel_cos_integrable

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (h : Real) (r : Int),
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
    Real Real.measurableSpace
    (fun (w : Real) =>
      Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m) w))
    (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace) Real
      (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
      (@Shao.OQ4.killedKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h)
      (@Int.cast.{0} Real Real.instIntCast r))
```

## Shao.OQ4.RademacherCosine.killedKernel_integral_principal

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hrlo : @LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r)
  (hrhi : @LE.le.{0} Int Int.instLEInt r (@Nat.cast.{0} Int instNatCastInt m)),
  @Eq.{1} Real
    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
      (@NormedField.toNormedSpace.{0} Real Real.normedField) Real.measurableSpace
      (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        Real (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        (@Shao.OQ4.killedKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h)
        (@Int.cast.{0} Real Real.instIntCast r))
      fun (w : Real) =>
      Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m) w))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.rho m)
      (Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m)
          (@Int.cast.{0} Real Real.instIntCast r))))
```

## Shao.OQ4.RademacherCosine.killedKernel_row

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (h : Real) (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int),
  @Eq.{1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
    (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace) Real
      (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
      (@Shao.OQ4.killedKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h)
      (@Int.cast.{0} Real Real.instIntCast r))
    (@HAdd.hAdd.{0, 0, 0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.{0} Real Real.measurableSpace) (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@instHAdd.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@MeasureTheory.Measure.instAdd.{0} Real Real.measurableSpace))
      (@ite.{1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) r
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt m))
        (Int.decLe
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) r
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt m))
        (@HSMul.hSMul.{0, 0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
          (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
          (@instHSMul.{0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
            (@MeasureTheory.Measure.instSMul.{0, 0} Real ENNReal Real.measurableSpace
              (@instSMulOfMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (@IsScalarTower.right.{0, 0} ENNReal ENNReal ENNReal.instCommSemiring
                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring)
                (@Algebra.id.{0} ENNReal ENNReal.instCommSemiring))))
          Shao.OQ4.RademacherCosine.halfENNReal
          (@MeasureTheory.Measure.dirac.{0} Real Real.measurableSpace
            (@Int.cast.{0} Real Real.instIntCast
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) r
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))))
        (@OfNat.ofNat.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace) (nat_lit 0)
          (@Zero.toOfNat0.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
            (@MeasureTheory.Measure.instZero.{0} Real Real.measurableSpace))))
      (@ite.{1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) r
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt m))
        (Int.decLe
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) r
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt m))
        (@HSMul.hSMul.{0, 0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
          (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
          (@instHSMul.{0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
            (@MeasureTheory.Measure.instSMul.{0, 0} Real ENNReal Real.measurableSpace
              (@instSMulOfMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (@IsScalarTower.right.{0, 0} ENNReal ENNReal ENNReal.instCommSemiring
                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring)
                (@Algebra.id.{0} ENNReal ENNReal.instCommSemiring))))
          Shao.OQ4.RademacherCosine.halfENNReal
          (@MeasureTheory.Measure.dirac.{0} Real Real.measurableSpace
            (@Int.cast.{0} Real Real.instIntCast
              (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) r
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))))
        (@OfNat.ofNat.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace) (nat_lit 0)
          (@Zero.toOfNat0.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
            (@MeasureTheory.Measure.instZero.{0} Real Real.measurableSpace)))))
```

## Shao.OQ4.RademacherCosine.killedKernel_row._simp_1_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] {a b x : α},
  @Eq.{1} Prop (@Membership.mem.{u_1, u_1} α (Set.{u_1} α) (@Set.instMembership.{u_1} α) (@Set.Icc.{u_1} α inst a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## Shao.OQ4.RademacherCosine.killedKernel_row._simp_1_2

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Quot.sound`

```lean
∀ {G : Type u_1} [inst : AddCommGroup.{u_1} G] [inst_1 : LinearOrder.{u_1} G]
  [@IsOrderedAddMonoid.{u_1} G (@AddCommGroup.toAddCommMonoid.{u_1} G inst)
      (@PartialOrder.toPreorder.{u_1} G
        (@SemilatticeInf.toPartialOrder.{u_1} G
          (@Lattice.toSemilatticeInf.{u_1} G
            (@DistribLattice.toLattice.{u_1} G (@instDistribLatticeOfLinearOrder.{u_1} G inst_1)))))]
  {a b : G},
  @Eq.{1} Prop
    (And
      (@LE.le.{u_1} G
        (@Preorder.toLE.{u_1} G
          (@PartialOrder.toPreorder.{u_1} G
            (@SemilatticeInf.toPartialOrder.{u_1} G
              (@Lattice.toSemilatticeInf.{u_1} G
                (@DistribLattice.toLattice.{u_1} G (@instDistribLatticeOfLinearOrder.{u_1} G inst_1))))))
        (@Neg.neg.{u_1} G
          (@NegZeroClass.toNeg.{u_1} G
            (@SubNegZeroMonoid.toNegZeroClass.{u_1} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{u_1} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{u_1} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{u_1} G inst)))))
          b)
        a)
      (@LE.le.{u_1} G
        (@Preorder.toLE.{u_1} G
          (@PartialOrder.toPreorder.{u_1} G
            (@SemilatticeInf.toPartialOrder.{u_1} G
              (@Lattice.toSemilatticeInf.{u_1} G
                (@DistribLattice.toLattice.{u_1} G (@instDistribLatticeOfLinearOrder.{u_1} G inst_1))))))
        a b))
    (@LE.le.{u_1} G
      (@Preorder.toLE.{u_1} G
        (@PartialOrder.toPreorder.{u_1} G
          (@SemilatticeInf.toPartialOrder.{u_1} G
            (@Lattice.toSemilatticeInf.{u_1} G
              (@DistribLattice.toLattice.{u_1} G (@instDistribLatticeOfLinearOrder.{u_1} G inst_1))))))
      (@abs.{u_1} G (@DistribLattice.toLattice.{u_1} G (@instDistribLatticeOfLinearOrder.{u_1} G inst_1))
        (@AddCommGroup.toAddGroup.{u_1} G inst) a)
      b)
```

## Shao.OQ4.RademacherCosine.law

- 分类：definition
- kind：`definition`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
@MeasureTheory.Measure.{0} Real Real.measurableSpace
```

## Shao.OQ4.RademacherCosine.law._proof_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
@IsScalarTower.{0, 0, 0} ENNReal ENNReal ENNReal
  (@Algebra.toSMul.{0, 0} ENNReal ENNReal ENNReal.instCommSemiring
    (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring) (@Algebra.id.{0} ENNReal ENNReal.instCommSemiring))
  (@instSMulOfMul.{0} ENNReal
    (@Distrib.toMul.{0} ENNReal
      (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
  (@Algebra.toSMul.{0, 0} ENNReal ENNReal ENNReal.instCommSemiring
    (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring) (@Algebra.id.{0} ENNReal ENNReal.instCommSemiring))
```

## Shao.OQ4.RademacherCosine.law.eq_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
@Eq.{1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace) Shao.OQ4.RademacherCosine.law
  (@HAdd.hAdd.{0, 0, 0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
    (@MeasureTheory.Measure.{0} Real Real.measurableSpace) (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
    (@instHAdd.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.instAdd.{0} Real Real.measurableSpace))
    (@HSMul.hSMul.{0, 0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@instHSMul.{0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@MeasureTheory.Measure.instSMul.{0, 0} Real ENNReal Real.measurableSpace
          (@instSMulOfMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          Shao.OQ4.RademacherCosine.law._proof_1))
      Shao.OQ4.RademacherCosine.halfENNReal
      (@MeasureTheory.Measure.dirac.{0} Real Real.measurableSpace
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (@HSMul.hSMul.{0, 0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@instHSMul.{0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@MeasureTheory.Measure.instSMul.{0, 0} Real ENNReal Real.measurableSpace
          (@instSMulOfMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          Shao.OQ4.RademacherCosine.law._proof_1))
      Shao.OQ4.RademacherCosine.halfENNReal
      (@MeasureTheory.Measure.dirac.{0} Real Real.measurableSpace
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```

## Shao.OQ4.RademacherCosine.law_isProbabilityMeasure

- 分类：named instance
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`true`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
@MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace Shao.OQ4.RademacherCosine.law
```

## Shao.OQ4.RademacherCosine.rho

- 分类：definition
- kind：`definition`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
(m : Nat) → Real
```

## Shao.OQ4.RademacherCosine.rho.eq_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat), @Eq.{1} Real (Shao.OQ4.RademacherCosine.rho m) (Real.cos (Shao.OQ4.RademacherCosine.angle m))
```

## Shao.OQ4.RademacherCosine.rho_lt_one

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherCosine.rho m)
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherCosine.rho_pos

- 分类：public theorem
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherCosine.rho m)
```

## _private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.absorbing_cos_zero

- 分类：private explicit helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (s : Int)
  (hs :
    @Eq.{1} Int (@abs.{0} Int instLatticeInt Int.instAddGroup s)
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))),
  @Eq.{1} Real
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m)
        (@Int.cast.{0} Real Real.instIntCast s)))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## _private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.cut_cos_eq

- 分类：private explicit helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (s : Int)
  (hs :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup s)
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))),
  @Eq.{1} Real
    (@ite.{1} Real
      (@LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup (@Int.cast.{0} Real Real.instIntCast s)) h)
      (Real.decidableLE (@abs.{0} Real Real.lattice Real.instAddGroup (@Int.cast.{0} Real Real.instIntCast s)) h)
      (Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m)
          (@Int.cast.{0} Real Real.instIntCast s)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m)
        (@Int.cast.{0} Real Real.instIntCast s)))
```

## _private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.cut_cos_eq._proof_1_1

- 分类：generated helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Quot.sound`

```lean
∀ (m : Nat) (s : Int)
  (hs :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup s)
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
  (hc :
    Not
      (@LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup s)
        (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (@Eq.{1} Int (@abs.{0} Int instLatticeInt Int.instAddGroup s)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
    False
```

## _private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.half_ne_top

- 分类：private explicit helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
@Ne.{1} ENNReal Shao.OQ4.RademacherCosine.halfENNReal (@Top.top.{0} ENNReal ENNReal.instTop)
```

## _private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.half_toReal

- 分类：private explicit helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
@Eq.{1} Real (ENNReal.toReal Shao.OQ4.RademacherCosine.halfENNReal)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
```

## _private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.integral_law

- 分类：private explicit helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (f : Real → Real),
  @Eq.{1} Real
    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
      (@NormedField.toNormedSpace.{0} Real Real.normedField) Real.measurableSpace Shao.OQ4.RademacherCosine.law
      fun (y : Real) => f y)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (f (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (f (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```

## _private.Shao.OQ4.RademacherCosine.0.Shao.OQ4.RademacherCosine.law_map

- 分类：private explicit helper
- kind：`theorem`
- 模块所有者：`Shao.OQ4.RademacherCosine`
- 注册实例：`false`
- 传递公理：`propext`, `Classical.choice`, `Quot.sound`

```lean
∀ (z : Real),
  @Eq.{1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
    (@MeasureTheory.Measure.map.{0, 0} Real Real Real.measurableSpace Real.measurableSpace
      (fun (y : Real) => @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) z y)
      Shao.OQ4.RademacherCosine.law)
    (@HAdd.hAdd.{0, 0, 0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.{0} Real Real.measurableSpace) (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@instHAdd.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@MeasureTheory.Measure.instAdd.{0} Real Real.measurableSpace))
      (@HSMul.hSMul.{0, 0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@instHSMul.{0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
          (@MeasureTheory.Measure.instSMul.{0, 0} Real ENNReal Real.measurableSpace
            (@instSMulOfMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
            (@IsScalarTower.right.{0, 0} ENNReal ENNReal ENNReal.instCommSemiring
              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring)
              (@Algebra.id.{0} ENNReal ENNReal.instCommSemiring))))
        Shao.OQ4.RademacherCosine.halfENNReal
        (@MeasureTheory.Measure.dirac.{0} Real Real.measurableSpace
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) z
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
      (@HSMul.hSMul.{0, 0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@instHSMul.{0, 0} ENNReal (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
          (@MeasureTheory.Measure.instSMul.{0, 0} Real ENNReal Real.measurableSpace
            (@instSMulOfMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
            (@IsScalarTower.right.{0, 0} ENNReal ENNReal ENNReal.instCommSemiring
              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring)
              (@Algebra.id.{0} ENNReal ENNReal.instCommSemiring))))
        Shao.OQ4.RademacherCosine.halfENNReal
        (@MeasureTheory.Measure.dirac.{0} Real Real.measurableSpace
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) z
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```
