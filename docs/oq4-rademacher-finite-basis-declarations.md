# 完整规范声明清单：RademacherFiniteBasis

STATUS: AUTHOR_CANONICAL_READY; independent final review pending. Sole canonical olean emitted.

实际规范模块：`Shao.OQ4.RademacherFiniteBasis`。canonical source 原字节不变；以该实际路径的 --stdin 模式仅附加审计命令，无额外 import。79项与随后实际40模块导入环境的所有对应字段完全一致。

选取规则：`getModuleIdxFor? = none` 的全部常量；没有 name/namespace 过滤。

原始 import：`import Shao.OQ4.RademacherCosine`。

编译器 import 记录：`['Init', 'Init', 'Shao.OQ4.RademacherCosine']`。

计数：`{"owned": 79, "explicit_public_theorems": 9, "explicit_public_definitions": 7, "explicit_private": 20, "explicit_private_definitions": 3, "generated_helpers": 43, "all_definition_kind": 10, "all_theorem_kind": 69, "all_private_names": 49, "registered_instances": 0}`。

每项列出实际名称、kind、universe 参数、实例注册、完整类型及传递公理；definition 另列完整值。raw Name/Expr 保存在服务器 owned-raw.json。

## Shao.OQ4.RademacherFiniteBasis.coefficient

- 分类：public explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
(m j : Nat) → (F : Int → Real) → Real
```

完整 definition value：

```lean
fun (m j : Nat) (F : Int → Real) =>
  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (F s)
        (Shao.OQ4.RademacherFiniteBasis.vector m j s))
```

## Shao.OQ4.RademacherFiniteBasis.dual_orthogonal

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (r s : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r)
  (hs :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) s),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherFiniteBasis.vector m j r) (Shao.OQ4.RademacherFiniteBasis.vector m j s)))
    (@ite.{1} Real (@Eq.{1} Int r s) (Int.instDecidableEq r s)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## Shao.OQ4.RademacherFiniteBasis.killedKernel_integrable

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

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
      (Shao.OQ4.RademacherFiniteBasis.states m) r),
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
      (@Shao.OQ4.killedKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h)
      (@Int.cast.{0} Real Real.instIntCast r))
```

## Shao.OQ4.RademacherFiniteBasis.killedKernel_integral

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (_hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (j : Nat)
  (_hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j)
  (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r),
  @Eq.{1} Real
    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
      (@NormedField.toNormedSpace.{0} Real Real.normedField) Real.measurableSpace
      (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        Real (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        (@Shao.OQ4.killedKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h)
        (@Int.cast.{0} Real Real.instIntCast r))
      fun (w : Real) => Shao.OQ4.RademacherFiniteBasis.phi m j w)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherFiniteBasis.mu m j)
      (Shao.OQ4.RademacherFiniteBasis.vector m j r))
```

## Shao.OQ4.RademacherFiniteBasis.killedKernel_integral._proof_1_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (r : Int)
  (hr' :
    And
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r)
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder) r (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (And
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
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@LE.le.{0} Int
          (@Preorder.toLE.{0} Int
            (@PartialOrder.toPreorder.{0} Int
              (@SemilatticeInf.toPartialOrder.{0} Int
                (@Lattice.toSemilatticeInf.{0} Int
                  (@DistribLattice.toLattice.{0} Int (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder))))))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) r
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
    False
```

## Shao.OQ4.RademacherFiniteBasis.killedKernel_integral._proof_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (r : Int)
  (hr' :
    And
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r)
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder) r (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (And
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
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@LE.le.{0} Int
          (@Preorder.toLE.{0} Int
            (@PartialOrder.toPreorder.{0} Int
              (@SemilatticeInf.toPartialOrder.{0} Int
                (@Lattice.toSemilatticeInf.{0} Int
                  (@DistribLattice.toLattice.{0} Int (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder))))))
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) r
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
    False
```

## Shao.OQ4.RademacherFiniteBasis.modes

- 分类：public explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
(m : Nat) → Finset.{0} Nat
```

完整 definition value：

```lean
fun (m : Nat) =>
  @Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherFiniteBasis.modes.eq_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat),
  @Eq.{1} (Finset.{0} Nat) (Shao.OQ4.RademacherFiniteBasis.modes m)
    (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## Shao.OQ4.RademacherFiniteBasis.mu

- 分类：public explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
(m j : Nat) → Real
```

完整 definition value：

```lean
fun (m j : Nat) => Real.cos (Shao.OQ4.RademacherFiniteBasis.theta m j)
```

## Shao.OQ4.RademacherFiniteBasis.mu.eq_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.mu m j) (Real.cos (Shao.OQ4.RademacherFiniteBasis.theta m j))
```

## Shao.OQ4.RademacherFiniteBasis.mu_one

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.mu m (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (Shao.OQ4.RademacherCosine.rho m)
```

## Shao.OQ4.RademacherFiniteBasis.orthogonal

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (_hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (j k : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j)
  (hk :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) k),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherFiniteBasis.vector m j s) (Shao.OQ4.RademacherFiniteBasis.vector m k s))
    (@ite.{1} Real (@Eq.{1} Nat j k) (instDecidableEqNat j k)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## Shao.OQ4.RademacherFiniteBasis.phi

- 分类：public explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
(m j : Nat) → (w : Real) → Real
```

完整 definition value：

```lean
fun (m j : Nat) (w : Real) =>
  Real.sin
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherFiniteBasis.theta m j)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) w
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## Shao.OQ4.RademacherFiniteBasis.phi.eq_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat) (w : Real),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.phi m j w)
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherFiniteBasis.theta m j)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) w
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```

## Shao.OQ4.RademacherFiniteBasis.phi_one

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (w : Real),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.phi m (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
    (Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m) w))
```

## Shao.OQ4.RademacherFiniteBasis.phi_one._simp_1_1

- 分类：generated helper
- kind：`theorem`
- universes：`["u_2"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherFiniteBasis.phi_one._simp_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`["u_2"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherFiniteBasis.phi_one._simp_1_3

- 分类：generated helper
- kind：`theorem`
- universes：`["u_2"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherFiniteBasis.phi_one._simp_1_4

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## Shao.OQ4.RademacherFiniteBasis.phi_one._simp_1_5

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀}
  [@IsReduced.{u_1} M₀
      (@MulZeroClass.toZero.{u_1} M₀
        (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))
      (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst)))]
  (n : Nat)
  (h :
    @Ne.{u_1 + 1} M₀ a
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀
      (@HPow.hPow.{u_1, 0, u_1} M₀ Nat M₀
        (@instHPow.{u_1, 0} M₀ Nat
          (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst))))
        a n)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst))))))
    False
```

## Shao.OQ4.RademacherFiniteBasis.phi_one._simp_1_6

- 分类：generated helper
- kind：`theorem`
- universes：`["u_3"]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : Int),
  @Ne.{u_3 + 1} G₀ a
      (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_3} G₀
          (@MulZeroClass.toZero.{u_3} G₀
            (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
              (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))) →
    @Eq.{1} Prop
      (@Eq.{u_3 + 1} G₀
        (@HPow.hPow.{u_3, 0, u_3} G₀ Int G₀
          (@instHPow.{u_3, 0} G₀ Int
            (@ZPow.toPow.{u_3} G₀ (@DivInvMonoid.toZPow.{u_3} G₀ (@GroupWithZero.toDivInvMonoid.{u_3} G₀ inst))))
          a n)
        (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
          (@Zero.toOfNat0.{u_3} G₀
            (@MulZeroClass.toZero.{u_3} G₀
              (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
                (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))))
      False
```

## Shao.OQ4.RademacherFiniteBasis.phi_one._simp_1_7

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [@CharZero.{u_1} R inst] (n : Nat),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} R
      (@HAdd.hAdd.{u_1, u_1, u_1} R R R
        (@instHAdd.{u_1} R
          (@AddSemigroup.toAdd.{u_1} R
            (@AddMonoid.toAddSemigroup.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst))))
        (@Nat.cast.{u_1} R (@AddMonoidWithOne.toNatCast.{u_1} R inst) n)
        (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R inst))))
      (@OfNat.ofNat.{u_1} R (nat_lit 0)
        (@Zero.toOfNat0.{u_1} R
          (@AddZero.toZero.{u_1} R
            (@AddZeroClass.toAddZero.{u_1} R
              (@AddMonoid.toAddZeroClass.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst)))))))
    False
```

## Shao.OQ4.RademacherFiniteBasis.reconstruction

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m)
  (F : Int → Real) (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r),
  @Eq.{1} Real (F r)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherFiniteBasis.coefficient m j F) (Shao.OQ4.RademacherFiniteBasis.vector m j r))
```

## Shao.OQ4.RademacherFiniteBasis.square_norm

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (j : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) =>
      @HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherFiniteBasis.vector m j s) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
```

## Shao.OQ4.RademacherFiniteBasis.states

- 分类：public explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
(m : Nat) → Finset.{0} Int
```

完整 definition value：

```lean
fun (m : Nat) =>
  @Finset.Icc.{0} Int Int.instPreorder Int.instLocallyFiniteOrder
    (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) (@Nat.cast.{0} Int instNatCastInt m)
```

## Shao.OQ4.RademacherFiniteBasis.states.eq_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat),
  @Eq.{1} (Finset.{0} Int) (Shao.OQ4.RademacherFiniteBasis.states m)
    (@Finset.Icc.{0} Int Int.instPreorder Int.instLocallyFiniteOrder
      (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) (@Nat.cast.{0} Int instNatCastInt m))
```

## Shao.OQ4.RademacherFiniteBasis.theta

- 分类：public explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
(m j : Nat) → Real
```

完整 definition value：

```lean
fun (m j : Nat) =>
  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast j)
    (Shao.OQ4.RademacherCosine.angle m)
```

## Shao.OQ4.RademacherFiniteBasis.theta.eq_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.theta m j)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast j)
      (Shao.OQ4.RademacherCosine.angle m))
```

## Shao.OQ4.RademacherFiniteBasis.theta_one

- 分类：public explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.theta m (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (Shao.OQ4.RademacherCosine.angle m)
```

## Shao.OQ4.RademacherFiniteBasis.vector

- 分类：public explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
(m j : Nat) → (s : Int) → Real
```

完整 definition value：

```lean
fun (m j : Nat) (s : Int) => Shao.OQ4.RademacherFiniteBasis.phi m j (@Int.cast.{0} Real Real.instIntCast s)
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.at_index

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (s : Int)
  (hs :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) s),
  @Eq.{1} Int
    (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt m
      (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateIndex m s))
    s
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.at_index._proof_1_5

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m : Nat) (s : Int)
  (hs :
    And
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) s)
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder) s (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (@Eq.{1} Int
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@Nat.cast.{0} Int instNatCastInt
            (Int.toNat
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s
                (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        s) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.at_index._simp_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.at_mem

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j),
  @Membership.mem.{0, 0} Int (Finset.{0} Int)
    (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
    (Shao.OQ4.RademacherFiniteBasis.states m)
    (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt m j)
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.at_mem._proof_1_5

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat)
  (hj :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) j
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  Not
      (And
        (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
          (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m))
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt j)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt j)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt m))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.at_mem._simp_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum

- 分类：private explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
(m : Nat) → (n : Int) → Real
```

完整 definition value：

```lean
fun (m : Nat) (n : Int) =>
  @Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
    (Finset.range
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    fun (q : Nat) =>
    Real.cos
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast q)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Int.cast.{0} Real Real.instIntCast n)
            Real.pi)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum._proof_1))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast m)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum._proof_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext`

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum.eq_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (n : Int),
  @Eq.{1} Real (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum m n)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (q : Nat) =>
      Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast q)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Int.cast.{0} Real Real.instIntCast n) Real.pi)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum._proof_1))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@Nat.cast.{0} Real Real.instNatCast m)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum_nonzero

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (n : Int) (hn : @Ne.{1} Int n (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
  (hnl :
    @LT.lt.{0} Int Int.instLTInt
      (@Neg.neg.{0} Int Int.instNegInt
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt m))
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))))
      n)
  (hnu :
    @LT.lt.{0} Int Int.instLTInt n
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt m))
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))),
  @Eq.{1} Real (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum m n)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Neg.neg.{0} Real Real.instNeg
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (Real.cos
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Int.cast.{0} Real Real.instIntCast n) Real.pi))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum_zero

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat),
  @Eq.{1} Real
    (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cosSum m
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (@Nat.cast.{0} Real Real.instNatCast
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cut_phi

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat) (t : Int)
  (ht :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup t)
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))),
  @Eq.{1} Real
    (@ite.{1} Real
      (@LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup t)
        (@Nat.cast.{0} Int instNatCastInt m))
      (Int.decLe (@abs.{0} Int instLatticeInt Int.instAddGroup t) (@Nat.cast.{0} Int instNatCastInt m))
      (Shao.OQ4.RademacherFiniteBasis.phi m j (@Int.cast.{0} Real Real.instIntCast t))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (Shao.OQ4.RademacherFiniteBasis.phi m j (@Int.cast.{0} Real Real.instIntCast t))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cut_phi._proof_1_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m : Nat) (t : Int)
  (ht :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup t)
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
  (hcut :
    Not
      (@LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup t)
        (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (@Eq.{1} Int (@abs.{0} Int instLatticeInt Int.instAddGroup t)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cut_phi._proof_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m : Nat) (t : Int)
  (hpos : Not (@LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) t)),
  Not
      (@LT.lt.{0} Int
        (@Preorder.toLT.{0} Int
          (@PartialOrder.toPreorder.{0} Int
            (@SemilatticeInf.toPartialOrder.{0} Int (@Lattice.toSemilatticeInf.{0} Int instLatticeInt))))
        t
        (@OfNat.ofNat.{0} Int (nat_lit 0)
          (@Zero.toOfNat0.{0} Int
            (@NegZeroClass.toZero.{0} Int
              (@SubNegZeroMonoid.toNegZeroClass.{0} Int
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} Int
                  (@AddGroup.toSubtractionMonoid.{0} Int Int.instAddGroup))))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.cut_phi._proof_1_3

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m : Nat) (t : Int)
  (ht :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup t)
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
  (hcut :
    Not
      (@LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup t)
        (@Nat.cast.{0} Int instNatCastInt m)))
  (he :
    @Eq.{1} Int
      (@Neg.neg.{0} Int
        (@NegZeroClass.toNeg.{0} Int
          (@SubNegZeroMonoid.toNegZeroClass.{0} Int
            (@SubtractionMonoid.toSubNegZeroMonoid.{0} Int (@AddGroup.toSubtractionMonoid.{0} Int Int.instAddGroup))))
        t)
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))),
  Not
      (@Eq.{1} Int t
        (@Neg.neg.{0} Int Int.instNegInt
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.index_at

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j),
  @Eq.{1} Nat
    (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateIndex m
      (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt m j))
    j
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.index_at._proof_1_5

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m j : Nat)
  (hj :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) j
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  Not
      (@Eq.{1} Nat
        (Int.toNat
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt j)
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        j) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.index_at._simp_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.index_mem

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (s : Int)
  (hs :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) s),
  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
    (Shao.OQ4.RademacherFiniteBasis.modes m)
    (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateIndex m s)
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.index_mem._proof_1_5

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (s : Int)
  (hs :
    And
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) s)
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder) s (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (And
        (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Int.toNat
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))))
        (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
          (Int.toNat
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.index_mem._simp_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_integrable_finite

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat) (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace)
  [@MeasureTheory.IsFiniteMeasure.{0} Real Real.measurableSpace ν],
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
    Real Real.measurableSpace (Shao.OQ4.RademacherFiniteBasis.phi m j) ν
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_lower

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat),
  @Eq.{1} Real
    (Shao.OQ4.RademacherFiniteBasis.phi m j
      (@Neg.neg.{0} Real Real.instNeg
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_upper

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat),
  @Eq.{1} Real
    (Shao.OQ4.RademacherFiniteBasis.phi m j
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_upper._simp_1_1

- 分类：generated helper
- kind：`theorem`
- universes：`["u_2"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_upper._simp_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`["u_2"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_upper._simp_1_3

- 分类：generated helper
- kind：`theorem`
- universes：`["u_2"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_upper._simp_1_4

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_upper._simp_1_5

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀}
  [@IsReduced.{u_1} M₀
      (@MulZeroClass.toZero.{u_1} M₀
        (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))
      (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst)))]
  (n : Nat)
  (h :
    @Ne.{u_1 + 1} M₀ a
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀
      (@HPow.hPow.{u_1, 0, u_1} M₀ Nat M₀
        (@instHPow.{u_1, 0} M₀ Nat
          (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst))))
        a n)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst))))))
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_upper._simp_1_6

- 分类：generated helper
- kind：`theorem`
- universes：`["u_3"]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : Int),
  @Ne.{u_3 + 1} G₀ a
      (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_3} G₀
          (@MulZeroClass.toZero.{u_3} G₀
            (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
              (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))) →
    @Eq.{1} Prop
      (@Eq.{u_3 + 1} G₀
        (@HPow.hPow.{u_3, 0, u_3} G₀ Int G₀
          (@instHPow.{u_3, 0} G₀ Int
            (@ZPow.toPow.{u_3} G₀ (@DivInvMonoid.toZPow.{u_3} G₀ (@GroupWithZero.toDivInvMonoid.{u_3} G₀ inst))))
          a n)
        (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
          (@Zero.toOfNat0.{u_3} G₀
            (@MulZeroClass.toZero.{u_3} G₀
              (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
                (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))))
      False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.phi_upper._simp_1_7

- 分类：generated helper
- kind：`theorem`
- universes：`["u_1"]`
- instance：`false`
- axioms：`propext`

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [@CharZero.{u_1} R inst] (n : Nat),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} R
      (@HAdd.hAdd.{u_1, u_1, u_1} R R R
        (@instHAdd.{u_1} R
          (@AddSemigroup.toAdd.{u_1} R
            (@AddMonoid.toAddSemigroup.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst))))
        (@Nat.cast.{u_1} R (@AddMonoidWithOne.toNatCast.{u_1} R inst) n)
        (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R inst))))
      (@OfNat.ofNat.{u_1} R (nat_lit 0)
        (@Zero.toOfNat0.{u_1} R
          (@AddZero.toZero.{u_1} R
            (@AddZeroClass.toAddZero.{u_1} R
              (@AddMonoid.toAddZeroClass.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst)))))))
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.sin_ne_zero_small

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (t : Real) (hl : @LT.lt.{0} Real Real.instLT (@Neg.neg.{0} Real Real.instNeg Real.pi) t)
  (hu : @LT.lt.{0} Real Real.instLT t Real.pi)
  (ht : @Ne.{1} Real t (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @Ne.{1} Real (Real.sin t) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.sin_ne_zero_small._proof_1_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (k : Int)
  (hkl' :
    @LT.lt.{0} Int Int.instLTInt
      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))) k)
  (hku' : @LT.lt.{0} Int Int.instLTInt k (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))),
  Not (@Eq.{1} Int k (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) → False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt

- 分类：private explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：``

```lean
(m j : Nat) → Int
```

完整 definition value：

```lean
fun (m j : Nat) =>
  @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt j)
    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt.eq_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：``

```lean
∀ (m j : Nat),
  @Eq.{1} Int (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt m j)
    (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt j)
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateIndex

- 分类：private explicit def
- kind：`definition`
- universes：`[]`
- instance：`false`
- axioms：``

```lean
(m : Nat) → (s : Int) → Nat
```

完整 definition value：

```lean
fun (m : Nat) (s : Int) =>
  Int.toNat
    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateIndex.eq_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：``

```lean
∀ (m : Nat) (s : Int),
  @Eq.{1} Nat (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateIndex m s)
    (Int.toNat
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt m)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.sum_modes

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (f : Nat → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) => f j)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (q : Nat) =>
      f
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.sum_states

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m : Nat) (f : Int → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) => f s)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) =>
      f (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt m j))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.table_orthogonal

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j k : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j)
  (hk :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) k),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (q : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Real.sin
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast j) Real.pi)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast m)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
            (@Nat.cast.{0} Real Real.instNatCast q)))
        (Real.sin
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast k) Real.pi)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast m)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
            (@Nat.cast.{0} Real Real.instNatCast q))))
    (@ite.{1} Real (@Eq.{1} Nat j k) (instDecidableEqNat j k)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.table_orthogonal._proof_1_1

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m j k : Nat)
  (hj' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) j
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) k
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  @Eq.{1} Int
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt j)
        (@Nat.cast.{0} Int instNatCastInt k))
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.table_orthogonal._proof_1_2

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m j k : Nat)
  (hj' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) j
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) k
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  Not
      (@LT.lt.{0} Int Int.instLTInt
        (@Neg.neg.{0} Int Int.instNegInt
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt m))
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt j)
          (@Nat.cast.{0} Int instNatCastInt k))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.table_orthogonal._proof_1_3

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m j k : Nat)
  (hj' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) j
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) k
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  Not
      (@LT.lt.{0} Int Int.instLTInt
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt j)
          (@Nat.cast.{0} Int instNatCastInt k))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt m))
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.table_orthogonal._proof_1_4

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m j k : Nat) (heq : Not (@Eq.{1} Nat j k)),
  @Eq.{1} Int
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt j)
        (@Nat.cast.{0} Int instNatCastInt k))
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.table_orthogonal._proof_1_5

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m j k : Nat)
  (hj' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) j
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) k
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  Not
      (@LT.lt.{0} Int Int.instLTInt
        (@Neg.neg.{0} Int Int.instNegInt
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt m))
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))))
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt j)
          (@Nat.cast.{0} Int instNatCastInt k))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.table_orthogonal._proof_1_6

- 分类：generated helper
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Quot.sound`

```lean
∀ (m j k : Nat)
  (hj' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) j
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk' :
    And
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
      (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) k
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  Not
      (@LT.lt.{0} Int Int.instLTInt
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt j)
          (@Nat.cast.{0} Int instNatCastInt k))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt m))
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.telescope_cos

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (n : Nat) (x : Real),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (Real.sin
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            x
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range n) fun (q : Nat) =>
        Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast q)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            x)))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast n)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          x))
      (Real.sin
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) x
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.vector_at

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j q : Nat),
  @Eq.{1} Real
    (Shao.OQ4.RademacherFiniteBasis.vector m j
      (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt m q))
    (Real.sin
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast j)
            Real.pi)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast m)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
        (@Nat.cast.{0} Real Real.instNatCast q)))
```

## _private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.vector_symmetry

- 分类：private explicit theorem
- kind：`theorem`
- universes：`[]`
- instance：`false`
- axioms：`propext, Classical.choice, Quot.sound`

```lean
∀ (m j : Nat) (r : Int)
  (hr :
    @Membership.mem.{0, 0} Int (Finset.{0} Int)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int))
      (Shao.OQ4.RademacherFiniteBasis.states m) r),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.vector m j r)
    (Shao.OQ4.RademacherFiniteBasis.vector m
      (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateIndex m r)
      (_private.Shao.OQ4.RademacherFiniteBasis.0.Shao.OQ4.RademacherFiniteBasis.stateAt m j))
```
