# EnergyJointTransport canonical 声明账

来源：实际 38 模块导入环境中，owner 为 Shao.OQ4.EnergyJointTransport 的每个常量，包含私有及生成声明。所有完整类型、宇宙参数和传递公理如下。

显式公开定理 6；定义 9；显式私有引理 3；生成定理 18；实际模块自有常量 36。

| 分类 | 名称 | 种类 | 宇宙参数 | 公理 |
|---|---|---|---|---|
| explicit_definition | `Shao.OQ4.energyJointBaseProbability` | definition | `[]` | propext, Classical.choice, Quot.sound |
| explicit_definition | `Shao.OQ4.energyJointCenteredProbability` | definition | `[]` | propext, Classical.choice, Quot.sound |
| explicit_definition | `Shao.OQ4.energyJointErrorLimits` | definition | `[]` | propext, Classical.choice, Quot.sound |
| explicit_definition | `Shao.OQ4.energyJointFiniteConclusion` | definition | `[]` | propext, Classical.choice, Quot.sound |
| explicit_definition | `Shao.OQ4.energyJointIIDConclusion` | definition | `[u, v, w]` | propext, Classical.choice, Quot.sound |
| explicit_definition | `Shao.OQ4.energyJointIIDTail` | definition | `[u, v, w]` | propext, Classical.choice, Quot.sound |
| explicit_definition | `Shao.OQ4.energyJointIntegral` | definition | `[]` | propext, Classical.choice, Quot.sound |
| explicit_definition | `Shao.OQ4.energyJointNormalizationLimits` | definition | `[]` | propext, Classical.choice, Quot.sound |
| explicit_definition | `Shao.OQ4.energyJointSequenceConclusion` | definition | `[]` | propext, Classical.choice, Quot.sound |
| explicit_private_theorem | `_private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_pow_eq_exp_log` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| explicit_private_theorem | `_private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_relative_abs` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| explicit_private_theorem | `_private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_zero_of_abs_le` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| explicit_public_theorem | `Shao.OQ4.energyJointTransport_common_bounds` | theorem | `[u, v, w]` | propext, Classical.choice, Quot.sound |
| explicit_public_theorem | `Shao.OQ4.energyJointTransport_error_limits` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| explicit_public_theorem | `Shao.OQ4.energyJointTransport_finite_of_e2` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| explicit_public_theorem | `Shao.OQ4.energyJointTransport_iid_of_e2` | theorem | `[u, v, w]` | propext, Classical.choice, Quot.sound |
| explicit_public_theorem | `Shao.OQ4.energyJointTransport_normalization_limits` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| explicit_public_theorem | `Shao.OQ4.energyJointTransport_sequence_of_e2` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| generated_theorem | `Shao.OQ4.energyJointBaseProbability.eq_1` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| generated_theorem | `Shao.OQ4.energyJointCenteredProbability.eq_1` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| generated_theorem | `Shao.OQ4.energyJointIntegral.eq_1` | theorem | `[]` | propext, Classical.choice, Quot.sound |
| generated_theorem | `Shao.OQ4.energyJointTransport_error_limits._simp_1_1` | theorem | `[u_2]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_error_limits._simp_1_2` | theorem | `[u_2]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_error_limits._simp_1_3` | theorem | `[u_2]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_error_limits._simp_1_4` | theorem | `[u_1]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_error_limits._simp_1_5` | theorem | `[u_1]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_error_limits._simp_1_6` | theorem | `[u_3]` | propext, Classical.choice, Quot.sound |
| generated_theorem | `Shao.OQ4.energyJointTransport_error_limits._simp_1_7` | theorem | `[u_1]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_normalization_limits._simp_1_1` | theorem | `[u_2]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_normalization_limits._simp_1_2` | theorem | `[u_2]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_normalization_limits._simp_1_3` | theorem | `[u_2]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_normalization_limits._simp_1_4` | theorem | `[u_1]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_normalization_limits._simp_1_5` | theorem | `[u_1]` | propext |
| generated_theorem | `Shao.OQ4.energyJointTransport_normalization_limits._simp_1_6` | theorem | `[u_3]` | propext, Classical.choice, Quot.sound |
| generated_theorem | `Shao.OQ4.energyJointTransport_normalization_limits._simp_1_7` | theorem | `[u_1]` | propext |
| generated_theorem | `Shao.OQ4.energyRelativePathError2.eq_1` | theorem | `[]` | propext, Classical.choice, Quot.sound |

## Shao.OQ4.energyJointBaseProbability

分类：explicit_definition；种类：definition；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointBaseProbability :
@MeasureTheory.Measure.{0} Real Real.measurableSpace → Nat → Real → Real → Real
```

## Shao.OQ4.energyJointCenteredProbability

分类：explicit_definition；种类：definition；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointCenteredProbability :
@MeasureTheory.Measure.{0} Real Real.measurableSpace → Nat → Real → Real → Real → Real
```

## Shao.OQ4.energyJointErrorLimits

分类：explicit_definition；种类：definition；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointErrorLimits :
Real → Real → (Nat → Real) → (Nat → Nat) → Prop
```

## Shao.OQ4.energyJointFiniteConclusion

分类：explicit_definition；种类：definition；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointFiniteConclusion :
@MeasureTheory.Measure.{0} Real Real.measurableSpace → Real → Real → Real → Real → Real → Nat → Prop
```

## Shao.OQ4.energyJointIIDConclusion

分类：explicit_definition；种类：definition；宇宙：`[u, v, w]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointIIDConclusion :
{Ων : Type u} →
  {Ωμ : Type v} →
    {Ωθ : Type w} →
      [inst : MeasurableSpace.{u} Ων] →
        [inst_1 : MeasurableSpace.{v} Ωμ] →
          [inst_2 : MeasurableSpace.{w} Ωθ] →
            @MeasureTheory.Measure.{u} Ων inst →
              @MeasureTheory.Measure.{v} Ωμ inst_1 →
                @MeasureTheory.Measure.{w} Ωθ inst_2 →
                  @MeasureTheory.Measure.{0} Real Real.measurableSpace →
                    Real →
                      Real →
                        Real →
                          Real →
                            Real → {n : Nat} → (Fin n → Ων → Real) → (Fin n → Ωμ → Real) → (Fin n → Ωθ → Real) → Prop
```

## Shao.OQ4.energyJointIIDTail

分类：explicit_definition；种类：definition；宇宙：`[u, v, w]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointIIDTail :
@MeasureTheory.Measure.{0} Real Real.measurableSpace →
  Real → Real → (Nat → Real) → (Nat → Real) → (Nat → Real) → Prop
```

## Shao.OQ4.energyJointIntegral

分类：explicit_definition；种类：definition；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointIntegral :
@MeasureTheory.Measure.{0} Real Real.measurableSpace → Nat → Real → Real → Real
```

## Shao.OQ4.energyJointNormalizationLimits

分类：explicit_definition；种类：definition；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointNormalizationLimits :
@MeasureTheory.Measure.{0} Real Real.measurableSpace →
  (Nat → Real) → (Nat → Real) → (Nat → Real) → (Nat → Nat) → Prop
```

## Shao.OQ4.energyJointSequenceConclusion

分类：explicit_definition；种类：definition；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointSequenceConclusion :
@MeasureTheory.Measure.{0} Real Real.measurableSpace →
  Real → Real → (Nat → Real) → (Nat → Real) → (Nat → Real) → (Nat → Nat) → Prop
```

## _private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_pow_eq_exp_log

分类：explicit_private_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
_private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_pow_eq_exp_log :
∀ (x : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x →
    ∀ (n : Nat),
      @Eq.{1} Real
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x n)
        (Real.exp
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast n)
            (Real.log x)))
```

## _private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_relative_abs

分类：explicit_private_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
_private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_relative_abs :
∀ {a x r : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r →
    @LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Real.exp (@Neg.neg.{0} Real Real.instNeg a)) r)
        x →
      @LE.le.{0} Real Real.instLE x
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Real.exp a) r) →
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) x r))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (Real.exp a)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            r)
```

## _private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_zero_of_abs_le

分类：explicit_private_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
_private.Shao.OQ4.EnergyJointTransport.0.Shao.OQ4.joint_zero_of_abs_le :
∀ {f g : Nat → Real},
  @Filter.Tendsto.{0, 0} Nat Real g (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    @Filter.Eventually.{0} Nat
        (fun j => @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (f j)) (g j))
        (@Filter.atTop.{0} Nat Nat.instPreorder) →
      @Filter.Tendsto.{0, 0} Nat Real f (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## Shao.OQ4.energyJointTransport_common_bounds

分类：explicit_public_theorem；种类：theorem；宇宙：`[u, v, w]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointTransport_common_bounds :
∀ (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace)
  [@MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace ν] (M T : Real) (h s : Nat → Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T →
      @Filter.Tendsto.{0, 0} Nat Real h (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@Filter.atTop.{0} Real Real.instPreorder) →
        (∀ (j : Nat), @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (s j)) T) →
          @MeasureTheory.Integrable.{0, 0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                  (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
              Real Real.measurableSpace
              (fun x =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              ν →
            @MeasureTheory.Integrable.{0, 0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                    (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
                Real Real.measurableSpace
                (fun x =>
                  @HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@abs.{0} Real Real.lattice Real.instAddGroup x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                ν →
              @Eq.{1} Real
                  (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    Real.measurableSpace ν fun x =>
                    @HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                @Eq.{1} Real
                    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                      Real.measurableSpace ν fun x => x)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @LE.le.{0} Real Real.instLE
                      (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                        Real.measurableSpace ν fun x =>
                        @HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@abs.{0} Real Real.lattice Real.instAddGroup x)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      M →
                    ∃ θ,
                      And
                        (∀ (j : Nat),
                          @LT.lt.{0} Real Real.instLT (h j) (Shao.OQ4.energyE2Threshold M T) →
                            @Eq.{1} Real (θ j)
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                        (And
                          (@Filter.Eventually.{0} Nat
                            (fun j =>
                              And (Shao.OQ4.energyE2Conclusion ν M T (h j) (s j) (θ j))
                                (∀ (m : Nat), Shao.OQ4.energyRelativePathConclusion ν M T (h j) (s j) (θ j) m))
                            (@Filter.atTop.{0} Nat Nat.instPreorder))
                          (And (Shao.OQ4.energyJointIIDTail.{u, v, w} ν M T h s θ)
                            (∀ (n : Nat → Nat),
                              @Filter.Tendsto.{0, 0} Nat Real
                                  (fun j =>
                                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                      (@Nat.cast.{0} Real Real.instNatCast (n j))
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat
                                          (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                        (h j) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                                  (@nhds.{0} Real
                                    (@UniformSpace.toTopologicalSpace.{0} Real
                                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                                Shao.OQ4.energyJointSequenceConclusion ν M T h s θ n)))
```

## Shao.OQ4.energyJointTransport_error_limits

分类：explicit_public_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointTransport_error_limits :
∀ (M T : Real) (h : Nat → Real) (n : Nat → Nat),
  @Filter.Tendsto.{0, 0} Nat Real h (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@Filter.atTop.{0} Real Real.instPreorder) →
    @Filter.Tendsto.{0, 0} Nat Real
        (fun j =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast (n j))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (h j)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
      Shao.OQ4.energyJointErrorLimits M T h n
```

## Shao.OQ4.energyJointTransport_finite_of_e2

分类：explicit_public_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointTransport_finite_of_e2 :
∀ (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace)
  [@MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace ν] (M T h s θ : Real) (n : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T →
      @LE.le.{0} Real Real.instLE (Shao.OQ4.energyE2Threshold M T) h →
        @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup s) T →
          @MeasureTheory.Integrable.{0, 0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                  (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
              Real Real.measurableSpace
              (fun x =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              ν →
            @MeasureTheory.Integrable.{0, 0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                    (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
                Real Real.measurableSpace
                (fun x =>
                  @HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@abs.{0} Real Real.lattice Real.instAddGroup x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                ν →
              @Eq.{1} Real
                  (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    Real.measurableSpace ν fun x =>
                    @HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                @Eq.{1} Real
                    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                      Real.measurableSpace ν fun x => x)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @LE.le.{0} Real Real.instLE
                      (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                        Real.measurableSpace ν fun x =>
                        @HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@abs.{0} Real Real.lattice Real.instAddGroup x)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      M →
                    Shao.OQ4.energyE2Conclusion ν M T h s θ → Shao.OQ4.energyJointFiniteConclusion ν M T h s θ n
```

## Shao.OQ4.energyJointTransport_iid_of_e2

分类：explicit_public_theorem；种类：theorem；宇宙：`[u, v, w]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointTransport_iid_of_e2 :
∀ {Ων : Type u} {Ωμ : Type v} {Ωθ : Type w} [inst : MeasurableSpace.{u} Ων] [inst_1 : MeasurableSpace.{v} Ωμ]
  [inst_2 : MeasurableSpace.{w} Ωθ] (pν : @MeasureTheory.Measure.{u} Ων inst)
  [@MeasureTheory.IsProbabilityMeasure.{u} Ων inst pν] (pμ : @MeasureTheory.Measure.{v} Ωμ inst_1)
  [@MeasureTheory.IsProbabilityMeasure.{v} Ωμ inst_1 pμ] (pθ : @MeasureTheory.Measure.{w} Ωθ inst_2)
  [@MeasureTheory.IsProbabilityMeasure.{w} Ωθ inst_2 pθ] (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace)
  [@MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace ν] (M T h s θ : Real) (n : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T →
      @LE.le.{0} Real Real.instLE (Shao.OQ4.energyE2Threshold M T) h →
        @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup s) T →
          @MeasureTheory.Integrable.{0, 0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                  (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
              Real Real.measurableSpace
              (fun x =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              ν →
            @MeasureTheory.Integrable.{0, 0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                    (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
                Real Real.measurableSpace
                (fun x =>
                  @HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@abs.{0} Real Real.lattice Real.instAddGroup x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                ν →
              @Eq.{1} Real
                  (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    Real.measurableSpace ν fun x =>
                    @HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                @Eq.{1} Real
                    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                      Real.measurableSpace ν fun x => x)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @LE.le.{0} Real Real.instLE
                      (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                        Real.measurableSpace ν fun x =>
                        @HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@abs.{0} Real Real.lattice Real.instAddGroup x)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      M →
                    Shao.OQ4.energyE2Conclusion ν M T h s θ →
                      ∀ (X : Fin n → Ων → Real),
                        (∀ (i : Fin n), @Measurable.{u, 0} Ων Real inst Real.measurableSpace (X i)) →
                          @ProbabilityTheory.iIndepFun.{u, 0, 0} Ων (Fin n) inst (fun x => Real)
                              (fun x => Real.measurableSpace) X pν →
                            (∀ (i : Fin n),
                                @ProbabilityTheory.IdentDistrib.{u, 0, 0} Ων Real Real inst Real.measurableSpace
                                  Real.measurableSpace (X i) (@id.{1} Real) pν ν) →
                              ∀ (Y : Fin n → Ωμ → Real),
                                (∀ (i : Fin n), @Measurable.{v, 0} Ωμ Real inst_1 Real.measurableSpace (Y i)) →
                                  @ProbabilityTheory.iIndepFun.{v, 0, 0} Ωμ (Fin n) inst_1 (fun x => Real)
                                      (fun x => Real.measurableSpace) Y pμ →
                                    (∀ (i : Fin n),
                                        @ProbabilityTheory.IdentDistrib.{v, 0, 0} Ωμ Real Real inst_1
                                          Real.measurableSpace Real.measurableSpace (Y i) (@id.{1} Real) pμ
                                          (Shao.OQ4.energyTiltedLaw ν h s)) →
                                      ∀ (W : Fin n → Ωθ → Real),
                                        (∀ (i : Fin n), @Measurable.{w, 0} Ωθ Real inst_2 Real.measurableSpace (W i)) →
                                          @ProbabilityTheory.iIndepFun.{w, 0, 0} Ωθ (Fin n) inst_2 (fun x => Real)
                                              (fun x => Real.measurableSpace) W pθ →
                                            (∀ (i : Fin n),
                                                @ProbabilityTheory.IdentDistrib.{w, 0, 0} Ωθ Real Real inst_2
                                                  Real.measurableSpace Real.measurableSpace (W i) (@id.{1} Real) pθ
                                                  (Shao.OQ4.energyLinearTiltLaw ν h s θ)) →
                                              @Shao.OQ4.energyJointIIDConclusion.{u, v, w} Ων Ωμ Ωθ inst inst_1 inst_2
                                                pν pμ pθ ν M T h s θ n X Y W
```

## Shao.OQ4.energyJointTransport_normalization_limits

分类：explicit_public_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointTransport_normalization_limits :
∀ (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace)
  [@MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace ν] (M T : Real) (h s θ : Nat → Real)
  (n : Nat → Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T →
      @Filter.Tendsto.{0, 0} Nat Real h (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@Filter.atTop.{0} Real Real.instPreorder) →
        (∀ (j : Nat), @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (s j)) T) →
          @MeasureTheory.Integrable.{0, 0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                  (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
              Real Real.measurableSpace
              (fun x =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              ν →
            @MeasureTheory.Integrable.{0, 0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                    (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
                Real Real.measurableSpace
                (fun x =>
                  @HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@abs.{0} Real Real.lattice Real.instAddGroup x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                ν →
              @Eq.{1} Real
                  (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    Real.measurableSpace ν fun x =>
                    @HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                @Eq.{1} Real
                    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                      Real.measurableSpace ν fun x => x)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @LE.le.{0} Real Real.instLE
                      (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                        Real.measurableSpace ν fun x =>
                        @HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@abs.{0} Real Real.lattice Real.instAddGroup x)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      M →
                    @Filter.Eventually.{0} Nat (fun j => Shao.OQ4.energyE2Conclusion ν M T (h j) (s j) (θ j))
                        (@Filter.atTop.{0} Nat Nat.instPreorder) →
                      @Filter.Tendsto.{0, 0} Nat Real
                          (fun j =>
                            @HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@Nat.cast.{0} Real Real.instNatCast (n j))
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat
                                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                (h j) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@Filter.atTop.{0} Nat Nat.instPreorder)
                          (@nhds.{0} Real
                            (@UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                        Shao.OQ4.energyJointNormalizationLimits ν h s θ n
```

## Shao.OQ4.energyJointTransport_sequence_of_e2

分类：explicit_public_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointTransport_sequence_of_e2 :
∀ (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace)
  [@MeasureTheory.IsProbabilityMeasure.{0} Real Real.measurableSpace ν] (M T : Real) (h s θ : Nat → Real)
  (n : Nat → Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T →
      @Filter.Tendsto.{0, 0} Nat Real h (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@Filter.atTop.{0} Real Real.instPreorder) →
        (∀ (j : Nat), @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (s j)) T) →
          @MeasureTheory.Integrable.{0, 0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                  (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                          (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
              Real Real.measurableSpace
              (fun x =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              ν →
            @MeasureTheory.Integrable.{0, 0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@ESeminormedAddMonoid.toContinuousENorm.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@SeminormedAddGroup.toESeminormedAddMonoid.{0} Real
                    (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)))))))
                Real Real.measurableSpace
                (fun x =>
                  @HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@abs.{0} Real Real.lattice Real.instAddGroup x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                ν →
              @Eq.{1} Real
                  (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    Real.measurableSpace ν fun x =>
                    @HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                @Eq.{1} Real
                    (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                      Real.measurableSpace ν fun x => x)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @LE.le.{0} Real Real.instLE
                      (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                        Real.measurableSpace ν fun x =>
                        @HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@abs.{0} Real Real.lattice Real.instAddGroup x)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      M →
                    @Filter.Eventually.{0} Nat (fun j => Shao.OQ4.energyE2Conclusion ν M T (h j) (s j) (θ j))
                        (@Filter.atTop.{0} Nat Nat.instPreorder) →
                      @Filter.Tendsto.{0, 0} Nat Real
                          (fun j =>
                            @HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@Nat.cast.{0} Real Real.instNatCast (n j))
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat
                                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                (h j) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@Filter.atTop.{0} Nat Nat.instPreorder)
                          (@nhds.{0} Real
                            (@UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                        Shao.OQ4.energyJointSequenceConclusion ν M T h s θ n
```

## Shao.OQ4.energyJointBaseProbability.eq_1

分类：generated_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointBaseProbability.eq_1 :
∀ (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace) (n : Nat) (h s : Real),
  @Eq.{1} Real (Shao.OQ4.energyJointBaseProbability ν n h s)
    (@MeasureTheory.Measure.real.{0} (Fin n → Real)
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun i => Real.measurableSpace)
      (@MeasureTheory.Measure.pi.{0, 0} (Fin n) (fun x => Real) (Fin.fintype n) (fun i => Real.measurableSpace) fun x =>
        Shao.OQ4.energyTiltedLaw ν h s)
      (@Shao.closedStrip n h))
```

## Shao.OQ4.energyJointCenteredProbability.eq_1

分类：generated_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointCenteredProbability.eq_1 :
∀ (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace) (n : Nat) (h s θ : Real),
  @Eq.{1} Real (Shao.OQ4.energyJointCenteredProbability ν n h s θ)
    (@MeasureTheory.Measure.real.{0} (Fin n → Real)
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun i => Real.measurableSpace)
      (@MeasureTheory.Measure.pi.{0, 0} (Fin n) (fun x => Real) (Fin.fintype n) (fun i => Real.measurableSpace) fun x =>
        Shao.OQ4.energyLinearTiltLaw ν h s θ)
      (@Shao.closedStrip n h))
```

## Shao.OQ4.energyJointIntegral.eq_1

分类：generated_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointIntegral.eq_1 :
∀ (ν : @MeasureTheory.Measure.{0} Real Real.measurableSpace) (n : Nat) (h s : Real),
  @Eq.{1} Real (Shao.OQ4.energyJointIntegral ν n h s)
    (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun x => Real) fun i => Real.measurableSpace)
      (@MeasureTheory.Measure.pi.{0, 0} (Fin n) (fun x => Real) (Fin.fintype n) (fun i => Real.measurableSpace) fun x =>
        ν)
      fun a => @Shao.OQ4.energyPathIntegrand n h s a)
```

## Shao.OQ4.energyJointTransport_error_limits._simp_1_1

分类：generated_theorem；种类：theorem；宇宙：`[u_2]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_error_limits._simp_1_1 :
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.energyJointTransport_error_limits._simp_1_2

分类：generated_theorem；种类：theorem；宇宙：`[u_2]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_error_limits._simp_1_2 :
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.energyJointTransport_error_limits._simp_1_3

分类：generated_theorem；种类：theorem；宇宙：`[u_2]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_error_limits._simp_1_3 :
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.energyJointTransport_error_limits._simp_1_4

分类：generated_theorem；种类：theorem；宇宙：`[u_1]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_error_limits._simp_1_4 :
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀},
  @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)) →
    @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)) →
      @Eq.{1} Prop
        (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
          (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
        False
```

## Shao.OQ4.energyJointTransport_error_limits._simp_1_5

分类：generated_theorem；种类：theorem；宇宙：`[u_1]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_error_limits._simp_1_5 :
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀}
  [@IsReduced.{u_1} M₀
      (@MulZeroClass.toZero.{u_1} M₀
        (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))
      (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst)))]
  (n : Nat),
  @Ne.{u_1 + 1} M₀ a
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst))))) →
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

## Shao.OQ4.energyJointTransport_error_limits._simp_1_6

分类：generated_theorem；种类：theorem；宇宙：`[u_3]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointTransport_error_limits._simp_1_6 :
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

## Shao.OQ4.energyJointTransport_error_limits._simp_1_7

分类：generated_theorem；种类：theorem；宇宙：`[u_1]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_error_limits._simp_1_7 :
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

## Shao.OQ4.energyJointTransport_normalization_limits._simp_1_1

分类：generated_theorem；种类：theorem；宇宙：`[u_2]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_normalization_limits._simp_1_1 :
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.energyJointTransport_normalization_limits._simp_1_2

分类：generated_theorem；种类：theorem；宇宙：`[u_2]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_normalization_limits._simp_1_2 :
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.energyJointTransport_normalization_limits._simp_1_3

分类：generated_theorem；种类：theorem；宇宙：`[u_2]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_normalization_limits._simp_1_3 :
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.energyJointTransport_normalization_limits._simp_1_4

分类：generated_theorem；种类：theorem；宇宙：`[u_1]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_normalization_limits._simp_1_4 :
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀},
  @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)) →
    @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)) →
      @Eq.{1} Prop
        (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
          (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
        False
```

## Shao.OQ4.energyJointTransport_normalization_limits._simp_1_5

分类：generated_theorem；种类：theorem；宇宙：`[u_1]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_normalization_limits._simp_1_5 :
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀}
  [@IsReduced.{u_1} M₀
      (@MulZeroClass.toZero.{u_1} M₀
        (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))
      (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst)))]
  (n : Nat),
  @Ne.{u_1 + 1} M₀ a
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst))))) →
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

## Shao.OQ4.energyJointTransport_normalization_limits._simp_1_6

分类：generated_theorem；种类：theorem；宇宙：`[u_3]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyJointTransport_normalization_limits._simp_1_6 :
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

## Shao.OQ4.energyJointTransport_normalization_limits._simp_1_7

分类：generated_theorem；种类：theorem；宇宙：`[u_1]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext。

```lean
Shao.OQ4.energyJointTransport_normalization_limits._simp_1_7 :
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

## Shao.OQ4.energyRelativePathError2.eq_1

分类：generated_theorem；种类：theorem；宇宙：`[]`；owner：`Shao.OQ4.EnergyJointTransport`。

传递公理：propext, Classical.choice, Quot.sound。

```lean
Shao.OQ4.energyRelativePathError2.eq_1 :
∀ (M T : Real) (n : Nat) (h : Real),
  @Eq.{1} Real (Shao.OQ4.energyRelativePathError2 M T n h)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Shao.OQ4.energyE2Constant M T) h)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.energyE2Constant M T)
          (@Nat.cast.{0} Real Real.instNatCast n))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
```
