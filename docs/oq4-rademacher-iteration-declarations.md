# RademacherIteration: complete canonical declarations

Source SHA256: `dd8986ebe885d4f5cbe9ea021ee6b193ab927e066b9a15f2e5e22e0d030ad360` (8111 bytes).
Actual full-source module: `Shao.OQ4.RademacherIteration`.
Selection: every constant whose full-source `getModuleIdxFor?` is `none`; no name or namespace filter.
The same 9 declarations are owned by the canonical imported module. Names, kinds, universes, complete types, definition values, instance registration and axiom sets match exactly.
Counts: 7 explicitly public theorems, 1 public definition, 1 private theorem; 0 generated declarations; 0 registered instances.
All39 selection: actual owner in the 39 OQ4 modules OR raw/user namespace `Shao.OQ4`; 768 declarations, including all 9 new declarations and 759 old declarations.

## `Shao.OQ4.RademacherIteration.grid`

- User name: `Shao.OQ4.RademacherIteration.grid`.
- Kind: `definition`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
(m : Nat) → Set.{0} Real
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app (Lean.Expr.const `Set [Lean.Level.zero]) (Lean.Expr.const `Real []))
  (Lean.BinderInfo.default)
```

Complete definition value (`pp.all`):

```lean
fun (m : Nat) =>
  @Set.ofPred.{0} Real fun (w : Real) =>
    @Exists.{1} Int fun (s : Int) =>
      And (@LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) s)
        (And (@LE.le.{0} Int Int.instLEInt s (@Nat.cast.{0} Int instNatCastInt m))
          (@Eq.{1} Real w (@Int.cast.{0} Real Real.instIntCast s)))
```

Raw definition value:

```text
Lean.Expr.lam
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Set.ofPred [Lean.Level.zero]) (Lean.Expr.const `Real []))
    (Lean.Expr.lam
      `w
      (Lean.Expr.const `Real [])
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Int []))
        (Lean.Expr.lam
          `s
          (Lean.Expr.const `Int [])
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `And [])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                    (Lean.Expr.const `Int.instLEInt []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instNegInt []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                        (Lean.Expr.const `instNatCastInt []))
                      (Lean.Expr.bvar 2))))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `And [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instLEInt []))
                    (Lean.Expr.bvar 0))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `instNatCastInt []))
                    (Lean.Expr.bvar 2))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Real []))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Int.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instIntCast []))
                  (Lean.Expr.bvar 0)))))
          (Lean.BinderInfo.default)))
      (Lean.BinderInfo.default)))
  (Lean.BinderInfo.default)
```

## `Shao.OQ4.RademacherIteration.grid_finite`

- User name: `Shao.OQ4.RademacherIteration.grid_finite`.
- Kind: `theorem`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
∀ (m : Nat), @Set.Finite.{0} Real (Shao.OQ4.RademacherIteration.grid m)
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Set.Finite [Lean.Level.zero]) (Lean.Expr.const `Real []))
    (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherIteration.grid []) (Lean.Expr.bvar 0)))
  (Lean.BinderInfo.default)
```

## `Shao.OQ4.RademacherIteration.killedAction_principal_power`

- User name: `Shao.OQ4.RademacherIteration.killedAction_principal_power`.
- Kind: `theorem`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hrlo : @LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r)
  (hrhi : @LE.le.{0} Int Int.instLEInt r (@Nat.cast.{0} Int instNatCastInt m)) (n : Nat),
  @Eq.{1} Real
    (@Shao.OQ4.killedAction Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h n
      (fun (w : Real) =>
        Real.cos
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m) w))
      (@Int.cast.{0} Real Real.instIntCast r))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherCosine.rho m) n)
      (Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m)
          (@Int.cast.{0} Real Real.instIntCast r))))
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `hm
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLENat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 1)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
      (Lean.Expr.bvar 0))
    (Lean.Expr.forallE
      `h
      (Lean.Expr.const `Real [])
      (Lean.Expr.forallE
        `hmh
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Real []))
              (Lean.Expr.const `Real.instLE []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instNatCast []))
              (Lean.Expr.bvar 2)))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          `hhm
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instLT []))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instAdd [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instNatCast []))
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.lit (Lean.Literal.natVal 1)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `One.toOfNat1 [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.const `Real.instOne [])))))
          (Lean.Expr.forallE
            `r
            (Lean.Expr.const `Int [])
            (Lean.Expr.forallE
              `hrlo
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                    (Lean.Expr.const `Int.instLEInt []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instNegInt []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                        (Lean.Expr.const `instNatCastInt []))
                      (Lean.Expr.bvar 5))))
                (Lean.Expr.bvar 0))
              (Lean.Expr.forallE
                `hrhi
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instLEInt []))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `instNatCastInt []))
                    (Lean.Expr.bvar 6)))
                (Lean.Expr.forallE
                  `n
                  (Lean.Expr.const `Nat [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Shao.OQ4.killedAction [])
                                  (Lean.Expr.const `Shao.OQ4.RademacherCosine.law []))
                                (Lean.Expr.const `Shao.OQ4.RademacherCosine.law_isProbabilityMeasure []))
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 0))
                          (Lean.Expr.lam
                            `w
                            (Lean.Expr.const `Real [])
                            (Lean.Expr.app
                              (Lean.Expr.const `Real.cos [])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `HMul.hMul
                                            [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `Real []))
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `instHMul [Lean.Level.zero])
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real.instMul [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Shao.OQ4.RademacherCosine.angle [])
                                    (Lean.Expr.bvar 9)))
                                (Lean.Expr.bvar 0)))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Int.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real.instIntCast []))
                          (Lean.Expr.bvar 3))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real.instMul [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Nat []))
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Nat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real.instMonoid [])))))
                            (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherCosine.rho []) (Lean.Expr.bvar 8)))
                          (Lean.Expr.bvar 0)))
                      (Lean.Expr.app
                        (Lean.Expr.const `Real.cos [])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real.instMul [])))
                            (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherCosine.angle []) (Lean.Expr.bvar 8)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Int.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real.instIntCast []))
                            (Lean.Expr.bvar 3))))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
```

## `Shao.OQ4.RademacherIteration.killedIterKernel_ae_grid`

- User name: `Shao.OQ4.RademacherIteration.killedIterKernel_ae_grid`.
- Kind: `theorem`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hrlo : @LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r)
  (hrhi : @LE.le.{0} Int Int.instLEInt r (@Nat.cast.{0} Int instNatCastInt m)) (n : Nat),
  @Filter.Eventually.{0} Real
    (fun (w : Real) =>
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) (Shao.OQ4.RademacherIteration.grid m) w)
    (@MeasureTheory.ae.{0, 0} Real (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.instFunLike.{0} Real Real.measurableSpace)
      (@MeasureTheory.Measure.instOuterMeasureClass.{0} Real Real.measurableSpace)
      (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        Real (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        (@Shao.OQ4.killedIterKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h
          n)
        (@Int.cast.{0} Real Real.instIntCast r)))
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `hm
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLENat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 1)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
      (Lean.Expr.bvar 0))
    (Lean.Expr.forallE
      `h
      (Lean.Expr.const `Real [])
      (Lean.Expr.forallE
        `hmh
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Real []))
              (Lean.Expr.const `Real.instLE []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instNatCast []))
              (Lean.Expr.bvar 2)))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          `hhm
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instLT []))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instAdd [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instNatCast []))
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.lit (Lean.Literal.natVal 1)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `One.toOfNat1 [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.const `Real.instOne [])))))
          (Lean.Expr.forallE
            `r
            (Lean.Expr.const `Int [])
            (Lean.Expr.forallE
              `hrlo
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                    (Lean.Expr.const `Int.instLEInt []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instNegInt []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                        (Lean.Expr.const `instNatCastInt []))
                      (Lean.Expr.bvar 5))))
                (Lean.Expr.bvar 0))
              (Lean.Expr.forallE
                `hrhi
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instLEInt []))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `instNatCastInt []))
                    (Lean.Expr.bvar 6)))
                (Lean.Expr.forallE
                  `n
                  (Lean.Expr.const `Nat [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Filter.Eventually [Lean.Level.zero]) (Lean.Expr.const `Real []))
                      (Lean.Expr.lam
                        `w
                        (Lean.Expr.const `Real [])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Membership.mem [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Real []))
                                (Lean.Expr.app (Lean.Expr.const `Set [Lean.Level.zero]) (Lean.Expr.const `Real [])))
                              (Lean.Expr.app
                                (Lean.Expr.const `Set.instMembership [Lean.Level.zero])
                                (Lean.Expr.const `Real [])))
                            (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherIteration.grid []) (Lean.Expr.bvar 9)))
                          (Lean.Expr.bvar 0))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `MeasureTheory.ae [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Real []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `MeasureTheory.Measure [Lean.Level.zero])
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real.measurableSpace [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `MeasureTheory.Measure.instFunLike [Lean.Level.zero])
                              (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real.measurableSpace [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `MeasureTheory.Measure.instOuterMeasureClass [Lean.Level.zero])
                            (Lean.Expr.const `Real []))
                          (Lean.Expr.const `Real.measurableSpace [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `DFunLike.coe
                                    [Lean.Level.succ (Lean.Level.zero),
                                     Lean.Level.succ (Lean.Level.zero),
                                     Lean.Level.succ (Lean.Level.zero)])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `ProbabilityTheory.Kernel [Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `Real []))
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real.measurableSpace []))
                                    (Lean.Expr.const `Real.measurableSpace [])))
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.lam
                                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Basic.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                                (Lean.Expr.const `Real [])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `MeasureTheory.Measure [Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real.measurableSpace []))
                                (Lean.BinderInfo.default)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `ProbabilityTheory.Kernel.instFunLike
                                      [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real.measurableSpace []))
                              (Lean.Expr.const `Real.measurableSpace [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Shao.OQ4.killedIterKernel [])
                                  (Lean.Expr.const `Shao.OQ4.RademacherCosine.law []))
                                (Lean.Expr.const `Shao.OQ4.RademacherCosine.law_isProbabilityMeasure []))
                              (Lean.Expr.bvar 6))
                            (Lean.Expr.bvar 0)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Int.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real.instIntCast []))
                          (Lean.Expr.bvar 3)))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
```

## `Shao.OQ4.RademacherIteration.killedIterKernel_grid_compl`

- User name: `Shao.OQ4.RademacherIteration.killedIterKernel_grid_compl`.
- Kind: `theorem`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
∀ (m : Nat) (_hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hrlo : @LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r)
  (hrhi : @LE.le.{0} Int Int.instLEInt r (@Nat.cast.{0} Int instNatCastInt m)) (n : Nat),
  @Eq.{1} ENNReal
    (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace) (Set.{0} Real)
      (fun (x : Set.{0} Real) => ENNReal) (@MeasureTheory.Measure.instFunLike.{0} Real Real.measurableSpace)
      (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        Real (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        (@Shao.OQ4.killedIterKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h
          n)
        (@Int.cast.{0} Real Real.instIntCast r))
      (@Compl.compl.{0} (Set.{0} Real) (@Set.instCompl.{0} Real) (Shao.OQ4.RademacherIteration.grid m)))
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `_hm
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLENat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 1)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
      (Lean.Expr.bvar 0))
    (Lean.Expr.forallE
      `h
      (Lean.Expr.const `Real [])
      (Lean.Expr.forallE
        `hmh
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Real []))
              (Lean.Expr.const `Real.instLE []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instNatCast []))
              (Lean.Expr.bvar 2)))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          `hhm
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instLT []))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instAdd [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instNatCast []))
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.lit (Lean.Literal.natVal 1)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `One.toOfNat1 [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.const `Real.instOne [])))))
          (Lean.Expr.forallE
            `r
            (Lean.Expr.const `Int [])
            (Lean.Expr.forallE
              `hrlo
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                    (Lean.Expr.const `Int.instLEInt []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instNegInt []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                        (Lean.Expr.const `instNatCastInt []))
                      (Lean.Expr.bvar 5))))
                (Lean.Expr.bvar 0))
              (Lean.Expr.forallE
                `hrhi
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instLEInt []))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `instNatCastInt []))
                    (Lean.Expr.bvar 6)))
                (Lean.Expr.forallE
                  `n
                  (Lean.Expr.const `Nat [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `ENNReal []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `DFunLike.coe
                                    [Lean.Level.succ (Lean.Level.zero),
                                     Lean.Level.succ (Lean.Level.zero),
                                     Lean.Level.succ (Lean.Level.zero)])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `MeasureTheory.Measure [Lean.Level.zero])
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real.measurableSpace [])))
                                (Lean.Expr.app (Lean.Expr.const `Set [Lean.Level.zero]) (Lean.Expr.const `Real [])))
                              (Lean.Expr.lam
                                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Basic.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                                (Lean.Expr.app (Lean.Expr.const `Set [Lean.Level.zero]) (Lean.Expr.const `Real []))
                                (Lean.Expr.const `ENNReal [])
                                (Lean.BinderInfo.default)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `MeasureTheory.Measure.instFunLike [Lean.Level.zero])
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real.measurableSpace [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `DFunLike.coe
                                        [Lean.Level.succ (Lean.Level.zero),
                                         Lean.Level.succ (Lean.Level.zero),
                                         Lean.Level.succ (Lean.Level.zero)])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `ProbabilityTheory.Kernel
                                                [Lean.Level.zero, Lean.Level.zero])
                                              (Lean.Expr.const `Real []))
                                            (Lean.Expr.const `Real []))
                                          (Lean.Expr.const `Real.measurableSpace []))
                                        (Lean.Expr.const `Real.measurableSpace [])))
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.lam
                                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Basic.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                                    (Lean.Expr.const `Real [])
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `MeasureTheory.Measure [Lean.Level.zero])
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real.measurableSpace []))
                                    (Lean.BinderInfo.default)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `ProbabilityTheory.Kernel.instFunLike
                                          [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real.measurableSpace []))
                                  (Lean.Expr.const `Real.measurableSpace [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Shao.OQ4.killedIterKernel [])
                                      (Lean.Expr.const `Shao.OQ4.RademacherCosine.law []))
                                    (Lean.Expr.const `Shao.OQ4.RademacherCosine.law_isProbabilityMeasure []))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 0)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `Int.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real.instIntCast []))
                              (Lean.Expr.bvar 3))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Compl.compl [Lean.Level.zero])
                              (Lean.Expr.app (Lean.Expr.const `Set [Lean.Level.zero]) (Lean.Expr.const `Real [])))
                            (Lean.Expr.app
                              (Lean.Expr.const `Set.instCompl [Lean.Level.zero])
                              (Lean.Expr.const `Real [])))
                          (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherIteration.grid []) (Lean.Expr.bvar 8)))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `ENNReal []))
                        (Lean.Expr.lit (Lean.Literal.natVal 0)))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Zero.toOfNat0 [Lean.Level.zero]) (Lean.Expr.const `ENNReal []))
                        (Lean.Expr.const `ENNReal.instZero []))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
```

## `Shao.OQ4.RademacherIteration.killedIterKernel_integral_principal_power`

- User name: `Shao.OQ4.RademacherIteration.killedIterKernel_integral_principal_power`.
- Kind: `theorem`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (r : Int)
  (hrlo : @LE.le.{0} Int Int.instLEInt (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) r)
  (hrhi : @LE.le.{0} Int Int.instLEInt r (@Nat.cast.{0} Int instNatCastInt m)) (n : Nat),
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
      fun (w : Real) =>
      Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m) w))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherCosine.rho m) n)
      (Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherCosine.angle m)
          (@Int.cast.{0} Real Real.instIntCast r))))
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `hm
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLENat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 1)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
      (Lean.Expr.bvar 0))
    (Lean.Expr.forallE
      `h
      (Lean.Expr.const `Real [])
      (Lean.Expr.forallE
        `hmh
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Real []))
              (Lean.Expr.const `Real.instLE []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instNatCast []))
              (Lean.Expr.bvar 2)))
          (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          `hhm
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instLT []))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instAdd [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.instNatCast []))
                  (Lean.Expr.bvar 3)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.lit (Lean.Literal.natVal 1)))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `One.toOfNat1 [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.const `Real.instOne [])))))
          (Lean.Expr.forallE
            `r
            (Lean.Expr.const `Int [])
            (Lean.Expr.forallE
              `hrlo
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                    (Lean.Expr.const `Int.instLEInt []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instNegInt []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                        (Lean.Expr.const `instNatCastInt []))
                      (Lean.Expr.bvar 5))))
                (Lean.Expr.bvar 0))
              (Lean.Expr.forallE
                `hrhi
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `Int.instLEInt []))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Int []))
                      (Lean.Expr.const `instNatCastInt []))
                    (Lean.Expr.bvar 6)))
                (Lean.Expr.forallE
                  `n
                  (Lean.Expr.const `Nat [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `MeasureTheory.integral [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real.normedAddCommGroup []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `InnerProductSpace.toNormedSpace
                                          [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real.instRCLike []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `NormedAddCommGroup.toSeminormedAddCommGroup [Lean.Level.zero])
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real.normedAddCommGroup [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RCLike.toInnerProductSpaceReal [Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real.instRCLike []))))
                            (Lean.Expr.const `Real.measurableSpace []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const
                                        `DFunLike.coe
                                        [Lean.Level.succ (Lean.Level.zero),
                                         Lean.Level.succ (Lean.Level.zero),
                                         Lean.Level.succ (Lean.Level.zero)])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const
                                                `ProbabilityTheory.Kernel
                                                [Lean.Level.zero, Lean.Level.zero])
                                              (Lean.Expr.const `Real []))
                                            (Lean.Expr.const `Real []))
                                          (Lean.Expr.const `Real.measurableSpace []))
                                        (Lean.Expr.const `Real.measurableSpace [])))
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.lam
                                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Basic.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                                    (Lean.Expr.const `Real [])
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `MeasureTheory.Measure [Lean.Level.zero])
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real.measurableSpace []))
                                    (Lean.BinderInfo.default)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `ProbabilityTheory.Kernel.instFunLike
                                          [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real.measurableSpace []))
                                  (Lean.Expr.const `Real.measurableSpace [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Shao.OQ4.killedIterKernel [])
                                      (Lean.Expr.const `Shao.OQ4.RademacherCosine.law []))
                                    (Lean.Expr.const `Shao.OQ4.RademacherCosine.law_isProbabilityMeasure []))
                                  (Lean.Expr.bvar 6))
                                (Lean.Expr.bvar 0)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `Int.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real.instIntCast []))
                              (Lean.Expr.bvar 3))))
                        (Lean.Expr.lam
                          `w
                          (Lean.Expr.const `Real [])
                          (Lean.Expr.app
                            (Lean.Expr.const `Real.cos [])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Real []))
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `instHMul [Lean.Level.zero])
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real.instMul [])))
                                (Lean.Expr.app
                                  (Lean.Expr.const `Shao.OQ4.RademacherCosine.angle [])
                                  (Lean.Expr.bvar 9)))
                              (Lean.Expr.bvar 0)))
                          (Lean.BinderInfo.default))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real.instMul [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Nat []))
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Nat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real.instMonoid [])))))
                            (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherCosine.rho []) (Lean.Expr.bvar 8)))
                          (Lean.Expr.bvar 0)))
                      (Lean.Expr.app
                        (Lean.Expr.const `Real.cos [])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real.instMul [])))
                            (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherCosine.angle []) (Lean.Expr.bvar 8)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Int.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real.instIntCast []))
                            (Lean.Expr.bvar 3))))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
```

## `Shao.OQ4.RademacherIteration.measurableSet_grid`

- User name: `Shao.OQ4.RademacherIteration.measurableSet_grid`.
- Kind: `theorem`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
∀ (m : Nat), @MeasurableSet.{0} Real Real.measurableSpace (Shao.OQ4.RademacherIteration.grid m)
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `MeasurableSet [Lean.Level.zero]) (Lean.Expr.const `Real []))
      (Lean.Expr.const `Real.measurableSpace []))
    (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherIteration.grid []) (Lean.Expr.bvar 0)))
  (Lean.BinderInfo.default)
```

## `Shao.OQ4.RademacherIteration.principal_integrable`

- User name: `Shao.OQ4.RademacherIteration.principal_integrable`.
- Kind: `theorem`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
∀ (m : Nat) (h : Real) (n : Nat) (z : Real),
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
      (@Shao.OQ4.killedIterKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h n)
      z)
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `h
    (Lean.Expr.const `Real [])
    (Lean.Expr.forallE
      `n
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE
        `z
        (Lean.Expr.const `Real [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `MeasureTheory.Integrable [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Real []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `UniformSpace.toTopologicalSpace [Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `PseudoMetricSpace.toUniformSpace [Lean.Level.zero])
                          (Lean.Expr.const `Real []))
                        (Lean.Expr.const `Real.pseudoMetricSpace []))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `ESeminormedAddMonoid.toContinuousENorm [Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `UniformSpace.toTopologicalSpace [Lean.Level.zero])
                          (Lean.Expr.const `Real []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `PseudoMetricSpace.toUniformSpace [Lean.Level.zero])
                            (Lean.Expr.const `Real []))
                          (Lean.Expr.const `Real.pseudoMetricSpace []))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `SeminormedAddGroup.toESeminormedAddMonoid [Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `SeminormedAddCommGroup.toSeminormedAddGroup [Lean.Level.zero])
                          (Lean.Expr.const `Real []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `NonUnitalSeminormedRing.toSeminormedAddCommGroup [Lean.Level.zero])
                            (Lean.Expr.const `Real []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing [Lean.Level.zero])
                              (Lean.Expr.const `Real []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `SeminormedCommRing.toNonUnitalSeminormedCommRing [Lean.Level.zero])
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `NormedCommRing.toSeminormedCommRing [Lean.Level.zero])
                                  (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real.normedCommRing [])))))))))
                (Lean.Expr.const `Real []))
              (Lean.Expr.const `Real.measurableSpace []))
            (Lean.Expr.lam
              `w
              (Lean.Expr.const `Real [])
              (Lean.Expr.app
                (Lean.Expr.const `Real.cos [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Real []))
                          (Lean.Expr.const `Real []))
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Real []))
                        (Lean.Expr.const `Real.instMul [])))
                    (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherCosine.angle []) (Lean.Expr.bvar 4)))
                  (Lean.Expr.bvar 0)))
              (Lean.BinderInfo.default)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `DFunLike.coe
                        [Lean.Level.succ (Lean.Level.zero),
                         Lean.Level.succ (Lean.Level.zero),
                         Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `ProbabilityTheory.Kernel [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real []))
                          (Lean.Expr.const `Real.measurableSpace []))
                        (Lean.Expr.const `Real.measurableSpace [])))
                    (Lean.Expr.const `Real []))
                  (Lean.Expr.lam
                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Basic.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                    (Lean.Expr.const `Real [])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `MeasureTheory.Measure [Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.const `Real.measurableSpace []))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `ProbabilityTheory.Kernel.instFunLike [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real.measurableSpace []))
                  (Lean.Expr.const `Real.measurableSpace [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Shao.OQ4.killedIterKernel [])
                      (Lean.Expr.const `Shao.OQ4.RademacherCosine.law []))
                    (Lean.Expr.const `Shao.OQ4.RademacherCosine.law_isProbabilityMeasure []))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.bvar 0)))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
```

## `_private.Shao.OQ4.RademacherIteration.0.Shao.OQ4.RademacherIteration.killedKernel_grid_compl`

- User name: `Shao.OQ4.RademacherIteration.killedKernel_grid_compl`.
- Kind: `theorem`.
- Universes: `[]`.
- Registered instance: `false`.
- Transitive axioms: `Classical.choice, Quot.sound, propext`.

Complete type (`pp.all`):

```lean
∀ (m : Nat) (h : Real) (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (s : Int),
  @Eq.{1} ENNReal
    (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace) (Set.{0} Real)
      (fun (x : Set.{0} Real) => ENNReal) (@MeasureTheory.Measure.instFunLike.{0} Real Real.measurableSpace)
      (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        Real (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
        (@Shao.OQ4.killedKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h)
        (@Int.cast.{0} Real Real.instIntCast s))
      (@Compl.compl.{0} (Set.{0} Real) (@Set.instCompl.{0} Real) (Shao.OQ4.RademacherIteration.grid m)))
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
```

Raw expression type:

```text
Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `h
    (Lean.Expr.const `Real [])
    (Lean.Expr.forallE
      `hmh
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Real []))
            (Lean.Expr.const `Real.instLE []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
              (Lean.Expr.const `Real.instNatCast []))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.bvar 0))
      (Lean.Expr.forallE
        `hhm
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Real []))
              (Lean.Expr.const `Real.instLT []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Real []))
                    (Lean.Expr.const `Real []))
                  (Lean.Expr.const `Real []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.const `Real.instAdd [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                  (Lean.Expr.const `Real.instNatCast []))
                (Lean.Expr.bvar 2)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.lit (Lean.Literal.natVal 1)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `One.toOfNat1 [Lean.Level.zero]) (Lean.Expr.const `Real []))
                (Lean.Expr.const `Real.instOne [])))))
        (Lean.Expr.forallE
          `s
          (Lean.Expr.const `Int [])
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `ENNReal []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `DFunLike.coe
                            [Lean.Level.succ (Lean.Level.zero),
                             Lean.Level.succ (Lean.Level.zero),
                             Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `MeasureTheory.Measure [Lean.Level.zero])
                              (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real.measurableSpace [])))
                        (Lean.Expr.app (Lean.Expr.const `Set [Lean.Level.zero]) (Lean.Expr.const `Real [])))
                      (Lean.Expr.lam
                        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Basic.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                        (Lean.Expr.app (Lean.Expr.const `Set [Lean.Level.zero]) (Lean.Expr.const `Real []))
                        (Lean.Expr.const `ENNReal [])
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `MeasureTheory.Measure.instFunLike [Lean.Level.zero])
                        (Lean.Expr.const `Real []))
                      (Lean.Expr.const `Real.measurableSpace [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `DFunLike.coe
                                [Lean.Level.succ (Lean.Level.zero),
                                 Lean.Level.succ (Lean.Level.zero),
                                 Lean.Level.succ (Lean.Level.zero)])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `ProbabilityTheory.Kernel [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real.measurableSpace []))
                                (Lean.Expr.const `Real.measurableSpace [])))
                            (Lean.Expr.const `Real []))
                          (Lean.Expr.lam
                            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Basic.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                            (Lean.Expr.const `Real [])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `MeasureTheory.Measure [Lean.Level.zero])
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real.measurableSpace []))
                            (Lean.BinderInfo.default)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `ProbabilityTheory.Kernel.instFunLike
                                  [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real []))
                            (Lean.Expr.const `Real.measurableSpace []))
                          (Lean.Expr.const `Real.measurableSpace [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Shao.OQ4.killedKernel [])
                            (Lean.Expr.const `Shao.OQ4.RademacherCosine.law []))
                          (Lean.Expr.const `Shao.OQ4.RademacherCosine.law_isProbabilityMeasure []))
                        (Lean.Expr.bvar 3)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Int.cast [Lean.Level.zero]) (Lean.Expr.const `Real []))
                        (Lean.Expr.const `Real.instIntCast []))
                      (Lean.Expr.bvar 0))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Compl.compl [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `Set [Lean.Level.zero]) (Lean.Expr.const `Real [])))
                    (Lean.Expr.app (Lean.Expr.const `Set.instCompl [Lean.Level.zero]) (Lean.Expr.const `Real [])))
                  (Lean.Expr.app (Lean.Expr.const `Shao.OQ4.RademacherIteration.grid []) (Lean.Expr.bvar 4)))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `ENNReal []))
                (Lean.Expr.lit (Lean.Literal.natVal 0)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Zero.toOfNat0 [Lean.Level.zero]) (Lean.Expr.const `ENNReal []))
                (Lean.Expr.const `ENNReal.instZero []))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
```
