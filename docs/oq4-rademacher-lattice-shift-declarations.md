# RademacherLatticeShift 规范源码全声明账

STATUS: AUTHOR_CANONICAL_CHECKED

逻辑模块：Shao.OQ4.RademacherLatticeShift。
全部 getModuleIdxFor? = none 项，无命名空间过滤；定理证明值不输出，全部定义和 opaque 值完整输出。

## Shao.OQ4.RademacherLatticeShift.C

- kind：definition
- user_name：Shao.OQ4.RademacherLatticeShift.C
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
Real
```

完整定义值：

```lean
@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) Shao.OQ4.RademacherScalarBounds.C_rho
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 3)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast Shao.OQ4.RademacherLatticeShift.C._proof_1))
      Shao.OQ4.RademacherScalarBounds.lambda))
  Shao.OQ4.RademacherLatticeShift.C_log
```

## Shao.OQ4.RademacherLatticeShift.C_log

- kind：definition
- user_name：Shao.OQ4.RademacherLatticeShift.C_log
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
Real
```

完整定义值：

```lean
@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi Shao.OQ4.RademacherScalarBounds.C_a)
    (@OfNat.ofNat.{0} Real (nat_lit 4)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast Shao.OQ4.RademacherLatticeShift.C_log._proof_1)))
  Shao.OQ4.RademacherLatticeShift.cos_lower
```

## Shao.OQ4.RademacherLatticeShift.C_log_pos

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.C_log_pos
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  Shao.OQ4.RademacherLatticeShift.C_log
```

## Shao.OQ4.RademacherLatticeShift.C_pos

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.C_pos
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  Shao.OQ4.RademacherLatticeShift.C
```

## Shao.OQ4.RademacherLatticeShift.DA0

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.DA0
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) {h : Real}
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hmh1 :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h)
    (And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
      (And
        (@LE.le.{0} Real Real.instLE
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (Shao.OQ4.RademacherScalarBounds.H m))
        (And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (Shao.OQ4.RademacherScalarBounds.H m))
          (And
            (@Eq.{1} Real (Shao.OQ4.RademacherScalarBounds.H m)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) h
                (Shao.OQ4.RademacherLatticeShift.delta m h)))
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (Shao.OQ4.RademacherLatticeShift.delta m h))
              (And
                (@LE.le.{0} Real Real.instLE (Shao.OQ4.RademacherLatticeShift.delta m h)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                (And
                  (@Ne.{1} Real
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                  (And
                    (@Ne.{1} Real
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                    (And
                      (@Ne.{1} Real
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                      (And
                        (@Ne.{1} Real
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (Shao.OQ4.RademacherScalarBounds.H m)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                        (And
                          (@Ne.{1} Real
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (Shao.OQ4.RademacherScalarBounds.H m)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                          (And
                            (@Ne.{1} Real
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 4)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                (Shao.OQ4.RademacherScalarBounds.H m))
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                            (And
                              (@Ne.{1} Real
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                  (Shao.OQ4.RademacherScalarBounds.H m))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                              (And
                                (@Ne.{1} Real (Real.sin (Shao.OQ4.RademacherScalarBounds.u m))
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                                (And
                                  (@LT.lt.{0} Real Real.instLT
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (Shao.OQ4.RademacherScalarBounds.a m))
                                  (And
                                    (@LT.lt.{0} Real Real.instLT
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      (Shao.OQ4.RademacherScalarBounds.rho m))
                                    (And
                                      (@LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherScalarBounds.rho m)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                      (@LT.lt.{0} Real Real.instLT
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
                                            (Shao.OQ4.RademacherScalarBounds.a m))
                                          (@OfNat.ofNat.{0} Real (nat_lit 4)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                              (@Nat.instAtLeastTwoHAddOfNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                (@Nat.instNeZeroSucc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                    (instOfNatNat (nat_lit 2))))))))))))))))))))))))))
```

## Shao.OQ4.RademacherLatticeShift.DA1

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.DA1
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
@Exists.{1} Real fun (K : Real) =>
  And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K)
    (∀ (m : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m →
        ∀ (h : Real),
          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h →
            @LT.lt.{0} Real Real.instLT h
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast m)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
              ∀ (n : Nat),
                @LE.le.{0} Real Real.instLE
                  (@abs.{0} Real Real.lattice Real.instAddGroup
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@OfNat.ofNat.{0} Real (nat_lit 8)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
                              (@Nat.cast.{0} Real Real.instNatCast n))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              h (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast n) (Real.log (Shao.OQ4.RademacherScalarBounds.rho m))))
                        (Real.log
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
                              (Shao.OQ4.RademacherScalarBounds.a m))
                            (@OfNat.ofNat.{0} Real (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@OfNat.ofNat.{0} Real (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@Nat.cast.{0} Real Real.instNatCast n)
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              h (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (Shao.OQ4.RademacherScalarBounds.H m) h))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) K
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (Shao.OQ4.RademacherScalarBounds.H m)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
```

## Shao.OQ4.RademacherLatticeShift.cell_legality

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.cell_legality
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) {h : Real}
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hmh1 :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h)
    (And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
      (And
        (@LE.le.{0} Real Real.instLE
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (Shao.OQ4.RademacherScalarBounds.H m))
        (And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (Shao.OQ4.RademacherScalarBounds.H m))
          (And
            (@Eq.{1} Real (Shao.OQ4.RademacherScalarBounds.H m)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) h
                (Shao.OQ4.RademacherLatticeShift.delta m h)))
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (Shao.OQ4.RademacherLatticeShift.delta m h))
              (@LE.le.{0} Real Real.instLE (Shao.OQ4.RademacherLatticeShift.delta m h)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))))
```

## Shao.OQ4.RademacherLatticeShift.cos_lower

- kind：definition
- user_name：Shao.OQ4.RademacherLatticeShift.cos_lower
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
Real
```

完整定义值：

```lean
Real.cos
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
    (@OfNat.ofNat.{0} Real (nat_lit 8)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast Shao.OQ4.RademacherLatticeShift.cos_lower._proof_1)))
```

## Shao.OQ4.RademacherLatticeShift.delta

- kind：definition
- user_name：Shao.OQ4.RademacherLatticeShift.delta
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
(m : Nat) → (h : Real) → Real
```

完整定义值：

```lean
fun (m : Nat) (h : Real) =>
  @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (Shao.OQ4.RademacherScalarBounds.H m) h
```

## Shao.OQ4.RademacherLatticeShift.delta_at_left

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.delta_at_left
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ (m : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherLatticeShift.delta m (@Nat.cast.{0} Real Real.instNatCast m))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherLatticeShift.displacement_remainder_bound

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.displacement_remainder_bound
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) {h : Real}
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hmh1 :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (Shao.OQ4.RademacherLatticeShift.delta m h))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 3)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
```

## Shao.OQ4.RademacherLatticeShift.finite_bound

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.finite_bound
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) {h : Real}
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hmh1 :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (n : Nat),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                Shao.OQ4.RademacherScalarBounds.lambda (@Nat.cast.{0} Real Real.instNatCast n))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast n) (Real.log (Shao.OQ4.RademacherScalarBounds.rho m))))
          (Real.log
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
                (Shao.OQ4.RademacherScalarBounds.a m))
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              Shao.OQ4.RademacherScalarBounds.lambda)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Nat.cast.{0} Real Real.instNatCast n)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (Shao.OQ4.RademacherLatticeShift.delta m h))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Shao.OQ4.RademacherLatticeShift.C
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast n)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
```

## Shao.OQ4.RademacherLatticeShift.normalized_log_bound

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_log_bound
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (Real.log
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
            (Shao.OQ4.RademacherScalarBounds.a m))
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Shao.OQ4.RademacherLatticeShift.C_log
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.cos_lower_le_one

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.cos_lower_le_one
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
@LE.le.{0} Real Real.instLE Shao.OQ4.RademacherLatticeShift.cos_lower
  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.cos_lower_pos

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.cos_lower_pos
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  Shao.OQ4.RademacherLatticeShift.cos_lower
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.displacement_identity

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.displacement_identity
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ (m : Nat) (h : Real) (hh : @Ne.{1} Real h (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hH :
    @Ne.{1} Real (Shao.OQ4.RademacherScalarBounds.H m)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (Shao.OQ4.RademacherLatticeShift.delta m h))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Neg.neg.{0} Real Real.instNeg
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherLatticeShift.delta m h) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              h)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (Shao.OQ4.RademacherLatticeShift.delta m h)))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) h
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.lambda_pos

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.lambda_pos
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  Shao.OQ4.RademacherScalarBounds.lambda
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.log_abs_le_of_lower

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.log_abs_le_of_lower
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ {q c : Real}
  (hc : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
  (hc1 : @LE.le.{0} Real Real.instLE c (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hcq : @LE.le.{0} Real Real.instLE c q),
  @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (Real.log q))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Inv.inv.{0} Real Real.instInv c)
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) q
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
            (Shao.OQ4.RademacherScalarBounds.a m))
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
          Shao.OQ4.RademacherScalarBounds.C_a)
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LE.le.{0} Real Real.instLE Shao.OQ4.RademacherLatticeShift.cos_lower
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
        (Shao.OQ4.RademacherScalarBounds.a m))
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
```

## Shao.OQ4.RademacherLatticeShift.C._proof_1

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.C._proof_1
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext

完整类型：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherLatticeShift.C_log._proof_1

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.C_log._proof_1
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext

完整类型：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherLatticeShift.cos_lower._proof_1

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.cos_lower._proof_1
- owner：Shao.OQ4.RademacherLatticeShift
- private：false
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext

完整类型：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_1

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_1
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

```lean
@Eq.{1} Prop (@Eq.{1} Real Real.pi (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_2

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_2
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_2]
- 传递公理：propext

完整类型：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_3

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_3
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_2]
- 传递公理：propext

完整类型：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_4

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_4
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_2]
- 传递公理：propext

完整类型：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_5

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_5
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_1]
- 传递公理：propext

完整类型：

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_6

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_6
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_1]
- 传递公理：propext

完整类型：

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

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_7

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_7
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_3]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

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

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_8

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_error_bound._simp_1_8
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_1]
- 传递公理：propext

完整类型：

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

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_1

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_1
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_2]
- 传递公理：propext

完整类型：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_2

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_2
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_2]
- 传递公理：propext

完整类型：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_3

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_3
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_2]
- 传递公理：propext

完整类型：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_4

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_4
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_1]
- 传递公理：propext

完整类型：

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_5

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_5
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_1]
- 传递公理：propext

完整类型：

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

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_6

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_6
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_3]
- 传递公理：propext, Classical.choice, Quot.sound

完整类型：

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

## _private.Shao.OQ4.RademacherLatticeShift.0.Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_7

- kind：theorem
- user_name：Shao.OQ4.RademacherLatticeShift.normalized_a_lower_bound._simp_1_7
- owner：Shao.OQ4.RademacherLatticeShift
- private：true
- unsafe/partial/instance：false/false/false
- universe_params：[`u_1]
- 传递公理：propext

完整类型：

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

全部声明计数：38。
