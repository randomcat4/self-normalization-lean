# RademacherScalarBounds 规范源码声明账

STATUS: AUTHOR_CANONICAL_READY；独立终审待办。
逻辑模块：Shao.OQ4.RademacherScalarBounds。
规范源码与完整私有 Source 原字节一致；仅发射一次目标 olean。

全部 59 个源所有项均无命名空间过滤地检查，并在实际直接导入、全 43 模块环境中按 owner 实测。
其中 8 个定义、51 个定理；21 个显式公开定理、8 个显式公开定义、9 个私有定理、21 个自动生成定理。
9 个原始名称位于 _private 包装空间，全部保留；解包后的用户命名空间均为本模块。
全部完整 Expr 类型、8 个定义值、宇宙、公理及实例元数据与私有完整 Source 精确一致。
旧全集 931 项与 100 个定义完整保全；全 43 模块实测 990 项与 108 个定义。
本模块无 unsafe、partial、实例或默认实例导出；公理并集只含 propext、Classical.choice、Quot.sound。

## Shao.OQ4.RademacherScalarBounds.C_a

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：definition
- raw_name：`Shao.OQ4.RademacherScalarBounds.C_a
- user_name：Shao.OQ4.RademacherScalarBounds.C_a
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.C_a
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
Real
```

透明定义值：

```lean
@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
  (@OfNat.ofNat.{0} Real (nat_lit 3)
    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast Shao.OQ4.RademacherScalarBounds.C_a._proof_1))
```

## Shao.OQ4.RademacherScalarBounds.C_a._proof_1

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.C_a._proof_1
- user_name：Shao.OQ4.RademacherScalarBounds.C_a._proof_1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.C_a._proof_1
- universe_params：[]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherScalarBounds.C_a_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.C_a_pos
- user_name：Shao.OQ4.RademacherScalarBounds.C_a_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.C_a_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  Shao.OQ4.RademacherScalarBounds.C_a
```

## Shao.OQ4.RademacherScalarBounds.C_rho

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：definition
- raw_name：`Shao.OQ4.RademacherScalarBounds.C_rho
- user_name：Shao.OQ4.RademacherScalarBounds.C_rho
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.C_rho
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
Real
```

透明定义值：

```lean
@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) Real.pi
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (@OfNat.ofNat.{0} Real (nat_lit 48)
    (@instOfNatAtLeastTwo.{0} Real (nat_lit 48) Real.instNatCast Shao.OQ4.RademacherScalarBounds.C_rho._proof_1))
```

## Shao.OQ4.RademacherScalarBounds.C_rho._proof_1

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.C_rho._proof_1
- user_name：Shao.OQ4.RademacherScalarBounds.C_rho._proof_1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.C_rho._proof_1
- universe_params：[]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 47) (instOfNatNat (nat_lit 47)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherScalarBounds.C_rho_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.C_rho_pos
- user_name：Shao.OQ4.RademacherScalarBounds.C_rho_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.C_rho_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  Shao.OQ4.RademacherScalarBounds.C_rho
```

## Shao.OQ4.RademacherScalarBounds.H

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：definition
- raw_name：`Shao.OQ4.RademacherScalarBounds.H
- user_name：Shao.OQ4.RademacherScalarBounds.H
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.H
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
(m : Nat) → Real
```

透明定义值：

```lean
fun (m : Nat) =>
  @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherScalarBounds.H_ge_two

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.H_ge_two
- user_name：Shao.OQ4.RademacherScalarBounds.H_ge_two
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.H_ge_two
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LE.le.{0} Real Real.instLE
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (Shao.OQ4.RademacherScalarBounds.H m)
```

## Shao.OQ4.RademacherScalarBounds.H_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.H_pos
- user_name：Shao.OQ4.RademacherScalarBounds.H_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.H_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherScalarBounds.H m)
```

## Shao.OQ4.RademacherScalarBounds.SCA0

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA0
- user_name：Shao.OQ4.RademacherScalarBounds.SCA0
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA0
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  And
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
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (Shao.OQ4.RademacherScalarBounds.u m))
            (And
              (@LE.le.{0} Real Real.instLE (Shao.OQ4.RademacherScalarBounds.u m)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                    (@OfNat.ofNat.{0} Real (nat_lit 8)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                (And
                  (@LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (Shao.OQ4.RademacherScalarBounds.z m))
                  (And
                    (@LE.le.{0} Real Real.instLE (Shao.OQ4.RademacherScalarBounds.z m)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                        (@OfNat.ofNat.{0} Real (nat_lit 4)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                    (And
                      (@LT.lt.{0} Real Real.instLT
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                          (@OfNat.ofNat.{0} Real (nat_lit 4)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                      (And
                        (@LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (Real.sin (Shao.OQ4.RademacherScalarBounds.u m)))
                        (And
                          (@LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (Real.cos (Shao.OQ4.RademacherScalarBounds.u m)))
                          (And
                            (@LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (Real.cos (Shao.OQ4.RademacherScalarBounds.z m)))
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
                                                (instOfNatNat (nat_lit 2))))))))))))))))))))))))
```

## Shao.OQ4.RademacherScalarBounds.SCA1

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (Shao.OQ4.RademacherScalarBounds.a m)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          Real.pi)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Shao.OQ4.RademacherScalarBounds.C_a
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
```

## Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_1

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_1
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_1
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
@Eq.{1} Prop (@Eq.{1} Real Real.pi (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) False
```

## Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_2

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_2
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_2
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_2
- universe_params：[`u_2]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_3

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_3
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_3
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_3
- universe_params：[`u_2]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_4

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_4
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_4
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_4
- universe_params：[`u_2]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_5

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_5
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_5
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_5
- universe_params：[`u_1]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_6

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_6
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_6
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_6
- universe_params：[`u_1]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

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

## Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_7

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_7
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_7
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_7
- universe_params：[`u_3]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

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

## Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_8

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_8
- user_name：Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_8
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA1._simp_1_8
- universe_params：[`u_1]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

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

## Shao.OQ4.RademacherScalarBounds.SCA2

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA2
- user_name：Shao.OQ4.RademacherScalarBounds.SCA2
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA2
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (Real.log (Shao.OQ4.RademacherScalarBounds.rho m))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          Shao.OQ4.RademacherScalarBounds.lambda
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Shao.OQ4.RademacherScalarBounds.C_rho
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherScalarBounds.H m) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
```

## Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_1

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_1
- user_name：Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_1
- universe_params：[`u_2]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_2

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_2
- user_name：Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_2
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_2
- universe_params：[`u_2]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_3

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_3
- user_name：Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_3
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_3
- universe_params：[`u_2]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_4

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_4
- user_name：Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_4
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_4
- universe_params：[`u_1]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_5

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_5
- user_name：Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_5
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_5
- universe_params：[`u_1]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

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

## Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_6

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_6
- user_name：Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_6
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_6
- universe_params：[`u_3]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

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

## Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_7

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_7
- user_name：Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_7
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.SCA2._simp_1_7
- universe_params：[`u_1]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

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

## Shao.OQ4.RademacherScalarBounds.a

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：definition
- raw_name：`Shao.OQ4.RademacherScalarBounds.a
- user_name：Shao.OQ4.RademacherScalarBounds.a
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.a
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
(m : Nat) → Real
```

透明定义值：

```lean
fun (m : Nat) =>
  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (Shao.OQ4.RademacherScalarBounds.H m))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.cos (Shao.OQ4.RademacherScalarBounds.u m)) (Real.sin (Shao.OQ4.RademacherScalarBounds.u m)))
```

## Shao.OQ4.RademacherScalarBounds.a_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.a_pos
- user_name：Shao.OQ4.RademacherScalarBounds.a_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.a_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherScalarBounds.a m)
```

## Shao.OQ4.RademacherScalarBounds.cos_u_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.cos_u_pos
- user_name：Shao.OQ4.RademacherScalarBounds.cos_u_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.cos_u_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.cos (Shao.OQ4.RademacherScalarBounds.u m))
```

## Shao.OQ4.RademacherScalarBounds.cos_z_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.cos_z_pos
- user_name：Shao.OQ4.RademacherScalarBounds.cos_z_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.cos_z_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.cos (Shao.OQ4.RademacherScalarBounds.z m))
```

## Shao.OQ4.RademacherScalarBounds.lambda

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：definition
- raw_name：`Shao.OQ4.RademacherScalarBounds.lambda
- user_name：Shao.OQ4.RademacherScalarBounds.lambda
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.lambda
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
Real
```

透明定义值：

```lean
@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
  (@HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) Real.pi
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@OfNat.ofNat.{0} Real (nat_lit 8)
    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast Shao.OQ4.RademacherScalarBounds.lambda._proof_1))
```

## Shao.OQ4.RademacherScalarBounds.lambda._proof_1

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.lambda._proof_1
- user_name：Shao.OQ4.RademacherScalarBounds.lambda._proof_1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.lambda._proof_1
- universe_params：[]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherScalarBounds.pi_mul_a_div_four_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.pi_mul_a_div_four_pos
- user_name：Shao.OQ4.RademacherScalarBounds.pi_mul_a_div_four_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.pi_mul_a_div_four_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
        (Shao.OQ4.RademacherScalarBounds.a m))
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
```

## Shao.OQ4.RademacherScalarBounds.rho

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：definition
- raw_name：`Shao.OQ4.RademacherScalarBounds.rho
- user_name：Shao.OQ4.RademacherScalarBounds.rho
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.rho
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
(m : Nat) → Real
```

透明定义值：

```lean
fun (m : Nat) => Real.cos (Shao.OQ4.RademacherScalarBounds.z m)
```

## Shao.OQ4.RademacherScalarBounds.rho.eq_1

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.rho.eq_1
- user_name：Shao.OQ4.RademacherScalarBounds.rho.eq_1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.rho.eq_1
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ (m : Nat), @Eq.{1} Real (Shao.OQ4.RademacherScalarBounds.rho m) (Real.cos (Shao.OQ4.RademacherScalarBounds.z m))
```

## Shao.OQ4.RademacherScalarBounds.rho_eq_cosine_rho

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.rho_eq_cosine_rho
- user_name：Shao.OQ4.RademacherScalarBounds.rho_eq_cosine_rho
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.rho_eq_cosine_rho
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ (m : Nat), @Eq.{1} Real (Shao.OQ4.RademacherScalarBounds.rho m) (Shao.OQ4.RademacherCosine.rho m)
```

## Shao.OQ4.RademacherScalarBounds.rho_lt_one

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.rho_lt_one
- user_name：Shao.OQ4.RademacherScalarBounds.rho_lt_one
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.rho_lt_one
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherScalarBounds.rho m)
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherScalarBounds.rho_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.rho_pos
- user_name：Shao.OQ4.RademacherScalarBounds.rho_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.rho_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherScalarBounds.rho m)
```

## Shao.OQ4.RademacherScalarBounds.scalar_bounds

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.scalar_bounds
- user_name：Shao.OQ4.RademacherScalarBounds.scalar_bounds
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.scalar_bounds
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
@Exists.{1} Real fun (Ca : Real) =>
  @Exists.{1} Real fun (Crho : Real) =>
    And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Ca)
      (And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Crho)
        (∀ (m : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m →
            And
              (@LE.le.{0} Real Real.instLE
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (Shao.OQ4.RademacherScalarBounds.a m)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      Real.pi)))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Ca
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Nat.cast.{0} Real Real.instNatCast m)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (@LE.le.{0} Real Real.instLE
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (Real.log (Shao.OQ4.RademacherScalarBounds.rho m))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          Real.pi (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@OfNat.ofNat.{0} Real (nat_lit 8)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast m)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Crho
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Nat.cast.{0} Real Real.instNatCast m)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
```

## Shao.OQ4.RademacherScalarBounds.sin_u_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.sin_u_pos
- user_name：Shao.OQ4.RademacherScalarBounds.sin_u_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.sin_u_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.sin (Shao.OQ4.RademacherScalarBounds.u m))
```

## Shao.OQ4.RademacherScalarBounds.u

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：definition
- raw_name：`Shao.OQ4.RademacherScalarBounds.u
- user_name：Shao.OQ4.RademacherScalarBounds.u
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.u
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
(m : Nat) → Real
```

透明定义值：

```lean
fun (m : Nat) =>
  @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast Shao.OQ4.RademacherScalarBounds.u._proof_1))
      (Shao.OQ4.RademacherScalarBounds.H m))
```

## Shao.OQ4.RademacherScalarBounds.u._proof_1

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.u._proof_1
- user_name：Shao.OQ4.RademacherScalarBounds.u._proof_1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.u._proof_1
- universe_params：[]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherScalarBounds.u_le_pi_div_eight

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.u_le_pi_div_eight
- user_name：Shao.OQ4.RademacherScalarBounds.u_le_pi_div_eight
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.u_le_pi_div_eight
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LE.le.{0} Real Real.instLE (Shao.OQ4.RademacherScalarBounds.u m)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Real.pi
      (@OfNat.ofNat.{0} Real (nat_lit 8)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
```

## Shao.OQ4.RademacherScalarBounds.u_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.u_pos
- user_name：Shao.OQ4.RademacherScalarBounds.u_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.u_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherScalarBounds.u m)
```

## Shao.OQ4.RademacherScalarBounds.z

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：definition
- raw_name：`Shao.OQ4.RademacherScalarBounds.z
- user_name：Shao.OQ4.RademacherScalarBounds.z
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.z
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
(m : Nat) → Real
```

透明定义值：

```lean
fun (m : Nat) =>
  @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast Shao.OQ4.RademacherScalarBounds.z._proof_1))
      (Shao.OQ4.RademacherScalarBounds.H m))
```

## Shao.OQ4.RademacherScalarBounds.z._proof_1

- 分类：自动生成项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.z._proof_1
- user_name：Shao.OQ4.RademacherScalarBounds.z._proof_1
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.z._proof_1
- universe_params：[]
- 传递公理：propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherScalarBounds.z_eq_angle

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.z_eq_angle
- user_name：Shao.OQ4.RademacherScalarBounds.z_eq_angle
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.z_eq_angle
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ (m : Nat), @Eq.{1} Real (Shao.OQ4.RademacherScalarBounds.z m) (Shao.OQ4.RademacherCosine.angle m)
```

## Shao.OQ4.RademacherScalarBounds.z_le_pi_div_four

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.z_le_pi_div_four
- user_name：Shao.OQ4.RademacherScalarBounds.z_le_pi_div_four
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.z_le_pi_div_four
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LE.le.{0} Real Real.instLE (Shao.OQ4.RademacherScalarBounds.z m)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Real.pi
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
```

## Shao.OQ4.RademacherScalarBounds.z_pos

- 分类：显式公开项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：`Shao.OQ4.RademacherScalarBounds.z_pos
- user_name：Shao.OQ4.RademacherScalarBounds.z_pos
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.z_pos
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherScalarBounds.z m)
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.cos_pos_on_quarter

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "cos_pos_on_quarter"
- user_name：Shao.OQ4.RademacherScalarBounds.cos_pos_on_quarter
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.cos_pos_on_quarter
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {t : Real}
  (ht :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          Real.pi
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
      t),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (Real.cos t)
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.cos_sq_half_le

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "cos_sq_half_le"
- user_name：Shao.OQ4.RademacherScalarBounds.cos_sq_half_le
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.cos_sq_half_le
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {t : Real}
  (ht :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          Real.pi
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
      t),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (Real.cos t)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.eval_nonneg_of_deriv

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "eval_nonneg_of_deriv"
- user_name：Shao.OQ4.RademacherScalarBounds.eval_nonneg_of_deriv
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.eval_nonneg_of_deriv
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {f f' : Real → Real} {t : Real}
  (ht : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t)
  (hzero :
    @Eq.{1} Real (f (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hd :
    ∀ (x : Real),
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Icc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t)
          x →
        @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
          Real.instAddCommGroup
          (@Semiring.toModule.{0} Real
            (@CommSemiring.toSemiring.{0} Real
              (@Semifield.toCommSemiring.{0} Real
                (@Field.toSemifield.{0} Real
                  (@NormedField.toField.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@IsModuleTopology.toContinuousSMul.{0, 0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real
                (@SeminormedRing.toPseudoMetricSpace.{0} Real
                  (@SeminormedCommRing.toSeminormedRing.{0} Real
                    (@NormedCommRing.toSeminormedCommRing.{0} Real
                      (@NormedField.toNormedCommRing.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
            Real Real.instAdd
            (@SMulZeroClass.toSMul.{0, 0} Real Real
              (@AddZero.toZero.{0} Real
                (@AddZeroClass.toAddZero.{0} Real
                  (@AddMonoid.toAddZeroClass.{0} Real
                    (@SubNegMonoid.toAddMonoid.{0} Real
                      (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))))
              (@DistribSMul.toSMulZeroClass.{0, 0} Real Real
                (@AddMonoid.toAddZeroClass.{0} Real
                  (@SubNegMonoid.toAddMonoid.{0} Real
                    (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))
                (@DistribMulAction.toDistribSMul.{0, 0} Real Real
                  (@Semiring.toMonoid.{0} Real
                    (@CommSemiring.toSemiring.{0} Real
                      (@Semifield.toCommSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
                  (@SubNegMonoid.toAddMonoid.{0} Real
                    (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))
                  (@Module.toDistribMulAction.{0, 0} Real Real
                    (@CommSemiring.toSemiring.{0} Real
                      (@Semifield.toCommSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                    (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
                    (@Semiring.toModule.{0} Real
                      (@CommSemiring.toSemiring.{0} Real
                        (@Semifield.toCommSemiring.{0} Real
                          (@Field.toSemifield.{0} Real
                            (@NormedField.toField.{0} Real
                              (@NontriviallyNormedField.toNormedField.{0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                  Real.denselyNormedField)))))))))))
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@IsTopologicalSemiring.toIsModuleTopology.{0} Real Real.semiring
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real
                  (@SeminormedRing.toPseudoMetricSpace.{0} Real
                    (@SeminormedCommRing.toSeminormedRing.{0} Real
                      (@NormedCommRing.toSeminormedCommRing.{0} Real
                        (@NormedField.toNormedCommRing.{0} Real
                          (@NontriviallyNormedField.toNormedField.{0} Real
                            (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
              (@IsTopologicalRing.toIsTopologicalSemiring.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real
                    (@SeminormedRing.toPseudoMetricSpace.{0} Real
                      (@SeminormedCommRing.toSeminormedRing.{0} Real
                        (@NormedCommRing.toSeminormedCommRing.{0} Real
                          (@NormedField.toNormedCommRing.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                    (@CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))
                instIsTopologicalRingReal)))
          f (f' x) x)
  (hn :
    ∀ (x : Real),
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Icc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t)
          x →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (f' x)),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (f t)
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.log_cos_quartic_remainder

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "log_cos_quartic_remainder"
- user_name：Shao.OQ4.RademacherScalarBounds.log_cos_quartic_remainder
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.log_cos_quartic_remainder
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {t : Real}
  (ht :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          Real.pi
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
      t),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@Neg.neg.{0} Real Real.instNeg (Real.log (Real.cos t)))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) t
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
    (@LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@Neg.neg.{0} Real Real.instNeg (Real.log (Real.cos t)))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) t
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) t
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.log_cos_remainder_hasDeriv

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "log_cos_remainder_hasDeriv"
- user_name：Shao.OQ4.RademacherScalarBounds.log_cos_remainder_hasDeriv
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.log_cos_remainder_hasDeriv
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {x : Real}
  (hx : @Ne.{1} Real (Real.cos x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.instAddCommGroup
    (@Semiring.toModule.{0} Real
      (@CommSemiring.toSemiring.{0} Real
        (@Semifield.toCommSemiring.{0} Real
          (@Field.toSemifield.{0} Real
            (@NormedField.toField.{0} Real
              (@NontriviallyNormedField.toNormedField.{0} Real
                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@IsModuleTopology.toContinuousSMul.{0, 0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real
        (@PseudoMetricSpace.toUniformSpace.{0} Real
          (@SeminormedRing.toPseudoMetricSpace.{0} Real
            (@SeminormedCommRing.toSeminormedRing.{0} Real
              (@NormedCommRing.toSeminormedCommRing.{0} Real
                (@NormedField.toNormedCommRing.{0} Real
                  (@NontriviallyNormedField.toNormedField.{0} Real
                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
      Real Real.instAdd
      (@SMulZeroClass.toSMul.{0, 0} Real Real
        (@AddZero.toZero.{0} Real
          (@AddZeroClass.toAddZero.{0} Real
            (@AddMonoid.toAddZeroClass.{0} Real
              (@SubNegMonoid.toAddMonoid.{0} Real
                (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} Real Real
          (@AddMonoid.toAddZeroClass.{0} Real
            (@SubNegMonoid.toAddMonoid.{0} Real
              (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))
          (@DistribMulAction.toDistribSMul.{0, 0} Real Real
            (@Semiring.toMonoid.{0} Real
              (@CommSemiring.toSemiring.{0} Real
                (@Semifield.toCommSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
            (@SubNegMonoid.toAddMonoid.{0} Real
              (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))
            (@Module.toDistribMulAction.{0, 0} Real Real
              (@CommSemiring.toSemiring.{0} Real
                (@Semifield.toCommSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
              (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
              (@Semiring.toModule.{0} Real
                (@CommSemiring.toSemiring.{0} Real
                  (@Semifield.toCommSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))))))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@IsTopologicalSemiring.toIsModuleTopology.{0} Real Real.semiring
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real
            (@SeminormedRing.toPseudoMetricSpace.{0} Real
              (@SeminormedCommRing.toSeminormedRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real
                  (@NormedField.toNormedCommRing.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
        (@IsTopologicalRing.toIsTopologicalSemiring.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real
              (@SeminormedRing.toPseudoMetricSpace.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
              (@CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))
          instIsTopologicalRingReal)))
    (fun (t : Real) =>
      @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@Neg.neg.{0} Real Real.instNeg (Real.log (Real.cos t)))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) t
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (Real.tan x) x) x
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.tan_cubic_remainder

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "tan_cubic_remainder"
- user_name：Shao.OQ4.RademacherScalarBounds.tan_cubic_remainder
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.tan_cubic_remainder
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {t : Real}
  (ht :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          Real.pi
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
      t),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (Real.tan t) t))
    (@LE.le.{0} Real Real.instLE (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (Real.tan t) t)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) t
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.tan_ge_id

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "tan_ge_id"
- user_name：Shao.OQ4.RademacherScalarBounds.tan_ge_id
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.tan_ge_id
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {t : Real}
  (ht :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          Real.pi
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
      t),
  @LE.le.{0} Real Real.instLE t (Real.tan t)
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.tan_le_two_mul

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "tan_le_two_mul"
- user_name：Shao.OQ4.RademacherScalarBounds.tan_le_two_mul
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.tan_le_two_mul
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {t : Real}
  (ht :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          Real.pi
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
      t),
  @LE.le.{0} Real Real.instLE (Real.tan t)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      t)
```

## _private.Shao.OQ4.RademacherScalarBounds.0.Shao.OQ4.RademacherScalarBounds.tan_sub_id_hasDeriv

- 分类：私有辅助项
- owner：Shao.OQ4.RademacherScalarBounds
- kind：theorem
- raw_name：Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Shao.OQ4.RademacherScalarBounds 0) "Shao") "OQ4") "RademacherScalarBounds") "tan_sub_id_hasDeriv"
- user_name：Shao.OQ4.RademacherScalarBounds.tan_sub_id_hasDeriv
- raw_user_name：`Shao.OQ4.RademacherScalarBounds.tan_sub_id_hasDeriv
- universe_params：[]
- 传递公理：Quot.sound, Classical.choice, propext
- unsafe/partial/instance：false；priority/attribute：无。

```lean
∀ {x : Real}
  (hx : @Ne.{1} Real (Real.cos x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.instAddCommGroup
    (@Semiring.toModule.{0} Real
      (@CommSemiring.toSemiring.{0} Real
        (@Semifield.toCommSemiring.{0} Real
          (@Field.toSemifield.{0} Real
            (@NormedField.toField.{0} Real
              (@NontriviallyNormedField.toNormedField.{0} Real
                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@IsModuleTopology.toContinuousSMul.{0, 0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real
        (@PseudoMetricSpace.toUniformSpace.{0} Real
          (@SeminormedRing.toPseudoMetricSpace.{0} Real
            (@SeminormedCommRing.toSeminormedRing.{0} Real
              (@NormedCommRing.toSeminormedCommRing.{0} Real
                (@NormedField.toNormedCommRing.{0} Real
                  (@NontriviallyNormedField.toNormedField.{0} Real
                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
      Real Real.instAdd
      (@SMulZeroClass.toSMul.{0, 0} Real Real
        (@AddZero.toZero.{0} Real
          (@AddZeroClass.toAddZero.{0} Real
            (@AddMonoid.toAddZeroClass.{0} Real
              (@SubNegMonoid.toAddMonoid.{0} Real
                (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} Real Real
          (@AddMonoid.toAddZeroClass.{0} Real
            (@SubNegMonoid.toAddMonoid.{0} Real
              (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))
          (@DistribMulAction.toDistribSMul.{0, 0} Real Real
            (@Semiring.toMonoid.{0} Real
              (@CommSemiring.toSemiring.{0} Real
                (@Semifield.toCommSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
            (@SubNegMonoid.toAddMonoid.{0} Real
              (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))
            (@Module.toDistribMulAction.{0, 0} Real Real
              (@CommSemiring.toSemiring.{0} Real
                (@Semifield.toCommSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
              (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
              (@Semiring.toModule.{0} Real
                (@CommSemiring.toSemiring.{0} Real
                  (@Semifield.toCommSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))))))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@IsTopologicalSemiring.toIsModuleTopology.{0} Real Real.semiring
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real
            (@SeminormedRing.toPseudoMetricSpace.{0} Real
              (@SeminormedCommRing.toSeminormedRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real
                  (@NormedField.toNormedCommRing.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
        (@IsTopologicalRing.toIsTopologicalSemiring.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real
              (@SeminormedRing.toPseudoMetricSpace.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
              (@CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))
          instIsTopologicalRingReal)))
    (fun (t : Real) => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (Real.tan t) t)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (Real.tan x)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    x
```
