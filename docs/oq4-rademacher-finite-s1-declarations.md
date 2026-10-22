# RademacherFiniteS1 完整规范声明清单

STATUS: AUTHOR_CANONICAL_READY；已冻结，独立最终审查待完成。

实际规范模块：Shao.OQ4.RademacherFiniteS1。原始 Source 唯一导入 Shao.OQ4.RademacherAllModes。

规范源与已冻结私有 Source 原字节相同，SHA256 d51b0d0712867e7a078871a49e3ffa7c8c59edf6695e07a306b9fe7bb4c65d13；13559B。

唯一新 olean SHA256 96f0010c733402bcf2a67fac0a8a631ec3642e91c0dffaa57e6c2d1196f61a41；942160B。

完整原 Source 的真实模块反射按全部 getModuleIdxFor?=none 选取，无名字/命名空间过滤。source、actual direct target 与 all42 的全部目标项逐字段一致，包括原名、kind、universes、完整 raw Expr 类型、公理、全部定义体及实例标记。

实测分类：{"public explicit theorem": 19, "generated helper": 40, "private explicit theorem": 8, "public explicit def": 1}；source/direct/all42 target=68/68/68。

all42 实际 owner OR namespace 联集 931 项，definition-kind 100；旧 863 项及全部旧 owner/字段精确保全。新增 distinct 68；旧名交集 0；外命名空间项 0。

完整实例注册表：source/direct 24838 项完全一致；old41/all42 25020 项完全一致，active、erased、imported global/scoped/new-entry 域逐项核对。新实例 0。

原始 Expr、注册表和日志只保留在服务器自有 repro_outputs/oq4-rademacher-finite-s1。

## Shao.OQ4.RademacherFiniteS1.odd_mode_inverse

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m j : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j)
  (hodd :
    @Eq.{1} Nat
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) j
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
  And
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) j
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) j
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      j)
```

## Shao.OQ4.RademacherFiniteS1.sum_vector_odd._simp_1_2

- 分类：generated helper
- kind：theorem
- universes：["u_2"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherFiniteS1.sum_vector_odd._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：["u_2"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sine_sum_telescope

- 分类：private explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (a : Real) (N : Nat),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (Real.sin
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            a
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range N) fun (k : Nat) =>
        Real.sin
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast k)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (Real.cos
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) a
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      (Real.cos
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_states_range._proof_1_6

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ (m k : Nat),
  Not
      (@Eq.{1} Nat
        (Int.toNat
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt k)
              (@Nat.cast.{0} Int instNatCastInt m))
            (@Nat.cast.{0} Int instNatCastInt m)))
        k) →
    False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_even_zero_raw

- 分类：private explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m k : Nat),
  @Eq.{1} Real
    (Shao.OQ4.RademacherFiniteBasis.vector m
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_zero_raw._simp_1_4

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## Shao.OQ4.RademacherFiniteS1.mode_parity_partition._simp_1_4

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## Shao.OQ4.RademacherFiniteS1.mode_parity_partition._proof_1_5

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

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
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (ho :
    @Eq.{1} Nat
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) j
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
  Not
      (@LT.lt.{0} Nat instLTNat
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) j
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_states_range._simp_1_2

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## Shao.OQ4.RademacherFiniteS1.mode_parity_partition._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## Shao.OQ4.RademacherFiniteS1.cotangent

- 分类：public explicit def
- kind：definition
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
(x : Real) → Real
```

完整定义体（pp.all）：

```lean
fun (x : Real) =>
  @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (Real.cos x) (Real.sin x)
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_states_range

- 分类：private explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (F : Int → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) => F s)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (k : Nat) =>
      F
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt k)
          (@Nat.cast.{0} Int instNatCastInt m)))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_modes_odd

- 分类：private explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (F : Nat → Real)
  (heven :
    ∀ (k : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m)
          k →
        @Eq.{1} Real
          (F
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.modes m) fun (j : Nat) => F j)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (ell : Nat) =>
      F
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_zero_raw._simp_1_2

- 分类：generated helper
- kind：theorem
- universes：["u_2"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherFiniteS1.vector_odd_zero

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (_hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (ell : Nat)
  (_hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  @Eq.{1} Real
    (Shao.OQ4.RademacherFiniteBasis.vector m
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) ell)
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_states_range._proof_1_4

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (s t : Int)
  (he :
    @Eq.{1} Nat
      (Int.toNat
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s (@Nat.cast.{0} Int instNatCastInt m)))
      (Int.toNat
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) t (@Nat.cast.{0} Int instNatCastInt m))))
  (hs :
    And
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) s)
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder) s (@Nat.cast.{0} Int instNatCastInt m)))
  (ht :
    And
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) t)
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder) t (@Nat.cast.{0} Int instNatCastInt m))),
  Not (@Eq.{1} Int s t) → False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_states_range._proof_1_3

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (s : Int)
  (hs :
    And
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) s)
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder) s (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (@LT.lt.{0} Nat instLTNat
        (Int.toNat
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s (@Nat.cast.{0} Int instNatCastInt m)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherFiniteS1.odd_half_angle_bounds._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## Shao.OQ4.RademacherFiniteS1.mode_parity_partition._proof_1_2

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

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
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (he :
    @Eq.{1} Nat
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) j
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  Not
      (And
        (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) j
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) j
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          m)) →
    False
```

## Shao.OQ4.RademacherFiniteS1.even_mode_mem_iff

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m k : Nat),
  Iff
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m)
      k)
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_inverse._simp_1_2

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## Shao.OQ4.RademacherFiniteS1.mode_parity_partition

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m j : Nat)
  (hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j),
  Or
    (@Exists.{1} Nat fun (k : Nat) =>
      And
        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m)
          k)
        (@Eq.{1} Nat j
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
    (@Exists.{1} Nat fun (ell : Nat) =>
      And
        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (Finset.range
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          ell)
        (@Eq.{1} Nat j
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

## Shao.OQ4.RademacherFiniteS1.vector_even_zero

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (_hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (k : Nat)
  (_hk :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m)
      k),
  @Eq.{1} Real
    (Shao.OQ4.RademacherFiniteBasis.vector m
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_zero_raw._simp_1_3

- 分类：generated helper
- kind：theorem
- universes：["u_2"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_inverse._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_odd_zero_raw

- 分类：private explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Real
    (Shao.OQ4.RademacherFiniteBasis.vector m
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) ell)
```

## Shao.OQ4.RademacherFiniteS1.odd_half_angle_bounds

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (_hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (ell : Nat)
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Real.pi)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
    (@LT.lt.{0} Real Real.instLT
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Real.pi)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        Real.pi
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## Shao.OQ4.RademacherFiniteS1.killedMass_low._proof_1_2

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ (k : Nat),
  Not
      (@Eq.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)) →
    False
```

## Shao.OQ4.RademacherFiniteS1.killedMass_low._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ (n : Nat), @Eq.{1} Prop (@Eq.{1} Nat (Nat.succ n) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_vector_range

- 分类：private explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m j : Nat),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) =>
      Shao.OQ4.RademacherFiniteBasis.vector m j s)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (k : Nat) =>
      Real.sin
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherFiniteBasis.theta m j)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast k)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## Shao.OQ4.RademacherFiniteS1.killedMass_low

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (h : Real)
  (hh : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
  (hh1 : @LT.lt.{0} Real Real.instLT h (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (n : Nat),
  @Eq.{1} Real
    (@Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h n
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (@ite.{1} Real (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (instDecidableEqNat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_states_range._proof_1_5

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m k : Nat)
  (hk :
    @LT.lt.{0} Nat instLTNat k
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  Not
      (And
        (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
          (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m))
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt k)
            (@Nat.cast.{0} Int instNatCastInt m)))
        (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt k)
            (@Nat.cast.{0} Int instNatCastInt m))
          (@Nat.cast.{0} Int instNatCastInt m))) →
    False
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_inverse._proof_1_3

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m j : Nat)
  (hodd :
    @Eq.{1} Nat
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) j
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
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
        (@LT.lt.{0} Nat instLTNat
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) j
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Eq.{1} Nat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) j
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          j)) →
    False
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_injective

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
@Function.Injective.{1, 1} Nat Nat fun (ell : Nat) =>
  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_zero_raw

- 分类：private explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m j : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.vector m j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (Real.sin
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast j)
          Real.pi)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## Shao.OQ4.RademacherFiniteS1.mode_parity_partition._proof_1_3

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ (m j : Nat)
  (he :
    @Eq.{1} Nat
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) j
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  Not
      (@Eq.{1} Nat j
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) j
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) →
    False
```

## Shao.OQ4.RademacherFiniteS1.survivalCoefficient_odd

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (ell : Nat)
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  @Eq.{1} Real
    (Shao.OQ4.RademacherAllModes.survivalCoefficient m
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (Shao.OQ4.RademacherFiniteS1.cotangent
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Real.pi)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast m)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))
```

## Shao.OQ4.RademacherFiniteS1.sum_vector_odd._simp_1_7

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

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

## Shao.OQ4.RademacherFiniteS1.killedKernel_zero_low

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (h : Real)
  (hh : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
  (hh1 : @LT.lt.{0} Real Real.instLT h (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Eq.{1} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
    (@DFunLike.coe.{1, 1, 1} (@ProbabilityTheory.Kernel.{0, 0} Real Real Real.measurableSpace Real.measurableSpace) Real
      (fun (x : Real) => @MeasureTheory.Measure.{0} Real Real.measurableSpace)
      (@ProbabilityTheory.Kernel.instFunLike.{0, 0} Real Real Real.measurableSpace Real.measurableSpace)
      (@Shao.OQ4.killedKernel Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (@OfNat.ofNat.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace) (nat_lit 0)
      (@Zero.toOfNat0.{0} (@MeasureTheory.Measure.{0} Real Real.measurableSpace)
        (@MeasureTheory.Measure.instZero.{0} Real Real.measurableSpace)))
```

## Shao.OQ4.RademacherFiniteS1.sum_vector_odd._simp_1_4

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_zero_raw._simp_1_7

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

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

## Shao.OQ4.RademacherFiniteS1.vector_zero

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (_hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (j : Nat)
  (_hj :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m) j),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.vector m j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (Real.sin
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast j)
          Real.pi)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_injective._proof_1_1

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ ⦃a b : Nat⦄
  (hab :
    @Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  Not (@Eq.{1} Nat a b) → False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_states_range._proof_1_7

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (s : Int)
  (hs :
    And
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt m)) s)
      (@LE.le.{0} Int (@Preorder.toLE.{0} Int Int.instPreorder) s (@Nat.cast.{0} Int instNatCastInt m))),
  Not
      (@Eq.{1} Int s
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@Nat.cast.{0} Int instNatCastInt
            (Int.toNat
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) s
                (@Nat.cast.{0} Int instNatCastInt m))))
          (@Nat.cast.{0} Int instNatCastInt m))) →
    False
```

## Shao.OQ4.RademacherFiniteS1.sum_vector_odd._simp_1_6

- 分类：generated helper
- kind：theorem
- universes：["u_3"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

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

## Shao.OQ4.RademacherFiniteS1.sum_vector_odd._simp_1_3

- 分类：generated helper
- kind：theorem
- universes：["u_2"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherFiniteS1.finite_s1_zero

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
        (Finset.range
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        fun (ell : Nat) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              ell)
            (Shao.OQ4.RademacherFiniteS1.cotangent
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Real.pi)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast m)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Real.cos
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Real.pi)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast m)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherFiniteS1.modes_eq

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} (Finset.{0} Nat) (Shao.OQ4.RademacherFiniteBasis.modes m)
    (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_mem_iff._simp_1_2

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## Shao.OQ4.RademacherFiniteS1.odd_half_angle_sin_ne_zero

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (ell : Nat)
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  @Ne.{1} Real
    (Real.sin
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Real.pi)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_zero_raw._simp_1_5

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

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

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.theta_formula

- 分类：private explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m j : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherFiniteBasis.theta m j)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast j)
        Real.pi)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## Shao.OQ4.RademacherFiniteS1.killedMass_finite_s1

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (n : Nat),
  @Eq.{1} Real
    (@Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h n
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
        (Finset.range
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        fun (ell : Nat) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              ell)
            (Shao.OQ4.RademacherFiniteS1.cotangent
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Real.pi)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast m)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Real.cos
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Real.pi)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast m)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
            n)))
```

## Shao.OQ4.RademacherFiniteS1.even_mode_mem_iff._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## Shao.OQ4.RademacherFiniteS1.odd_half_angle_bounds._proof_1_2

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ (m ell : Nat)
  (hell :
    @LT.lt.{0} Nat instLTNat ell
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  Not
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_zero_raw._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：["u_2"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_mem_iff._proof_1_3

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m ell : Nat),
  Not
      (Iff
        (And
          (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@LT.lt.{0} Nat instLTNat ell
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
    False
```

## Shao.OQ4.RademacherFiniteS1.mode_parity_partition._proof_1_6

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, propext

完整类型（pp.all）：

```lean
∀ (m j : Nat)
  (ho :
    @Eq.{1} Nat
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) j
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
  Not
      (@Eq.{1} Nat j
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) j
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.sum_states_range._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## Shao.OQ4.RademacherFiniteS1.even_mode_mem_iff._proof_1_2

- 分类：generated helper
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m k : Nat),
  Not
      (Iff
        (And
          (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
          (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (And
          (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
          (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) k m))) →
    False
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_mem_iff._simp_1_1

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Icc.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) x b))
```

## _private.Shao.OQ4.RademacherFiniteS1.0.Shao.OQ4.RademacherFiniteS1.vector_zero_raw._simp_1_6

- 分类：generated helper
- kind：theorem
- universes：["u_3"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

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

## Shao.OQ4.RademacherFiniteS1.sum_vector_odd._simp_1_5

- 分类：generated helper
- kind：theorem
- universes：["u_1"]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：propext

完整类型（pp.all）：

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

## Shao.OQ4.RademacherFiniteS1.closedStrip_probability_finite_s1

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

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
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
        (Finset.range
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        fun (ell : Nat) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              ell)
            (Shao.OQ4.RademacherFiniteS1.cotangent
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Real.pi)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast m)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Real.cos
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Real.pi)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast m)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
            n)))
```

## Shao.OQ4.RademacherFiniteS1.sum_vector_odd

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (ell : Nat)
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Int Real Real.instAddCommMonoid (Shao.OQ4.RademacherFiniteBasis.states m) fun (s : Int) =>
      Shao.OQ4.RademacherFiniteBasis.vector m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        s)
    (Shao.OQ4.RademacherFiniteS1.cotangent
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Real.pi)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```

## Shao.OQ4.RademacherFiniteS1.odd_mode_mem_iff

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (m ell : Nat),
  Iff
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherFiniteBasis.modes m)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell)
```

## Shao.OQ4.RademacherFiniteS1.closedStrip_probability_low

- 分类：public explicit theorem
- kind：theorem
- universes：[]
- instance：false
- unsafe：false
- all42 actual owner：Shao.OQ4.RademacherFiniteS1
- old41 overlap：false
- axioms：Quot.sound, Classical.choice, propext

完整类型（pp.all）：

```lean
∀ (h : Real)
  (hh : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
  (hh1 : @LT.lt.{0} Real Real.instLT h (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (n : Nat),
  @Eq.{1} Real
    (@MeasureTheory.Measure.real.{0} ((i : Fin n) → Real)
      (@MeasurableSpace.pi.{0, 0} (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.measurableSpace)
      (@MeasureTheory.Measure.pi.{0, 0} (Fin n) (fun (x : Fin n) => Real) (Fin.fintype n)
        (fun (i : Fin n) => Real.measurableSpace) fun (x : Fin n) => Shao.OQ4.RademacherCosine.law)
      (@Shao.closedStrip n h))
    (@ite.{1} Real (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (instDecidableEqNat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```
