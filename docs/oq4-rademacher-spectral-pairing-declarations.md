# RademacherSpectralPairing 完整规范声明清单

STATUS: AUTHOR_CANONICAL_READY
AUTHOR_TARGET_WRITES: FROZEN
INDEPENDENT_FINAL: PENDING_HOLD

本清单是唯一规范作者的完整交付，尚非独立最终形式审查。P1/P2对应一个原始精确配对义务；69个显式公开定理等数量是声明清点，不作69个独立数学目标。

规范Source与选择原Source同字节：7cc1e142db3c9e6f2c788ca83f213bb2ea1c4d58d2207b30a43ed5fd471d50ea；24435B。唯一规范olean：b90ac1f16d32e4ebca0b616e6bada7da37d9e07f4648f8a7bf80c1f812be4df1；1234496B；sole emit attempt1，空日志退出0。

实际原Source -R/all-none145、实际direct145、actual full44 target145的原名/kind/universes/完整Expr类型、13个全部定义值、metadata/flags/axioms等字段一致。完整原Source不自导入own olean，不前置旧43 imports。

69 public explicit theorem、13 public explicit def、2 private explicit theorem、61 generated helper；rawoutsideprefix2恰为_private wrappers，usernamespaceoutside0。raw及user实际旧43交集均0。

全44实际1135记录/121定义值；旧43的990记录/108定义值全保留。实际header模块44；有record owner模块43；Foundations没有自身声明，不混用两种模块计数。

本规范补全了旧私有d79收据未覆盖的完整登记结构，旧d79及f05文件保持原字节。相同scope完整active/global/scoped/private/inactive/erased/new/default、stateStack/flags、实际discrTree paths/entries/children顺序均已比较。generic metadata工具按lead授权复用并披露，不假称工具独立。

## Shao.OQ4.RademacherSpectralPairing.alpha

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"alpha"]
- user Name：Shao.OQ4.RademacherSpectralPairing.alpha
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m ell : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m ell : Nat) =>
  @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real.pi)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast Shao.OQ4.RademacherSpectralPairing.alpha._proof_1))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## Shao.OQ4.RademacherSpectralPairing.alpha._proof_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"alpha"],"_proof_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.alpha._proof_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext

完整类型（actual direct pp.all）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherSpectralPairing.alpha.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"alpha"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.alpha.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.alpha m ell)
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
            Shao.OQ4.RademacherSpectralPairing.alpha._proof_1))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## Shao.OQ4.RademacherSpectralPairing.alpha_bounds

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"alpha_bounds"]
- user Name：Shao.OQ4.RademacherSpectralPairing.alpha_bounds
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (Shao.OQ4.RademacherSpectralPairing.alpha m ell))
    (@LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherSpectralPairing.alpha m ell)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        Real.pi
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## Shao.OQ4.RademacherSpectralPairing.alpha_bounds._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"alpha_bounds"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.alpha_bounds._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (helle : @LE.le.{0} Nat instLENat ell m),
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

## Shao.OQ4.RademacherSpectralPairing.alpha_center

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"alpha_center"]
- user Name：Shao.OQ4.RademacherSpectralPairing.alpha_center
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @Even.{0} Nat instAddNat m),
  @Eq.{1} Real
    (Shao.OQ4.RademacherSpectralPairing.alpha m
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Real.pi
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
```

## Shao.OQ4.RademacherSpectralPairing.alpha_reflect

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"alpha_reflect"]
- user Name：Shao.OQ4.RademacherSpectralPairing.alpha_reflect
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.alpha m (Shao.OQ4.RademacherSpectralPairing.reflect m ell))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        Real.pi
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (Shao.OQ4.RademacherSpectralPairing.alpha m ell))
```

## Shao.OQ4.RademacherSpectralPairing.amplitude

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"amplitude"]
- user Name：Shao.OQ4.RademacherSpectralPairing.amplitude
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m : Nat) =>
  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (Shao.OQ4.RademacherFiniteS1.cotangent
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        Real.pi
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              Shao.OQ4.RademacherSpectralPairing.alpha._proof_1))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```

## Shao.OQ4.RademacherSpectralPairing.amplitude_pos

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"amplitude_pos"]
- user Name：Shao.OQ4.RademacherSpectralPairing.amplitude_pos
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherSpectralPairing.amplitude m)
```

## Shao.OQ4.RademacherSpectralPairing.beta

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m ell : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m ell : Nat) =>
  @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real.pi)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast Shao.OQ4.RademacherSpectralPairing.beta._proof_1))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## Shao.OQ4.RademacherSpectralPairing.beta._proof_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta"],"_proof_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta._proof_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext

完整类型（actual direct pp.all）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## Shao.OQ4.RademacherSpectralPairing.beta.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.beta m ell)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Nat.cast.{0} Real Real.instNatCast
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        Real.pi)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast Shao.OQ4.RademacherSpectralPairing.beta._proof_1))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## Shao.OQ4.RademacherSpectralPairing.beta_bounds

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta_bounds"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta_bounds
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (Shao.OQ4.RademacherSpectralPairing.beta m ell))
    (@LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherSpectralPairing.beta m ell) Real.pi)
```

## Shao.OQ4.RademacherSpectralPairing.beta_center

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta_center"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta_center
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @Even.{0} Nat instAddNat m),
  @Eq.{1} Real
    (Shao.OQ4.RademacherSpectralPairing.beta m
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Real.pi
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
```

## Shao.OQ4.RademacherSpectralPairing.beta_eq_twice_alpha

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta_eq_twice_alpha"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta_eq_twice_alpha
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.beta m ell)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (Shao.OQ4.RademacherSpectralPairing.alpha m ell))
```

## Shao.OQ4.RademacherSpectralPairing.beta_reflect

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta_reflect"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta_reflect
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.beta m (Shao.OQ4.RademacherSpectralPairing.reflect m ell))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) Real.pi
      (Shao.OQ4.RademacherSpectralPairing.beta m ell))
```

## Shao.OQ4.RademacherSpectralPairing.beta_strict_mono

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta_strict_mono"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta_strict_mono
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat), @StrictMono.{0, 0} Nat Real Nat.instPreorder Real.instPreorder (Shao.OQ4.RademacherSpectralPairing.beta m)
```

## Shao.OQ4.RademacherSpectralPairing.beta_strict_mono._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"beta_strict_mono"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.beta_strict_mono._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ ⦃i j : Nat⦄ (hij : @LT.lt.{0} Nat (@Preorder.toLT.{0} Nat Nat.instPreorder) i j),
  Not
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.centerModes

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"centerModes"]
- user Name：Shao.OQ4.RademacherSpectralPairing.centerModes
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m : Nat) → Finset.{0} Nat
```

完整定义体（actual direct pp.all）：

```lean
fun (m : Nat) =>
  @Finset.filter.{0} Nat
    (fun (ell : Nat) =>
      @Eq.{1} Nat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        m)
    (fun (a : Nat) =>
      instDecidableEqNat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
        m)
    (Finset.range
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## Shao.OQ4.RademacherSpectralPairing.centerModes.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"centerModes"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.centerModes.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} (Finset.{0} Nat) (Shao.OQ4.RademacherSpectralPairing.centerModes m)
    (@Finset.filter.{0} Nat
      (fun (ell : Nat) =>
        @Eq.{1} Nat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          m)
      (fun (a : Nat) =>
        instDecidableEqNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
          m)
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

## Shao.OQ4.RademacherSpectralPairing.centerModes_eq

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"centerModes_eq"]
- user Name：Shao.OQ4.RademacherSpectralPairing.centerModes_eq
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} (Finset.{0} Nat) (Shao.OQ4.RademacherSpectralPairing.centerModes m)
    (@ite.{1} (Finset.{0} Nat) (@Even.{0} Nat instAddNat m) (Nat.instDecidablePredEven m)
      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@EmptyCollection.emptyCollection.{0} (Finset.{0} Nat) (@Finset.instEmptyCollection.{0} Nat)))
```

## Shao.OQ4.RademacherSpectralPairing.centerModes_eq._proof_1_3

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"centerModes_eq"],"_proof_1_3"]
- user Name：Shao.OQ4.RademacherSpectralPairing.centerModes_eq._proof_1_3
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat)
  (hhalf :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      m),
  Not
      (Iff
        (@Eq.{1} Nat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          m)
        (@Eq.{1} Nat ell
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.centerModes_eq._proof_1_5

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"centerModes_eq"],"_proof_1_5"]
- user Name：Shao.OQ4.RademacherSpectralPairing.centerModes_eq._proof_1_5
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat)
  (he :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m),
  Not (@Eq.{1} Nat m (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ell ell)) → False
```

## Shao.OQ4.RademacherSpectralPairing.centerModes_eq._simp_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"centerModes_eq"],"_simp_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.centerModes_eq._simp_1_1
- universes：[["str",["anonymous"],"u_1"]]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {α : Type u_1} {a b : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Singleton.singleton.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instSingleton.{u_1} α) a) b)
    (@Eq.{u_1 + 1} α b a)
```

## Shao.OQ4.RademacherSpectralPairing.centerModes_eq._simp_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"centerModes_eq"],"_simp_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.centerModes_eq._simp_1_2
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.centerModes m) ell)
    (@Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
```

## Shao.OQ4.RademacherSpectralPairing.centerModes_eq._simp_1_4

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"centerModes_eq"],"_simp_1_4"]
- user Name：Shao.OQ4.RademacherSpectralPairing.centerModes_eq._simp_1_4
- universes：[["str",["anonymous"],"u_1"]]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {α : Type u_1} (a : α),
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@EmptyCollection.emptyCollection.{u_1} (Finset.{u_1} α) (@Finset.instEmptyCollection.{u_1} α)) a)
    False
```

## Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_eq_killedMass

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"closedStrip_probability_eq_killedMass"]
- user Name：Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_eq_killedMass
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

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
    (@Shao.OQ4.killedMass Shao.OQ4.RademacherCosine.law Shao.OQ4.RademacherCosine.law_isProbabilityMeasure h n
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_normalized

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"closedStrip_probability_normalized"]
- user Name：Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_normalized
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

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
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherSpectralPairing.amplitude m)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (Shao.OQ4.RademacherSpectralPairing.rho m) n))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Shao.OQ4.RademacherSpectralPairing.epsilon m n)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Real.tan
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Nat.cast.{0} Real Real.instNatCast m)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (Shao.OQ4.RademacherSpectralPairing.remainder m n)))
```

## Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_paired

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"closedStrip_probability_paired"]
- user Name：Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_paired
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

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
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
          fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.pairedTerm m n ell))
      (Shao.OQ4.RademacherSpectralPairing.zeroMode m n))
```

## Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_zero

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"closedStrip_probability_zero"]
- user Name：Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_zero
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (h : Real)
  (hmh : @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) h)
  (hhm :
    @LT.lt.{0} Real Real.instLT h
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  @Eq.{1} Real
    (@MeasureTheory.Measure.real.{0} ((i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) → Real)
      (@MeasurableSpace.pi.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) => Real.measurableSpace)
      (@MeasureTheory.Measure.pi.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) => Real)
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) => Real.measurableSpace)
        fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) => Shao.OQ4.RademacherCosine.law)
      (@Shao.closedStrip (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) h))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherSpectralPairing.cos_beta_neg

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cos_beta_neg"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cos_beta_neg
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@Finset.image.{0, 0} Nat Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.reflect m)
        (Shao.OQ4.RademacherSpectralPairing.lowerModes m))
      ell),
  @LT.lt.{0} Real Real.instLT (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## Shao.OQ4.RademacherSpectralPairing.cos_beta_pos

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cos_beta_pos"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cos_beta_pos
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell))
```

## Shao.OQ4.RademacherSpectralPairing.cos_beta_reflect

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cos_beta_reflect"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cos_beta_reflect
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  @Eq.{1} Real (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m (Shao.OQ4.RademacherSpectralPairing.reflect m ell)))
    (@Neg.neg.{0} Real Real.instNeg (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell)))
```

## Shao.OQ4.RademacherSpectralPairing.cos_beta_zero_iff

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cos_beta_zero_iff"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cos_beta_zero_iff
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  Iff
    (@Eq.{1} Real (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (@Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
```

## Shao.OQ4.RademacherSpectralPairing.cos_beta_zero_iff._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cos_beta_zero_iff"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cos_beta_zero_iff._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (he :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m),
  Not (@Eq.{1} Nat m (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ell ell)) → False
```

## Shao.OQ4.RademacherSpectralPairing.cos_beta_zero_iff._proof_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cos_beta_zero_iff"],"_proof_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cos_beta_zero_iff._proof_1_2
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (he :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m),
  Not
      (@Eq.{1} Nat ell
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.cotangent_pi_div_four

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cotangent_pi_div_four"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cotangent_pi_div_four
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
@Eq.{1} Real
  (Shao.OQ4.RademacherFiniteS1.cotangent
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Real.pi
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherSpectralPairing.cotangent_reflect

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cotangent_reflect"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cotangent_reflect
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  @Eq.{1} Real
    (Shao.OQ4.RademacherFiniteS1.cotangent
      (Shao.OQ4.RademacherSpectralPairing.alpha m (Shao.OQ4.RademacherSpectralPairing.reflect m ell)))
    (Real.tan (Shao.OQ4.RademacherSpectralPairing.alpha m ell))
```

## Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"eigenvalue_le_rho"]
- user Name：Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  @LE.le.{0} Real Real.instLE (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell))
    (Shao.OQ4.RademacherSpectralPairing.rho m)
```

## Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho._proof_1_4

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"eigenvalue_le_rho"],"_proof_1_4"]
- user Name：Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho._proof_1_4
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat},
  Not
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho._proof_1_5

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"eigenvalue_le_rho"],"_proof_1_5"]
- user Name：Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho._proof_1_5
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {ell : Nat} (he : Not (@Eq.{1} Nat ell (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))),
  Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ell) → False
```

## Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho._simp_1_3

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"eigenvalue_le_rho"],"_simp_1_3"]
- user Name：Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho._simp_1_3
- universes：[["str",["anonymous"],"u_1"]]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext

完整类型（actual direct pp.all）：

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] (a : α), @Eq.{1} Prop (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a a) True
```

## Shao.OQ4.RademacherSpectralPairing.epsilon

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"epsilon"]
- user Name：Shao.OQ4.RademacherSpectralPairing.epsilon
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m n : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m n : Nat) =>
  @HPow.hPow.{0, 0, 0} Real Nat Real
    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n m)
```

## Shao.OQ4.RademacherSpectralPairing.epsilon.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"epsilon"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.epsilon.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m n : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.epsilon m n)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n m))
```

## Shao.OQ4.RademacherSpectralPairing.even_twice_half

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"even_twice_half"]
- user Name：Shao.OQ4.RademacherSpectralPairing.even_twice_half
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @Even.{0} Nat instAddNat m),
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    m
```

## Shao.OQ4.RademacherSpectralPairing.even_twice_half._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"even_twice_half"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.even_twice_half._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat}
  (hmod :
    @Eq.{1} Nat
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) m
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  Not
      (@Eq.{1} Nat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        m) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.first_pair

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"first_pair"]
- user Name：Shao.OQ4.RademacherSpectralPairing.first_pair
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (n : Nat),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (Shao.OQ4.RademacherSpectralPairing.pairedTerm m n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherSpectralPairing.amplitude m)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (Shao.OQ4.RademacherSpectralPairing.rho m) n))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherSpectralPairing.epsilon m n)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Real.tan
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast m)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
```

## Shao.OQ4.RademacherSpectralPairing.full_sum_pairing

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"full_sum_pairing"]
- user Name：Shao.OQ4.RademacherSpectralPairing.full_sum_pairing
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m n : Nat),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.rawTerm m n ell)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
        fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.pairedTerm m n ell)
      (@ite.{1} Real (@Even.{0} Nat instAddNat m) (Nat.instDecidablePredEven m)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) n))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
```

## Shao.OQ4.RademacherSpectralPairing.killedMass_normalized

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"killedMass_normalized"]
- user Name：Shao.OQ4.RademacherSpectralPairing.killedMass_normalized
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

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
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherSpectralPairing.amplitude m)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (Shao.OQ4.RademacherSpectralPairing.rho m) n))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Shao.OQ4.RademacherSpectralPairing.epsilon m n)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Real.tan
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Nat.cast.{0} Real Real.instNatCast m)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (Shao.OQ4.RademacherSpectralPairing.remainder m n)))
```

## Shao.OQ4.RademacherSpectralPairing.killedMass_paired

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"killedMass_paired"]
- user Name：Shao.OQ4.RademacherSpectralPairing.killedMass_paired
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

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
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
          fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.pairedTerm m n ell))
      (Shao.OQ4.RademacherSpectralPairing.zeroMode m n))
```

## Shao.OQ4.RademacherSpectralPairing.last_mode_coefficient

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"last_mode_coefficient"]
- user Name：Shao.OQ4.RademacherSpectralPairing.last_mode_coefficient
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) m)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (Shao.OQ4.RademacherFiniteS1.cotangent (Shao.OQ4.RademacherSpectralPairing.alpha m m)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) m)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (Real.tan
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          Real.pi
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast m)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))
```

## Shao.OQ4.RademacherSpectralPairing.last_mode_coefficient._proof_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"last_mode_coefficient"],"_proof_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.last_mode_coefficient._proof_1_2
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat)
  (hr :
    @Eq.{1} Nat
      (Shao.OQ4.RademacherSpectralPairing.reflect m (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) m),
  Not (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) → False
```

## Shao.OQ4.RademacherSpectralPairing.last_mode_contribution

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"last_mode_contribution"]
- user Name：Shao.OQ4.RademacherSpectralPairing.last_mode_contribution
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m n : Nat),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (Shao.OQ4.RademacherSpectralPairing.rawTerm m n m))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            m)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (Real.tan
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            Real.pi
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
        (@Neg.neg.{0} Real Real.instNeg (Shao.OQ4.RademacherSpectralPairing.rho m)) n))
```

## Shao.OQ4.RademacherSpectralPairing.last_mode_eigenvalue

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"last_mode_eigenvalue"]
- user Name：Shao.OQ4.RademacherSpectralPairing.last_mode_eigenvalue
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} Real (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m m))
    (@Neg.neg.{0} Real Real.instNeg (Shao.OQ4.RademacherSpectralPairing.rho m))
```

## Shao.OQ4.RademacherSpectralPairing.last_mode_eigenvalue._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"last_mode_eigenvalue"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.last_mode_eigenvalue._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat), Not (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) → False
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m : Nat) → Finset.{0} Nat
```

完整定义体（actual direct pp.all）：

```lean
fun (m : Nat) =>
  @Finset.filter.{0} Nat
    (fun (ell : Nat) =>
      @LT.lt.{0} Nat instLTNat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        m)
    (fun (a : Nat) =>
      Nat.decLt
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
        m)
    (Finset.range
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} (Finset.{0} Nat) (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
    (@Finset.filter.{0} Nat
      (fun (ell : Nat) =>
        @LT.lt.{0} Nat instLTNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          m)
      (fun (a : Nat) =>
        Nat.decLt
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
          m)
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_le

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_le"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_le
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell),
  @LE.le.{0} Nat instLENat ell m
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_le._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_le"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_le._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m),
  Not (@LE.le.{0} Nat instLENat ell m) → False
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_one

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_one"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_one
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
@Eq.{1} (Finset.{0} Nat)
  (Shao.OQ4.RademacherSpectralPairing.lowerModes (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_one._proof_1_3

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_one"],"_proof_1_3"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_one._proof_1_3
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (ell : Nat),
  Not
      (Iff
        (@LT.lt.{0} Nat instLTNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat ell (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_one._simp_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_one"],"_simp_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_one._simp_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell)
    (@LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_one._simp_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_one"],"_simp_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_one._simp_1_2
- universes：[["str",["anonymous"],"u_1"]]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {α : Type u_1} {a b : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Singleton.singleton.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instSingleton.{u_1} α) a) b)
    (@Eq.{u_1 + 1} α b a)
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_two

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_two"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_two
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
@Eq.{1} (Finset.{0} Nat)
  (Shao.OQ4.RademacherSpectralPairing.lowerModes (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_two._proof_1_3

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_two"],"_proof_1_3"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_two._proof_1_3
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (ell : Nat),
  Not
      (Iff
        (@LT.lt.{0} Nat instLTNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Eq.{1} Nat ell (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_two._simp_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_two"],"_simp_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_two._simp_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell)
    (@LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
```

## Shao.OQ4.RademacherSpectralPairing.lowerModes_two._simp_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lowerModes_two"],"_simp_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lowerModes_two._simp_1_2
- universes：[["str",["anonymous"],"u_1"]]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {α : Type u_1} {a b : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Singleton.singleton.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instSingleton.{u_1} α) a) b)
    (@Eq.{u_1 + 1} α b a)
```

## Shao.OQ4.RademacherSpectralPairing.lower_alpha_bounds

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lower_alpha_bounds"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lower_alpha_bounds
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (Shao.OQ4.RademacherSpectralPairing.alpha m ell))
    (@LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherSpectralPairing.alpha m ell)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        Real.pi
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
```

## Shao.OQ4.RademacherSpectralPairing.lower_beta_bounds

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lower_beta_bounds"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lower_beta_bounds
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (Shao.OQ4.RademacherSpectralPairing.beta m ell))
    (@LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherSpectralPairing.beta m ell)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        Real.pi
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## Shao.OQ4.RademacherSpectralPairing.lower_frequency

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lower_frequency"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lower_frequency
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell),
  And
    (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## Shao.OQ4.RademacherSpectralPairing.lower_frequency._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lower_frequency"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lower_frequency._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m),
  Not
      (And
        (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@LT.lt.{0} Nat instLTNat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.lower_reflected_disjoint

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lower_reflected_disjoint"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lower_reflected_disjoint
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat)
    (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
    (@Finset.image.{0, 0} Nat Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.reflect m)
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m))
```

## Shao.OQ4.RademacherSpectralPairing.lower_reflected_disjoint._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lower_reflected_disjoint"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lower_reflected_disjoint._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) ⦃ell : Nat⦄
  (hl' :
    @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
  (hr' :
    And (@LE.le.{0} Nat instLENat ell m)
      (@LT.lt.{0} Nat instLTNat m
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell))),
  False
```

## Shao.OQ4.RademacherSpectralPairing.lower_trig_denominators

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"lower_trig_denominators"]
- user Name：Shao.OQ4.RademacherSpectralPairing.lower_trig_denominators
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (Real.sin (Shao.OQ4.RademacherSpectralPairing.alpha m ell)))
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (Real.cos (Shao.OQ4.RademacherSpectralPairing.alpha m ell)))
```

## Shao.OQ4.RademacherSpectralPairing.mem_centerModes

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_centerModes"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_centerModes
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  Iff
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.centerModes m) ell)
    (@Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
```

## Shao.OQ4.RademacherSpectralPairing.mem_centerModes._proof_1_4

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_centerModes"],"_proof_1_4"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_centerModes._proof_1_4
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  Not
      (Iff
        (And
          (@LT.lt.{0} Nat instLTNat ell
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Eq.{1} Nat
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
            m))
        (@Eq.{1} Nat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          m)) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.mem_centerModes._simp_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_centerModes"],"_simp_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_centerModes._simp_1_2
- universes：[["str",["anonymous"],"u_1"]]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## Shao.OQ4.RademacherSpectralPairing.mem_centerModes._simp_1_3

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_centerModes"],"_simp_1_3"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_centerModes._simp_1_3
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## Shao.OQ4.RademacherSpectralPairing.mem_lowerModes

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_lowerModes"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_lowerModes
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  Iff
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell)
    (@LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
```

## Shao.OQ4.RademacherSpectralPairing.mem_lowerModes._proof_1_4

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_lowerModes"],"_proof_1_4"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_lowerModes._proof_1_4
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  Not
      (Iff
        (And
          (@LT.lt.{0} Nat instLTNat ell
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@LT.lt.{0} Nat instLTNat
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
            m))
        (@LT.lt.{0} Nat instLTNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          m)) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.mem_lowerModes._simp_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_lowerModes"],"_simp_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_lowerModes._simp_1_2
- universes：[["str",["anonymous"],"u_1"]]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## Shao.OQ4.RademacherSpectralPairing.mem_lowerModes._simp_1_3

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_lowerModes"],"_simp_1_3"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_lowerModes._simp_1_3
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## Shao.OQ4.RademacherSpectralPairing.mem_reflectedModes

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_reflectedModes"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_reflectedModes
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  Iff
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@Finset.image.{0, 0} Nat Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.reflect m)
        (Shao.OQ4.RademacherSpectralPairing.lowerModes m))
      ell)
    (And (@LE.le.{0} Nat instLENat ell m)
      (@LT.lt.{0} Nat instLTNat m
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)))
```

## Shao.OQ4.RademacherSpectralPairing.mem_reflectedModes._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_reflectedModes"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_reflectedModes._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m k : Nat)
  (hk' :
    @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
      m),
  Not
      (And (@LE.le.{0} Nat instLENat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m k) m)
        (@LT.lt.{0} Nat instLTNat m
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m k)))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.mem_reflectedModes._proof_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"mem_reflectedModes"],"_proof_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.mem_reflectedModes._proof_1_2
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat) (hle : @LE.le.{0} Nat instLENat ell m)
  (hgt :
    @LT.lt.{0} Nat instLTNat m
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)),
  Not
      (@LT.lt.{0} Nat instLTNat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m ell))
        m) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.neg_rho_le_eigenvalue

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"neg_rho_le_eigenvalue"]
- user Name：Shao.OQ4.RademacherSpectralPairing.neg_rho_le_eigenvalue
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  @LE.le.{0} Real Real.instLE (@Neg.neg.{0} Real Real.instNeg (Shao.OQ4.RademacherSpectralPairing.rho m))
    (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell))
```

## Shao.OQ4.RademacherSpectralPairing.neg_rho_le_eigenvalue._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"neg_rho_le_eigenvalue"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.neg_rho_le_eigenvalue._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hle : @LE.le.{0} Nat instLENat ell m),
  Not
      (@LT.lt.{0} Nat instLTNat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m ell)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.normalizedTerm

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"normalizedTerm"]
- user Name：Shao.OQ4.RademacherSpectralPairing.normalizedTerm
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m n ell : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m n ell : Nat) =>
  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) ell)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (Shao.OQ4.RademacherFiniteS1.cotangent (Shao.OQ4.RademacherSpectralPairing.alpha m ell))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Shao.OQ4.RademacherSpectralPairing.epsilon m n)
            (Real.tan (Shao.OQ4.RademacherSpectralPairing.alpha m ell))))
        (Shao.OQ4.RademacherFiniteS1.cotangent
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            Real.pi
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  Shao.OQ4.RademacherSpectralPairing.alpha._proof_1))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@Nat.cast.{0} Real Real.instNatCast m)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell)) (Shao.OQ4.RademacherSpectralPairing.rho m))
      n)
```

## Shao.OQ4.RademacherSpectralPairing.normalized_term

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"normalized_term"]
- user Name：Shao.OQ4.RademacherSpectralPairing.normalized_term
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m)
  (n ell : Nat),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherSpectralPairing.amplitude m)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (Shao.OQ4.RademacherSpectralPairing.rho m) n))
      (Shao.OQ4.RademacherSpectralPairing.normalizedTerm m n ell))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (Shao.OQ4.RademacherSpectralPairing.pairedTerm m n ell))
```

## Shao.OQ4.RademacherSpectralPairing.normalized_zero

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"normalized_zero"]
- user Name：Shao.OQ4.RademacherSpectralPairing.normalized_zero
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Shao.OQ4.RademacherSpectralPairing.amplitude m)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              m)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Real.tan
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Nat.cast.{0} Real Real.instNatCast m)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (Shao.OQ4.RademacherSpectralPairing.remainder m (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherSpectralPairing.normalizer_pos

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"normalizer_pos"]
- user Name：Shao.OQ4.RademacherSpectralPairing.normalizer_pos
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (n : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (Shao.OQ4.RademacherSpectralPairing.amplitude m)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Shao.OQ4.RademacherSpectralPairing.rho m) n))
```

## Shao.OQ4.RademacherSpectralPairing.pair_term

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"pair_term"]
- user Name：Shao.OQ4.RademacherSpectralPairing.pair_term
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell)
  (n : Nat),
  @Eq.{1} Real
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (Shao.OQ4.RademacherSpectralPairing.rawTerm m n ell)
      (Shao.OQ4.RademacherSpectralPairing.rawTerm m n (Shao.OQ4.RademacherSpectralPairing.reflect m ell)))
    (Shao.OQ4.RademacherSpectralPairing.pairedTerm m n ell)
```

## Shao.OQ4.RademacherSpectralPairing.pairedTerm

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"pairedTerm"]
- user Name：Shao.OQ4.RademacherSpectralPairing.pairedTerm
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m n ell : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m n ell : Nat) =>
  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) ell)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (Shao.OQ4.RademacherFiniteS1.cotangent (Shao.OQ4.RademacherSpectralPairing.alpha m ell))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherSpectralPairing.epsilon m n)
          (Real.tan (Shao.OQ4.RademacherSpectralPairing.alpha m ell)))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell)) n)
```

## Shao.OQ4.RademacherSpectralPairing.paired_center_disjoint

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"paired_center_disjoint"]
- user Name：Shao.OQ4.RademacherSpectralPairing.paired_center_disjoint
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat)
    (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
      (@Finset.image.{0, 0} Nat Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.reflect m)
        (Shao.OQ4.RademacherSpectralPairing.lowerModes m)))
    (Shao.OQ4.RademacherSpectralPairing.centerModes m)
```

## Shao.OQ4.RademacherSpectralPairing.paired_center_disjoint._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"paired_center_disjoint"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.paired_center_disjoint._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) ⦃ell : Nat⦄
  (hc' :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
  (hl' :
    @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m),
  False
```

## Shao.OQ4.RademacherSpectralPairing.paired_center_disjoint._proof_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"paired_center_disjoint"],"_proof_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.paired_center_disjoint._proof_1_2
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) ⦃ell : Nat⦄
  (hc' :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
  (hr' :
    And (@LE.le.{0} Nat instLENat ell m)
      (@LT.lt.{0} Nat instLTNat m
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell))),
  False
```

## Shao.OQ4.RademacherSpectralPairing.paired_sum_normalized

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"paired_sum_normalized"]
- user Name：Shao.OQ4.RademacherSpectralPairing.paired_sum_normalized
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m) (n : Nat),
  @Eq.{1} Real
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
          fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.pairedTerm m n ell))
      (Shao.OQ4.RademacherSpectralPairing.zeroMode m n))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherSpectralPairing.amplitude m)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (Shao.OQ4.RademacherSpectralPairing.rho m) n))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Shao.OQ4.RademacherSpectralPairing.epsilon m n)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Real.tan
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Real.pi
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Nat.cast.{0} Real Real.instNatCast m)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (Shao.OQ4.RademacherSpectralPairing.remainder m n)))
```

## Shao.OQ4.RademacherSpectralPairing.principal_cotangent_pos

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"principal_cotangent_pos"]
- user Name：Shao.OQ4.RademacherSpectralPairing.principal_cotangent_pos
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherFiniteS1.cotangent
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        Real.pi
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```

## Shao.OQ4.RademacherSpectralPairing.range_partition

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"range_partition"]
- user Name：Shao.OQ4.RademacherSpectralPairing.range_partition
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} (Finset.{0} Nat)
    (Finset.range
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
      (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
        (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
        (@Finset.image.{0, 0} Nat Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.reflect m)
          (Shao.OQ4.RademacherSpectralPairing.lowerModes m)))
      (Shao.OQ4.RademacherSpectralPairing.centerModes m))
```

## Shao.OQ4.RademacherSpectralPairing.range_partition._proof_1_6

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"range_partition"],"_proof_1_6"]
- user Name：Shao.OQ4.RademacherSpectralPairing.range_partition._proof_1_6
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  Not
      (Iff
        (@LT.lt.{0} Nat instLTNat ell
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Or
          (Or
            (@LT.lt.{0} Nat instLTNat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
              m)
            (And (@LE.le.{0} Nat instLENat ell m)
              (@LT.lt.{0} Nat instLTNat m
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell))))
          (@Eq.{1} Nat
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
            m))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"range_partition"],"_simp_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"range_partition"],"_simp_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_2
- universes：[["str",["anonymous"],"u_1"]]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] {s t : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) s t) a)
    (Or
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) t a))
```

## Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_3

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"range_partition"],"_simp_1_3"]
- user Name：Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_3
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell)
    (@LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
```

## Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_4

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"range_partition"],"_simp_1_4"]
- user Name：Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_4
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@Finset.image.{0, 0} Nat Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.reflect m)
        (Shao.OQ4.RademacherSpectralPairing.lowerModes m))
      ell)
    (And (@LE.le.{0} Nat instLENat ell m)
      (@LT.lt.{0} Nat instLTNat m
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)))
```

## Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_5

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"range_partition"],"_simp_1_5"]
- user Name：Shao.OQ4.RademacherSpectralPairing.range_partition._simp_1_5
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Shao.OQ4.RademacherSpectralPairing.centerModes m) ell)
    (@Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
      m)
```

## Shao.OQ4.RademacherSpectralPairing.rawTerm

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"rawTerm"]
- user Name：Shao.OQ4.RademacherSpectralPairing.rawTerm
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m n ell : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m n ell : Nat) =>
  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) ell)
      (Shao.OQ4.RademacherFiniteS1.cotangent (Shao.OQ4.RademacherSpectralPairing.alpha m ell)))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell)) n)
```

## Shao.OQ4.RademacherSpectralPairing.rawTerm.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"rawTerm"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.rawTerm.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m n ell : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.rawTerm m n ell)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          ell)
        (Shao.OQ4.RademacherFiniteS1.cotangent (Shao.OQ4.RademacherSpectralPairing.alpha m ell)))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Real.cos (Shao.OQ4.RademacherSpectralPairing.beta m ell)) n))
```

## Shao.OQ4.RademacherSpectralPairing.raw_spectral_pairing

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"raw_spectral_pairing"]
- user Name：Shao.OQ4.RademacherSpectralPairing.raw_spectral_pairing
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m n : Nat),
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
        fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.rawTerm m n ell))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
          fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.pairedTerm m n ell))
      (Shao.OQ4.RademacherSpectralPairing.zeroMode m n))
```

## Shao.OQ4.RademacherSpectralPairing.reflect

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"reflect"]
- user Name：Shao.OQ4.RademacherSpectralPairing.reflect
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：(none)

完整类型（actual direct pp.all）：

```lean
(m ell : Nat) → Nat
```

完整定义体（actual direct pp.all）：

```lean
fun (m ell : Nat) => @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m ell
```

## Shao.OQ4.RademacherSpectralPairing.reflect.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"reflect"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.reflect.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：(none)

完整类型（actual direct pp.all）：

```lean
∀ (m ell : Nat),
  @Eq.{1} Nat (Shao.OQ4.RademacherSpectralPairing.reflect m ell)
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m ell)
```

## Shao.OQ4.RademacherSpectralPairing.reflect_injective_on

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"reflect_injective_on"]
- user Name：Shao.OQ4.RademacherSpectralPairing.reflect_injective_on
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Set.InjOn.{0, 0} Nat Nat (Shao.OQ4.RademacherSpectralPairing.reflect m)
    (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
      (Shao.OQ4.RademacherSpectralPairing.lowerModes m))
```

## Shao.OQ4.RademacherSpectralPairing.reflect_injective_on._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"reflect_injective_on"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.reflect_injective_on._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) ⦃i j : Nat⦄
  (he :
    @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m i)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m j))
  (hi' : @LE.le.{0} Nat instLENat i m) (hj' : @LE.le.{0} Nat instLENat j m), Not (@Eq.{1} Nat i j) → False
```

## Shao.OQ4.RademacherSpectralPairing.reflect_involutive

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"reflect_involutive"]
- user Name：Shao.OQ4.RademacherSpectralPairing.reflect_involutive
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  @Eq.{1} Nat (Shao.OQ4.RademacherSpectralPairing.reflect m (Shao.OQ4.RademacherSpectralPairing.reflect m ell)) ell
```

## Shao.OQ4.RademacherSpectralPairing.reflect_involutive._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"reflect_involutive"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.reflect_involutive._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  Not
      (@Eq.{1} Nat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m ell))
        ell) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.reflected_frequency

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"reflected_frequency"]
- user Name：Shao.OQ4.RademacherSpectralPairing.reflected_frequency
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Shao.OQ4.RademacherSpectralPairing.reflect m ell))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## Shao.OQ4.RademacherSpectralPairing.reflected_frequency._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"reflected_frequency"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.reflected_frequency._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  Not
      (@Eq.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m ell))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.remainder

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m n : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m n : Nat) =>
  @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (@Finset.erase.{0} Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.normalizedTerm m n ell)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Shao.OQ4.RademacherSpectralPairing.zeroMode m n)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (Shao.OQ4.RademacherSpectralPairing.amplitude m)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (Shao.OQ4.RademacherSpectralPairing.rho m) n)))
```

## Shao.OQ4.RademacherSpectralPairing.remainder.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m n : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.remainder m n)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
        (@Finset.erase.{0} Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.normalizedTerm m n ell)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Shao.OQ4.RademacherSpectralPairing.zeroMode m n)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (Shao.OQ4.RademacherSpectralPairing.amplitude m)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (Shao.OQ4.RademacherSpectralPairing.rho m) n))))
```

## Shao.OQ4.RademacherSpectralPairing.remainder_frequency

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder_frequency"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder_frequency
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@Finset.erase.{0} Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      ell),
  And
    (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (And
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Odd.{0} Nat Nat.instSemiring
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
```

## Shao.OQ4.RademacherSpectralPairing.remainder_frequency._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder_frequency"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder_frequency._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hp :
    And (@Ne.{1} Nat ell (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
        (Shao.OQ4.RademacherSpectralPairing.lowerModes m) ell))
  (hf :
    And
      (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  Not
      (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.remainder_frequency._proof_1_2

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder_frequency"],"_proof_1_2"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder_frequency._proof_1_2
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat},
  Not
      (@Eq.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
          (@instHAdd.{0} Nat (@Distrib.toAdd.{0} Nat (@instDistribOfSemiring.{0} Nat Nat.instSemiring)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
            (@instHMul.{0} Nat (@Distrib.toMul.{0} Nat (@instDistribOfSemiring.{0} Nat Nat.instSemiring)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Nat (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{0} Nat
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
                    (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
                      (@Semiring.toNonAssocSemiring.{0} Nat Nat.instSemiring))))
                Odd._proof_1))
            ell)
          (@OfNat.ofNat.{0} Nat (nat_lit 1)
            (@One.toOfNat1.{0} Nat
              (@AddMonoidWithOne.toOne.{0} Nat
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat
                  (@NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat
                    (@Semiring.toNonAssocSemiring.{0} Nat Nat.instSemiring)))))))) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.remainder_one

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder_one"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder_one
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (n : Nat),
  @Eq.{1} Real
    (Shao.OQ4.RademacherSpectralPairing.remainder (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## Shao.OQ4.RademacherSpectralPairing.remainder_positive_time

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder_positive_time"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder_positive_time
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.remainder m n)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (@Finset.erase.{0} Nat instDecidableEqNat (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      fun (ell : Nat) => Shao.OQ4.RademacherSpectralPairing.normalizedTerm m n ell)
```

## Shao.OQ4.RademacherSpectralPairing.remainder_two_positive_time

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder_two_positive_time"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder_two_positive_time
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n),
  @Eq.{1} Real
    (Shao.OQ4.RademacherSpectralPairing.remainder (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## Shao.OQ4.RademacherSpectralPairing.remainder_two_zero

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"remainder_two_zero"]
- user Name：Shao.OQ4.RademacherSpectralPairing.remainder_two_zero
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
@Eq.{1} Real
  (Shao.OQ4.RademacherSpectralPairing.remainder (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 3)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      (Shao.OQ4.RademacherSpectralPairing.amplitude (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
```

## Shao.OQ4.RademacherSpectralPairing.rho

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"rho"]
- user Name：Shao.OQ4.RademacherSpectralPairing.rho
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m : Nat) =>
  Real.cos
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      Real.pi
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast Shao.OQ4.RademacherSpectralPairing.beta._proof_1))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## Shao.OQ4.RademacherSpectralPairing.rho.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"rho"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.rho.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.rho m)
    (Real.cos
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        Real.pi
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              Shao.OQ4.RademacherSpectralPairing.beta._proof_1))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
```

## Shao.OQ4.RademacherSpectralPairing.rho_lt_one

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"rho_lt_one"]
- user Name：Shao.OQ4.RademacherSpectralPairing.rho_lt_one
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (Shao.OQ4.RademacherSpectralPairing.rho m)
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
```

## Shao.OQ4.RademacherSpectralPairing.rho_pos

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"rho_pos"]
- user Name：Shao.OQ4.RademacherSpectralPairing.rho_pos
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Shao.OQ4.RademacherSpectralPairing.rho m)
```

## Shao.OQ4.RademacherSpectralPairing.sign_reflect

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"sign_reflect"]
- user Name：Shao.OQ4.RademacherSpectralPairing.sign_reflect
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  @Eq.{1} Real
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (Shao.OQ4.RademacherSpectralPairing.reflect m ell))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) ell)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) m))
```

## Shao.OQ4.RademacherSpectralPairing.sign_reflect._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"sign_reflect"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.sign_reflect._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat} (hell : @LE.le.{0} Nat instLENat ell m),
  Not
      (@Eq.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ell
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) m ell))
        m) →
    False
```

## Shao.OQ4.RademacherSpectralPairing.sin_alpha_pos

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"sin_alpha_pos"]
- user Name：Shao.OQ4.RademacherSpectralPairing.sin_alpha_pos
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m ell : Nat}
  (hell :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      ell),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.sin (Shao.OQ4.RademacherSpectralPairing.alpha m ell))
```

## Shao.OQ4.RademacherSpectralPairing.sum_reflection_partition

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"sum_reflection_partition"]
- user Name：Shao.OQ4.RademacherSpectralPairing.sum_reflection_partition
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) (f : Nat → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (ell : Nat) => f ell)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Shao.OQ4.RademacherSpectralPairing.lowerModes m)
        fun (ell : Nat) =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (f ell)
          (f (Shao.OQ4.RademacherSpectralPairing.reflect m ell)))
      (@ite.{1} Real (@Even.{0} Nat instAddNat m) (Nat.instDecidablePredEven m)
        (f
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
```

## Shao.OQ4.RademacherSpectralPairing.tail_one_empty

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"tail_one_empty"]
- user Name：Shao.OQ4.RademacherSpectralPairing.tail_one_empty
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
@Eq.{1} (Finset.{0} Nat)
  (@Finset.erase.{0} Nat instDecidableEqNat
    (Shao.OQ4.RademacherSpectralPairing.lowerModes (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@EmptyCollection.emptyCollection.{0} (Finset.{0} Nat) (@Finset.instEmptyCollection.{0} Nat))
```

## Shao.OQ4.RademacherSpectralPairing.tail_two_empty

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"tail_two_empty"]
- user Name：Shao.OQ4.RademacherSpectralPairing.tail_two_empty
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
@Eq.{1} (Finset.{0} Nat)
  (@Finset.erase.{0} Nat instDecidableEqNat
    (Shao.OQ4.RademacherSpectralPairing.lowerModes (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@EmptyCollection.emptyCollection.{0} (Finset.{0} Nat) (@Finset.instEmptyCollection.{0} Nat))
```

## Shao.OQ4.RademacherSpectralPairing.zeroMode

- 分类：public explicit def
- kind：definition
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"zeroMode"]
- user Name：Shao.OQ4.RademacherSpectralPairing.zeroMode
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
(m n : Nat) → Real
```

完整定义体（actual direct pp.all）：

```lean
fun (m n : Nat) =>
  @ite.{1} Real (@Even.{0} Nat instAddNat m) (Nat.instDecidablePredEven m)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) n))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## Shao.OQ4.RademacherSpectralPairing.zeroMode.eq_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"zeroMode"],"eq_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.zeroMode.eq_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m n : Nat),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.zeroMode m n)
    (@ite.{1} Real (@Even.{0} Nat instAddNat m) (Nat.instDecidablePredEven m)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) n))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## Shao.OQ4.RademacherSpectralPairing.zeroMode_positive_time

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"zeroMode_positive_time"]
- user Name：Shao.OQ4.RademacherSpectralPairing.zeroMode_positive_time
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat) {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n),
  @Eq.{1} Real (Shao.OQ4.RademacherSpectralPairing.zeroMode m n)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## Shao.OQ4.RademacherSpectralPairing.zeroMode_positive_time._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"zeroMode_positive_time"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.zeroMode_positive_time._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n),
  @Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → False
```

## Shao.OQ4.RademacherSpectralPairing.zeroMode_two_zero

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"zeroMode_two_zero"]
- user Name：Shao.OQ4.RademacherSpectralPairing.zeroMode_two_zero
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
@Eq.{1} Real
  (Shao.OQ4.RademacherSpectralPairing.zeroMode (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@Neg.neg.{0} Real Real.instNeg
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 3)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
```

## Shao.OQ4.RademacherSpectralPairing.zeroMode_zero

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"zeroMode_zero"]
- user Name：Shao.OQ4.RademacherSpectralPairing.zeroMode_zero
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (m : Nat),
  @Eq.{1} Real
    (Shao.OQ4.RademacherSpectralPairing.zeroMode m (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@ite.{1} Real (@Even.{0} Nat instAddNat m) (Nat.instDecidablePredEven m)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) m
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast m)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## Shao.OQ4.RademacherSpectralPairing.zero_mem_lowerModes

- 分类：public explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"zero_mem_lowerModes"]
- user Name：Shao.OQ4.RademacherSpectralPairing.zero_mem_lowerModes
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
    (Shao.OQ4.RademacherSpectralPairing.lowerModes m) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

## Shao.OQ4.RademacherSpectralPairing.zero_mem_lowerModes._proof_1_1

- 分类：generated helper
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["str",["anonymous"],"Shao"],"OQ4"],"RademacherSpectralPairing"],"zero_mem_lowerModes"],"_proof_1_1"]
- user Name：Shao.OQ4.RademacherSpectralPairing.zero_mem_lowerModes._proof_1_1
- universes：[]
- private：false
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ {m : Nat} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m),
  Not
      (@LT.lt.{0} Nat instLTNat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        m) →
    False
```

## _private.Shao.OQ4.RademacherSpectralPairing.0.Shao.OQ4.RademacherSpectralPairing.cotangent_pair_factor

- 分类：private explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["num",["str",["str",["str",["str",["anonymous"],"_private"],"Shao"],"OQ4"],"RademacherSpectralPairing"],0],"Shao"],"OQ4"],"RademacherSpectralPairing"],"cotangent_pair_factor"]
- user Name：Shao.OQ4.RademacherSpectralPairing.cotangent_pair_factor
- universes：[]
- private：true
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (x e : Real)
  (hs : @Ne.{1} Real (Real.sin x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hc : @Ne.{1} Real (Real.cos x) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @Eq.{1} Real
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (Shao.OQ4.RademacherFiniteS1.cotangent x)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) e (Real.tan x)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (Shao.OQ4.RademacherFiniteS1.cotangent x)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) e
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (Real.tan x)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
```

## _private.Shao.OQ4.RademacherSpectralPairing.0.Shao.OQ4.RademacherSpectralPairing.normalization_factor

- 分类：private explicit theorem
- kind：theorem
- actual owner：Shao.OQ4.RademacherSpectralPairing
- raw Name：["str",["str",["str",["str",["num",["str",["str",["str",["str",["anonymous"],"_private"],"Shao"],"OQ4"],"RademacherSpectralPairing"],0],"Shao"],"OQ4"],"RademacherSpectralPairing"],"normalization_factor"]
- user Name：Shao.OQ4.RademacherSpectralPairing.normalization_factor
- universes：[]
- private：true
- unsafe / partial：false / false
- active instance：false
- axioms：propext, Classical.choice, Quot.sound

完整类型（actual direct pp.all）：

```lean
∀ (A C P s b q : Real) (hc : @Ne.{1} Real C (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hp : @Ne.{1} Real P (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) A C) P)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            b C))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) q
          P)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) A
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s b) q))
```
