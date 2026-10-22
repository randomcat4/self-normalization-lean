# 实际全owner接口及完整定义值

来源：本次唯一独立Native的actualkernel审计。这里逐项展示全部10个owned类型及全部definition完整值；raw Expr仅机器读取与哈希，不宣称人工全文。

## 1. Shao.OQ4.RademacherCriticalPhase.nearestIndex.eq_1
kind=theorem; module=Shao.OQ4.RademacherCubeRootRates; public=False; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: 4a7d17c799827c99e3984b1c40753cc9ede0333b2e7f4702bc9947999ec17dda

Actual type:
~~~lean
∀ (c α : ℝ) (k : ℕ),
  Eq.{1} (Shao.OQ4.RademacherCriticalPhase.nearestIndex c α k)
    (Nat.floor.{0} (HAdd.hAdd.{0, 0, 0} (Shao.OQ4.RademacherCriticalPhase.target c α k) (1 / 2)))
~~~

## 2. Shao.OQ4.RademacherCubeRootRates.BelowCubeBigO
kind=definition; module=Shao.OQ4.RademacherCubeRootRates; public=True; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: 0ab8b7f4e6bed5f929550238d966ef6326ca2c942a6599921a522882bc9572d6

Actual type:
~~~lean
ℝ → ℕ → Prop
~~~

Full explicit elaborated type:
~~~lean
(C : Real) → (k₀ : Nat) → Prop
~~~

definition value UTF8 SHA256: 5122610e26198c550856d28c11d192479e3850a9e11d9dcd7934c72a3ce59891
Complete actual definition value:
~~~lean
fun C k₀ =>
  LT.lt.{0} 0 C ∧
    ∀ (k : ℕ),
      LE.le.{0} k₀ k →
        LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0}
              (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
              (HSub.hSub.{0, 0, 0} (↑k) (HDiv.hDiv.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} 3 (HPow.hPow.{0, 0, 0} (↑k) 2))))))
          (HDiv.hDiv.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (↑k) 5))
~~~

Full explicit elaborated definition value:
~~~lean
fun (C : Real) (k₀ : Nat) =>
  And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
    (∀ (k : Nat),
      @LE.le.{0} Nat instLENat k₀ k →
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@Nat.cast.{0} Real Real.instNatCast k)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 3)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                        Shao.OQ4.RademacherCubeRootRates.BelowCubeBigO._proof_1))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                      (@Nat.cast.{0} Real Real.instNatCast k)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            C
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast k) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
~~~

## 3. Shao.OQ4.RademacherCubeRootRates.BelowCubeBigO._proof_1
kind=theorem; module=Shao.OQ4.RademacherCubeRootRates; public=False; unsafe=False; partial=False; axioms=['propext']
actual type UTF8 SHA256: db97428092ced56efd521f21b33f57856e726d1757c9e6cdb65d101712388167

Actual type:
~~~lean
(HAdd.hAdd.{0, 0, 0} 2 1).AtLeastTwo
~~~

## 4. Shao.OQ4.RademacherCubeRootRates.NearestCubeBigO
kind=definition; module=Shao.OQ4.RademacherCubeRootRates; public=True; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: 11ee6c38031d1bf219670361e97aac8c6dc9b5025edf1e68eb63e9318f4c42e4

Actual type:
~~~lean
ℝ → ℝ → ℕ → Prop
~~~

Full explicit elaborated type:
~~~lean
(α C : Real) → (k₀ : Nat) → Prop
~~~

definition value UTF8 SHA256: 136b67da012833c853cd6828409fbb748938732f703b917ea3851d188ad0c390
Complete actual definition value:
~~~lean
fun α C k₀ =>
  LT.lt.{0} 0 C ∧
    ∀ (k : ℕ),
      LE.le.{0} k₀ k →
        LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0}
              (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k))
              (HAdd.hAdd.{0, 0, 0} (↑k) α)))
          (HDiv.hDiv.{0, 0, 0} C (HPow.hPow.{0, 0, 0} (↑k) 2))
~~~

Full explicit elaborated definition value:
~~~lean
fun (α C : Real) (k₀ : Nat) =>
  And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
    (∀ (k : Nat),
      @LE.le.{0} Nat instLENat k₀ k →
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (Shao.OQ4.RademacherCriticalPhase.root
                (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@Nat.cast.{0} Real Real.instNatCast k) α)))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            C
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast k) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
~~~

## 5. Shao.OQ4.RademacherCubeRootRates.below_cube_bigO
kind=theorem; module=Shao.OQ4.RademacherCubeRootRates; public=True; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: 63afb4605f9cbe289292187c692201e4c7f4efe97e51575e5510ca138d01f070

Actual type:
~~~lean
∃ C k₀, Eq.{1} C 1 ∧ Eq.{1} k₀ 2 ∧ LT.lt.{0} 0 C ∧ Shao.OQ4.RademacherCubeRootRates.BelowCubeBigO C k₀
~~~

Full explicit elaborated type:
~~~lean
@Exists.{1} Real fun (C : Real) =>
  @Exists.{1} Nat fun (k₀ : Nat) =>
    And (@Eq.{1} Real C (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (And (@Eq.{1} Nat k₀ (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
          (Shao.OQ4.RademacherCubeRootRates.BelowCubeBigO C k₀)))
~~~

## 6. Shao.OQ4.RademacherCubeRootRates.below_cube_finite
kind=theorem; module=Shao.OQ4.RademacherCubeRootRates; public=True; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: b0f4c7f2aa012bb1788cb3d8c8c36d284ed1b7c0458438a443dce2623ccdb687

Actual type:
~~~lean
∀ {k : ℕ},
  LE.le.{0} 2 k →
    Eq.{1} (↑(Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k)) (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑k) 3) 1) ∧
      LE.le.{0} 1 (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k) ∧
        LE.le.{0} 0 (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k)) ∧
          Eq.{1}
              (HPow.hPow.{0, 0, 0}
                (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k)) 3)
              (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑k) 3) 1) ∧
            Eq.{1} (Shao.OQ4.RademacherCriticalPhase.height 1 (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
                (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k)) ∧
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
                    (HSub.hSub.{0, 0, 0} (↑k)
                      (HDiv.hDiv.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} 3 (HPow.hPow.{0, 0, 0} (↑k) 2))))))
                (HDiv.hDiv.{0, 0, 0} 1 (HPow.hPow.{0, 0, 0} (↑k) 5))
~~~

Full explicit elaborated type:
~~~lean
∀ {k : Nat} (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k),
  And
    (@Eq.{1} Real (@Nat.cast.{0} Real Real.instNatCast (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast k) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (And
      (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
      (And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k)))
        (And
          (@Eq.{1} Real
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@Nat.cast.{0} Real Real.instNatCast k) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
          (And
            (@Eq.{1} Real
              (Shao.OQ4.RademacherCriticalPhase.height
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
              (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k)))
            (@LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.belowCubeIndex k))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@Nat.cast.{0} Real Real.instNatCast k)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@Nat.cast.{0} Real Real.instNatCast k)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@Nat.cast.{0} Real Real.instNatCast k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))))
~~~

## 7. Shao.OQ4.RademacherCubeRootRates.nearest_cube_bigO
kind=theorem; module=Shao.OQ4.RademacherCubeRootRates; public=True; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: ebe4031b561d0c327723cc3c4348359a783a97c498a228ea3295d5dfffb9e083

Actual type:
~~~lean
∀ {α : ℝ},
  LT.lt.{0} 0 α →
    LT.lt.{0} α 1 →
      ∃ C k₀, Eq.{1} C (1 / 2) ∧ Eq.{1} k₀ 2 ∧ LT.lt.{0} 0 C ∧ Shao.OQ4.RademacherCubeRootRates.NearestCubeBigO α C k₀
~~~

Full explicit elaborated type:
~~~lean
∀ {α : Real}
  (hα0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) α)
  (hα1 : @LT.lt.{0} Real Real.instLT α (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Exists.{1} Real fun (C : Real) =>
    @Exists.{1} Nat fun (k₀ : Nat) =>
      And
        (@Eq.{1} Real C
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
        (And (@Eq.{1} Nat k₀ (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
            (Shao.OQ4.RademacherCubeRootRates.NearestCubeBigO α C k₀)))
~~~

## 8. Shao.OQ4.RademacherCubeRootRates.nearest_cube_finite
kind=theorem; module=Shao.OQ4.RademacherCubeRootRates; public=True; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: 3fc38919d437e16bc33bb704fb7f48d687f91e2e60fa06daf509d535deeae8a9

Actual type:
~~~lean
∀ {α : ℝ},
  LT.lt.{0} 0 α →
    LT.lt.{0} α 1 →
      ∀ {k : ℕ},
        LE.le.{0} 2 k →
          Eq.{1} (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k)
              (Nat.floor.{0} (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (↑k) α) 3) (1 / 2))) ∧
            LT.lt.{0} 0 (HAdd.hAdd.{0, 0, 0} (↑k) α) ∧
              LE.le.{0} 1 (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k) ∧
                LE.le.{0} 0
                    (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k)) ∧
                  Eq.{1}
                      (HPow.hPow.{0, 0, 0}
                        (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k)) 3)
                      ↑(Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k) ∧
                    Eq.{1}
                        (Shao.OQ4.RademacherCriticalPhase.height 1
                          (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k))
                        (Shao.OQ4.RademacherCriticalPhase.root (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k)) ∧
                      LT.lt.{0} (Neg.neg.{0} (1 / 2))
                          (HSub.hSub.{0, 0, 0} (↑(Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k))
                            (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (↑k) α) 3)) ∧
                        LE.le.{0}
                            (HSub.hSub.{0, 0, 0} (↑(Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k))
                              (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (↑k) α) 3))
                            (1 / 2) ∧
                          LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0} (↑(Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k))
                                  (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (↑k) α) 3)))
                              (1 / 2) ∧
                            (∀ (l : ℕ),
                                Eq.{1} (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (↑k) α) 3)
                                    (HAdd.hAdd.{0, 0, 0} (↑l) (1 / 2)) →
                                  Eq.{1} (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k)
                                    (HAdd.hAdd.{0, 0, 0} l 1)) ∧
                              LE.le.{0}
                                (abs.{0}
                                  (HSub.hSub.{0, 0, 0}
                                    (Shao.OQ4.RademacherCriticalPhase.root
                                      (Shao.OQ4.RademacherCriticalPhase.nearestIndex 1 α k))
                                    (HAdd.hAdd.{0, 0, 0} (↑k) α)))
                                (HDiv.hDiv.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} 2 (HPow.hPow.{0, 0, 0} (↑k) 2)))
~~~

Full explicit elaborated type:
~~~lean
∀ {α : Real}
  (hα0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) α)
  (hα1 : @LT.lt.{0} Real Real.instLT α (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  {k : Nat} (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k),
  And
    (@Eq.{1} Nat
      (Shao.OQ4.RademacherCriticalPhase.nearestIndex
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k)
      (@Nat.floor.{0} Real Real.semiring Real.partialOrder
        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast k) α)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))
    (And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast k)
          α))
      (And
        (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (Shao.OQ4.RademacherCriticalPhase.nearestIndex
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k))
        (And
          (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (Shao.OQ4.RademacherCriticalPhase.root
              (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k)))
          (And
            (@Eq.{1} Real
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (Shao.OQ4.RademacherCriticalPhase.root
                  (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Nat.cast.{0} Real Real.instNatCast
                (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k)))
            (And
              (@Eq.{1} Real
                (Shao.OQ4.RademacherCriticalPhase.height
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k))
                (Shao.OQ4.RademacherCriticalPhase.root
                  (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Neg.neg.{0} Real Real.instNeg
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@Nat.cast.{0} Real Real.instNatCast
                      (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Nat.cast.{0} Real Real.instNatCast k) α)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (And
                  (@LE.le.{0} Real Real.instLE
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast k) α)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@abs.{0} Real Real.lattice Real.instAddGroup
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast k) α)
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                    (And
                      (∀ (l : Nat),
                        @Eq.{1} Real
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@Nat.cast.{0} Real Real.instNatCast k) α)
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast l)
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
                          @Eq.{1} Nat
                            (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@LE.le.{0} Real Real.instLE
                        (@abs.{0} Real Real.lattice Real.instAddGroup
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (Shao.OQ4.RademacherCriticalPhase.root
                              (Shao.OQ4.RademacherCriticalPhase.nearestIndex
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α k))
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast k) α)))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (@Nat.cast.{0} Real Real.instNatCast k)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))))
~~~

## 9. _private.Shao.OQ4.RademacherCubeRootRates.0.Shao.OQ4.RademacherCubeRootRates.below_cube_error
kind=theorem; module=Shao.OQ4.RademacherCubeRootRates; public=False; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: b84dd13620e5fa08237ac492d505a0cc3842cd34f7c775d194737be44673daf1

Actual type:
~~~lean
∀ {K r : ℝ},
  LE.le.{0} 2 K →
    LE.le.{0} 0 r →
      Eq.{1} (HPow.hPow.{0, 0, 0} r 3) (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} K 3) 1) →
        LE.le.{0}
          (abs.{0}
            (HSub.hSub.{0, 0, 0} r
              (HSub.hSub.{0, 0, 0} K (HDiv.hDiv.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} 3 (HPow.hPow.{0, 0, 0} K 2))))))
          (HDiv.hDiv.{0, 0, 0} 1 (HPow.hPow.{0, 0, 0} K 5))
~~~

## 10. _private.Shao.OQ4.RademacherCubeRootRates.0.Shao.OQ4.RademacherCubeRootRates.nearest_cube_error
kind=theorem; module=Shao.OQ4.RademacherCubeRootRates; public=False; unsafe=False; partial=False; axioms=['propext', 'Classical.choice', 'Quot.sound']
actual type UTF8 SHA256: 378ccf93cedba096d913043dae8a0ab3b41ba72a5b04ac7ea3a278c688a913f1

Actual type:
~~~lean
∀ {K t r : ℝ},
  LE.le.{0} 2 K →
    LE.le.{0} K t →
      LE.le.{0} 0 r →
        LE.le.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} r 3) (HPow.hPow.{0, 0, 0} t 3))) (1 / 2) →
          LE.le.{0} (abs.{0} (HSub.hSub.{0, 0, 0} r t))
            (HDiv.hDiv.{0, 0, 0} 1 (HMul.hMul.{0, 0, 0} 2 (HPow.hPow.{0, 0, 0} K 2)))
~~~

## 项目依赖全清单（仅名称、owner、kind、安全与公理元数据；不展示上游实现）

- Shao.OQ4.RademacherCriticalPhase.WeakCell | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.belowCubeIndex | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext']
- Shao.OQ4.RademacherCriticalPhase.cutoff | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.delta | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.exact_below_cube | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.exact_below_cube._proof_1_1 | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.exact_below_cube._proof_1_2 | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.height | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.nearestIndex | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.nearestIndex._proof_1 | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext']
- Shao.OQ4.RademacherCriticalPhase.nearest_rounding | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.phaseFloor | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.root | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.root._proof_1 | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext']
- Shao.OQ4.RademacherCriticalPhase.root_spec | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.target | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- Shao.OQ4.RademacherCriticalPhase.upperHeight | Shao.OQ4.RademacherCriticalPhase | definition | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_below_cube_cast | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_below_cube_cast._proof_1_1 | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_injective_nonneg | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_le_inv | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_lt_inv | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_mono | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_strict | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cutoff_one | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_delta_range | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube._proof_1_1 | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube_weakCell | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_height_cube | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_height_nonneg | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nat_floor_bounds | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nearest_error | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nearest_tie_up | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_root_cube | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_root_nonneg | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
- _private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_weakCell_of_cutoff | Shao.OQ4.RademacherCriticalPhase | theorem | unsafe=False partial=False axioms=['propext', 'Classical.choice', 'Quot.sound']
