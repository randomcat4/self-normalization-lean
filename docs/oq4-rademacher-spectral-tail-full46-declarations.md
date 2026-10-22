# U1: complete readable actual Full46 target declaration ledger

STATUS: AUTHOR_CANONICAL_READY; AUTHOR ONLY; FRESH FINAL REVIEW GATE CLOSED.

This is a complete readable transcription of the already captured Full46 records selected by actual owner equal to the target, without a raw/user namespace filter; the whole inherited-project capture remains server-side. Actual types and definition values come from saved Expr records, not copied Source signatures. Curation itself uses pure Python on completed actual native audit records; it does not recompile or emit anything. The source-to-record classification alone uses explicit headers in the author's own immutable Source.

Captured source: `Full46-target-records.ndjson`, SHA256 `a1f7b9722597072af965e9995bace2862b1cd0ef131518af4947a6b1b6245468`, 363144 bytes; 75 records in original order. Full structural raw records remain exclusively on the server. This local ledger contains readable terms and human-readable metadata, not structural Expr JSON arrays. The historic hash-only ALLnone-ledger.json is an index and is not a substitute for this ledger.

Actual kind counts: 66 theorems, 9 definitions, no opaque declarations. Explicit public 10 = 8 theorems + 2 definitions (absoluteC and decayRatio). Explicit private 34 = 27 theorems + 7 definitions. Generated 31 = 31 theorems (28 private and 3 nonprivate). Thus the public theorem increment from Source headers is 8, not 10; the original receipt's public_explicit_count=10 retains its historical declaration-count meaning. All 75 actual owners are Shao.OQ4.RademacherSpectralTail in this measured canonical Full46 capture. All 9 definition values and all 75 types are displayed in full.

## Reading the fully explicit notation

`@Name.{levels}` displays a constant and all its actual universe arguments; all term arguments, including class dictionaries and coercions, are printed. `nat_lit(n)` and `string_lit(s)` are literal values. `Prop` is Sort 0; Sort(l) retains the actual level expression. `forall` and `fun` retain every binder. Binder labels gain a fresh __b suffix to resolve de Bruijn indices without capture; each binder's original Name is also annotated. Parentheses, braces, strict braces and square brackets retain default/implicit/strictImplicit/instImplicit binder kinds. `meta[...]` preserves every metadata entry and ordered DataValue. No expression is replaced by a hash, ellipsis or omitted implicit argument. This notation is a readable complete transcription, not a claim of re-elaboratable Lean surface syntax.

Names use `#n` for a numeric Name component, while a string component consisting of digits stays plain `n`; full raw/user/owner Name paths additionally spell out every str/num constructor from anonymous. This preserves the distinction between actual private raw Names and user Names. Universe parameters retain their actual ordered Names. The constructor-coverage check traverses all captured type/value nodes independently and matches every node consumed by the renderer; it validates transcription coverage, not a new mathematical or kernel check.

## Inventory in captured order

| Index | Classification | Actual kind | Actual user Name |
|---|---|---|---|
| 01 | explicit public | definition | `Shao.OQ4.RademacherSpectralTail.absoluteC` |
| 02 | explicit public | theorem | `Shao.OQ4.RademacherSpectralTail.absoluteC_pos` |
| 03 | explicit public | definition | `Shao.OQ4.RademacherSpectralTail.decayRatio` |
| 04 | explicit public | theorem | `Shao.OQ4.RademacherSpectralTail.decayRatio_lt_one` |
| 05 | explicit public | theorem | `Shao.OQ4.RademacherSpectralTail.decayRatio_pos` |
| 06 | explicit public | theorem | `Shao.OQ4.RademacherSpectralTail.exists_absolute_uniform_remainder_bound` |
| 07 | explicit public | theorem | `Shao.OQ4.RademacherSpectralTail.remainder_one_positive_time` |
| 08 | explicit public | theorem | `Shao.OQ4.RademacherSpectralTail.remainder_two_positive_time` |
| 09 | explicit public | theorem | `Shao.OQ4.RademacherSpectralTail.remainder_uniform` |
| 10 | explicit public | theorem | `Shao.OQ4.RademacherSpectralTail.remainder_uniform_weakCell` |
| 11 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.alpha_eq` |
| 12 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.antitoneOn_Icc_of_nonpos_derivative` |
| 13 | explicit private | definition | `Shao.OQ4.RademacherSpectralTail.baseAngle` |
| 14 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.baseAngle_bounds` |
| 15 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.beta_eq` |
| 16 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le` |
| 17 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds` |
| 18 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.cos_pos_of_nonneg_of_lt_half_pi` |
| 19 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.exponential_frequency_le` |
| 20 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.finite_geometric_sum_le` |
| 21 | explicit private | definition | `Shao.OQ4.RademacherSpectralTail.frequency` |
| 22 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.hasDerivAt_logCosEnergy` |
| 23 | explicit private | definition | `Shao.OQ4.RademacherSpectralTail.height` |
| 24 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.height_ge_two` |
| 25 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.height_pos` |
| 26 | explicit private | definition | `Shao.OQ4.RademacherSpectralTail.logCosEnergy` |
| 27 | explicit private | definition | `Shao.OQ4.RademacherSpectralTail.mainAngle` |
| 28 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.mainAngle_bounds` |
| 29 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.mainAngle_eq` |
| 30 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.monotoneOn_Icc_of_nonneg_derivative` |
| 31 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.normalizedTerm_abs_le` |
| 32 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.normalizedTerm_eq` |
| 33 | explicit private | definition | `Shao.OQ4.RademacherSpectralTail.pairedCoefficient` |
| 34 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.relative_cosine_bound` |
| 35 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.remainder_eq_sum` |
| 36 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.rho_eq` |
| 37 | explicit private | definition | `Shao.OQ4.RademacherSpectralTail.scaledTime` |
| 38 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.self_le_tan` |
| 39 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le` |
| 40 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le` |
| 41 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.tail_membership` |
| 42 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.tan_convex_Icc` |
| 43 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.tan_scale_le` |
| 44 | explicit private | theorem | `Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes` |
| 45 | generated | theorem | `Shao.OQ4.RademacherFiniteS1.cotangent.eq_1` |
| 46 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.decayRatio._proof_1` |
| 47 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.remainder_uniform._proof_1_2` |
| 48 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.baseAngle._proof_1` |
| 49 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.baseAngle.eq_1` |
| 50 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._proof_1_1` |
| 51 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_3` |
| 52 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_4` |
| 53 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_5` |
| 54 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_6` |
| 55 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_7` |
| 56 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_8` |
| 57 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_9` |
| 58 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds._proof_1_1` |
| 59 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.exponential_frequency_le._proof_1_1` |
| 60 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.frequency.eq_1` |
| 61 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.height.eq_1` |
| 62 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1` |
| 63 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.mainAngle.eq_1` |
| 64 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.pairedCoefficient.eq_1` |
| 65 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_1` |
| 66 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_2` |
| 67 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_3` |
| 68 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_4` |
| 69 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_5` |
| 70 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_6` |
| 71 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_7` |
| 72 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_1` |
| 73 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_2` |
| 74 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.tail_membership._proof_1_1` |
| 75 | generated | theorem | `Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes._proof_1_1` |

## 01. Shao.OQ4.RademacherSpectralTail.absoluteC

Classification: **explicit public**. Actual kind: **definition**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.absoluteC`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("absoluteC").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.absoluteC`.
- User Name: `Shao.OQ4.RademacherSpectralTail.absoluteC`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("absoluteC").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.absoluteC)); hints = sequence(0: "regular", 1: 34); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
@Real
```

Full actual definition value:

```text
(@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2)
@Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1))
(@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@OfNat.ofNat.{0} @Real nat_lit(3)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(3) @Real.instNatCast
@Shao.OQ4.RademacherSpectralTail.decayRatio._proof_1)) (@HSub.hSub.{0, 0, 0} @Real @Real @Real (@instHSub.{0}
@Real @Real.instSub) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))
@Shao.OQ4.RademacherSpectralTail.decayRatio)))
```

## 02. Shao.OQ4.RademacherSpectralTail.absoluteC_pos

Classification: **explicit public**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.absoluteC_pos`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("absoluteC_pos").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.absoluteC_pos`.
- User Name: `Shao.OQ4.RademacherSpectralTail.absoluteC_pos`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("absoluteC_pos").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.absoluteC_pos)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(@LT.lt.{0} @Real @Real.instLT (@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero))
@Shao.OQ4.RademacherSpectralTail.absoluteC)
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 03. Shao.OQ4.RademacherSpectralTail.decayRatio

Classification: **explicit public**. Actual kind: **definition**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.decayRatio`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("decayRatio").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.decayRatio`.
- User Name: `Shao.OQ4.RademacherSpectralTail.decayRatio`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("decayRatio").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.decayRatio)); hints = sequence(0: "regular", 1: 33); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
@Real
```

Full actual definition value:

```text
(@Real.exp (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul)
(@Neg.neg.{0} @Real @Real.instNeg (@OfNat.ofNat.{0} @Real nat_lit(3) (@instOfNatAtLeastTwo.{0} @Real nat_lit(3)
@Real.instNatCast @Shao.OQ4.RademacherSpectralTail.decayRatio._proof_1))) (@HPow.hPow.{0, 0, 0} @Real @Nat @Real
(@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) @Real.pi
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))) (@OfNat.ofNat.{0} @Real nat_lit(2)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1))))
```

## 04. Shao.OQ4.RademacherSpectralTail.decayRatio_lt_one

Classification: **explicit public**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.decayRatio_lt_one`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("decayRatio_lt_one").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.decayRatio_lt_one`.
- User Name: `Shao.OQ4.RademacherSpectralTail.decayRatio_lt_one`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("decayRatio_lt_one").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.decayRatio_lt_one)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(@LT.lt.{0} @Real @Real.instLT @Shao.OQ4.RademacherSpectralTail.decayRatio (@OfNat.ofNat.{0} @Real nat_lit(1)
(@One.toOfNat1.{0} @Real @Real.instOne)))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 05. Shao.OQ4.RademacherSpectralTail.decayRatio_pos

Classification: **explicit public**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.decayRatio_pos`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("decayRatio_pos").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.decayRatio_pos`.
- User Name: `Shao.OQ4.RademacherSpectralTail.decayRatio_pos`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("decayRatio_pos").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.decayRatio_pos)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(@LT.lt.{0} @Real @Real.instLT (@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero))
@Shao.OQ4.RademacherSpectralTail.decayRatio)
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 06. Shao.OQ4.RademacherSpectralTail.exists_absolute_uniform_remainder_bound

Classification: **explicit public**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.exists_absolute_uniform_remainder_bound`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("exists_absolute_uniform_remainder_bound").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.exists_absolute_uniform_remainder_bound`.
- User Name: `Shao.OQ4.RademacherSpectralTail.exists_absolute_uniform_remainder_bound`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("exists_absolute_uniform_remainder_bound").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.exists_absolute_uniform_remainder_bound)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(@Exists.{(0 + 1)} @Real (fun (C__b1 : @Real) /* binder Name C */ => (@And (@LT.lt.{0} @Real @Real.instLT
(@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)) C__b1) (forall (m__b2 : @Nat) /*
binder Name m */, (forall (x_0__b3 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1)
(@instOfNatNat nat_lit(1))) m__b2)) /* binder Name a._@._internal._hyg.#0 */, (forall (h__b4 : @Real) /* binder
Name h */, (forall (x_0__b5 : (@LE.le.{0} @Real @Real.instLE (@Nat.cast.{0} @Real @Real.instNatCast m__b2)
h__b4)) /* binder Name a._@._internal._hyg.#0 */, (forall (x_0__b6 : (@LT.lt.{0} @Real @Real.instLT h__b4
(@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0} @Real @Real.instAdd) (@Nat.cast.{0} @Real
@Real.instNatCast m__b2) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))))) /*
binder Name a._@._internal._hyg.#0 */, (forall (n__b7 : @Nat) /* binder Name n */, (forall (x_0__b8 :
(@LE.le.{0} @Real @Real.instLE (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat
(@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real
(@instHAdd.{0} @Real @Real.instAdd) (@Nat.cast.{0} @Real @Real.instNatCast m__b2) (@OfNat.ofNat.{0} @Real
nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))) (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat
nat_lit(2)))) (@Nat.cast.{0} @Real @Real.instNatCast n__b7))) /* binder Name a._@._internal._hyg.#0 */,
(@LE.le.{0} @Real @Real.instLE (@abs.{0} @Real @Real.lattice @Real.instAddGroup
(@Shao.OQ4.RademacherSpectralPairing.remainder m__b2 n__b7)) (@HMul.hMul.{0, 0, 0} @Real @Real @Real
(@instHMul.{0} @Real @Real.instMul) C__b1 (@Real.exp (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0}
@Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@HMul.hMul.{0, 0, 0} @Real @Real @Real
(@instHMul.{0} @Real @Real.instMul) (@Neg.neg.{0} @Real @Real.instNeg (@HPow.hPow.{0, 0, 0} @Real @Nat @Real
(@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) @Real.pi
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))) (@Nat.cast.{0} @Real @Real.instNatCast n__b7))
(@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0}
@Real @Real.instMonoid))) (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0} @Real @Real.instAdd)
(@Nat.cast.{0} @Real @Real.instNatCast m__b2) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real
@Real.instOne))) (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))))))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 07. Shao.OQ4.RademacherSpectralTail.remainder_one_positive_time

Classification: **explicit public**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.remainder_one_positive_time`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_one_positive_time").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.remainder_one_positive_time`.
- User Name: `Shao.OQ4.RademacherSpectralTail.remainder_one_positive_time`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_one_positive_time").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.remainder_one_positive_time)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {n__b1 : @Nat} /* binder Name n */, (forall (_hn__b2 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0}
@Nat nat_lit(1) (@instOfNatNat nat_lit(1))) n__b1)) /* binder Name _hn */, (@Eq.{(0 + 1)} @Real
(@Shao.OQ4.RademacherSpectralPairing.remainder (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))
n__b1) (@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 08. Shao.OQ4.RademacherSpectralTail.remainder_two_positive_time

Classification: **explicit public**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.remainder_two_positive_time`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_two_positive_time").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.remainder_two_positive_time`.
- User Name: `Shao.OQ4.RademacherSpectralTail.remainder_two_positive_time`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_two_positive_time").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.remainder_two_positive_time)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {n__b1 : @Nat} /* binder Name n */, (forall (hn__b2 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))) n__b1)) /* binder Name hn */, (@Eq.{(0 + 1)} @Real
(@Shao.OQ4.RademacherSpectralPairing.remainder (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2)))
n__b1) (@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 09. Shao.OQ4.RademacherSpectralTail.remainder_uniform

Classification: **explicit public**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.remainder_uniform`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_uniform").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.remainder_uniform`.
- User Name: `Shao.OQ4.RademacherSpectralTail.remainder_uniform`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_uniform").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.remainder_uniform)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {n__b2 : @Nat} /* binder Name n */, (forall (hm__b3 :
(@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) m__b1)) /* binder Name
hm */, (forall (hn__b4 : (@LE.le.{0} @Real @Real.instLE (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0}
@Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) (@HAdd.hAdd.{0, 0, 0} @Real
@Real @Real (@instHAdd.{0} @Real @Real.instAdd) (@Nat.cast.{0} @Real @Real.instNatCast m__b1) (@OfNat.ofNat.{0}
@Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))) (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat
nat_lit(2)))) (@Nat.cast.{0} @Real @Real.instNatCast n__b2))) /* binder Name hn */, (@LE.le.{0} @Real
@Real.instLE (@abs.{0} @Real @Real.lattice @Real.instAddGroup (@Shao.OQ4.RademacherSpectralPairing.remainder
m__b1 n__b2)) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul)
@Shao.OQ4.RademacherSpectralTail.absoluteC (@Real.exp (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0}
@Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@HMul.hMul.{0, 0, 0} @Real @Real @Real
(@instHMul.{0} @Real @Real.instMul) (@Neg.neg.{0} @Real @Real.instNeg (@HPow.hPow.{0, 0, 0} @Real @Nat @Real
(@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) @Real.pi
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))) (@Nat.cast.{0} @Real @Real.instNatCast n__b2))
(@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0}
@Real @Real.instMonoid))) (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0} @Real @Real.instAdd)
(@Nat.cast.{0} @Real @Real.instNatCast m__b1) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real
@Real.instOne))) (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 10. Shao.OQ4.RademacherSpectralTail.remainder_uniform_weakCell

Classification: **explicit public**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.remainder_uniform_weakCell`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_uniform_weakCell").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.remainder_uniform_weakCell`.
- User Name: `Shao.OQ4.RademacherSpectralTail.remainder_uniform_weakCell`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_uniform_weakCell").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.remainder_uniform_weakCell)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall (hm__b2 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))) m__b1)) /* binder Name hm */, (forall {h__b3 : @Real} /* binder Name h
*/, (forall (_hmh__b4 : (@LE.le.{0} @Real @Real.instLE (@Nat.cast.{0} @Real @Real.instNatCast m__b1) h__b3)) /*
binder Name _hmh */, (forall (_hhm__b5 : (@LT.lt.{0} @Real @Real.instLT h__b3 (@HAdd.hAdd.{0, 0, 0} @Real @Real
@Real (@instHAdd.{0} @Real @Real.instAdd) (@Nat.cast.{0} @Real @Real.instNatCast m__b1) (@OfNat.ofNat.{0} @Real
nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))))) /* binder Name _hhm */, (forall {n__b6 : @Nat} /* binder
Name n */, (forall (hn__b7 : (@LE.le.{0} @Real @Real.instLE (@HPow.hPow.{0, 0, 0} @Real @Nat @Real
(@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid)))
(@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0} @Real @Real.instAdd) (@Nat.cast.{0} @Real
@Real.instNatCast m__b1) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne)))
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2)))) (@Nat.cast.{0} @Real @Real.instNatCast n__b6)))
/* binder Name hn */, (@LE.le.{0} @Real @Real.instLE (@abs.{0} @Real @Real.lattice @Real.instAddGroup
(@Shao.OQ4.RademacherSpectralPairing.remainder m__b1 n__b6)) (@HMul.hMul.{0, 0, 0} @Real @Real @Real
(@instHMul.{0} @Real @Real.instMul) @Shao.OQ4.RademacherSpectralTail.absoluteC (@Real.exp (@HDiv.hDiv.{0, 0, 0}
@Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@HMul.hMul.{0,
0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@Neg.neg.{0} @Real @Real.instNeg (@HPow.hPow.{0, 0,
0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real
@Real.instMonoid))) @Real.pi (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))) (@Nat.cast.{0}
@Real @Real.instNatCast n__b6)) (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat
(@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real
(@instHAdd.{0} @Real @Real.instAdd) (@Nat.cast.{0} @Real @Real.instNatCast m__b1) (@OfNat.ofNat.{0} @Real
nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))) (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat
nat_lit(2)))))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 11. Shao.OQ4.RademacherSpectralTail.alpha_eq

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.alpha_eq`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("alpha_eq").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.alpha_eq`.
- User Name: `Shao.OQ4.RademacherSpectralTail.alpha_eq`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("alpha_eq").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.alpha_eq)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (forall (ell__b2 : @Nat) /* binder Name ell */, (@Eq.{(0 + 1)} @Real
(@Shao.OQ4.RademacherSpectralPairing.alpha m__b1 ell__b2) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0}
@Real @Real.instMul) (@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency
ell__b2) (@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle m__b1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 12. Shao.OQ4.RademacherSpectralTail.antitoneOn_Icc_of_nonpos_derivative

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.antitoneOn_Icc_of_nonpos_derivative`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("antitoneOn_Icc_of_nonpos_derivative").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.antitoneOn_Icc_of_nonpos_derivative`.
- User Name: `Shao.OQ4.RademacherSpectralTail.antitoneOn_Icc_of_nonpos_derivative`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("antitoneOn_Icc_of_nonpos_derivative").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.antitoneOn_Icc_of_nonpos_derivative)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {f__b1 : (forall (x_0__b2 : @Real) /* binder Name a._@._internal._hyg.#0 */, @Real)} /* binder Name f
*/, (forall {f___b3 : (forall (x_0__b4 : @Real) /* binder Name a._@._internal._hyg.#0 */, @Real)} /* binder Name
f' */, (forall {a__b5 : @Real} /* binder Name a */, (forall {b__b6 : @Real} /* binder Name b */, (forall (hd__b7
: (forall (u__b8 : @Real) /* binder Name u */, (forall (x_0__b9 : (@Membership.mem.{0, 0} @Real (@Set.{0} @Real)
(@Set.instMembership.{0} @Real) (@Set.Icc.{0} @Real @Real.instPreorder a__b5 b__b6) u__b8)) /* binder Name
a._@._internal._hyg.#0 */, (@HasDerivAt.{0, 0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField) @Real @Real.instAddCommGroup (@Semiring.toModule.{0} @Real
(@CommSemiring.toSemiring.{0} @Real (@Semifield.toCommSemiring.{0} @Real (@Field.toSemifield.{0} @Real
(@NormedField.toField.{0} @Real (@NontriviallyNormedField.toNormedField.{0} @Real
(@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
@Real.pseudoMetricSpace)) (@IsModuleTopology.toContinuousSMul.{0, 0} @Real (@UniformSpace.toTopologicalSpace.{0}
@Real (@PseudoMetricSpace.toUniformSpace.{0} @Real (@SeminormedRing.toPseudoMetricSpace.{0} @Real
(@SeminormedCommRing.toSeminormedRing.{0} @Real (@NormedCommRing.toSeminormedCommRing.{0} @Real
(@NormedField.toNormedCommRing.{0} @Real (@NontriviallyNormedField.toNormedField.{0} @Real
(@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))) @Real @Real.instAdd
(@SMulZeroClass.toSMul.{0, 0} @Real @Real (@AddZero.toZero.{0} @Real (@AddZeroClass.toAddZero.{0} @Real
(@AddMonoid.toAddZeroClass.{0} @Real (@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0} @Real
(@AddCommGroup.toAddGroup.{0} @Real @Real.instAddCommGroup)))))) (@DistribSMul.toSMulZeroClass.{0, 0} @Real
@Real (@AddMonoid.toAddZeroClass.{0} @Real (@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0}
@Real (@AddCommGroup.toAddGroup.{0} @Real @Real.instAddCommGroup)))) (@DistribMulAction.toDistribSMul.{0, 0}
@Real @Real (@Semiring.toMonoid.{0} @Real (@CommSemiring.toSemiring.{0} @Real (@Semifield.toCommSemiring.{0}
@Real (@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real (@NontriviallyNormedField.toNormedField.{0}
@Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))
(@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0} @Real (@AddCommGroup.toAddGroup.{0} @Real
@Real.instAddCommGroup))) (@Module.toDistribMulAction.{0, 0} @Real @Real (@CommSemiring.toSemiring.{0} @Real
(@Semifield.toCommSemiring.{0} @Real (@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))) (@AddCommGroup.toAddCommMonoid.{0} @Real @Real.instAddCommGroup)
(@Semiring.toModule.{0} @Real (@CommSemiring.toSemiring.{0} @Real (@Semifield.toCommSemiring.{0} @Real
(@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real (@NontriviallyNormedField.toNormedField.{0} @Real
(@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))))))
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
@Real.pseudoMetricSpace)) (@IsTopologicalSemiring.toIsModuleTopology.{0} @Real @Real.semiring
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
(@SeminormedRing.toPseudoMetricSpace.{0} @Real (@SeminormedCommRing.toSeminormedRing.{0} @Real
(@NormedCommRing.toSeminormedCommRing.{0} @Real (@NormedField.toNormedCommRing.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))))) (@IsTopologicalRing.toIsTopologicalSemiring.{0} @Real
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
(@SeminormedRing.toPseudoMetricSpace.{0} @Real (@SeminormedCommRing.toSeminormedRing.{0} @Real
(@NormedCommRing.toSeminormedCommRing.{0} @Real (@NormedField.toNormedCommRing.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))))) (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} @Real
(@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} @Real (@CommRing.toNonUnitalCommRing.{0} @Real
@Real.commRing))) @instIsTopologicalRingReal))) f__b1 (f___b3 u__b8) u__b8)))) /* binder Name hd */, (forall
(hneg__b10 : (forall (u__b11 : @Real) /* binder Name u */, (forall (x_0__b12 : (@Membership.mem.{0, 0} @Real
(@Set.{0} @Real) (@Set.instMembership.{0} @Real) (@Set.Icc.{0} @Real @Real.instPreorder a__b5 b__b6) u__b11)) /*
binder Name a._@._internal._hyg.#0 */, (@LE.le.{0} @Real @Real.instLE (f___b3 u__b11) (@OfNat.ofNat.{0} @Real
nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)))))) /* binder Name hneg */, (@AntitoneOn.{0, 0} @Real
@Real @Real.instPreorder @Real.instPreorder f__b1 (@Set.Icc.{0} @Real @Real.instPreorder a__b5 b__b6))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 13. Shao.OQ4.RademacherSpectralTail.baseAngle

Classification: **explicit private**. Actual kind: **definition**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("baseAngle").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.baseAngle`.
- User Name: `Shao.OQ4.RademacherSpectralTail.baseAngle`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("baseAngle").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle)); hints = sequence(0: "regular", 1: 33); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, @Real)
```

Full actual definition value:

```text
(fun (m__b1 : @Nat) /* binder Name m */ => (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) @Real.pi (@HMul.hMul.{0, 0, 0} @Real @Real @Real
(@instHMul.{0} @Real @Real.instMul) (@OfNat.ofNat.{0} @Real nat_lit(4) (@instOfNatAtLeastTwo.{0} @Real
nat_lit(4) @Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle._proof_1))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height m__b1))))
```

## 14. Shao.OQ4.RademacherSpectralTail.baseAngle_bounds

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle_bounds`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("baseAngle_bounds").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.baseAngle_bounds`.
- User Name: `Shao.OQ4.RademacherSpectralTail.baseAngle_bounds`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("baseAngle_bounds").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle_bounds)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall (hm__b2 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))) m__b1)) /* binder Name hm */, (@And (@LT.lt.{0} @Real @Real.instLT
(@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle m__b1)) (@LT.lt.{0}
@Real @Real.instLT (@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle
m__b1) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) @Real.pi (@OfNat.ofNat.{0} @Real nat_lit(4) (@instOfNatAtLeastTwo.{0} @Real nat_lit(4)
@Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(3) (@instOfNatNat nat_lit(3)))
(@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 15. Shao.OQ4.RademacherSpectralTail.beta_eq

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.beta_eq`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("beta_eq").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.beta_eq`.
- User Name: `Shao.OQ4.RademacherSpectralTail.beta_eq`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("beta_eq").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.beta_eq)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (forall (ell__b2 : @Nat) /* binder Name ell */, (@Eq.{(0 + 1)} @Real
(@Shao.OQ4.RademacherSpectralPairing.beta m__b1 ell__b2) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0}
@Real @Real.instMul) (@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency
ell__b2) (@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle m__b1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 16. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {n__b2 : @Nat} /* binder Name n */, (forall {ell__b3 : @Nat}
/* binder Name ell */, (forall (hm__b4 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1)
(@instOfNatNat nat_lit(1))) m__b1)) /* binder Name hm */, (forall (hell__b5 : (@Membership.mem.{0, 0} @Nat
(@Finset.{0} @Nat) (@SetLike.instMembership.{0, 0} (@Finset.{0} @Nat) @Nat (@Finset.instSetLike.{0} @Nat))
(@Finset.erase.{0} @Nat @instDecidableEqNat (@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1)
(@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0)))) ell__b3)) /* binder Name hell */, (@LE.le.{0}
@Real @Real.instLE (@abs.{0} @Real @Real.lattice @Real.instAddGroup
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient m__b1 n__b2
ell__b3)) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2)
@Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))
(@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0)))))))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency ell__b3))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 17. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le_two_thirds").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le_two_thirds").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {n__b2 : @Nat} /* binder Name n */, (forall {ell__b3 : @Nat}
/* binder Name ell */, (forall (hm__b4 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1)
(@instOfNatNat nat_lit(1))) m__b1)) /* binder Name hm */, (forall (hell__b5 : (@Membership.mem.{0, 0} @Nat
(@Finset.{0} @Nat) (@SetLike.instMembership.{0, 0} (@Finset.{0} @Nat) @Nat (@Finset.instSetLike.{0} @Nat))
(@Finset.erase.{0} @Nat @instDecidableEqNat (@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1)
(@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0)))) ell__b3)) /* binder Name hell */, (@LE.le.{0}
@Real @Real.instLE (@abs.{0} @Real @Real.lattice @Real.instAddGroup
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient m__b1 n__b2
ell__b3)) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2)
@Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))
(@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0))))))) (@OfNat.ofNat.{0} @Real
nat_lit(3) (@instOfNatAtLeastTwo.{0} @Real nat_lit(3) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 18. Shao.OQ4.RademacherSpectralTail.cos_pos_of_nonneg_of_lt_half_pi

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.cos_pos_of_nonneg_of_lt_half_pi`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("cos_pos_of_nonneg_of_lt_half_pi").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.cos_pos_of_nonneg_of_lt_half_pi`.
- User Name: `Shao.OQ4.RademacherSpectralTail.cos_pos_of_nonneg_of_lt_half_pi`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("cos_pos_of_nonneg_of_lt_half_pi").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.cos_pos_of_nonneg_of_lt_half_pi)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {u__b1 : @Real} /* binder Name u */, (forall (hu__b2 : (@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0}
@Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)) u__b1)) /* binder Name hu */, (forall (hu___b3 :
(@LT.lt.{0} @Real @Real.instLT u__b1 (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) @Real.pi (@OfNat.ofNat.{0} @Real nat_lit(2)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0}
@Nat nat_lit(1) (@instOfNatNat nat_lit(1))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0)
(@instOfNatNat nat_lit(0)))))))))) /* binder Name hu' */, (@LT.lt.{0} @Real @Real.instLT (@OfNat.ofNat.{0} @Real
nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)) (@Real.cos u__b1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 19. Shao.OQ4.RademacherSpectralTail.exponential_frequency_le

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.exponential_frequency_le`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("exponential_frequency_le").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.exponential_frequency_le`.
- User Name: `Shao.OQ4.RademacherSpectralTail.exponential_frequency_le`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("exponential_frequency_le").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.exponential_frequency_le)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {ell__b1 : @Nat} /* binder Name ell */, (forall (hell__b2 : (@LE.le.{0} @Nat @instLENat
(@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) ell__b1)) /* binder Name hell */, (forall {t__b3 :
@Real} /* binder Name t */, (forall (ht__b4 : (@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0} @Real nat_lit(1)
(@One.toOfNat1.{0} @Real @Real.instOne)) t__b3)) /* binder Name ht */, (@LE.le.{0} @Real @Real.instLE (@Real.exp
(@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul)
(@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@Neg.neg.{0} @Real @Real.instNeg
(@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0}
@Real @Real.instMonoid))) @Real.pi (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2)))))
(@HSub.hSub.{0, 0, 0} @Real @Real @Real (@instHSub.{0} @Real @Real.instSub) (@HPow.hPow.{0, 0, 0} @Real @Nat
@Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid)))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency ell__b1)
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2)))) (@OfNat.ofNat.{0} @Real nat_lit(1)
(@One.toOfNat1.{0} @Real @Real.instOne)))) t__b3) (@OfNat.ofNat.{0} @Real nat_lit(8) (@instOfNatAtLeastTwo.{0}
@Real nat_lit(8) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(7)
(@instOfNatNat nat_lit(7))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(6) (@instOfNatNat
nat_lit(6))))))))) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@Real.exp
(@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@Neg.neg.{0} @Real @Real.instNeg
(@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0}
@Real @Real.instMonoid))) @Real.pi (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))) t__b3))
(@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0}
@Real @Real.instMonoid))) @Shao.OQ4.RademacherSpectralTail.decayRatio (@HSub.hSub.{0, 0, 0} @Nat @Nat @Nat
(@instHSub.{0} @Nat @instSubNat) ell__b1 (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 20. Shao.OQ4.RademacherSpectralTail.finite_geometric_sum_le

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.finite_geometric_sum_le`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("finite_geometric_sum_le").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.finite_geometric_sum_le`.
- User Name: `Shao.OQ4.RademacherSpectralTail.finite_geometric_sum_le`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("finite_geometric_sum_le").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.finite_geometric_sum_le)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {q__b1 : @Real} /* binder Name q */, (forall (hq__b2 : (@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0}
@Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)) q__b1)) /* binder Name hq */, (forall (hq___b3 :
(@LT.lt.{0} @Real @Real.instLT q__b1 (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real
@Real.instOne)))) /* binder Name hq' */, (forall (M__b4 : @Nat) /* binder Name M */, (@LE.le.{0} @Real
@Real.instLE (@Finset.sum.{0, 0} @Nat @Real @Real.instAddCommMonoid (@Finset.range M__b4) (fun (k__b5 : @Nat) /*
binder Name k */ => (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real
(@Monoid.toNPow.{0} @Real @Real.instMonoid))) q__b1 k__b5))) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real
(@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@OfNat.ofNat.{0} @Real nat_lit(1)
(@One.toOfNat1.{0} @Real @Real.instOne)) (@HSub.hSub.{0, 0, 0} @Real @Real @Real (@instHSub.{0} @Real
@Real.instSub) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne)) q__b1)))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 21. Shao.OQ4.RademacherSpectralTail.frequency

Classification: **explicit private**. Actual kind: **definition**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("frequency").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.frequency`.
- User Name: `Shao.OQ4.RademacherSpectralTail.frequency`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("frequency").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency)); hints = sequence(0: "regular", 1: 22); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (ell__b1 : @Nat) /* binder Name ell */, @Real)
```

Full actual definition value:

```text
(fun (ell__b1 : @Nat) /* binder Name ell */ => (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0} @Real
@Real.instAdd) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@OfNat.ofNat.{0}
@Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1)) (@Nat.cast.{0}
@Real @Real.instNatCast ell__b1)) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))))
```

## 22. Shao.OQ4.RademacherSpectralTail.hasDerivAt_logCosEnergy

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.hasDerivAt_logCosEnergy`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("hasDerivAt_logCosEnergy").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.hasDerivAt_logCosEnergy`.
- User Name: `Shao.OQ4.RademacherSpectralTail.hasDerivAt_logCosEnergy`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("hasDerivAt_logCosEnergy").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.hasDerivAt_logCosEnergy)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {u__b1 : @Real} /* binder Name u */, (forall (hu__b2 : (@Ne.{(0 + 1)} @Real (@Real.cos u__b1)
(@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)))) /* binder Name hu */,
(@HasDerivAt.{0, 0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)
@Real @Real.instAddCommGroup (@Semiring.toModule.{0} @Real (@CommSemiring.toSemiring.{0} @Real
(@Semifield.toCommSemiring.{0} @Real (@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField))))))) (@UniformSpace.toTopologicalSpace.{0} @Real
(@PseudoMetricSpace.toUniformSpace.{0} @Real @Real.pseudoMetricSpace)) (@IsModuleTopology.toContinuousSMul.{0,
0} @Real (@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
(@SeminormedRing.toPseudoMetricSpace.{0} @Real (@SeminormedCommRing.toSeminormedRing.{0} @Real
(@NormedCommRing.toSeminormedCommRing.{0} @Real (@NormedField.toNormedCommRing.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))))) @Real @Real.instAdd (@SMulZeroClass.toSMul.{0, 0} @Real @Real
(@AddZero.toZero.{0} @Real (@AddZeroClass.toAddZero.{0} @Real (@AddMonoid.toAddZeroClass.{0} @Real
(@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0} @Real (@AddCommGroup.toAddGroup.{0} @Real
@Real.instAddCommGroup)))))) (@DistribSMul.toSMulZeroClass.{0, 0} @Real @Real (@AddMonoid.toAddZeroClass.{0}
@Real (@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0} @Real (@AddCommGroup.toAddGroup.{0}
@Real @Real.instAddCommGroup)))) (@DistribMulAction.toDistribSMul.{0, 0} @Real @Real (@Semiring.toMonoid.{0}
@Real (@CommSemiring.toSemiring.{0} @Real (@Semifield.toCommSemiring.{0} @Real (@Field.toSemifield.{0} @Real
(@NormedField.toField.{0} @Real (@NontriviallyNormedField.toNormedField.{0} @Real
(@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))
(@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0} @Real (@AddCommGroup.toAddGroup.{0} @Real
@Real.instAddCommGroup))) (@Module.toDistribMulAction.{0, 0} @Real @Real (@CommSemiring.toSemiring.{0} @Real
(@Semifield.toCommSemiring.{0} @Real (@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))) (@AddCommGroup.toAddCommMonoid.{0} @Real @Real.instAddCommGroup)
(@Semiring.toModule.{0} @Real (@CommSemiring.toSemiring.{0} @Real (@Semifield.toCommSemiring.{0} @Real
(@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real (@NontriviallyNormedField.toNormedField.{0} @Real
(@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))))))
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
@Real.pseudoMetricSpace)) (@IsTopologicalSemiring.toIsModuleTopology.{0} @Real @Real.semiring
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
(@SeminormedRing.toPseudoMetricSpace.{0} @Real (@SeminormedCommRing.toSeminormedRing.{0} @Real
(@NormedCommRing.toSeminormedCommRing.{0} @Real (@NormedField.toNormedCommRing.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))))) (@IsTopologicalRing.toIsTopologicalSemiring.{0} @Real
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
(@SeminormedRing.toPseudoMetricSpace.{0} @Real (@SeminormedCommRing.toSeminormedRing.{0} @Real
(@NormedCommRing.toSeminormedCommRing.{0} @Real (@NormedField.toNormedCommRing.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))))) (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} @Real
(@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} @Real (@CommRing.toNonUnitalCommRing.{0} @Real
@Real.commRing))) @instIsTopologicalRingReal)))
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.logCosEnergy (@HAdd.hAdd.{0, 0, 0}
@Real @Real @Real (@instHAdd.{0} @Real @Real.instAdd) (@Neg.neg.{0} @Real @Real.instNeg (@Real.tan u__b1))
u__b1) u__b1)))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 23. Shao.OQ4.RademacherSpectralTail.height

Classification: **explicit private**. Actual kind: **definition**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("height").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.height`.
- User Name: `Shao.OQ4.RademacherSpectralTail.height`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("height").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height)); hints = sequence(0: "regular", 1: 22); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, @Real)
```

Full actual definition value:

```text
(fun (m__b1 : @Nat) /* binder Name m */ => (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0} @Real
@Real.instAdd) (@Nat.cast.{0} @Real @Real.instNatCast m__b1) (@OfNat.ofNat.{0} @Real nat_lit(1)
(@One.toOfNat1.{0} @Real @Real.instOne))))
```

## 24. Shao.OQ4.RademacherSpectralTail.height_ge_two

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height_ge_two`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("height_ge_two").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.height_ge_two`.
- User Name: `Shao.OQ4.RademacherSpectralTail.height_ge_two`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("height_ge_two").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height_ge_two)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall (hm__b2 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))) m__b1)) /* binder Name hm */, (@LE.le.{0} @Real @Real.instLE
(@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast
(@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) (@Nat.instNeZeroSucc
(@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0)))))))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height m__b1))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 25. Shao.OQ4.RademacherSpectralTail.height_pos

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height_pos`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("height_pos").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.height_pos`.
- User Name: `Shao.OQ4.RademacherSpectralTail.height_pos`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("height_pos").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height_pos)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (@LT.lt.{0} @Real @Real.instLT (@OfNat.ofNat.{0} @Real nat_lit(0)
(@Zero.toOfNat0.{0} @Real @Real.instZero))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height m__b1)))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 26. Shao.OQ4.RademacherSpectralTail.logCosEnergy

Classification: **explicit private**. Actual kind: **definition**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.logCosEnergy`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("logCosEnergy").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.logCosEnergy`.
- User Name: `Shao.OQ4.RademacherSpectralTail.logCosEnergy`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("logCosEnergy").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.logCosEnergy)); hints = sequence(0: "regular", 1: 32); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (u__b1 : @Real) /* binder Name u */, @Real)
```

Full actual definition value:

```text
(fun (u__b1 : @Real) /* binder Name u */ => (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0} @Real
@Real.instAdd) (@Real.log (@Real.cos u__b1)) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0}
@Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) u__b1 (@OfNat.ofNat.{0} @Nat
nat_lit(2) (@instOfNatNat nat_lit(2)))) (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real
nat_lit(2) @Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1)))))
```

## 27. Shao.OQ4.RademacherSpectralTail.mainAngle

Classification: **explicit private**. Actual kind: **definition**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.mainAngle`.
- User Name: `Shao.OQ4.RademacherSpectralTail.mainAngle`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle)); hints = sequence(0: "regular", 1: 33); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, @Real)
```

Full actual definition value:

```text
(fun (m__b1 : @Nat) /* binder Name m */ => (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) @Real.pi (@HMul.hMul.{0, 0, 0} @Real @Real @Real
(@instHMul.{0} @Real @Real.instMul) (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real
nat_lit(2) @Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height m__b1))))
```

## 28. Shao.OQ4.RademacherSpectralTail.mainAngle_bounds

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle_bounds`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle_bounds").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.mainAngle_bounds`.
- User Name: `Shao.OQ4.RademacherSpectralTail.mainAngle_bounds`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle_bounds").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle_bounds)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall (hm__b2 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))) m__b1)) /* binder Name hm */, (@And (@LT.lt.{0} @Real @Real.instLT
(@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle m__b1)) (@LT.lt.{0}
@Real @Real.instLT (@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle
m__b1) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) @Real.pi (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2)
@Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))
(@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 29. Shao.OQ4.RademacherSpectralTail.mainAngle_eq

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle_eq`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle_eq").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.mainAngle_eq`.
- User Name: `Shao.OQ4.RademacherSpectralTail.mainAngle_eq`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle_eq").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle_eq)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (@Eq.{(0 + 1)} @Real
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle m__b1) (@HMul.hMul.{0,
0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@OfNat.ofNat.{0} @Real nat_lit(2)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0}
@Nat nat_lit(1) (@instOfNatNat nat_lit(1))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0)
(@instOfNatNat nat_lit(0)))))))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle m__b1))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 30. Shao.OQ4.RademacherSpectralTail.monotoneOn_Icc_of_nonneg_derivative

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.monotoneOn_Icc_of_nonneg_derivative`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("monotoneOn_Icc_of_nonneg_derivative").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.monotoneOn_Icc_of_nonneg_derivative`.
- User Name: `Shao.OQ4.RademacherSpectralTail.monotoneOn_Icc_of_nonneg_derivative`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("monotoneOn_Icc_of_nonneg_derivative").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.monotoneOn_Icc_of_nonneg_derivative)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {f__b1 : (forall (x_0__b2 : @Real) /* binder Name a._@._internal._hyg.#0 */, @Real)} /* binder Name f
*/, (forall {f___b3 : (forall (x_0__b4 : @Real) /* binder Name a._@._internal._hyg.#0 */, @Real)} /* binder Name
f' */, (forall {a__b5 : @Real} /* binder Name a */, (forall {b__b6 : @Real} /* binder Name b */, (forall (hd__b7
: (forall (u__b8 : @Real) /* binder Name u */, (forall (x_0__b9 : (@Membership.mem.{0, 0} @Real (@Set.{0} @Real)
(@Set.instMembership.{0} @Real) (@Set.Icc.{0} @Real @Real.instPreorder a__b5 b__b6) u__b8)) /* binder Name
a._@._internal._hyg.#0 */, (@HasDerivAt.{0, 0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField) @Real @Real.instAddCommGroup (@Semiring.toModule.{0} @Real
(@CommSemiring.toSemiring.{0} @Real (@Semifield.toCommSemiring.{0} @Real (@Field.toSemifield.{0} @Real
(@NormedField.toField.{0} @Real (@NontriviallyNormedField.toNormedField.{0} @Real
(@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
@Real.pseudoMetricSpace)) (@IsModuleTopology.toContinuousSMul.{0, 0} @Real (@UniformSpace.toTopologicalSpace.{0}
@Real (@PseudoMetricSpace.toUniformSpace.{0} @Real (@SeminormedRing.toPseudoMetricSpace.{0} @Real
(@SeminormedCommRing.toSeminormedRing.{0} @Real (@NormedCommRing.toSeminormedCommRing.{0} @Real
(@NormedField.toNormedCommRing.{0} @Real (@NontriviallyNormedField.toNormedField.{0} @Real
(@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))) @Real @Real.instAdd
(@SMulZeroClass.toSMul.{0, 0} @Real @Real (@AddZero.toZero.{0} @Real (@AddZeroClass.toAddZero.{0} @Real
(@AddMonoid.toAddZeroClass.{0} @Real (@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0} @Real
(@AddCommGroup.toAddGroup.{0} @Real @Real.instAddCommGroup)))))) (@DistribSMul.toSMulZeroClass.{0, 0} @Real
@Real (@AddMonoid.toAddZeroClass.{0} @Real (@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0}
@Real (@AddCommGroup.toAddGroup.{0} @Real @Real.instAddCommGroup)))) (@DistribMulAction.toDistribSMul.{0, 0}
@Real @Real (@Semiring.toMonoid.{0} @Real (@CommSemiring.toSemiring.{0} @Real (@Semifield.toCommSemiring.{0}
@Real (@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real (@NontriviallyNormedField.toNormedField.{0}
@Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))
(@SubNegMonoid.toAddMonoid.{0} @Real (@AddGroup.toSubNegMonoid.{0} @Real (@AddCommGroup.toAddGroup.{0} @Real
@Real.instAddCommGroup))) (@Module.toDistribMulAction.{0, 0} @Real @Real (@CommSemiring.toSemiring.{0} @Real
(@Semifield.toCommSemiring.{0} @Real (@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))) (@AddCommGroup.toAddCommMonoid.{0} @Real @Real.instAddCommGroup)
(@Semiring.toModule.{0} @Real (@CommSemiring.toSemiring.{0} @Real (@Semifield.toCommSemiring.{0} @Real
(@Field.toSemifield.{0} @Real (@NormedField.toField.{0} @Real (@NontriviallyNormedField.toNormedField.{0} @Real
(@DenselyNormedField.toNontriviallyNormedField.{0} @Real @Real.denselyNormedField)))))))))))
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
@Real.pseudoMetricSpace)) (@IsTopologicalSemiring.toIsModuleTopology.{0} @Real @Real.semiring
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
(@SeminormedRing.toPseudoMetricSpace.{0} @Real (@SeminormedCommRing.toSeminormedRing.{0} @Real
(@NormedCommRing.toSeminormedCommRing.{0} @Real (@NormedField.toNormedCommRing.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))))) (@IsTopologicalRing.toIsTopologicalSemiring.{0} @Real
(@UniformSpace.toTopologicalSpace.{0} @Real (@PseudoMetricSpace.toUniformSpace.{0} @Real
(@SeminormedRing.toPseudoMetricSpace.{0} @Real (@SeminormedCommRing.toSeminormedRing.{0} @Real
(@NormedCommRing.toSeminormedCommRing.{0} @Real (@NormedField.toNormedCommRing.{0} @Real
(@NontriviallyNormedField.toNormedField.{0} @Real (@DenselyNormedField.toNontriviallyNormedField.{0} @Real
@Real.denselyNormedField)))))))) (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} @Real
(@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} @Real (@CommRing.toNonUnitalCommRing.{0} @Real
@Real.commRing))) @instIsTopologicalRingReal))) f__b1 (f___b3 u__b8) u__b8)))) /* binder Name hd */, (forall
(hpos__b10 : (forall (u__b11 : @Real) /* binder Name u */, (forall (x_0__b12 : (@Membership.mem.{0, 0} @Real
(@Set.{0} @Real) (@Set.instMembership.{0} @Real) (@Set.Icc.{0} @Real @Real.instPreorder a__b5 b__b6) u__b11)) /*
binder Name a._@._internal._hyg.#0 */, (@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0} @Real nat_lit(0)
(@Zero.toOfNat0.{0} @Real @Real.instZero)) (f___b3 u__b11))))) /* binder Name hpos */, (@MonotoneOn.{0, 0} @Real
@Real @Real.instPreorder @Real.instPreorder f__b1 (@Set.Icc.{0} @Real @Real.instPreorder a__b5 b__b6))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 31. Shao.OQ4.RademacherSpectralTail.normalizedTerm_abs_le

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.normalizedTerm_abs_le`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("normalizedTerm_abs_le").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.normalizedTerm_abs_le`.
- User Name: `Shao.OQ4.RademacherSpectralTail.normalizedTerm_abs_le`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("normalizedTerm_abs_le").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.normalizedTerm_abs_le)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {n__b2 : @Nat} /* binder Name n */, (forall {ell__b3 : @Nat}
/* binder Name ell */, (forall (hm__b4 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1)
(@instOfNatNat nat_lit(1))) m__b1)) /* binder Name hm */, (forall (hell__b5 : (@Membership.mem.{0, 0} @Nat
(@Finset.{0} @Nat) (@SetLike.instMembership.{0, 0} (@Finset.{0} @Nat) @Nat (@Finset.instSetLike.{0} @Nat))
(@Finset.erase.{0} @Nat @instDecidableEqNat (@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1)
(@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0)))) ell__b3)) /* binder Name hell */, (forall (ht__b6
: (@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.scaledTime m__b1 n__b2))) /*
binder Name ht */, (@LE.le.{0} @Real @Real.instLE (@abs.{0} @Real @Real.lattice @Real.instAddGroup
(@Shao.OQ4.RademacherSpectralPairing.normalizedTerm m__b1 n__b2 ell__b3)) (@HMul.hMul.{0, 0, 0} @Real @Real
@Real (@instHMul.{0} @Real @Real.instMul) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real
@Real.instMul) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2)
@Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))
(@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0))))))) (@OfNat.ofNat.{0} @Real
nat_lit(3) (@instOfNatAtLeastTwo.{0} @Real nat_lit(3) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1)))))))) (@Real.exp (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0}
@Real @Real.instMul) (@Neg.neg.{0} @Real @Real.instNeg (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0}
@Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) @Real.pi (@OfNat.ofNat.{0} @Nat
nat_lit(2) (@instOfNatNat nat_lit(2)))))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.scaledTime m__b1 n__b2))))
(@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0}
@Real @Real.instMonoid))) @Shao.OQ4.RademacherSpectralTail.decayRatio (@HSub.hSub.{0, 0, 0} @Nat @Nat @Nat
(@instHSub.{0} @Nat @instSubNat) ell__b3 (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 32. Shao.OQ4.RademacherSpectralTail.normalizedTerm_eq

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.normalizedTerm_eq`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("normalizedTerm_eq").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.normalizedTerm_eq`.
- User Name: `Shao.OQ4.RademacherSpectralTail.normalizedTerm_eq`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("normalizedTerm_eq").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.normalizedTerm_eq)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (forall (n__b2 : @Nat) /* binder Name n */, (forall (ell__b3 : @Nat)
/* binder Name ell */, (@Eq.{(0 + 1)} @Real (@Shao.OQ4.RademacherSpectralPairing.normalizedTerm m__b1 n__b2
ell__b3) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul)
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient m__b1 n__b2
ell__b3) (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real
(@Monoid.toNPow.{0} @Real @Real.instMonoid))) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@Real.cos (@Shao.OQ4.RademacherSpectralPairing.beta
m__b1 ell__b3)) (@Shao.OQ4.RademacherSpectralPairing.rho m__b1)) n__b2))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 33. Shao.OQ4.RademacherSpectralTail.pairedCoefficient

Classification: **explicit private**. Actual kind: **definition**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("pairedCoefficient").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient`.
- User Name: `Shao.OQ4.RademacherSpectralTail.pairedCoefficient`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("pairedCoefficient").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient)); hints = sequence(0: "regular", 1: 34); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (forall (n__b2 : @Nat) /* binder Name n */, (forall (ell__b3 : @Nat)
/* binder Name ell */, @Real)))
```

Full actual definition value:

```text
(fun (m__b1 : @Nat) /* binder Name m */ => (fun (n__b2 : @Nat) /* binder Name n */ => (fun (ell__b3 : @Nat) /*
binder Name ell */ => (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul)
(@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0}
@Real @Real.instMonoid))) (@Neg.neg.{0} @Real @Real.instNeg (@OfNat.ofNat.{0} @Real nat_lit(1)
(@One.toOfNat1.{0} @Real @Real.instOne))) ell__b3) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0}
@Real @Real.instAdd) (@Shao.OQ4.RademacherFiniteS1.cotangent (@Shao.OQ4.RademacherSpectralPairing.alpha m__b1
ell__b3)) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul)
(@Shao.OQ4.RademacherSpectralPairing.epsilon m__b1 n__b2) (@Real.tan (@Shao.OQ4.RademacherSpectralPairing.alpha
m__b1 ell__b3)))) (@Shao.OQ4.RademacherFiniteS1.cotangent
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle m__b1)))))))
```

## 34. Shao.OQ4.RademacherSpectralTail.relative_cosine_bound

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.relative_cosine_bound`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("relative_cosine_bound").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.relative_cosine_bound`.
- User Name: `Shao.OQ4.RademacherSpectralTail.relative_cosine_bound`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("relative_cosine_bound").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.relative_cosine_bound)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {v__b1 : @Real} /* binder Name v */, (forall {w__b2 : @Real} /* binder Name w */, (forall (hv__b3 :
(@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero))
v__b1)) /* binder Name hv */, (forall (hvw__b4 : (@LE.le.{0} @Real @Real.instLE v__b1 w__b2)) /* binder Name hvw
*/, (forall (hw__b5 : (@LT.lt.{0} @Real @Real.instLT w__b2 (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real
(@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) @Real.pi (@OfNat.ofNat.{0} @Real
nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat
(@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat
nat_lit(0) (@instOfNatNat nat_lit(0)))))))))) /* binder Name hw */, (@LE.le.{0} @Real @Real.instLE
(@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@Real.cos w__b2) (@Real.cos v__b1)) (@Real.exp (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real
(@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@Neg.neg.{0} @Real @Real.instNeg
(@HSub.hSub.{0, 0, 0} @Real @Real @Real (@instHSub.{0} @Real @Real.instSub) (@HPow.hPow.{0, 0, 0} @Real @Nat
@Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) w__b2
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2)))) (@HPow.hPow.{0, 0, 0} @Real @Nat @Real
(@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) v__b1
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2)))))) (@OfNat.ofNat.{0} @Real nat_lit(2)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0}
@Nat nat_lit(1) (@instOfNatNat nat_lit(1))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0)
(@instOfNatNat nat_lit(0)))))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 35. Shao.OQ4.RademacherSpectralTail.remainder_eq_sum

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.remainder_eq_sum`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_eq_sum").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.remainder_eq_sum`.
- User Name: `Shao.OQ4.RademacherSpectralTail.remainder_eq_sum`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_eq_sum").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.remainder_eq_sum)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {n__b1 : @Nat} /* binder Name n */, (forall (m__b2 : @Nat) /* binder Name m */, (forall (hn__b3 :
(@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) n__b1)) /* binder Name
hn */, (@Eq.{(0 + 1)} @Real (@Shao.OQ4.RademacherSpectralPairing.remainder m__b2 n__b1) (@Finset.sum.{0, 0} @Nat
@Real @Real.instAddCommMonoid (@Finset.erase.{0} @Nat @instDecidableEqNat
(@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b2) (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat
nat_lit(0)))) (fun (ell__b4 : @Nat) /* binder Name ell */ => (@Shao.OQ4.RademacherSpectralPairing.normalizedTerm
m__b2 n__b1 ell__b4)))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 36. Shao.OQ4.RademacherSpectralTail.rho_eq

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.rho_eq`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("rho_eq").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.rho_eq`.
- User Name: `Shao.OQ4.RademacherSpectralTail.rho_eq`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("rho_eq").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.rho_eq)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (@Eq.{(0 + 1)} @Real (@Shao.OQ4.RademacherSpectralPairing.rho m__b1)
(@Real.cos (@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle m__b1))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 37. Shao.OQ4.RademacherSpectralTail.scaledTime

Classification: **explicit private**. Actual kind: **definition**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.scaledTime`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("scaledTime").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.scaledTime`.
- User Name: `Shao.OQ4.RademacherSpectralTail.scaledTime`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("scaledTime").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.scaledTime)); hints = sequence(0: "regular", 1: 26); safety = "Lean.DefinitionSafety.safe".
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (forall (n__b2 : @Nat) /* binder Name n */, @Real))
```

Full actual definition value:

```text
(fun (m__b1 : @Nat) /* binder Name m */ => (fun (n__b2 : @Nat) /* binder Name n */ => (@HDiv.hDiv.{0, 0, 0}
@Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@Nat.cast.{0}
@Real @Real.instNatCast n__b2) (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat
(@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid)))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height m__b1) (@OfNat.ofNat.{0}
@Nat nat_lit(2) (@instOfNatNat nat_lit(2)))))))
```

## 38. Shao.OQ4.RademacherSpectralTail.self_le_tan

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.self_le_tan`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("self_le_tan").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.self_le_tan`.
- User Name: `Shao.OQ4.RademacherSpectralTail.self_le_tan`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("self_le_tan").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.self_le_tan)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {u__b1 : @Real} /* binder Name u */, (forall (hu__b2 : (@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0}
@Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)) u__b1)) /* binder Name hu */, (forall (hu___b3 :
(@LT.lt.{0} @Real @Real.instLT u__b1 (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) @Real.pi (@OfNat.ofNat.{0} @Real nat_lit(2)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0}
@Nat nat_lit(1) (@instOfNatNat nat_lit(1))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0)
(@instOfNatNat nat_lit(0)))))))))) /* binder Name hu' */, (@LE.le.{0} @Real @Real.instLE u__b1 (@Real.tan
u__b1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 39. Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le`.
- User Name: `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {ell__b2 : @Nat} /* binder Name ell */, (forall (hm__b3 :
(@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) m__b1)) /* binder Name
hm */, (forall (hell__b4 : (@Membership.mem.{0, 0} @Nat (@Finset.{0} @Nat) (@SetLike.instMembership.{0, 0}
(@Finset.{0} @Nat) @Nat (@Finset.instSetLike.{0} @Nat)) (@Finset.erase.{0} @Nat @instDecidableEqNat
(@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1) (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat
nat_lit(0)))) ell__b2)) /* binder Name hell */, (forall (n__b5 : @Nat) /* binder Name n */, (@LE.le.{0} @Real
@Real.instLE (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real
(@Monoid.toNPow.{0} @Real @Real.instMonoid))) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@Real.cos (@Shao.OQ4.RademacherSpectralPairing.beta
m__b1 ell__b2)) (@Shao.OQ4.RademacherSpectralPairing.rho m__b1)) n__b5) (@Real.exp (@HDiv.hDiv.{0, 0, 0} @Real
@Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@HMul.hMul.{0, 0, 0}
@Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0}
@Real @Real.instMul) (@Neg.neg.{0} @Real @Real.instNeg (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0}
@Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid))) @Real.pi (@OfNat.ofNat.{0} @Nat
nat_lit(2) (@instOfNatNat nat_lit(2))))) (@HSub.hSub.{0, 0, 0} @Real @Real @Real (@instHSub.{0} @Real
@Real.instSub) (@HPow.hPow.{0, 0, 0} @Real @Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real
(@Monoid.toNPow.{0} @Real @Real.instMonoid)))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency ell__b2)
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2)))) (@OfNat.ofNat.{0} @Real nat_lit(1)
(@One.toOfNat1.{0} @Real @Real.instOne))))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.scaledTime m__b1 n__b5))
(@OfNat.ofNat.{0} @Real nat_lit(8) (@instOfNatAtLeastTwo.{0} @Real nat_lit(8) @Real.instNatCast
(@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(7) (@instOfNatNat nat_lit(7))) (@Nat.instNeZeroSucc
(@OfNat.ofNat.{0} @Nat nat_lit(6) (@instOfNatNat nat_lit(6)))))))))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 40. Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_geometric_sum_le").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le`.
- User Name: `Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_geometric_sum_le").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (@LE.le.{0} @Real @Real.instLE (@Finset.sum.{0, 0} @Nat @Real
@Real.instAddCommMonoid (@Finset.erase.{0} @Nat @instDecidableEqNat
(@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1) (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat
nat_lit(0)))) (fun (ell__b2 : @Nat) /* binder Name ell */ => (@HPow.hPow.{0, 0, 0} @Real @Nat @Real
(@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid)))
@Shao.OQ4.RademacherSpectralTail.decayRatio (@HSub.hSub.{0, 0, 0} @Nat @Nat @Nat (@instHSub.{0} @Nat
@instSubNat) ell__b2 (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))))))) (@HDiv.hDiv.{0, 0, 0}
@Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) (@OfNat.ofNat.{0}
@Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne)) (@HSub.hSub.{0, 0, 0} @Real @Real @Real (@instHSub.{0}
@Real @Real.instSub) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne))
@Shao.OQ4.RademacherSpectralTail.decayRatio))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 41. Shao.OQ4.RademacherSpectralTail.tail_membership

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_membership`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_membership").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.tail_membership`.
- User Name: `Shao.OQ4.RademacherSpectralTail.tail_membership`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_membership").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_membership)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {ell__b2 : @Nat} /* binder Name ell */, (forall (hell__b3 :
(@Membership.mem.{0, 0} @Nat (@Finset.{0} @Nat) (@SetLike.instMembership.{0, 0} (@Finset.{0} @Nat) @Nat
(@Finset.instSetLike.{0} @Nat)) (@Finset.erase.{0} @Nat @instDecidableEqNat
(@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1) (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat
nat_lit(0)))) ell__b2)) /* binder Name hell */, (@And (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))) ell__b2) (@And (@LE.le.{0} @Nat @instLENat ell__b2 m__b1)
(@Membership.mem.{0, 0} @Nat (@Finset.{0} @Nat) (@SetLike.instMembership.{0, 0} (@Finset.{0} @Nat) @Nat
(@Finset.instSetLike.{0} @Nat)) (@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1) ell__b2))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 42. Shao.OQ4.RademacherSpectralTail.tan_convex_Icc

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tan_convex_Icc`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tan_convex_Icc").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.tan_convex_Icc`.
- User Name: `Shao.OQ4.RademacherSpectralTail.tan_convex_Icc`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tan_convex_Icc").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tan_convex_Icc)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {y__b1 : @Real} /* binder Name y */, (forall (hy__b2 : (@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0}
@Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)) y__b1)) /* binder Name hy */, (forall (hy___b3 :
(@LT.lt.{0} @Real @Real.instLT y__b1 (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real
(@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) @Real.pi (@OfNat.ofNat.{0} @Real nat_lit(2)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0}
@Nat nat_lit(1) (@instOfNatNat nat_lit(1))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0)
(@instOfNatNat nat_lit(0)))))))))) /* binder Name hy' */, (@ConvexOn.{0, 0, 0} @Real @Real @Real @Real.semiring
@Real.partialOrder @Real.instAddCommMonoid @Real.instAddCommMonoid @Real.partialOrder (@instSMulOfMul.{0} @Real
@Real.instMul) (@instSMulOfMul.{0} @Real @Real.instMul) (@Set.Icc.{0} @Real @Real.instPreorder (@OfNat.ofNat.{0}
@Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero)) y__b1) @Real.tan))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 43. Shao.OQ4.RademacherSpectralTail.tan_scale_le

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tan_scale_le`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tan_scale_le").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.tan_scale_le`.
- User Name: `Shao.OQ4.RademacherSpectralTail.tan_scale_le`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tan_scale_le").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tan_scale_le)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {x__b1 : @Real} /* binder Name x */, (forall {r__b2 : @Real} /* binder Name r */, (forall (hx__b3 :
(@LT.lt.{0} @Real @Real.instLT (@OfNat.ofNat.{0} @Real nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero))
x__b1)) /* binder Name hx */, (forall (hr__b4 : (@LE.le.{0} @Real @Real.instLE (@OfNat.ofNat.{0} @Real
nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne)) r__b2)) /* binder Name hr */, (forall (hrx__b5 : (@LT.lt.{0}
@Real @Real.instLT (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) r__b2 x__b1)
(@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) @Real.pi (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real nat_lit(2)
@Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))
(@Nat.instNeZeroSucc (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0)))))))))) /* binder Name hrx */,
(@LE.le.{0} @Real @Real.instLE (@Real.tan x__b1) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real
@Real.instMul) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne)) r__b2)
(@Real.tan (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) r__b2 x__b1)))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 44. Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes

Classification: **explicit private**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("zeroMode_vanishes").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes`.
- User Name: `Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("zeroMode_vanishes").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {n__b1 : @Nat} /* binder Name n */, (forall (m__b2 : @Nat) /* binder Name m */, (forall (hn__b3 :
(@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) n__b1)) /* binder Name
hn */, (@Eq.{(0 + 1)} @Real (@Shao.OQ4.RademacherSpectralPairing.zeroMode m__b2 n__b1) (@OfNat.ofNat.{0} @Real
nat_lit(0) (@Zero.toOfNat0.{0} @Real @Real.instZero))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 45. Shao.OQ4.RademacherFiniteS1.cotangent.eq_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherFiniteS1.cotangent.eq_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherFiniteS1") -> str("cotangent") -> str("eq_1").
  Captured raw display: `Shao.OQ4.RademacherFiniteS1.cotangent.eq_1`.
- User Name: `Shao.OQ4.RademacherFiniteS1.cotangent.eq_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherFiniteS1") -> str("cotangent") -> str("eq_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherFiniteS1.cotangent.eq_1)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (x__b1 : @Real) /* binder Name x */, (@Eq.{(0 + 1)} @Real (@Shao.OQ4.RademacherFiniteS1.cotangent x__b1)
(@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@Real.cos x__b1) (@Real.sin x__b1))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 46. Shao.OQ4.RademacherSpectralTail.decayRatio._proof_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.decayRatio._proof_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("decayRatio") -> str("_proof_1").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.decayRatio._proof_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.decayRatio._proof_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("decayRatio") -> str("_proof_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.decayRatio._proof_1)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(@Nat.AtLeastTwo (@HAdd.hAdd.{0, 0, 0} @Nat @Nat @Nat (@instHAdd.{0} @Nat @instAddNat) (@OfNat.ofNat.{0} @Nat
nat_lit(2) (@instOfNatNat nat_lit(2))) (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 47. Shao.OQ4.RademacherSpectralTail.remainder_uniform._proof_1_2

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `Shao.OQ4.RademacherSpectralTail.remainder_uniform._proof_1_2`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_uniform") -> str("_proof_1_2").
  Captured raw display: `Shao.OQ4.RademacherSpectralTail.remainder_uniform._proof_1_2`.
- User Name: `Shao.OQ4.RademacherSpectralTail.remainder_uniform._proof_1_2`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("remainder_uniform") -> str("_proof_1_2").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: false.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(Shao.OQ4.RademacherSpectralTail.remainder_uniform._proof_1_2)).
- Complete axiom set (captured order): `propext`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {n__b2 : @Nat} /* binder Name n */, (forall (hnpos__b3 :
(@LT.lt.{0} @Nat @instLTNat (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0))) n__b2)) /* binder Name
hnpos */, (forall (x_204__b4 : (@Not meta[0: noImplicitLambda = bool(true)]((@LE.le.{0} @Nat @instLENat
(@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) n__b2)))) /* binder Name
a._@._internal.#0.Shao.OQ4.RademacherSpectralTail.#214476760._hygCtx._hyg.#204 */, @False))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 48. Shao.OQ4.RademacherSpectralTail.baseAngle._proof_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle._proof_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("baseAngle") -> str("_proof_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.baseAngle._proof_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.baseAngle._proof_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("baseAngle") -> str("_proof_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle._proof_1)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(@Nat.AtLeastTwo (@HAdd.hAdd.{0, 0, 0} @Nat @Nat @Nat (@instHAdd.{0} @Nat @instAddNat) (@OfNat.ofNat.{0} @Nat
nat_lit(3) (@instOfNatNat nat_lit(3))) (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 49. Shao.OQ4.RademacherSpectralTail.baseAngle.eq_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle.eq_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("baseAngle") -> str("eq_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.baseAngle.eq_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.baseAngle.eq_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("baseAngle") -> str("eq_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle.eq_1)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (@Eq.{(0 + 1)} @Real
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle m__b1) (@HDiv.hDiv.{0,
0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) @Real.pi
(@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@OfNat.ofNat.{0} @Real nat_lit(4)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(4) @Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle._proof_1))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height m__b1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 50. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._proof_1_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._proof_1_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_proof_1_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._proof_1_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._proof_1_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_proof_1_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._proof_1_1)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {ell__b2 : @Nat} /* binder Name ell */, (forall (ht__b3 :
(@And (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) ell__b2) (@And
(@LE.le.{0} @Nat @instLENat ell__b2 m__b1) (@Membership.mem.{0, 0} @Nat (@Finset.{0} @Nat)
(@SetLike.instMembership.{0, 0} (@Finset.{0} @Nat) @Nat (@Finset.instSetLike.{0} @Nat))
(@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1) ell__b2)))) /* binder Name ht */, (forall (x_151__b4 :
(@Not (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(3) (@instOfNatNat nat_lit(3))) (@HAdd.hAdd.{0,
0, 0} @Nat @Nat @Nat (@instHAdd.{0} @Nat @instAddNat) (@HMul.hMul.{0, 0, 0} @Nat @Nat @Nat (@instHMul.{0} @Nat
@instMulNat) (@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))) ell__b2) (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))))))) /* binder Name
a._@._internal.#0.Shao.OQ4.RademacherSpectralTail.#1222550412._hygCtx._hyg.#151 */, @False))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 51. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_3

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_3`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_3").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_3`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_3`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_3").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_2 [anonymous -> str("u_2")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_3)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {___b1 : Sort((u_2 + 1))} /* binder Name α */, (forall [x_7__b2 : (@Zero.{u_2} ___b1)] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#2030121524._hygCtx._hyg.#7 */, (forall [x_10__b3 : (@OfNat.{u_2} ___b1
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#2030121524._hygCtx._hyg.#10 */, (forall [x_14__b4 : (@NeZero.{u_2} ___b1 x_7__b2
(@OfNat.ofNat.{u_2} ___b1 nat_lit(2) x_10__b3))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#2030121524._hygCtx._hyg.#14 */, (@Eq.{(0 + 1)} Prop (@Eq.{(u_2 + 1)} ___b1
(@OfNat.ofNat.{u_2} ___b1 nat_lit(2) x_10__b3) (@OfNat.ofNat.{u_2} ___b1 nat_lit(0) (@Zero.toOfNat0.{u_2} ___b1
x_7__b2))) @False)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 52. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_4

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_4`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_4").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_4`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_4`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_4").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_2 [anonymous -> str("u_2")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_4)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {___b1 : Sort((u_2 + 1))} /* binder Name α */, (forall [x_7__b2 : (@Zero.{u_2} ___b1)] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#289478065._hygCtx._hyg.#7 */, (forall [x_10__b3 : (@OfNat.{u_2} ___b1
(@OfNat.ofNat.{0} @Nat nat_lit(3) (@instOfNatNat nat_lit(3))))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#289478065._hygCtx._hyg.#10 */, (forall [x_14__b4 : (@NeZero.{u_2} ___b1 x_7__b2
(@OfNat.ofNat.{u_2} ___b1 nat_lit(3) x_10__b3))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#289478065._hygCtx._hyg.#14 */, (@Eq.{(0 + 1)} Prop (@Eq.{(u_2 + 1)} ___b1
(@OfNat.ofNat.{u_2} ___b1 nat_lit(3) x_10__b3) (@OfNat.ofNat.{u_2} ___b1 nat_lit(0) (@Zero.toOfNat0.{u_2} ___b1
x_7__b2))) @False)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 53. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_5

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_5`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_5").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_5`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_5`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_5").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_2 [anonymous -> str("u_2")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_5)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {___b1 : Sort((u_2 + 1))} /* binder Name α */, (forall [x_7__b2 : (@Zero.{u_2} ___b1)] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#1405315497._hygCtx._hyg.#7 */, (forall [x_10__b3 : (@OfNat.{u_2} ___b1
(@OfNat.ofNat.{0} @Nat nat_lit(4) (@instOfNatNat nat_lit(4))))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#1405315497._hygCtx._hyg.#10 */, (forall [x_14__b4 : (@NeZero.{u_2} ___b1 x_7__b2
(@OfNat.ofNat.{u_2} ___b1 nat_lit(4) x_10__b3))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#1405315497._hygCtx._hyg.#14 */, (@Eq.{(0 + 1)} Prop (@Eq.{(u_2 + 1)} ___b1
(@OfNat.ofNat.{u_2} ___b1 nat_lit(4) x_10__b3) (@OfNat.ofNat.{u_2} ___b1 nat_lit(0) (@Zero.toOfNat0.{u_2} ___b1
x_7__b2))) @False)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 54. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_6

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_6`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_6").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_6`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_6`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_6").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_1 [anonymous -> str("u_1")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_6)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {M___b1 : Sort((u_1 + 1))} /* binder Name M₀ */, (forall [x_4__b2 : (@Mul.{u_1} M___b1)] /* binder Name
inst._@.Mathlib.Algebra.GroupWithZero.Basic.#430946186._hygCtx._hyg.#4 */, (forall [x_7__b3 : (@Zero.{u_1}
M___b1)] /* binder Name inst._@.Mathlib.Algebra.GroupWithZero.Basic.#430946186._hygCtx._hyg.#7 */, (forall
[x_10__b4 : (@NoZeroDivisors.{u_1} M___b1 x_4__b2 x_7__b3)] /* binder Name
inst._@.Mathlib.Algebra.GroupWithZero.Basic.#430946186._hygCtx._hyg.#10 */, (forall {a__b5 : M___b1} /* binder
Name a */, (forall {b__b6 : M___b1} /* binder Name b */, (forall (ha__b7 : (@Ne.{(u_1 + 1)} M___b1 a__b5
(@OfNat.ofNat.{u_1} M___b1 nat_lit(0) (@Zero.toOfNat0.{u_1} M___b1 x_7__b3)))) /* binder Name ha */, (forall
(hb__b8 : (@Ne.{(u_1 + 1)} M___b1 b__b6 (@OfNat.ofNat.{u_1} M___b1 nat_lit(0) (@Zero.toOfNat0.{u_1} M___b1
x_7__b3)))) /* binder Name hb */, (@Eq.{(0 + 1)} Prop (@Eq.{(u_1 + 1)} M___b1 (@HMul.hMul.{u_1, u_1, u_1} M___b1
M___b1 M___b1 (@instHMul.{u_1} M___b1 x_4__b2) a__b5 b__b6) (@OfNat.ofNat.{u_1} M___b1 nat_lit(0)
(@Zero.toOfNat0.{u_1} M___b1 x_7__b3))) @False)))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 55. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_7

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_7`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_7").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_7`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_7`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_7").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_1 [anonymous -> str("u_1")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_7)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {M___b1 : Sort((u_1 + 1))} /* binder Name M₀ */, (forall [x_4__b2 : (@MonoidWithZero.{u_1} M___b1)] /*
binder Name inst._@.Mathlib.Algebra.GroupWithZero.Basic.#301975504._hygCtx._hyg.#4 */, (forall {a__b3 : M___b1}
/* binder Name a */, (forall [x_11__b4 : (@IsReduced.{u_1} M___b1 (@MulZeroClass.toZero.{u_1} M___b1
(@MulZeroOneClass.toMulZeroClass.{u_1} M___b1 (@MonoidWithZero.toMulZeroOneClass.{u_1} M___b1 x_4__b2)))
(@NPow.toPow.{u_1} M___b1 (@Monoid.toNPow.{u_1} M___b1 (@MonoidWithZero.toMonoid.{u_1} M___b1 x_4__b2))))] /*
binder Name inst._@.Mathlib.Algebra.GroupWithZero.Basic.#301975504._hygCtx._hyg.#11 */, (forall (n__b5 : @Nat)
/* binder Name n */, (forall (h__b6 : (@Ne.{(u_1 + 1)} M___b1 a__b3 (@OfNat.ofNat.{u_1} M___b1 nat_lit(0)
(@Zero.toOfNat0.{u_1} M___b1 (@MulZeroClass.toZero.{u_1} M___b1 (@MulZeroOneClass.toMulZeroClass.{u_1} M___b1
(@MonoidWithZero.toMulZeroOneClass.{u_1} M___b1 x_4__b2))))))) /* binder Name h */, (@Eq.{(0 + 1)} Prop
(@Eq.{(u_1 + 1)} M___b1 (@HPow.hPow.{u_1, 0, u_1} M___b1 @Nat M___b1 (@instHPow.{u_1, 0} M___b1 @Nat
(@NPow.toPow.{u_1} M___b1 (@Monoid.toNPow.{u_1} M___b1 (@MonoidWithZero.toMonoid.{u_1} M___b1 x_4__b2)))) a__b3
n__b5) (@OfNat.ofNat.{u_1} M___b1 nat_lit(0) (@Zero.toOfNat0.{u_1} M___b1 (@MulZeroClass.toZero.{u_1} M___b1
(@MulZeroOneClass.toMulZeroClass.{u_1} M___b1 (@MonoidWithZero.toMulZeroOneClass.{u_1} M___b1 x_4__b2))))))
@False)))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 56. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_8

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_8`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_8").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_8`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_8`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_8").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_3 [anonymous -> str("u_3")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_8)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {G___b1 : Sort((u_3 + 1))} /* binder Name G₀ */, (forall [x_8__b2 : (@GroupWithZero.{u_3} G___b1)] /*
binder Name inst._@.Mathlib.Algebra.GroupWithZero.Units.Basic.#2998152944._hygCtx._hyg.#8 */, (forall {a__b3 :
G___b1} /* binder Name a */, (forall (n__b4 : @Int) /* binder Name n */, (forall (x_0__b5 : (@Ne.{(u_3 + 1)}
G___b1 a__b3 (@OfNat.ofNat.{u_3} G___b1 nat_lit(0) (@Zero.toOfNat0.{u_3} G___b1 (@MulZeroClass.toZero.{u_3}
G___b1 (@MulZeroOneClass.toMulZeroClass.{u_3} G___b1 (@MonoidWithZero.toMulZeroOneClass.{u_3} G___b1
(@GroupWithZero.toMonoidWithZero.{u_3} G___b1 x_8__b2)))))))) /* binder Name a._@._internal._hyg.#0 */, (@Eq.{(0
+ 1)} Prop (@Eq.{(u_3 + 1)} G___b1 (@HPow.hPow.{u_3, 0, u_3} G___b1 @Int G___b1 (@instHPow.{u_3, 0} G___b1 @Int
(@ZPow.toPow.{u_3} G___b1 (@DivInvMonoid.toZPow.{u_3} G___b1 (@GroupWithZero.toDivInvMonoid.{u_3} G___b1
x_8__b2)))) a__b3 n__b4) (@OfNat.ofNat.{u_3} G___b1 nat_lit(0) (@Zero.toOfNat0.{u_3} G___b1
(@MulZeroClass.toZero.{u_3} G___b1 (@MulZeroOneClass.toMulZeroClass.{u_3} G___b1
(@MonoidWithZero.toMulZeroOneClass.{u_3} G___b1 (@GroupWithZero.toMonoidWithZero.{u_3} G___b1 x_8__b2)))))))
@False))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 57. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_9

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_9`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_9").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_9`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_9`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le") -> str("_simp_1_9").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_1 [anonymous -> str("u_1")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le._simp_1_9)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {R__b1 : Sort((u_1 + 1))} /* binder Name R */, (forall [x_3__b2 : (@AddMonoidWithOne.{u_1} R__b1)] /*
binder Name inst._@.Mathlib.Algebra.CharZero.Defs.#1325129559._hygCtx._hyg.#3 */, (forall [x_6__b3 :
(@CharZero.{u_1} R__b1 x_3__b2)] /* binder Name
inst._@.Mathlib.Algebra.CharZero.Defs.#1325129559._hygCtx._hyg.#6 */, (forall (n__b4 : @Nat) /* binder Name n
*/, (@Eq.{(0 + 1)} Prop (@Eq.{(u_1 + 1)} R__b1 (@HAdd.hAdd.{u_1, u_1, u_1} R__b1 R__b1 R__b1 (@instHAdd.{u_1}
R__b1 (@AddSemigroup.toAdd.{u_1} R__b1 (@AddMonoid.toAddSemigroup.{u_1} R__b1
(@AddMonoidWithOne.toAddMonoid.{u_1} R__b1 x_3__b2)))) (@Nat.cast.{u_1} R__b1 (@AddMonoidWithOne.toNatCast.{u_1}
R__b1 x_3__b2) n__b4) (@OfNat.ofNat.{u_1} R__b1 nat_lit(1) (@One.toOfNat1.{u_1} R__b1
(@AddMonoidWithOne.toOne.{u_1} R__b1 x_3__b2)))) (@OfNat.ofNat.{u_1} R__b1 nat_lit(0) (@Zero.toOfNat0.{u_1}
R__b1 (@AddZero.toZero.{u_1} R__b1 (@AddZeroClass.toAddZero.{u_1} R__b1 (@AddMonoid.toAddZeroClass.{u_1} R__b1
(@AddMonoidWithOne.toAddMonoid.{u_1} R__b1 x_3__b2))))))) @False)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 58. Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds._proof_1_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds._proof_1_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le_two_thirds") -> str("_proof_1_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds._proof_1_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds._proof_1_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("coefficient_abs_le_two_thirds") -> str("_proof_1_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.coefficient_abs_le_two_thirds._proof_1_1)).
- Complete axiom set (captured order): `propext`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {ell__b2 : @Nat} /* binder Name ell */, (forall (he__b3 :
(@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) ell__b2)) /* binder
Name he */, (forall (x_134__b4 : (@Not (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(3)
(@instOfNatNat nat_lit(3))) (@HAdd.hAdd.{0, 0, 0} @Nat @Nat @Nat (@instHAdd.{0} @Nat @instAddNat)
(@HMul.hMul.{0, 0, 0} @Nat @Nat @Nat (@instHMul.{0} @Nat @instMulNat) (@OfNat.ofNat.{0} @Nat nat_lit(2)
(@instOfNatNat nat_lit(2))) ell__b2) (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))))))) /* binder
Name a._@._internal.#0.Shao.OQ4.RademacherSpectralTail.#4255634682._hygCtx._hyg.#134 */, @False))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 59. Shao.OQ4.RademacherSpectralTail.exponential_frequency_le._proof_1_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.exponential_frequency_le._proof_1_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("exponential_frequency_le") -> str("_proof_1_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.exponential_frequency_le._proof_1_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.exponential_frequency_le._proof_1_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("exponential_frequency_le") -> str("_proof_1_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.exponential_frequency_le._proof_1_1)).
- Complete axiom set (captured order): `propext`, `Quot.sound`.

Full actual type:

```text
(forall {ell__b1 : @Nat} /* binder Name ell */, (forall (hell__b2 : (@LE.le.{0} @Nat @instLENat
(@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) ell__b1)) /* binder Name hell */, (forall
(x_111__b3 : (@Not (@Eq.{(0 + 1)} @Nat ell__b1 (@HAdd.hAdd.{0, 0, 0} @Nat @Nat @Nat (@instHAdd.{0} @Nat
@instAddNat) (@HSub.hSub.{0, 0, 0} @Nat @Nat @Nat (@instHSub.{0} @Nat @instSubNat) ell__b1 (@OfNat.ofNat.{0}
@Nat nat_lit(1) (@instOfNatNat nat_lit(1)))) (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))))))
/* binder Name a._@._internal.#0.Shao.OQ4.RademacherSpectralTail.#4100161698._hygCtx._hyg.#111 */, @False)))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 60. Shao.OQ4.RademacherSpectralTail.frequency.eq_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency.eq_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("frequency") -> str("eq_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.frequency.eq_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.frequency.eq_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("frequency") -> str("eq_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency.eq_1)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (ell__b1 : @Nat) /* binder Name ell */, (@Eq.{(0 + 1)} @Real
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.frequency ell__b1) (@HAdd.hAdd.{0,
0, 0} @Real @Real @Real (@instHAdd.{0} @Real @Real.instAdd) (@HMul.hMul.{0, 0, 0} @Real @Real @Real
(@instHMul.{0} @Real @Real.instMul) (@OfNat.ofNat.{0} @Real nat_lit(2) (@instOfNatAtLeastTwo.{0} @Real
nat_lit(2) @Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1)) (@Nat.cast.{0}
@Real @Real.instNatCast ell__b1)) (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 61. Shao.OQ4.RademacherSpectralTail.height.eq_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height.eq_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("height") -> str("eq_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.height.eq_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.height.eq_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("height") -> str("eq_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height.eq_1)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (@Eq.{(0 + 1)} @Real
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height m__b1) (@HAdd.hAdd.{0, 0,
0} @Real @Real @Real (@instHAdd.{0} @Real @Real.instAdd) (@Nat.cast.{0} @Real @Real.instNatCast m__b1)
(@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 62. Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle") -> str("_proof_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle") -> str("_proof_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(@Nat.AtLeastTwo (@HAdd.hAdd.{0, 0, 0} @Nat @Nat @Nat (@instHAdd.{0} @Nat @instAddNat) (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))) (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 63. Shao.OQ4.RademacherSpectralTail.mainAngle.eq_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle.eq_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle") -> str("eq_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.mainAngle.eq_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.mainAngle.eq_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("mainAngle") -> str("eq_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle.eq_1)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (@Eq.{(0 + 1)} @Real
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle m__b1) (@HDiv.hDiv.{0,
0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real @Real.instDivInvMonoid)) @Real.pi
(@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@OfNat.ofNat.{0} @Real nat_lit(2)
(@instOfNatAtLeastTwo.{0} @Real nat_lit(2) @Real.instNatCast
@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.mainAngle._proof_1))
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.height m__b1)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 64. Shao.OQ4.RademacherSpectralTail.pairedCoefficient.eq_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient.eq_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("pairedCoefficient") -> str("eq_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient.eq_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.pairedCoefficient.eq_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("pairedCoefficient") -> str("eq_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient.eq_1)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (forall (n__b2 : @Nat) /* binder Name n */, (forall (ell__b3 : @Nat)
/* binder Name ell */, (@Eq.{(0 + 1)} @Real
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.pairedCoefficient m__b1 n__b2
ell__b3) (@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul) (@HPow.hPow.{0, 0, 0} @Real
@Nat @Real (@instHPow.{0, 0} @Real @Nat (@NPow.toPow.{0} @Real (@Monoid.toNPow.{0} @Real @Real.instMonoid)))
(@Neg.neg.{0} @Real @Real.instNeg (@OfNat.ofNat.{0} @Real nat_lit(1) (@One.toOfNat1.{0} @Real @Real.instOne)))
ell__b3) (@HDiv.hDiv.{0, 0, 0} @Real @Real @Real (@instHDiv.{0} @Real (@DivInvMonoid.toDiv.{0} @Real
@Real.instDivInvMonoid)) (@HAdd.hAdd.{0, 0, 0} @Real @Real @Real (@instHAdd.{0} @Real @Real.instAdd)
(@Shao.OQ4.RademacherFiniteS1.cotangent (@Shao.OQ4.RademacherSpectralPairing.alpha m__b1 ell__b3))
(@HMul.hMul.{0, 0, 0} @Real @Real @Real (@instHMul.{0} @Real @Real.instMul)
(@Shao.OQ4.RademacherSpectralPairing.epsilon m__b1 n__b2) (@Real.tan (@Shao.OQ4.RademacherSpectralPairing.alpha
m__b1 ell__b3)))) (@Shao.OQ4.RademacherFiniteS1.cotangent
(@_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.baseAngle m__b1))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 65. Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_2 [anonymous -> str("u_2")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_1)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {___b1 : Sort((u_2 + 1))} /* binder Name α */, (forall [x_7__b2 : (@Zero.{u_2} ___b1)] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#2030121524._hygCtx._hyg.#7 */, (forall [x_10__b3 : (@OfNat.{u_2} ___b1
(@OfNat.ofNat.{0} @Nat nat_lit(2) (@instOfNatNat nat_lit(2))))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#2030121524._hygCtx._hyg.#10 */, (forall [x_14__b4 : (@NeZero.{u_2} ___b1 x_7__b2
(@OfNat.ofNat.{u_2} ___b1 nat_lit(2) x_10__b3))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#2030121524._hygCtx._hyg.#14 */, (@Eq.{(0 + 1)} Prop (@Eq.{(u_2 + 1)} ___b1
(@OfNat.ofNat.{u_2} ___b1 nat_lit(2) x_10__b3) (@OfNat.ofNat.{u_2} ___b1 nat_lit(0) (@Zero.toOfNat0.{u_2} ___b1
x_7__b2))) @False)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 66. Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_2

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_2`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_2").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_2`.
- User Name: `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_2`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_2").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_2 [anonymous -> str("u_2")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_2)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {___b1 : Sort((u_2 + 1))} /* binder Name α */, (forall [x_7__b2 : (@Zero.{u_2} ___b1)] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#289478065._hygCtx._hyg.#7 */, (forall [x_10__b3 : (@OfNat.{u_2} ___b1
(@OfNat.ofNat.{0} @Nat nat_lit(3) (@instOfNatNat nat_lit(3))))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#289478065._hygCtx._hyg.#10 */, (forall [x_14__b4 : (@NeZero.{u_2} ___b1 x_7__b2
(@OfNat.ofNat.{u_2} ___b1 nat_lit(3) x_10__b3))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#289478065._hygCtx._hyg.#14 */, (@Eq.{(0 + 1)} Prop (@Eq.{(u_2 + 1)} ___b1
(@OfNat.ofNat.{u_2} ___b1 nat_lit(3) x_10__b3) (@OfNat.ofNat.{u_2} ___b1 nat_lit(0) (@Zero.toOfNat0.{u_2} ___b1
x_7__b2))) @False)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 67. Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_3

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_3`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_3").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_3`.
- User Name: `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_3`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_3").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_2 [anonymous -> str("u_2")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_3)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {___b1 : Sort((u_2 + 1))} /* binder Name α */, (forall [x_7__b2 : (@Zero.{u_2} ___b1)] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#1405315497._hygCtx._hyg.#7 */, (forall [x_10__b3 : (@OfNat.{u_2} ___b1
(@OfNat.ofNat.{0} @Nat nat_lit(4) (@instOfNatNat nat_lit(4))))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#1405315497._hygCtx._hyg.#10 */, (forall [x_14__b4 : (@NeZero.{u_2} ___b1 x_7__b2
(@OfNat.ofNat.{u_2} ___b1 nat_lit(4) x_10__b3))] /* binder Name
inst._@.Mathlib.Algebra.NeZero.#1405315497._hygCtx._hyg.#14 */, (@Eq.{(0 + 1)} Prop (@Eq.{(u_2 + 1)} ___b1
(@OfNat.ofNat.{u_2} ___b1 nat_lit(4) x_10__b3) (@OfNat.ofNat.{u_2} ___b1 nat_lit(0) (@Zero.toOfNat0.{u_2} ___b1
x_7__b2))) @False)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 68. Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_4

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_4`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_4").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_4`.
- User Name: `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_4`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_4").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_1 [anonymous -> str("u_1")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_4)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {M___b1 : Sort((u_1 + 1))} /* binder Name M₀ */, (forall [x_4__b2 : (@Mul.{u_1} M___b1)] /* binder Name
inst._@.Mathlib.Algebra.GroupWithZero.Basic.#430946186._hygCtx._hyg.#4 */, (forall [x_7__b3 : (@Zero.{u_1}
M___b1)] /* binder Name inst._@.Mathlib.Algebra.GroupWithZero.Basic.#430946186._hygCtx._hyg.#7 */, (forall
[x_10__b4 : (@NoZeroDivisors.{u_1} M___b1 x_4__b2 x_7__b3)] /* binder Name
inst._@.Mathlib.Algebra.GroupWithZero.Basic.#430946186._hygCtx._hyg.#10 */, (forall {a__b5 : M___b1} /* binder
Name a */, (forall {b__b6 : M___b1} /* binder Name b */, (forall (ha__b7 : (@Ne.{(u_1 + 1)} M___b1 a__b5
(@OfNat.ofNat.{u_1} M___b1 nat_lit(0) (@Zero.toOfNat0.{u_1} M___b1 x_7__b3)))) /* binder Name ha */, (forall
(hb__b8 : (@Ne.{(u_1 + 1)} M___b1 b__b6 (@OfNat.ofNat.{u_1} M___b1 nat_lit(0) (@Zero.toOfNat0.{u_1} M___b1
x_7__b3)))) /* binder Name hb */, (@Eq.{(0 + 1)} Prop (@Eq.{(u_1 + 1)} M___b1 (@HMul.hMul.{u_1, u_1, u_1} M___b1
M___b1 M___b1 (@instHMul.{u_1} M___b1 x_4__b2) a__b5 b__b6) (@OfNat.ofNat.{u_1} M___b1 nat_lit(0)
(@Zero.toOfNat0.{u_1} M___b1 x_7__b3))) @False)))))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 69. Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_5

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_5`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_5").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_5`.
- User Name: `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_5`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_5").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_1 [anonymous -> str("u_1")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_5)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {M___b1 : Sort((u_1 + 1))} /* binder Name M₀ */, (forall [x_4__b2 : (@MonoidWithZero.{u_1} M___b1)] /*
binder Name inst._@.Mathlib.Algebra.GroupWithZero.Basic.#301975504._hygCtx._hyg.#4 */, (forall {a__b3 : M___b1}
/* binder Name a */, (forall [x_11__b4 : (@IsReduced.{u_1} M___b1 (@MulZeroClass.toZero.{u_1} M___b1
(@MulZeroOneClass.toMulZeroClass.{u_1} M___b1 (@MonoidWithZero.toMulZeroOneClass.{u_1} M___b1 x_4__b2)))
(@NPow.toPow.{u_1} M___b1 (@Monoid.toNPow.{u_1} M___b1 (@MonoidWithZero.toMonoid.{u_1} M___b1 x_4__b2))))] /*
binder Name inst._@.Mathlib.Algebra.GroupWithZero.Basic.#301975504._hygCtx._hyg.#11 */, (forall (n__b5 : @Nat)
/* binder Name n */, (forall (h__b6 : (@Ne.{(u_1 + 1)} M___b1 a__b3 (@OfNat.ofNat.{u_1} M___b1 nat_lit(0)
(@Zero.toOfNat0.{u_1} M___b1 (@MulZeroClass.toZero.{u_1} M___b1 (@MulZeroOneClass.toMulZeroClass.{u_1} M___b1
(@MonoidWithZero.toMulZeroOneClass.{u_1} M___b1 x_4__b2))))))) /* binder Name h */, (@Eq.{(0 + 1)} Prop
(@Eq.{(u_1 + 1)} M___b1 (@HPow.hPow.{u_1, 0, u_1} M___b1 @Nat M___b1 (@instHPow.{u_1, 0} M___b1 @Nat
(@NPow.toPow.{u_1} M___b1 (@Monoid.toNPow.{u_1} M___b1 (@MonoidWithZero.toMonoid.{u_1} M___b1 x_4__b2)))) a__b3
n__b5) (@OfNat.ofNat.{u_1} M___b1 nat_lit(0) (@Zero.toOfNat0.{u_1} M___b1 (@MulZeroClass.toZero.{u_1} M___b1
(@MulZeroOneClass.toMulZeroClass.{u_1} M___b1 (@MonoidWithZero.toMulZeroOneClass.{u_1} M___b1 x_4__b2))))))
@False)))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 70. Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_6

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_6`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_6").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_6`.
- User Name: `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_6`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_6").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_3 [anonymous -> str("u_3")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_6)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {G___b1 : Sort((u_3 + 1))} /* binder Name G₀ */, (forall [x_8__b2 : (@GroupWithZero.{u_3} G___b1)] /*
binder Name inst._@.Mathlib.Algebra.GroupWithZero.Units.Basic.#2998152944._hygCtx._hyg.#8 */, (forall {a__b3 :
G___b1} /* binder Name a */, (forall (n__b4 : @Int) /* binder Name n */, (forall (x_0__b5 : (@Ne.{(u_3 + 1)}
G___b1 a__b3 (@OfNat.ofNat.{u_3} G___b1 nat_lit(0) (@Zero.toOfNat0.{u_3} G___b1 (@MulZeroClass.toZero.{u_3}
G___b1 (@MulZeroOneClass.toMulZeroClass.{u_3} G___b1 (@MonoidWithZero.toMulZeroOneClass.{u_3} G___b1
(@GroupWithZero.toMonoidWithZero.{u_3} G___b1 x_8__b2)))))))) /* binder Name a._@._internal._hyg.#0 */, (@Eq.{(0
+ 1)} Prop (@Eq.{(u_3 + 1)} G___b1 (@HPow.hPow.{u_3, 0, u_3} G___b1 @Int G___b1 (@instHPow.{u_3, 0} G___b1 @Int
(@ZPow.toPow.{u_3} G___b1 (@DivInvMonoid.toZPow.{u_3} G___b1 (@GroupWithZero.toDivInvMonoid.{u_3} G___b1
x_8__b2)))) a__b3 n__b4) (@OfNat.ofNat.{u_3} G___b1 nat_lit(0) (@Zero.toOfNat0.{u_3} G___b1
(@MulZeroClass.toZero.{u_3} G___b1 (@MulZeroOneClass.toMulZeroClass.{u_3} G___b1
(@MonoidWithZero.toMulZeroOneClass.{u_3} G___b1 (@GroupWithZero.toMonoidWithZero.{u_3} G___b1 x_8__b2)))))))
@False))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 71. Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_7

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_7`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_7").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_7`.
- User Name: `Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_7`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("spectral_ratio_pow_le") -> str("_simp_1_7").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: 0: u_1 [anonymous -> str("u_1")].
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.spectral_ratio_pow_le._simp_1_7)).
- Complete axiom set (captured order): `propext`.

Full actual type:

```text
(forall {R__b1 : Sort((u_1 + 1))} /* binder Name R */, (forall [x_3__b2 : (@AddMonoidWithOne.{u_1} R__b1)] /*
binder Name inst._@.Mathlib.Algebra.CharZero.Defs.#1325129559._hygCtx._hyg.#3 */, (forall [x_6__b3 :
(@CharZero.{u_1} R__b1 x_3__b2)] /* binder Name
inst._@.Mathlib.Algebra.CharZero.Defs.#1325129559._hygCtx._hyg.#6 */, (forall (n__b4 : @Nat) /* binder Name n
*/, (@Eq.{(0 + 1)} Prop (@Eq.{(u_1 + 1)} R__b1 (@HAdd.hAdd.{u_1, u_1, u_1} R__b1 R__b1 R__b1 (@instHAdd.{u_1}
R__b1 (@AddSemigroup.toAdd.{u_1} R__b1 (@AddMonoid.toAddSemigroup.{u_1} R__b1
(@AddMonoidWithOne.toAddMonoid.{u_1} R__b1 x_3__b2)))) (@Nat.cast.{u_1} R__b1 (@AddMonoidWithOne.toNatCast.{u_1}
R__b1 x_3__b2) n__b4) (@OfNat.ofNat.{u_1} R__b1 nat_lit(1) (@One.toOfNat1.{u_1} R__b1
(@AddMonoidWithOne.toOne.{u_1} R__b1 x_3__b2)))) (@OfNat.ofNat.{u_1} R__b1 nat_lit(0) (@Zero.toOfNat0.{u_1}
R__b1 (@AddZero.toZero.{u_1} R__b1 (@AddZeroClass.toAddZero.{u_1} R__b1 (@AddMonoid.toAddZeroClass.{u_1} R__b1
(@AddMonoidWithOne.toAddMonoid.{u_1} R__b1 x_3__b2))))))) @False)))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 72. Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_geometric_sum_le") -> str("_proof_1_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_geometric_sum_le") -> str("_proof_1_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_1)).
- Complete axiom set (captured order): `propext`, `Quot.sound`.

Full actual type:

```text
(forall ⦃a__b1 : @Nat⦄ /* binder Name a */, (forall ⦃b__b2 : @Nat⦄ /* binder Name b */, (forall (ha___b3 :
(@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) a__b1)) /* binder Name
ha' */, (forall (hb___b4 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat
nat_lit(1))) b__b2)) /* binder Name hb' */, (forall (hab__b5 : (@Eq.{(0 + 1)} @Nat (@HSub.hSub.{0, 0, 0} @Nat
@Nat @Nat (@instHSub.{0} @Nat @instSubNat) a__b1 (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))))
(@HSub.hSub.{0, 0, 0} @Nat @Nat @Nat (@instHSub.{0} @Nat @instSubNat) b__b2 (@OfNat.ofNat.{0} @Nat nat_lit(1)
(@instOfNatNat nat_lit(1)))))) /* binder Name hab */, (forall (x_193__b6 : (@Not meta[0: noImplicitLambda =
bool(true)]((@Eq.{(0 + 1)} @Nat a__b1 b__b2)))) /* binder Name
a._@._internal.#0.Shao.OQ4.RademacherSpectralTail.#2286604730._hygCtx._hyg.#193 */, @False))))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 73. Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_2

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_2`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_geometric_sum_le") -> str("_proof_1_2").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_2`.
- User Name: `Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_2`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_geometric_sum_le") -> str("_proof_1_2").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_geometric_sum_le._proof_1_2)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall (m__b1 : @Nat) /* binder Name m */, (forall (ell__b2 : @Nat) /* binder Name ell */, (forall (he__b3 :
(@And (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1))) ell__b2) (@And
(@LE.le.{0} @Nat @instLENat ell__b2 m__b1) (@Membership.mem.{0, 0} @Nat (@Finset.{0} @Nat)
(@SetLike.instMembership.{0, 0} (@Finset.{0} @Nat) @Nat (@Finset.instSetLike.{0} @Nat))
(@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1) ell__b2)))) /* binder Name he */, (forall (x_275__b4 :
(@Not (@LT.lt.{0} @Nat @instLTNat (@HSub.hSub.{0, 0, 0} @Nat @Nat @Nat (@instHSub.{0} @Nat @instSubNat) ell__b2
(@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat nat_lit(1)))) m__b1))) /* binder Name
a._@._internal.#0.Shao.OQ4.RademacherSpectralTail.#2286604730._hygCtx._hyg.#275 */, @False))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 74. Shao.OQ4.RademacherSpectralTail.tail_membership._proof_1_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_membership._proof_1_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_membership") -> str("_proof_1_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.tail_membership._proof_1_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.tail_membership._proof_1_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("tail_membership") -> str("_proof_1_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.tail_membership._proof_1_1)).
- Complete axiom set (captured order): `propext`, `Classical.choice`, `Quot.sound`.

Full actual type:

```text
(forall {m__b1 : @Nat} /* binder Name m */, (forall {ell__b2 : @Nat} /* binder Name ell */, (forall (he__b3 :
(@And (@Ne.{(0 + 1)} @Nat ell__b2 (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0))))
(@Membership.mem.{0, 0} @Nat (@Finset.{0} @Nat) (@SetLike.instMembership.{0, 0} (@Finset.{0} @Nat) @Nat
(@Finset.instSetLike.{0} @Nat)) (@Shao.OQ4.RademacherSpectralPairing.lowerModes m__b1) ell__b2))) /* binder Name
he */, (forall (x_86__b4 : (@Not (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat nat_lit(1) (@instOfNatNat
nat_lit(1))) ell__b2))) /* binder Name
a._@._internal.#0.Shao.OQ4.RademacherSpectralTail.#2171976295._hygCtx._hyg.#86 */, @False))))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.

## 75. Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes._proof_1_1

Classification: **generated**. Actual kind: **theorem**.

- Raw Name: `_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes._proof_1_1`.
  Name path: anonymous -> str("_private") -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> num(0) -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("zeroMode_vanishes") -> str("_proof_1_1").
  Captured raw display: `_private.Shao.OQ4.RademacherSpectralTail.0.Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes._proof_1_1`.
- User Name: `Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes._proof_1_1`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail") -> str("zeroMode_vanishes") -> str("_proof_1_1").
- Actual owner: `Shao.OQ4.RademacherSpectralTail`.
  Name path: anonymous -> str("Shao") -> str("OQ4") -> str("RademacherSpectralTail").
- Universe parameters in actual order: none.
- private: true.
- unsafe: false.
- partial: false.
- activeInstance: false.
- sourceCurrent: false.
- oldModuleOwner: false.
- rawOrUserOQ4: true.
- getModuleIdxFor? result: some 5682.
- Complete captured metadata: all = sequence(0: Name(_private.Shao.OQ4.RademacherSpectralTail.#0.Shao.OQ4.RademacherSpectralTail.zeroMode_vanishes._proof_1_1)).
- Complete axiom set (captured order): `propext`, `Quot.sound`.

Full actual type:

```text
(forall {n__b1 : @Nat} /* binder Name n */, (forall (hn__b2 : (@LE.le.{0} @Nat @instLENat (@OfNat.ofNat.{0} @Nat
nat_lit(1) (@instOfNatNat nat_lit(1))) n__b1)) /* binder Name hn */, (forall (x_0__b3 : (@Eq.{(0 + 1)} @Nat
n__b1 (@OfNat.ofNat.{0} @Nat nat_lit(0) (@instOfNatNat nat_lit(0))))) /* binder Name a._@._internal._hyg.#0 */,
@False)))
```

Theorem proof value is intentionally not part of the public-interface capture; no theorem body is rendered.
