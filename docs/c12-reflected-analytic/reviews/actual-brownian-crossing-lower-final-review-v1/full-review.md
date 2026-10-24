# Units146 and148 independent complete final review

STATUS: CORRECT

Both exact released modules pass complete source-to-statement, proof, full actual-type, source/object/artifact binding and recursive-axiom review. This fresh gpt-6.1-sol/xhigh reviewer accepted the bounded148 extension before sealing. Derived totals: **12actual theorems =6public source +6generated;0private source/definitions/values**. Usage fields are unavailable/null. No Lean/audit/build was rerun, and no production/server/author-packet mutation occurred. Units145147 are excluded.

Unit146 supplies only the positive Brownian crossing denominator. Unit148 supplies only exact adaptive actual-energy cutoff event identities, reveal stopping observability and nesting. Neither closes a quantitative relative/root theorem. Unit148's immutable descriptive-count erratum is explicitly preserved and reviewed below. A single final release seals both reports.

# Unit146 independent complete final review

STATUS: CORRECT

Reviewer: `/root/actual_brownian_crossing_lower_final_review`, fresh independent context, configured `gpt-6.1-sol / xhigh`. Input, cached input, output and reasoning-subset usage are unavailable (`null`). The author's exact writer/execution release was verified before review. Only this review directory was written.

## Exact target and evidence

- Module: `Shao.C2.ActualBrownianCrossingLower`.
- Source SHA256: `3c6f1424f50c919c392a1cd6730159f084f6fa6342b7c900937838875821ffbb`.
- Complete pre-implementation freeze SHA256: `e7fa7f566b2298700e61c6657dfd7c078d29f746292b88cd8346e23af67af8fe`.
- Output and installed server object SHA256: `6dda95caa508bdd6064286039df296629322ca942be15cac1ec05991249b1ddf`.
- Local/server author receipt SHA256: `f5f7743ce18d3a31add61f71e85eac33f212fd440f5e640a1b77671daf7ab1b2`.
- Author release SHA256: `df94ec12045d7c4d8ed4a9fdc01d2c0084a6e8018007340c5e26b4fad6310b44`.
- Branch/head: `author/c12-actual-iid-v71` / `ec86cff56094dfb7e3ac5f674818cc0cd9c1fd40`.
- Lean `leanprover/lean4:v4.36.0-rc1`; mathlib `807d3836b165983210ee2ecf3cd28f239436949c`; accepted shared-v34 packages. Original gates used CPU14–17, c12-heavy.lock, -M8192, -j4.

The complete source, complete freeze/import context/three heads, every original kernel/audit/command log, all actual types and the empty value export were read. The author receipt remains unchanged with its original review-pending status; this independent report supplies the final review result. The reviewer ran **zero Lean/audit/build commands**, replayed zero successful gates, changed no server files, and copied no object or full log into this workspace.

## Statement fidelity and complete proof review

Let E_x={omegaB | x<B 1 omegaB} and A_x={omegaB | exists t in [0,1], x<=abs(B_t omegaB)}, with the physical NNReal evaluation used in the source. Native Brownian finite-dimensional laws give PB.real E_x=Psi(x). Every omegaB in E_x belongs to A_x by choosing t=1 and using x<B_1<=abs(B_1). Finite-measure monotonicity yields Psi(x)<=PB.real A_x. Since Psi(x)>0 for every finite real x, PB.real A_x>0. If x<=1, antitonicity gives Psi(1)<=Psi(x)<=PB.real A_x.

The arbitrary universe `u_1`, the sole sample-space measurable structure, original `B : NNReal → ΩB → Real`, original `PB : Measure ΩB`, probability instance, native `IsBrownianReal B PB` hypothesis and arbitrary real threshold are present in each complete elaborated type. Only the third theorem adds `hx : x ≤ 1`. There is no hidden process-measurability, complete-measure, joint-measurability, Gaussian-law witness, sample-space regularity or nonnegative-threshold assumption.

Native `IsBrownianReal` extends `IsPreBrownianReal` and contains almost-sure continuity. Native `IsPreBrownianReal.hasLaw_eval 1` has exactly `HasLaw (B 1) (gaussianReal 0 1) PB`. Native `HasLaw.measureReal_eq` uses the law's AEMeasurability and the measurable target predicate. The target predicate here is precisely `Ioi x`, so its real Gaussian measure is definitionally `Shao.standardNormalTail x`.

`BridgeTime` is the real closed unit interval, not an index convention. The literal witness `(1 : BridgeTime)` converts to NNReal one. For each endpoint-event sample, `homega.le.trans (le_abs_self _)` proves the required weak absolute crossing. This pointwise inclusion is valid for negative, zero and positive real thresholds. At `x ≤ 0` the target set is in fact all samples, by the same witness and nonnegativity of absolute value; at zero no one-sided/time-zero convention is involved. No null-set replacement or supremum encoding occurs.

`PB` is finite through the probability instances. Thus `measure_ne_top PB A_x` supplies exactly the right-side finiteness needed by `ENNReal.toReal_mono`; `measure_mono` applies to arbitrary sets. The proof does not pretend that an arbitrary uncountable crossing event is Borel measurable. Measure evaluation is the literal Lean measure evaluation on that set, and no additional measurability premise is required for this monotone lower bound.

## One-for-one coverage

The actual module owner map selects **3 constants, all 3 public source theorems**, with **0 private/generated constants and 0 non-theorem values**. These numbers are derived from the verified owner rows, rather than copied from prose. The source names, exact owner names and printed type names are identical sets. Every actual type was read in full with all universe, subtype, instance and coercion arguments.

### `Shao.C2.ActualBrownianCrossingLower.brownian_weak_absolute_crossing_pos`

Source lines 27–34; actual owner `Shao.C2.ActualBrownianCrossingLower`; kind `theorem`. Complete frozen-head SHA256 `ac030a9851adbf733aee26aa56fb24f94127c365f6189b8ed44795c89fdc69d3`; complete actual-type SHA256 `1451e974d92acc1f6c111a71be4cb532681942274e748e336a7a3d5cda17dcb3`; source proof-body SHA256 `4a93b6147631d1149c23ae5deddebefaeb0d758c73d3d67adb399a541f631b26`.

standardNormalTail_basic.2.2.1 x supplies 0<standardNormalTail x for every real x. trans_le with the just-reviewed lower theorem gives strict positivity of the same literal physical crossing real measure. No nonnegative-threshold assumption, extra instance, law witness or measurability premise is introduced.

Full source-to-statement, frozen-head, complete proof, full actual-type and recursive axiom coverage: PASS. Transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; all are on the project whitelist.

### `Shao.C2.ActualBrownianCrossingLower.brownian_weak_absolute_crossing_lower`

Source lines 11–25; actual owner `Shao.C2.ActualBrownianCrossingLower`; kind `theorem`. Complete frozen-head SHA256 `440f8ddb6d3222128b8d9206a8efa5fe214121c700d2f07ae4b087ef98266f2b`; complete actual-type SHA256 `379dc1a093fd980c847dd3d4a956d1effc08b8edbf9d401abc64f666ef31886e`; source proof-body SHA256 `aed37c8a4ddb7111e64f060cfc95e0482e00dbaefd0ee7ddba25f1e5f0cf334c`.

The endpoint law is HasLaw (B 1) (gaussianReal 0 1) PB, obtained from the same native hB and the same PB. HasLaw.measureReal_eq is applied to the measurable Ioi predicate x<z. Its right side is definitionally Shao.standardNormalTail x. Rewriting by that equality leaves real-measure monotonicity. PB is a probability measure, hence finite, so measure_ne_top applies to the entire target set without a measurability premise; ENNReal.toReal_mono therefore has its required finite right-hand argument. Pointwise inclusion sends omegaB with x<B 1 omegaB to the literal t=1 in BridgeTime. The NNReal made from that time is definitionally 1. The final inequality is x<=B 1 omegaB<=abs(B 1 omegaB). Strict-to-weak conversion uses homega.le, with no sign restriction on x and no exceptional-set or continuity replacement.

Full source-to-statement, frozen-head, complete proof, full actual-type and recursive axiom coverage: PASS. Transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; all are on the project whitelist.

### `Shao.C2.ActualBrownianCrossingLower.brownian_weak_absolute_crossing_small_window_lower`

Source lines 36–43; actual owner `Shao.C2.ActualBrownianCrossingLower`; kind `theorem`. Complete frozen-head SHA256 `f178349a29a7df0cb501c7f266a18e8140db450f35e07c12d87e984378409e8b`; complete actual-type SHA256 `232e7801cd82e5501160f43e8d04b31af99ab492f935848abc44a3c3456a7bb7`; source proof-body SHA256 `6c6c054edabe23509a74d4440cf74f50ca868f519d0cbd62aae792f86f329cfa`.

standardNormalTail_basic.1 is Antitone standardNormalTail. Applied to hx:x<=1 it gives standardNormalTail 1<=standardNormalTail x, in the correct direction. Transitivity with the lower theorem gives the same literal crossing event. The sole additional binder is hx:x<=1; x need not be nonnegative. The imported strict positivity at 1 makes this a fixed positive denominator, although this theorem only exports the stated non-strict bound.

Full source-to-statement, frozen-head, complete proof, full actual-type and recursive axiom coverage: PASS. Transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; all are on the project whitelist.

## Complete source and frozen context

The following complete production source was read. Removing only the three proof bodies reconstructs `frozen.lean.txt` **byte for byte**, retaining all imports, namespace/options, open/scoped declarations, complete heads and final namespace closure. The pre-implementation freeze record explicitly records `implementationStarted=false` at `2026-10-24T20:11:30.117031+00:00`.

```lean
import Shao.C2.BrownianBridgeLaw
import Shao.Probability.GaussianTail

set_option autoImplicit false
noncomputable section
namespace Shao.C2.ActualBrownianCrossingLower
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination
open scoped NNReal

theorem brownian_weak_absolute_crossing_lower
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (x : ℝ) :
    Shao.standardNormalTail x ≤ PB.real {omegaB | ∃ t : BridgeTime,
        x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|} := by
  have hEndpoint : PB.real {omegaB | x < B 1 omegaB} = Shao.standardNormalTail x := by
    exact (hB.toIsPreBrownianReal.hasLaw_eval 1).measureReal_eq measurableSet_Ioi
  rw [← hEndpoint]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro omegaB homega
  refine ⟨(1 : BridgeTime), ?_⟩
  change x ≤ |B 1 omegaB|
  exact homega.le.trans (le_abs_self _)

theorem brownian_weak_absolute_crossing_pos
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (x : ℝ) :
    0 < PB.real {omegaB | ∃ t : BridgeTime,
        x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|} := by
  exact ((Shao.standardNormalTail_basic.2.2.1 x).1).trans_le
    (brownian_weak_absolute_crossing_lower B PB hB x)

theorem brownian_weak_absolute_crossing_small_window_lower
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (x : ℝ) (hx : x ≤ 1) :
    Shao.standardNormalTail 1 ≤ PB.real {omegaB | ∃ t : BridgeTime,
        x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|} := by
  exact (Shao.standardNormalTail_basic.1 hx).trans
    (brownian_weak_absolute_crossing_lower B PB hB x)

end Shao.C2.ActualBrownianCrossingLower
```

## Complete actual types

This is the complete 8039-byte unabridged export read during review. No owner or binder is omitted. The complete non-theorem value export has zero bytes and SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

```text
TARGET_DECL Shao.C2.ActualBrownianCrossingLower.brownian_weak_absolute_crossing_pos KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {ΩB : Type u_1} [inst : MeasurableSpace.{u_1} ΩB] (B : NNReal → ΩB → Real)
  (PB : @MeasureTheory.Measure.{u_1} ΩB inst) [@MeasureTheory.IsProbabilityMeasure.{u_1} ΩB inst PB]
  (hB : @ProbabilityTheory.IsBrownianReal.{u_1} ΩB inst B PB) (x : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@MeasureTheory.Measure.real.{u_1} ΩB inst PB
      (@Set.ofPred.{u_1} ΩB fun (omegaB : ΩB) =>
        @Exists.{1} (@Set.Elem.{0} Real Shao.C2.BridgeDomination.BridgeTime)
          fun (t : @Set.Elem.{0} Real Shao.C2.BridgeDomination.BridgeTime) =>
          @LE.le.{0} Real Real.instLE x
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (B
                (@Subtype.mk.{1} Real
                  (fun (r : Real) =>
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
                  (@Subtype.val.{1} Real
                    (fun (x : Real) =>
                      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                        Shao.C2.BridgeDomination.BridgeTime x)
                    t)
                  (@And.left
                    (@LE.le.{0} Real (@Preorder.toLE.{0} Real Real.instPreorder)
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@Subtype.val.{1} Real
                        (fun (x : Real) =>
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            Shao.C2.BridgeDomination.BridgeTime x)
                        t))
                    (@LE.le.{0} Real (@Preorder.toLE.{0} Real Real.instPreorder)
                      (@Subtype.val.{1} Real
                        (fun (x : Real) =>
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            Shao.C2.BridgeDomination.BridgeTime x)
                        t)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@Subtype.property.{1} Real
                      (fun (x : Real) =>
                        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                          Shao.C2.BridgeDomination.BridgeTime x)
                      t)))
                omegaB))))
TARGET_DECL Shao.C2.ActualBrownianCrossingLower.brownian_weak_absolute_crossing_lower KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {ΩB : Type u_1} [inst : MeasurableSpace.{u_1} ΩB] (B : NNReal → ΩB → Real)
  (PB : @MeasureTheory.Measure.{u_1} ΩB inst) [@MeasureTheory.IsProbabilityMeasure.{u_1} ΩB inst PB]
  (hB : @ProbabilityTheory.IsBrownianReal.{u_1} ΩB inst B PB) (x : Real),
  @LE.le.{0} Real Real.instLE (Shao.standardNormalTail x)
    (@MeasureTheory.Measure.real.{u_1} ΩB inst PB
      (@Set.ofPred.{u_1} ΩB fun (omegaB : ΩB) =>
        @Exists.{1} (@Set.Elem.{0} Real Shao.C2.BridgeDomination.BridgeTime)
          fun (t : @Set.Elem.{0} Real Shao.C2.BridgeDomination.BridgeTime) =>
          @LE.le.{0} Real Real.instLE x
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (B
                (@Subtype.mk.{1} Real
                  (fun (r : Real) =>
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
                  (@Subtype.val.{1} Real
                    (fun (x : Real) =>
                      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                        Shao.C2.BridgeDomination.BridgeTime x)
                    t)
                  (@And.left
                    (@LE.le.{0} Real (@Preorder.toLE.{0} Real Real.instPreorder)
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@Subtype.val.{1} Real
                        (fun (x : Real) =>
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            Shao.C2.BridgeDomination.BridgeTime x)
                        t))
                    (@LE.le.{0} Real (@Preorder.toLE.{0} Real Real.instPreorder)
                      (@Subtype.val.{1} Real
                        (fun (x : Real) =>
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            Shao.C2.BridgeDomination.BridgeTime x)
                        t)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@Subtype.property.{1} Real
                      (fun (x : Real) =>
                        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                          Shao.C2.BridgeDomination.BridgeTime x)
                      t)))
                omegaB))))
TARGET_DECL Shao.C2.ActualBrownianCrossingLower.brownian_weak_absolute_crossing_small_window_lower KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {ΩB : Type u_1} [inst : MeasurableSpace.{u_1} ΩB] (B : NNReal → ΩB → Real)
  (PB : @MeasureTheory.Measure.{u_1} ΩB inst) [@MeasureTheory.IsProbabilityMeasure.{u_1} ΩB inst PB]
  (hB : @ProbabilityTheory.IsBrownianReal.{u_1} ΩB inst B PB) (x : Real)
  (hx : @LE.le.{0} Real Real.instLE x (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (Shao.standardNormalTail (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (@MeasureTheory.Measure.real.{u_1} ΩB inst PB
      (@Set.ofPred.{u_1} ΩB fun (omegaB : ΩB) =>
        @Exists.{1} (@Set.Elem.{0} Real Shao.C2.BridgeDomination.BridgeTime)
          fun (t : @Set.Elem.{0} Real Shao.C2.BridgeDomination.BridgeTime) =>
          @LE.le.{0} Real Real.instLE x
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (B
                (@Subtype.mk.{1} Real
                  (fun (r : Real) =>
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
                  (@Subtype.val.{1} Real
                    (fun (x : Real) =>
                      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                        Shao.C2.BridgeDomination.BridgeTime x)
                    t)
                  (@And.left
                    (@LE.le.{0} Real (@Preorder.toLE.{0} Real Real.instPreorder)
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@Subtype.val.{1} Real
                        (fun (x : Real) =>
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            Shao.C2.BridgeDomination.BridgeTime x)
                        t))
                    (@LE.le.{0} Real (@Preorder.toLE.{0} Real Real.instPreorder)
                      (@Subtype.val.{1} Real
                        (fun (x : Real) =>
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            Shao.C2.BridgeDomination.BridgeTime x)
                        t)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@Subtype.property.{1} Real
                      (fun (x : Real) =>
                        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                          Shao.C2.BridgeDomination.BridgeTime x)
                      t)))
                omegaB))))
```

## Server receipt, audit and export accounting

The original `attempt001/command.txt`, full 165-byte kernel log and full 8264-byte owned-audit log were read. Both exit markers are zero. There is exactly one attempt directory, `attempt001`, and no failed author attempt is present. All 11 receipt-listed server artifacts match their exact recorded hashes and lengths; all seven locally present receipt artifacts match as well. The current worktree source and original attempt snapshot have the same source bytes; the output and installed objects have identical hashes. The local receipt and server receipt match exactly. No local object is stored.

The inspected `OwnedAudit.lean` selects every constant whose actual `env.getModuleIdxFor?` owner is this target module, including any private/generated constants, and invokes recursive `Lean.collectAxioms` on every selection. Its complete selected set consists of the three source theorems above. Each transitive axiom list is the standard whitelist; no `sorryAx` or added axiom is accepted. The production source contains none of `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide`.

Reconstructing exports from the original audit log produces exactly **8039 type bytes + 0 value bytes + 225 residual bytes = 8264 raw bytes**. The residual consists only of the complete mathlib-local-changes warning, the summary `AUDITED_TARGET_CONSTANTS 3 PUBLIC 3 THEOREMS 3 DEFINITIONS 0`, blank lines and `AUDIT_EXIT=0`. Residual SHA256: `47b5b54860a78aeaedf9a39924fcfe4b508208d67c7e93769d56a1d0803a6154`. No declaration, type, proof or definition value remains outside the exports. No ellipsis, unresolved metavariable or truncation marker occurs.

The original warning does not conceal a changed consumed source: all nine native mathlib files whose declarations/definitions were inspected here match their exact pinned Git blobs. `server-observation.json` and `final-source-observation.json` record exact hashes. Tool inspection encountered unavailable server `rg` once and a compact-checkpoint list/dict parsing mismatch once; both were read-only inspections corrected with Python, not Lean/proof failures or gate replays.

## Accepted dependency reuse

No old producer or old complete proof review was rerun. Current local curated sources, current server sources and objects, and accepted integration-v83 source/object pairs match:

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| `Shao.C2.BridgeDomination` | `45b6733a6341fcf002bfa44738074419c118818e88ea8f0f2e07dc66d381e7b9` | `e527ff9d0a16c9585b1769e6286349b6a1a3f520ade44cd6bd28205ca109cf27` |
| `Shao.C2.BrownianBridgeLaw` | `8dd4cb52e900f36c162a5711a5455b31835825d0d224e0d7dd28bcbbc1e0dbdd` | `efebc84af2b2e6918bd9a61ff544ce974b50bb890bd9d4a1cd18d098598cbbd3` |
| `Shao.Probability.GaussianTail` | `f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922` | `37aa119d788f35dd21146e35116823ae689204c91553c3f5f43a386d2234013d` |

The exact accepted root export map is `coordination/root-cache-exports/c12-accepted-v83-interval-budget-20261025.json`. The older qualified complete independent BrownianBridgeLaw review is reused with JSON SHA256 `7eb667d7e53782be5eee0aff695d1965acda9d7db8d8a931c8e74d37760d5461`, verdict CORRECT, fresh gpt-6.1-sol/xhigh author-independent context, source/object hashes identical to those above, and original receipt SHA256 `8a3dcf22678b20c1db294b6f866ce23cdc7542be54564c4f82b69e3c3f9a9444`. Required consumed definitions/types and import context were read; unrelated old proofs retain their established evidence.

## Original source scope and constant-only deviation

Read-only original source: `C:/game/shao/current/c12/main.tex`, SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`, complete lines150–183 and233–258. Lines150–183 fix centered iid finite positive second moment, the weak multiplication events and the standard Brownian maximum/tail notation. Lines233–243 give the compact absolute and joint comparisons under that finite-second-moment scope, without extra distribution regularity. Lines246–258 use `H(x) ≥ H(1) ≥ 2 Ψ(1)>0` on `[0,1]` to divide the compact absolute error.

The author's explicit deviation is valid: this unit supplies the weaker `Ψ(1)>0`. Dividing `C R` by a quantity at least `Ψ(1)` yields `(C/Ψ(1)) R`; this only changes an unspecified universal numerical constant. There is no numerical-sharp-constant or reflection-principle claim. The source's hypotheses, weak-event convention and quantitative order are preserved. This unit supplies a denominator foundation only; it does not establish any compact relative comparison, growing-window assertion or original relative/root theorem. Units145 and147 are excluded from this review. It exports no separate supremum-equivalence theorem.

## Final observation and verdict

Final read-only observation at `2026-10-24T20:20:40.825736+00:00` rechecked 27 current evidence/dependency bindings, both object locations, local packet hashes and unchanged target source. Status: PASS_UNCHANGED. Final observation SHA256 `50b1664b7f008aaa9e7fa53d697824321c468ee9647b2b83a102f71309166e5f`. Deterministic validation: PASS; exact validation SHA256 `dbf0f78d4f1bb821986578e9fe8782c2c6689f171dabfbfc4af0d9523a9bf891`.

No critical mathematical or evidence gap was found in unit146. **CORRECT** applies to precisely its three frozen declarations and proofs. This is a classical endpoint/monotonicity helper, with no novelty claim. Original C12/OQ56 roots remain OPEN; OQ3 remains PAUSED_BY_USER with retained evidence; existing OQ4 limited acceptance is unchanged. p54 repairs and external attribution are untouched.

The full machine-readable one-for-one coverage, full actual types, frozen heads, proof/source hashes, all receipt artifact hashes and boundaries are in `full-review.json`. Reviewer writer/execution release and sealed artifact hashes are written last in `writer-release.json`; nothing in this review directory is edited after that seal.


---

# Unit148 independent complete final review

STATUS: CORRECT

This is the bounded scope extension accepted before the common review seal. The same fresh author-independent reviewer `/root/actual_brownian_crossing_lower_final_review`, configured gpt-6.1-sol/xhigh, reviews this released source. All usage fields are unavailable/null. Units145 and147 remain excluded.

## Exact source and interface

Source `aa83d298cd4b6249168fb66cb8d9b8e3e7b74aa8c07c082a0f26cdb7200dfb95`; complete pre-implementation freeze `d10df464706229d966d0b79d86f234a6ca7efed938740c4c6a0c22d8895f4a29`; output/installed object `766f1be06611d45381bc4169ea52fdb448d5620d4edf4b41ef69ade3efbd68e7`; unchanged local/server receipt `9f589ea5eaba88b8705445cac711b9b1606713ba27cb20dafbf3df5d04f796a5`; author release `836bdc1a9af400650c638fe69c799222871a8676db78fc9070938d022706201d`.

All source/import context/three frozen heads, all three proofs, all nine complete actual types, all six generated obligations, empty value export, complete original kernel/audit logs and commands were read. Removing only proof bodies reconstructs the full frozen file byte for byte. Source is UTF-8 without BOM, LF, CR=0. Forbidden production tokens are absent. No Lean/audit/build command, server mutation, producer rebuild or successful-gate replay was performed by the reviewer.

The actual owned map derives **9 theorems = 3 public source + 6 generated; 0 private source and 0 definitions/values**. All full types retain every binder, instance, natural subtraction, universe and exact native order operator. Public statements have no probability/filter assumptions; only the third adds h0≤H. Generated generic order obligations retain their universal alpha/LinearOrder/universe binders.

## Mathematical proof and boundaries

Write T_r for the actual remaining energy of the same labeled path/permutation and kappa_h for its strict first passage below h. The accepted producer, for h>0 and r≤n, gives kappa_h≤r iff T_r<h, kappa_h≤n, and exact reveal-prefix observability. Negation gives r<kappa_h iff h≤T_r. The minimum identities then give r<tau iff r<n-m and H≤T_r, and tau≤r<kappa_h0 iff h0≤T_r and (T_r<H or n-r≤m). The arithmetic identity n-m≤r iff n-r≤m is exact for natural truncated subtraction: both are equivalent to n≤m+r. Thus no short-suffix alternative is omitted.

The min cutoff is bounded by kappa_H≤n. Its event tau≤r is the disjunction kappa_H≤r OR n-m≤r; producer prefix observability and the identical deterministic branch preserve that iff. At the bounded rank kappa_h0, T is strictly below h0≤H, hence kappa_H≤kappa_h0 and therefore tau≤kappa_h0.

The full cases n=0, m=0, m≥n and r=n are covered. For n=0 both positive-threshold cutoffs are0; for m≥n adaptive tau=0 and the short-suffix condition is automatically true at r≤n. At r=n, T_n=0 and the h0 lower-energy condition is false. At energy exactly H or h0 the before-cutoff comparison remains closed, matching strict first passage. The second event identity allows h0>H and remains a Boolean identity; ordering is assumed only where nesting needs it. There is no replacement of actual energy by a variance, no new independent population and no natural iid-filtration stopping-time claim.

Native min/not/conjunction/disjunction interfaces were read with their contexts, including the generated dual `lt_min_iff`. Pinned Lean's omega frontend constructs and assigns a proof expression and makes an auxiliary theorem; that accounts for `_proof_1_3`. The full actual auxiliary type is precisely the negated Nat-subtraction iff implying False. All nine transitive audits exclude `sorryAx`, so the optional debug-admit branch in Lean's general frontend has not supplied this result.

## One-for-one source, generated proof and axiom coverage

### `Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff._simp_1_1`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, generated auxiliary. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff` lines20–33; associated frozen-head SHA256 `101fc8270f1eb4b03df0baaabe62239c959813413414d9b84d9348a4e73647a6`; actual full-type SHA256 `f3c89d8cb630d3639df270f4a189b7789698f5e60a53ef0326cb5a8e5ee48a4d`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

Universal LinearOrder alpha, universe u_1, Eq Prop (not(a<=b)) (b<a), associated with the h0 cutoff negation. It is the standard not_le proposition equality and has only propext.

Axioms: `propext`; whitelist PASS.

### `Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, public source. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff` lines20–33; associated frozen-head SHA256 `101fc8270f1eb4b03df0baaabe62239c959813413414d9b84d9348a4e73647a6`; actual full-type SHA256 `20419467da3778beb03857f774f7107e0f0aebe00d14d1631cafd5051c3174d0`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

The same qualified producer gives cutoffH<=r iff remainingEnergy<H and, by negation at positive h0, r<cutoffh0 iff h0<=remainingEnergy. min_le_iff keeps both alternatives cutoffH<=r OR n-m<=r. The exact Nat subtraction equivalence n-m<=r iff n-r<=m is proved by omega; both sides are equivalent to n<=m+r, including saturated cases. After these rewrites, and_comm yields h0<=energy AND (energy<H OR n-r<=m). Both omitted-interval branches are present. No h0<=H assumption is needed for this Boolean identity, and none is hidden in the full actual type.

Axioms: `propext`, `Classical.choice`, `Quot.sound`; whitelist PASS.

### `Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, public source. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le` lines35–56; associated frozen-head SHA256 `f1d8eec4c114a9e8df918c4227f60a64623c02f6515476dd028d1f18ce32dd09`; actual full-type SHA256 `b2ccd892ac5fef0dcad4d49f7d1094e27cdeb02f1c7dddd0b7e5745dc363dd5b`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

Unfolded IsRevealStoppingRank consists exactly of cutoff<=n for every seed and invariance of cutoff<=r under identical first-r labels. min(cutoffH,n-m)<=cutoffH<=n establishes the bound. min_le_iff rewrites the observation event to cutoffH<=r OR n-m<=r; producer prefix observability and or_congr with the identical deterministic branch establish the iff. For nesting, cutoffh0<=n permits applying the producer at that exact rank. Reflexivity yields energy(cutoffh0)<h0, and hh0H:h0<=H makes it <H. The H-cutoff equivalence then gives cutoffH<=cutoffh0. Transitivity with min_le_left proves the claimed adaptive bound. This is conditional reveal-prefix stopping rank, not an iid natural-filtration stopping time.

Axioms: `propext`, `Classical.choice`, `Quot.sound`; whitelist PASS.

### `Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff._simp_1_2`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, generated auxiliary. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff` lines8–18; associated frozen-head SHA256 `04c407bdb2ec2fc91ce54a0cfac37b50bf07cf98c70165c3c5a9c8910be079ee`; actual full-type SHA256 `01dc143859ab30d1fe3defea6510802fce077d47a11a5027f56e3ff3a4ba2597`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

Universal LinearOrder alpha, universe u_1, Eq Prop (not(a<b)) (b<=a). This is the proposition equality produced from not_lt via propext, used to negate the real strict energy crossing.

Axioms: `propext`; whitelist PASS.

### `Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, public source. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff` lines8–18; associated frozen-head SHA256 `04c407bdb2ec2fc91ce54a0cfac37b50bf07cf98c70165c3c5a9c8910be079ee`; actual full-type SHA256 `563656e8cf423cd7b77bf13ed8ba72599585c2ef777a412be95781bc7cb94938`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

energy_cutoff_data at the same a,H,hH,sigma,r,hr yields cutoffH<=r iff actual remainingEnergy<H. not_congr negates both sides; linear-order not_le/not_lt give r<cutoffH iff H<=remainingEnergy. lt_min_iff rewrites r<min(cutoffH,n-m) into the conjunction of both strict rank bounds, and and_comm puts the deterministic rank condition first. All thresholds use the same actual population and permutation. No assumption m<=n or H depending on a variance surrogate is added.

Axioms: `propext`, `Classical.choice`, `Quot.sound`; whitelist PASS.

### `Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff._simp_1_2`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, generated auxiliary. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff` lines20–33; associated frozen-head SHA256 `101fc8270f1eb4b03df0baaabe62239c959813413414d9b84d9348a4e73647a6`; actual full-type SHA256 `01dc143859ab30d1fe3defea6510802fce077d47a11a5027f56e3ff3a4ba2597`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

Universal LinearOrder alpha, universe u_1, Eq Prop (not(a<b)) (b<=a), associated with the h0 strict-energy negation. It is the standard not_lt proposition equality and has only propext.

Axioms: `propext`; whitelist PASS.

### `Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff._simp_1_1`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, generated auxiliary. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff` lines8–18; associated frozen-head SHA256 `04c407bdb2ec2fc91ce54a0cfac37b50bf07cf98c70165c3c5a9c8910be079ee`; actual full-type SHA256 `f3c89d8cb630d3639df270f4a189b7789698f5e60a53ef0326cb5a8e5ee48a4d`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

Universal LinearOrder alpha, universe u_1, Eq Prop (not(a<=b)) (b<a). This is the proposition equality produced from not_le via propext, used to negate the Nat cutoff-order condition. No energy/cutoff premise is manufactured.

Axioms: `propext`; whitelist PASS.

### `Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le._simp_1_1`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, generated auxiliary. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le` lines35–56; associated frozen-head SHA256 `f1d8eec4c114a9e8df918c4227f60a64623c02f6515476dd028d1f18ce32dd09`; actual full-type SHA256 `130f2865224c3d33f69679d2bc9a4f1835ec8406f8876863b049a9a240cdc676`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

Universal LinearOrder alpha, universe u_1, Eq Prop (min a b<=c) (a<=c OR b<=c). This is min_le_iff converted to a proposition equality by propext; it underlies reveal-prefix observability of the min cutoff.

Axioms: `propext`; whitelist PASS.

### `Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff._proof_1_3`

Actual owner `Shao.C2.AdaptiveRevealCutoff`, theorem, generated auxiliary. Associated complete source proof `Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff` lines20–33; associated frozen-head SHA256 `101fc8270f1eb4b03df0baaabe62239c959813413414d9b84d9348a4e73647a6`; actual full-type SHA256 `4a9bf74d9d146aca35b1df8dd2136ad083f87f16cd95b86506df290d62f80276`. Full source/frozen-head/actual-type/associated proof/transitive-axiom coverage: PASS.

Complete generated arithmetic proof type: forall {n:Nat} (m r:Nat) (hr:r<=n), NOT((n-m<=r) IFF(n-r<=m)) -> False. This is the omega auxiliary theorem corresponding exactly to the source hNat. Each side of the iff is equivalent to n<=m+r using natural truncated subtraction and addition commutativity; it remains valid for m>=n and r=n. The source omega frontend builds and assigns a proof expression, with this auxiliary theorem kernel-checked and recursively audited. The actual type and all standard axioms were reviewed; no unsafe/native decision or sorry axiom is introduced.

Axioms: `propext`, `Classical.choice`, `Quot.sound`; whitelist PASS.

## Complete source

```lean
import Shao.Probability.SourcePermutationReveal

set_option autoImplicit false
noncomputable section
namespace Shao.C2.AdaptiveRevealCutoff
open Shao.Probability.SourcePermutationReveal

theorem before_adaptive_cutoff_iff
    {n : ℕ} (a : Shao.Path n) (H : ℝ) (hH : 0 < H)
    (m r : ℕ) (hr : r ≤ n) (sigma : LabelPerm n) :
    r < min (energyCutoff a H sigma) (n - m) ↔
      r < n - m ∧ H ≤ remainingEnergy a r sigma := by
  have hc := (energy_cutoff_data a H hH).2.1 sigma r hr
  rw [lt_min_iff]
  have he : r < energyCutoff a H sigma ↔ H ≤ remainingEnergy a r sigma := by
    simpa only [not_le, not_lt] using not_congr hc
  rw [he]
  exact and_comm

theorem omitted_adaptive_cutoff_iff
    {n : ℕ} (a : Shao.Path n) (h0 H : ℝ) (hh0 : 0 < h0) (hH : 0 < H)
    (m r : ℕ) (hr : r ≤ n) (sigma : LabelPerm n) :
    (min (energyCutoff a H sigma) (n - m) ≤ r ∧ r < energyCutoff a h0 sigma) ↔
      h0 ≤ remainingEnergy a r sigma ∧
        (remainingEnergy a r sigma < H ∨ n - r ≤ m) := by
  have hcH := (energy_cutoff_data a H hH).2.1 sigma r hr
  have hc0 := (energy_cutoff_data a h0 hh0).2.1 sigma r hr
  have he0 : r < energyCutoff a h0 sigma ↔ h0 ≤ remainingEnergy a r sigma := by
    simpa only [not_le, not_lt] using not_congr hc0
  rw [min_le_iff, hcH, he0]
  have hNat : n - m ≤ r ↔ n - r ≤ m := by omega
  rw [hNat]
  exact and_comm

theorem adaptive_cutoff_stopping_and_le
    {n : ℕ} (a : Shao.Path n) (h0 H : ℝ) (hh0 : 0 < h0) (hH : 0 < H)
    (hh0H : h0 ≤ H) (m : ℕ) :
    IsRevealStoppingRank (fun sigma => min (energyCutoff a H sigma) (n - m)) ∧
      ∀ sigma : LabelPerm n,
        min (energyCutoff a H sigma) (n - m) ≤ energyCutoff a h0 sigma := by
  have hDataH := energy_cutoff_data a H hH
  have hData0 := energy_cutoff_data a h0 hh0
  constructor
  · constructor
    · intro sigma
      exact (min_le_left _ _).trans (hDataH.1.1 sigma)
    · intro r sigma tau hprefix
      simp only [min_le_iff]
      exact or_congr (hDataH.1.2 r sigma tau hprefix) Iff.rfl
  · intro sigma
    have hAt0 : remainingEnergy a (energyCutoff a h0 sigma) sigma < h0 :=
      ((hData0.2.1 sigma (energyCutoff a h0 sigma) (hData0.1.1 sigma))).mp le_rfl
    have hLe : energyCutoff a H sigma ≤ energyCutoff a h0 sigma :=
      ((hDataH.2.1 sigma (energyCutoff a h0 sigma) (hData0.1.1 sigma))).mpr
        (hAt0.trans_le hh0H)
    exact (min_le_left _ _).trans hLe

end Shao.C2.AdaptiveRevealCutoff
```

## Complete actual types

The complete export is6365bytes, and the complete value export is empty (SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).

```text
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff._simp_1_1 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] {a b : α},
  @Eq.{1} Prop
    (Not
      (@LE.le.{u_1} α
        (@Preorder.toLE.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) a b))
    (@LT.lt.{u_1} α
      (@Preorder.toLT.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) b a)
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {n : Nat} (a : Shao.Path n) (h0 H : Real)
  (hh0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h0)
  (hH : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) H)
  (m r : Nat) (hr : @LE.le.{0} Nat instLENat r n) (sigma : Shao.Probability.SourcePermutationReveal.LabelPerm n),
  Iff
    (And
      (@LE.le.{0} Nat instLENat
        (@Min.min.{0} Nat instMinNat (@Shao.Probability.SourcePermutationReveal.energyCutoff n a H sigma)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n m))
        r)
      (@LT.lt.{0} Nat instLTNat r (@Shao.Probability.SourcePermutationReveal.energyCutoff n a h0 sigma)))
    (And (@LE.le.{0} Real Real.instLE h0 (@Shao.Probability.SourcePermutationReveal.remainingEnergy n a r sigma))
      (Or (@LT.lt.{0} Real Real.instLT (@Shao.Probability.SourcePermutationReveal.remainingEnergy n a r sigma) H)
        (@LE.le.{0} Nat instLENat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n r) m)))
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {n : Nat} (a : Shao.Path n) (h0 H : Real)
  (hh0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h0)
  (hH : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) H)
  (hh0H : @LE.le.{0} Real Real.instLE h0 H) (m : Nat),
  And
    (@Shao.Probability.SourcePermutationReveal.IsRevealStoppingRank n
      fun (sigma : Shao.Probability.SourcePermutationReveal.LabelPerm n) =>
      @Min.min.{0} Nat instMinNat (@Shao.Probability.SourcePermutationReveal.energyCutoff n a H sigma)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n m))
    (∀ (sigma : Shao.Probability.SourcePermutationReveal.LabelPerm n),
      @LE.le.{0} Nat instLENat
        (@Min.min.{0} Nat instMinNat (@Shao.Probability.SourcePermutationReveal.energyCutoff n a H sigma)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n m))
        (@Shao.Probability.SourcePermutationReveal.energyCutoff n a h0 sigma))
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff._simp_1_2 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] {a b : α},
  @Eq.{1} Prop
    (Not
      (@LT.lt.{u_1} α
        (@Preorder.toLT.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) a b))
    (@LE.le.{u_1} α
      (@Preorder.toLE.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) b a)
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {n : Nat} (a : Shao.Path n) (H : Real)
  (hH : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) H)
  (m r : Nat) (hr : @LE.le.{0} Nat instLENat r n) (sigma : Shao.Probability.SourcePermutationReveal.LabelPerm n),
  Iff
    (@LT.lt.{0} Nat instLTNat r
      (@Min.min.{0} Nat instMinNat (@Shao.Probability.SourcePermutationReveal.energyCutoff n a H sigma)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n m)))
    (And (@LT.lt.{0} Nat instLTNat r (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n m))
      (@LE.le.{0} Real Real.instLE H (@Shao.Probability.SourcePermutationReveal.remainingEnergy n a r sigma)))
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff._simp_1_2 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] {a b : α},
  @Eq.{1} Prop
    (Not
      (@LT.lt.{u_1} α
        (@Preorder.toLT.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) a b))
    (@LE.le.{u_1} α
      (@Preorder.toLE.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) b a)
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.before_adaptive_cutoff_iff._simp_1_1 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] {a b : α},
  @Eq.{1} Prop
    (Not
      (@LE.le.{u_1} α
        (@Preorder.toLE.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) a b))
    (@LT.lt.{u_1} α
      (@Preorder.toLT.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) b a)
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.adaptive_cutoff_stopping_and_le._simp_1_1 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] {a b c : α},
  @Eq.{1} Prop
    (@LE.le.{u_1} α
      (@Preorder.toLE.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst)))
      (@Min.min.{u_1} α (@LinearOrder.toMin.{u_1} α inst) a b) c)
    (Or
      (@LE.le.{u_1} α
        (@Preorder.toLE.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) a c)
      (@LE.le.{u_1} α
        (@Preorder.toLE.{u_1} α (@PartialOrder.toPreorder.{u_1} α (@LinearOrder.toPartialOrder.{u_1} α inst))) b c))
TARGET_DECL Shao.C2.AdaptiveRevealCutoff.omitted_adaptive_cutoff_iff._proof_1_3 KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {n : Nat} (m r : Nat) (hr : @LE.le.{0} Nat instLENat r n),
  Not
      (Iff (@LE.le.{0} Nat instLENat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n m) r)
        (@LE.le.{0} Nat instLENat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n r) m)) →
    False
```

## Qualified producer, original source and byte provenance

`SourcePermutationReveal` source `eb8ca14665fddaa34b063f3d53a42333db4dcf813c635e4978751b5251287b5a` and object `83903b0cd75d5cdf839393b729c46ee5a3b5df1e617bbfa95cc65fe48372139d` match the current installed producer object, accepted integration-v83 source/object pair, original attempt012 object, curated read-only source and qualified review. Its original export `33c63f7abc2e3007c36c09739e1ddc7ff5818834adec325d8ecea099556d7db1` is unchanged. The five consumed full type/value blocks for LabelPerm, remainingEnergy, energyCutoff, IsRevealStoppingRank and energy_cutoff_data were read from that exact original export and match the old qualified type/value hashes. Source imports/context and the actual Path, squared energy, prefix and reorder definitions were read. The previous complete independent review is CORRECT, fresh gpt-6.1-sol/xhigh, SHA256 `be7d72a5783495605cfcba4fba35c61ec36b2b666333c6863bceff96a613f08b`, with root qualification `76628ffee23e7805e4f5dfc7677612783dc051c931f235b28322a2a59058343f`. Old proofs and producer checks were reused, not repeated.

The current worktree has no source file for this Probability producer. It imports the exact accepted `.olean` in place; the accepted original source remains at integration-bearing-v83 and in the curated library. This absence is explicitly recorded, not mistaken for a source mismatch. The type/value/object bindings close the dependency evidence chain.

Read-only original `C:/game/shao/current/c12/supplement.tex` SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`: complete target lines4978–4999, adjoining4958–5000, setup4687–4707, and5010–5019 were read. The source defines actual T=Q-Q_r, h0=4 beta², kappa_H as strict T<H, tau as the min cutoff and both exact events. It explicitly conditions on the full labeled sample and reveals a uniform permutation. The helper generalizes deterministic natural m and positive thresholds without deriving the source's residual parameter regime. No H/m estimates, quantitative tail/terminal integral, compensation expectation identity or original root theorem is claimed.

## Immutable descriptive-count erratum

The **final receipt and actual owned/axiom map correctly report9**. Its receipt-bound `source-and-proof.md` retains cloned prose saying3owners/0generated. The attempted corrected-note upload used a rejected relative local path; the original bound note, source, object, freeze, receipt and release were preserved. Separate `receipt-scope-erratum.json` SHA256 `29fb76784c6234d8276bb08f4c57c5d95ffbd72bd69805d755384381bc52dace` binds the original note `6e13eb6bee179f21e5af3170347d3fe879073f783f7060f1e7090a70ee7665c2` and corrected note `ea6cb4a2694786c58bef017407ad8e42174b7455345ab8cf3880e5e9252f4eae`. Independent comparison confirms the correction changes only the descriptive count sentence, to3public+6generated=9actual.

`receipt-construction-note.json` SHA256 `f0cae0e3928f3d81c0114e8e81eede4c7fd64d25bf30967ca8268424b648ff8d` records an initial cloned finish-helper assertion expecting3owners; it was corrected to the actual9owner map before final receipt/release construction. This was a metadata-helper assertion, not a kernel/audit failure. The original kernel and all-owned audit remain attempt001 PASS, with no successful replay. These are noncritical metadata issues, explicitly preserved and resolved by separate bound errata; the mathematical proofs and exhaustive coverage are unaffected.

## Server audit reconstruction and final observation

All11receipt-listed remote artifacts and7locally present receipt artifacts match exact recorded hashes and lengths. Both output/installed objects and current source/attempt snapshot match; receipt local/server bytes match. The complete6590byte audit log reconstructs as6365type bytes +0value bytes +225residual bytes. Residual SHA256 `0c0a03ead67a4ab75adae652678ed83e7545529fe5864906b6ce6dc1179b560e`; it contains only the original mathlib-local-changes warning, exact nine-owner summary, blank lines and `AUDIT_EXIT=0`. No declaration, type, value, truncation marker or unresolved metavariable is left unexplained. The selected set uses actual module ownership and recursive collectAxioms for every constant, including all6generated ones.

Same branch/head as146: `author/c12-actual-iid-v71` / `ec86cff56094dfb7e3ac5f674818cc0cd9c1fd40`. Original gates: Lean `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, CPU14–17/c12-heavy.lock/-M8192/-j4. The inspected mathlib order source matches its pinned Git blob; pinned Lean core source hashes are recorded. Final combined read-only observation `2026-10-24T20:25:36.453810+00:00` confirms both modules and all accepted dependencies/native bindings unchanged. Deterministic validation PASS: `d1f825cf116babb6b8fe81ce4ba30b8ccb815aa0da880e16e7f842c4f86452c4`.

No critical mathematical/evidence gap was found. **CORRECT** is restricted to these three frozen deterministic statements and all their six generated obligations. No novelty or quantitative/root closure claim is made; C12/OQ56 remain OPEN, OQ3 remains PAUSED_BY_USER, existing OQ4 limited acceptance and p54/external attribution remain unchanged. The single final writer/execution release is the common `writer-release.json`.
