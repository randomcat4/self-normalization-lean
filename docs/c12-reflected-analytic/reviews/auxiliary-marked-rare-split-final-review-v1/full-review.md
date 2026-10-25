# Unit 171 independent complete final review

STATUS: CORRECT

No critical gap found in the frozen declaration, its full production proof, either actual-owned complete type, the generated proof obligation, consumed interfaces, source translation or transitive-axiom evidence. Parent qualification is still required; this report is the independent review and does not merge or publish anything.

Reviewer: fresh independent context /root/auxiliary_marked_rare_split_final_review, explicitly configured gpt-6.1-sol / xhigh. I am not the source author. Actual backend model/effort and usage telemetry are unavailable, recorded as null with input/cachedInput/output/reasoningSubset separated. I wrote only this review folder. No Lean, axiom command, accepted gate replay, source/server mutation, extra agent, PR or merge was performed.

## Exact source and derived scope

Source SHA256 `1f3267e1fe36fd8c5dac721a0a5be504d94911ebbd7b0c89d7ae411493c4ddae`; object `5aa7d44ecea5fd056a4f9c16f99dad295848742bc74cd065c90832b09bf1a7df`; author receipt `75f97ab946ee3287f856876ec60a07768c4d4bae837441df2c86628b77f09372`; frozen declaration `eaba40d08f10505d1230a5049189c0395ec5f328adad25aeca9994c68ab15c95`. The entire imports/options/context/head reconstruction is byte-exact. The source is UTF-8 without BOM, LF only, and contains no sorry/admit/new axiom/unsafe/native_decide.

Derived directly from the full actual owner map and source declarations: {"modules": 1, "actualOwnedConstants": 2, "actualTheorems": 2, "publicSourceTheorems": 1, "privateSourceTheorems": 0, "generatedTheorems": 1, "globalNonTheoremValues": 0, "completeActualTypeBytes": 10206, "completeDefinitionValueBytes": 0}. The empty non-theorem-value export is genuinely 0 bytes. Both complete actual types were read unelided in full, with every nonrepeated binder, instance, local let and target. No dictionary compression or structural-summary substitution was used.

## Full frozen imports, context and declaration

```lean
import Shao.C2.AuxiliaryMarkedDeletion
import Shao.OQ4.KilledPathLaw

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryMarkedRareSplit
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_marked_rare_polynomial_split
    {n : ℕ} (w : Shao.Path n) (z x s : ℝ) (p : ℕ) (hx : 1 ≤ x) :
    let B : Set (Shao.Path (n + 1)) := {v |
      ((3 / 2) * x) * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v (n + 1)|}
    let A : Set (Shao.Path n) := {u | 0 < Shao.energy u ∧
      Real.sqrt ((9 / 4) * x ^ 2 - 1) * Real.sqrt (Shao.energy u) ≤
        |Shao.prefixSum u n|}
    let F : Shao.Path (n + 1) → ℝ := fun v =>
      |v 0| ^ 3 * |Shao.prefixSum v (n + 1)| ^ p * Real.exp (-s * Shao.energy v)
    B.indicator F (Fin.cons z w) ≤
      (2 : ℝ) ^ p * (|z| ^ (3 + p) + |z| ^ 3 * |Shao.prefixSum w n| ^ p) *
        Real.exp (-s * z ^ 2) *
        A.indicator (fun u => Real.exp (-s * Shao.energy u)) w := by

end Shao.C2.AuxiliaryMarkedRareSplit
```

## Full reviewed production proof

```lean
import Shao.C2.AuxiliaryMarkedDeletion
import Shao.OQ4.KilledPathLaw

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryMarkedRareSplit
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_marked_rare_polynomial_split
    {n : ℕ} (w : Shao.Path n) (z x s : ℝ) (p : ℕ) (hx : 1 ≤ x) :
    let B : Set (Shao.Path (n + 1)) := {v |
      ((3 / 2) * x) * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v (n + 1)|}
    let A : Set (Shao.Path n) := {u | 0 < Shao.energy u ∧
      Real.sqrt ((9 / 4) * x ^ 2 - 1) * Real.sqrt (Shao.energy u) ≤
        |Shao.prefixSum u n|}
    let F : Shao.Path (n + 1) → ℝ := fun v =>
      |v 0| ^ 3 * |Shao.prefixSum v (n + 1)| ^ p * Real.exp (-s * Shao.energy v)
    B.indicator F (Fin.cons z w) ≤
      (2 : ℝ) ^ p * (|z| ^ (3 + p) + |z| ^ 3 * |Shao.prefixSum w n| ^ p) *
        Real.exp (-s * z ^ 2) *
        A.indicator (fun u => Real.exp (-s * Shao.energy u)) w := by
  classical
  intro B A F
  let d : ℝ := Shao.prefixSum w n
  let M : ℝ := max |z| |d|
  have hMaxPow : M ^ p ≤ |z| ^ p + |d| ^ p := by
    rcases le_total |z| |d| with h | h
    · dsimp [M]
      rw [max_eq_right h]
      linarith [pow_nonneg (abs_nonneg z) p]
    · dsimp [M]
      rw [max_eq_left h]
      linarith [pow_nonneg (abs_nonneg d) p]
  have hTriangle : |z + d| ≤ 2 * M := (abs_add_le z d).trans (by
    dsimp [M]
    linarith [le_max_left |z| |d|, le_max_right |z| |d|])
  have hPolynomial : |z + d| ^ p ≤ (2 : ℝ) ^ p * (|z| ^ p + |d| ^ p) := by
    have hPower := pow_le_pow_left₀ (abs_nonneg (z + d)) hTriangle p
    rw [mul_pow] at hPower
    exact hPower.trans (mul_le_mul_of_nonneg_left hMaxPow (pow_nonneg (by norm_num) p))
  have hMarkedPolynomial : |z| ^ 3 * |z + d| ^ p ≤
      (2 : ℝ) ^ p * (|z| ^ (3 + p) + |z| ^ 3 * |d| ^ p) := by
    calc
      _ ≤ |z| ^ 3 * ((2 : ℝ) ^ p * (|z| ^ p + |d| ^ p)) :=
        mul_le_mul_of_nonneg_left hPolynomial (pow_nonneg (abs_nonneg z) 3)
      _ = _ := by rw [pow_add]; ring
  have hConsEnergy : Shao.energy (Fin.cons z w) = z ^ 2 + Shao.energy w := by
    simp only [Shao.energy, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have hRemainingWeight : 0 ≤ A.indicator (fun u => Real.exp (-s * Shao.energy u)) w := by
    by_cases ha : w ∈ A
    · rw [Set.indicator_of_mem ha]
      exact (Real.exp_pos _).le
    · simp only [Set.indicator_of_notMem ha, le_refl]
  by_cases hb : Fin.cons z w ∈ B
  · by_cases hE0 : Shao.energy (Fin.cons z w) = 0
    · have hz : z = 0 := by
        simpa only [Fin.cons_zero] using
          (Shao.energy_eq_zero_iff (Fin.cons z w)).mp hE0 0
      rw [Set.indicator_of_mem hb]
      simp [F, hz]
    · have hPositive : 0 < Shao.energy (Fin.cons z w) :=
        lt_of_le_of_ne (Shao.energy_nonneg _) (Ne.symm hE0)
      have hCross := hb
      change (3 / 2 : ℝ) * x * Real.sqrt (Shao.energy (Fin.cons z w)) ≤
        |Shao.prefixSum (Fin.cons z w) (n + 1)| at hCross
      rw [hConsEnergy, Shao.OQ4.prefixSum_cons] at hCross
      have ha : w ∈ A :=
        Shao.C2.AuxiliaryMarkedDeletion.auxiliary_marked_terminal_deletion w z x hx
          (by simpa only [hConsEnergy] using hPositive) hCross
      rw [Set.indicator_of_mem hb]
      change |z| ^ 3 * |Shao.prefixSum (Fin.cons z w) (n + 1)| ^ p *
        Real.exp (-s * Shao.energy (Fin.cons z w)) ≤ _
      rw [Shao.OQ4.prefixSum_cons, hConsEnergy, mul_add, Real.exp_add,
        Set.indicator_of_mem ha]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hMarkedPolynomial
        (mul_nonneg (Real.exp_pos (-s * z ^ 2)).le
          (Real.exp_pos (-s * Shao.energy w)).le)
  · rw [Set.indicator_of_notMem hb]
    exact mul_nonneg (by positivity) hRemainingWeight

end Shao.C2.AuxiliaryMarkedRareSplit
```

## Complete mathematical and semantic review

The complete statement quantifies implicit n : Nat, the actual path w : Fin n → Real, z/x/s : Real, p : Nat and the sole hypothesis hx : 1 ≤ x. There is no law, independence, integrability, moment, event implication or positive-energy premise. The local statement lets B, A, F are fully expanded in the actual type: B is the full weak 3x/2 endpoint event on Path(n+1), including zero energy; A uses actual remaining positive energy and sqrt((9/4)x²−1); F is one first-coordinate cubic absolute mark, the natural p-power of the actual complete sum, and exp((-s)*actual energy). Fin.cons has head z and tail w. All Nat additions/exponents and Real fractions in the actual elaborated type agree with the frozen declaration. Its right side has exactly 2^p, |z|^(3+p)+|z|³|prefixSum w n|^p, exp((-s)*z²), and the actual A-indicated remaining exponential. The division constants are in Real, the exponents are Nat, and −s*E means (-s)*E. There are no hidden binders, typeclass side conditions, substituted statistics or elided local let values.

Lines 25–34 set d to the actual remaining full sum and M=max(|z|,|d|). Each le_total branch rewrites M to the winning absolute value, so M^p≤|z|^p+|d|^p follows solely from nonnegativity of the other power. Equality and p=0 are retained: the latter reads 1≤1+1. Lines 35–41 apply the actual native triangle inequality, then |z|+|d|≤2M. pow_le_pow_left₀ needs the lower base nonnegative, supplied by abs_nonneg; the upper base is consequently nonnegative. mul_pow gives (2M)^p=2^p M^p, and multiplying the max bound by nonnegative 2^p preserves direction. Lines 42–47 multiply by nonnegative |z|³; pow_add is exactly the natural 3+p identity, and ring only reassociates/distributes real products. No division by a power or positive-p premise is used.

Lines 48–49 unfold the real finite sum of squares and use Fin.sum_univ_succ, Fin.cons_zero and Fin.cons_succ to obtain actual energy(cons z w)=z²+energy w for every n. The consumed OQ4 public prefixSum_cons with k=n gives actual full sum z+prefixSum w n. Lines 50–54 prove the actual A-indicated remaining weight nonnegative, either by Real.exp_pos or by its literal zero outside A.

Lines 55–61 handle B with zero full energy separately. energy_eq_zero_iff applied to the actual coordinate 0 forces z=0. The actual first-coordinate cubic mark then vanishes; 3+p≥3 also makes the marked-only right summand zero. This branch never removes the full zero-energy point or assumes it has probability zero. It remains valid for p=0, including Lean's ordinary 0^0 convention in the full-sum factor, because the independent cubic factor is zero.

Lines 62–70 infer positive full energy from nonnegativity and nonzero full energy. Rewriting hCross by the two actual cons identities supplies qualified unit 164 with precisely w,z,x,hx, positivity of z²+energy w, and the same weak endpoint inequality. Its complete conclusion is definitionally exactly w∈A, including strict remaining-energy positivity and the weak remaining threshold. No supplied oracle, moment assertion or altered event is involved. The 164 proof itself is reused from exact qualified evidence rather than re-reviewed.

Lines 71–78 remove the actual B and A indicators only with proved membership. Distributivity gives (-s)(z²+E)=(-s)z²+(-s)E, and the native Real.exp_add is an identity for every real s. Both factors are positive for every real s, so multiplying hMarkedPolynomial by their product preserves order. The final simpa uses only associativity and the local d definition. There is no integration step and no claim of a negative-s integrated moment. Lines 79–80 handle the complement of B by literal zero on the left and nonnegative 2^p, absolute-value powers, scalar exponential and indicated remaining weight on the right. These cases exhaust the full domain.

For n=0 the remaining energy is zero and A is empty; a nonzero z cannot meet B when x≥1, while z=0 is covered by the cubic-zero branch. p=0, z=0, equality thresholds, zero remaining energy and arbitrary signs of z/d are all included. This is an honest pointwise natural-exponent lemma, not a real-exponent or integrated bound.

The entire generated statement is ∀ {α : Type u_1} [inst : Preorder α] (a : α), (a ≤ a) = True. It is a proposition equality, not an assumption or a statement only about Real. The complete exported type includes the universe, Preorder instance, its exact induced LE, and the Eq Prop target. It arises at source line 54 when simp only turns the reflexive inequality after the outside-A indicator rewrite into True using le_refl. A complete direct proof is propext ⟨(fun _ => True.intro), (fun _ => le_refl a)⟩, valid for every displayed Preorder and with no additional hypothesis. This verifies both directions and the complete generated proof obligation, rather than accepting the generated name or its type alone. The actual generated certificate is bound by the exact accepted olean and source; its recursive axiom list is [propext]. No generated theorem term is reprinted or independently executed. This is proof-level semantic review of the source simp construction and its exact full obligation, with kernel-certificate identity supplied by the existing source-bound artifact.

The complete consumed unit-164 public interface is: ∀ {n : Nat} (w : Shao.Path n) (v x : Real), 1≤x → 0<v²+energy w → (3/2)*x*sqrt(v²+energy w)≤|v+prefixSum w n| → 0<energy w ∧ sqrt((9/4)*x²−1)*sqrt(energy w)≤|prefixSum w n|. In unit 171 v=z, hFull is hPositive rewritten by hConsEnergy, and hCross is exactly the actual B condition after the actual cons identities. The conclusion is literally A, with no change in coefficient, square root, strict energy condition, weak comparison or full remaining length. The exact old source d41692110c947b26f92f6bd2f9511a0c1f25a20e0a470d59dcd19b770cc196e5 and object e5b27b3e0a19791a148e8db4f210c9f2b7ba7df343e692fe65ff9f046ed3bd01 match current server bytes. Its complete independent review JSON 6bf95cca027918fdf4bcc0c497ffceb4d23f1c53985f3d1f48df7e5f3b6adcc4 and parent qualification f2aa5279ec91684de2bc70f8ca61be2f2b73b3a45873fcb090f629bd7de4f447 are intact; their existing full-proof evidence is reused.

The complete OQ4 interface is prefixSum_cons (n : Nat) (y : Real) (a : Shao.Path n) (k : Nat) : prefixSum (Fin.cons y a) (k+1)=y+prefixSum a k. Setting k=n gives the required complete sum. KilledPathLaw source 1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f and object 73cff303358b3121caf2c0d9c9976dbd323f75853bdf125bd3e7e067db789f43 are exact in the previously qualified 24-module unit-167 closure. Root-v85's PASS receipt bee6010790734dfc41f2819b76948946a7dec1ac6bd08a5139c8accf1e493fdd records the same accepted source. The qualified 167/168 review and its parent seal are intact. I read the consumed complete public interface and new interaction; I did not repeat an old OQ4 proof audit or gate.

The actual path is Fin n→Real. prefixSum filters the finite indices by i.val<k, so at k=n it is the complete actual sum. energy is ∑i,(a i)², energy_nonneg is unconditional, and energy_eq_zero_iff states energy a=0 iff every actual coordinate is zero. Their complete consumed definitions and theorem heads were read in the accepted source, whose exact SHA is also in the local and server dependency maps. None of these interfaces supplies a law or probability bound. Units 169 and 170 are absent from the imports and dependency map and were not reviewed here.

The actual native contracts read and checked are: abs_add_le : |a+b|≤|a|+|b|, generated by to_additive from mabs_mul_le in Algebra/Order/Group/Unbundled/Abs.lean; pow_le_pow_left₀ (ha:0≤a) (hab:a≤b) : ∀n,a^n≤b^n; pow_nonneg for natural powers; mul_pow in a commutative monoid; pow_add for natural sums; Real.exp_add and Real.exp_pos in the Real section of Analysis/Complex/Exponential.lean; Fin.sum_univ_succ generated additively from prod_univ_succ; Fin.cons_zero and Fin.cons_succ; and Set.indicator_of_mem / indicator_of_notMem generated additively from the exact Set.mulIndicator lemmas. Real meets all algebra/order instances in these contracts. All eight consumed mathlib source files were freshly compared byte-for-byte with the git blobs at pinned mathlib 807d3836b165983210ee2ecf3cd28f239436949c and matched. Initial name-location queries returned unrelated exp or Finsupp candidates; those were not used as the accepted Real/Set contracts. The supplemental observations resolve the namespaces and generated additive names explicitly.

The exact Lean Environment.getModuleIdxFor? implementation reads const2ModIdx; OwnedAudit maps it through header.moduleNames. The audit iterates every constant first and tests actual owner equality. Its publicNames array is used only for the additional public count check, not to filter the whole-owner axiom sweep. Every selected row calls Lean.collectAxioms. The full pinned CollectAxioms source was read: it walks the type and value of theorems/definitions/opaques and other declaration dependencies recursively, and uses precomputed imported axiom entries produced at export time with private body access. Thus imported entries remain transitive rather than being an empty namespace-only check. The two rows contain exactly [propext] and [propext,Classical.choice,Quot.sound], all whitelisted. There are no other owner kinds, private owners or non-theorem values in the actual owner map.

I read supplement.tex 5141–5166 in full with the needed definitions at 4907–4908, 5058–5059 and 5067–5076, and main.tex 1328–1344. The source deletes v=X₁, writes the actual remaining T′ and d′, obtains the weak remaining event with v_x=sqrt(9x²/4−1), and splits |v+d′|^a≤C_a(|v|^a+|d′|^a) before Fubini and before Cauchy on only the unmarked block. Unit 171 faithfully supplies this deterministic split for a=p∈Nat with the honest constant 2^p, one cubic coordinate mark and the actual exponential energy weight. It proves the full weak B-indicated pointwise inequality rather than assuming an event implication. The positive-energy source deletion is consumed only in that branch; the zero-energy extension is justified by the actual cubic-zero argument.

The source allows fixed real a≥0, whereas this frozen leaf expressly covers natural p only. The source's later expectations, β-linear integrated estimate, legal damping regimes, numerical moment bounds, inverse moments, finite sum/rank budgets and original roots are not proved by this lemma. Arbitrary real s here is valid solely because pointwise exponentials remain positive; no negative-s integrability claim follows. This change does not impose higher moments on the original finite-second-moment source, alter p54 repairs, or erase external attribution. It is an elementary source-bound auxiliary lemma with no originality or optimal-constant claim. Original C1 completion is retained; C2 and C12 remain OPEN.

## Full actual-owned type export

```text
TARGET_DECL Shao.C2.AuxiliaryMarkedRareSplit.auxiliary_actual_marked_rare_polynomial_split._simp_1_1 KIND theorem AXIOMS [propext]
ACTUAL_TYPE ∀ {α : Type u_1} [inst : Preorder.{u_1} α] (a : α),
  @Eq.{1} Prop (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a a) True
TARGET_DECL Shao.C2.AuxiliaryMarkedRareSplit.auxiliary_actual_marked_rare_polynomial_split KIND theorem AXIOMS [propext,
 Classical.choice,
 Quot.sound]
ACTUAL_TYPE ∀ {n : Nat} (w : Shao.Path n) (z x s : Real) (p : Nat)
  (hx : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x),
  have B :
    Set.{0}
      (Shao.Path
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) :=
    @Set.ofPred.{0}
      (Shao.Path
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun
        (v :
          Shao.Path
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            x)
          (Real.sqrt
            (@Shao.energy
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              v)))
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@Shao.prefixSum
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            v
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))));
  have A : Set.{0} (Shao.Path n) :=
    @Set.ofPred.{0} (Shao.Path n) fun (u : Shao.Path n) =>
      And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@Shao.energy n u))
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (Real.sqrt
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 9)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) x
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
            (Real.sqrt (@Shao.energy n u)))
          (@abs.{0} Real Real.lattice Real.instAddGroup (@Shao.prefixSum n u n)));
  have F :
    Shao.Path
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real :=
    fun
      (v :
        Shao.Path
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (v
              (@OfNat.ofNat.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@Shao.prefixSum
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              v
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          p))
      (Real.exp
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Neg.neg.{0} Real Real.instNeg s)
          (@Shao.energy
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            v)));
  @LE.le.{0} Real Real.instLE
    (@Set.indicator.{0, 0}
      (Shao.Path
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real Real.instZero B F
      (@Fin.cons.{1} n
        (fun
            (a :
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          Real)
        z w))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            p)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@abs.{0} Real Real.lattice Real.instAddGroup z)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) p))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@abs.{0} Real Real.lattice Real.instAddGroup z)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@abs.{0} Real Real.lattice Real.instAddGroup (@Shao.prefixSum n w n)) p))))
        (Real.exp
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Neg.neg.{0} Real Real.instNeg s)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@Set.indicator.{0, 0} (Shao.Path n) Real Real.instZero A
        (fun (u : Shao.Path n) =>
          Real.exp
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Neg.neg.{0} Real Real.instNeg s)
              (@Shao.energy n u)))
        w))
```

## Exact execution and evidence provenance

The existing attempt002 kernel and all-owner audit both exit 0 under Lean 4.36.0-rc1, mathlib 807d3836, shared-v34 read-only package view, c12-heavy.lock, CPU14–17, -M8192 -j4. The remote successful snapshot is byte-identical to production source, and both stored and worktree objects have the stated object hash. The full audit log reconstructs both exact type blocks and the empty value export; remaining text is the complete 2/PUBLIC1/THEOREMS2/DEFINITIONS0 marker, existing shared mathlib dirty-repository advisory and AUDIT_EXIT=0. The advisory does not conceal changed consumed native sources: all eight are exact pinned blobs.

Attempt001 is preserved at source SHA256 3f1e672890e7b1badad7b2497b093ec7cf0a23d0ef8e35901e86cee7677a013d with the sole failure Unknown identifier abs_add and KERNEL_EXIT=1. The exact source diff changes only abs_add to abs_add_le on line35; attempt002 is the frozen accepted signature and proof reviewed above. No successful old check was replayed.

Initial and final read-only observations each match all 80 exact remote paths, including source, successful and failed snapshots/commands/log hashes, object copies, receipt, release, freeze, audit source/map/types/empty values, direct/transitive recorded project sources, qualified 164 object and all 24 accepted OQ4 closure sources/objects. All 14 recorded dependency sources have matching local snapshot/author bytes. Branch/head/tree remain author/c12-rare-laplace-continuation-v71 / ddd9c7f5ad88f3a92f9bfe533b231c8782d15d90 / 34ec1668815aecd315869af0fd3a8dce1efc41fd. Paper hashes are main beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06 and supplement b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd.

One read-only location query failed because rg is absent on the server; Python source reads resolved it without executing proof tools. The initial CR-count query accidentally counted a literal backslash-r sequence; that observation is preserved, and the corrected bytes([13]) query independently confirms zero CR bytes. These query details are recorded in readonly-query-notes.json. Neither affects any author evidence or mathematical source.

The author writer/execution RELEASE is exact, true and zero-inflight. The reviewer is now complete with no heavy or in-flight work. The parent must read this full Markdown once, check its exact JSON/validation/release hashes and binding coverage, and record qualification. No extra full old-proof audit is needed absent a newly uncovered risk.
