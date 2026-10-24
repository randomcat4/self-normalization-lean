# Independent complete final review: C12 units 161, 163, 166

STATUS: CORRECT

This verdict covers the three exact frozen declarations and their complete current production proofs. No critical gap was found in their source fidelity, mathematical deductions, actual elaborated types, imported-interface use, or bound all-owner recursive axiom evidence. Qualification by the parent remains required; this reviewer does not accept an original C2/C12 root.

The reviewer is a fresh independent context, configured as gpt-6.1-sol/xhigh, with no authorship of these proofs and no child agents. Backend model/effort telemetry and separate input, cached-input, output, and reasoning-subset usage counts are unavailable and are null. The runtime acknowledgement is in runtime-checkpoint.json. Write ownership is this review folder only. No production, shared, old-review, publication, cache, or server write, and no Lean or audit execution, was performed.

## Source and exact scope

Read-only paper sources are main.tex SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` and supplement.tex SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. I read the common notation and original enlarged C1 domain in main.tex 147–234, the centered bounded auxiliary regime in 1193–1220, its rare-tilt use around 1328–1358, supplement.tex 3934–4023, the original cutoff at 4978–4988, and the complete relevant rare-tilt argument 5055–5139, especially 5094–5139. This includes the actual raw energy, weak multiplication events, positive-prefix convention, finite-third-moment status of the auxiliary law, source threshold, tilt, centering, own variance, rank restrictions, and selection order.

The paper asks at these lines for the deterministic-rank auxiliary probability ingredient P_s(T_l>0, |d_l|≥sqrt(9x²/4−1)sqrt(T_l))≤C Ψ(3x/2), for l=t or t−1 and t above the original ceiling cutoff. Units 161/163/166 supply that ingredient. Their finite third moment is a premise on the auxiliary law at this stage; it is not asserted for the original finite-second-moment law. They introduce no bounded support, symmetry, atomlessness, supplied tail estimate, or supplied drift/variance/domain oracle. Applying the accepted full C1 theorem to a finite-third-moment law is valid even though the paper only needs its bounded-law consequence here.

## Unit 161: actual product endpoint from original C1

The following is the complete frozen imports/context/public declaration, with the proof body removed only for display. Its exact bytes and hash are independently checked against the production head.

```lean
import Shao.C2.AuxiliaryOwnC1Budget
import Shao.Probability.SourceOriginalFullRelative

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryProductC1Endpoint
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem actual_product_absolute_endpoint_c1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ (chi : Measure ℝ) [IsProbabilityMeasure chi],
          Integrable (fun z : ℝ => z ^ 2) chi →
          (∫ z : ℝ, z ∂chi) = 0 →
          (0 < ∫ z : ℝ, z ^ 2 ∂chi) →
          Integrable (fun z : ℝ => |z| ^ 3) chi →
          ∀ (n : ℕ) (hn : 0 < n) (y : ℝ), 0 ≤ y →
            let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂chi
            let eta : Measure ℝ := Measure.map
              (fun z : ℝ => z / (Real.sqrt sigmaSq * Real.sqrt (n : ℝ))) chi
            Shao.truncationBudget eta n y ≤ rhoStar →
            (Measure.pi (fun _ : Fin n => chi)).real
              {v : Shao.Path n | y * Real.sqrt (Shao.energy v) ≤
                |Shao.prefixSum v n|} ≤ C * Shao.standardNormalTail y := by

end Shao.C2.AuxiliaryProductC1Endpoint
```

I read all production lines, including the complete proof, and the complete 8,355-byte pp.all actual type. The actual type has exactly the displayed universal C before rhoStar, law, n and y; probability, finite second and third moments, true mean zero, true positive second moment; the own-second-moment normalization; legal budget; and the true weak absolute endpoint event under the finite product. No additional instance, dependent let, or proposition weakens this statement. There are no private/generated declarations or global values to hide extra hypotheses.

The imported accepted original full C1 public type is read completely in consumed-full-c1-actual-type.txt, all 26,656 bytes, SHA256 `2311fb4e511c47d51ef4963c6edfebb2229efbeb270ac8c7aff6f7e28facb454`. The final observation independently extracts that entire exact block from the qualified 35,623-byte whole-owner type export, SHA256 `3248ad2494c711039fc094e03fd454b272dbe2ea90ee3842bd048f672b1f3a75`. The C1 source is `9fb2a134affb98aafead8012d9975e6b2de273fff7c2796867fb54b4b6af3b14`, object `120612e9a6ce6ba95ce5b36d809ba3c1d5e676312c2460840a04e9f395b18b52`, root qualification `db7ac57137befd238b2dfc21e25be68467cb169438e25996284251525e9ccb65`, author receipt `2d7984839d4326e0cdfe1e2c35a51662ce2d188e55091309023665d6f6009e61`. The already qualified original C1 proof is reused, not re-reviewed.

New interaction, checked in full:

1. P is the genuine pi-product of chi and X_i(v)=v_i. Evaluation measurability, native measure-preserving evaluation, and native iIndepFun_pi prove the actual common marginal chi and iid family. The IdentDistrib fields are its two ae-measurabilities and map equality, with map_id on the second law. There is no user-supplied iid/tail predicate.
2. The C1 exponent is literally real p=3, satisfying 2<p≤3. The explicit function equality uses Real.rpow_natCast at |z| to convert the given natural cubic integrability to exactly C1's real-power moment. Its pinned native statement has no missing positivity premise.
3. C1's sigmaSq is the true integral z² dchi, sigma its square root, and scale=sigma*sqrt(n). This is exactly eta in the new declaration. Its original domain is y≥0 and either the moment range or R_n(y)≤rhoStar; the proof supplies the actual second branch and never replaces it by the original auxiliary law's budget or by a bare rank assertion.
4. The fourth And component is exactly the absolute weak signed-crossing error |P(A_s)−2Ψ(y)|≤C_full R_n(y)Ψ(y), following two integrability outputs and the zero-energy output. The access `.2.2.2.1` selects this component correctly. Both s=1 and s=−1 are passed to the same law and the same raw energy. Their positivity and rhoStar≤1/16 imply R_n(y)≤1. Multiplication by C_full≥0 and Ψ(y)≥0 gives each P(A_s)≤(2+C_full)Ψ(y).
5. The absolute final sum event is contained in A_1∪A_(−1). If its sum is nonnegative, |S_n|=S_n; otherwise |S_n|=−S_n=S_n(−v). In each branch, n is a legal positive prefix and its final signed sum is at most the positive-prefix upperMax. The signed upperMax uses the actual path, not a max with time zero inserted. Reflection does not alter the raw energy used in the C1 crossing.
6. Native real-measure monotonicity applies because P is a probability, and union subadditivity needs no disjointness or atomlessness. The resulting constant 4+2*C_full is positive and universal. The weak equality cases, y=0, S_n=0, and energy=0 are included throughout. No division by sample energy appears; the degenerate all-zero path is paid by the accepted C1 crossing, not silently removed.

The current frozen head is unchanged in all four archived attempts. Attempt001 was an import-resolution interruption before the proof body, not a proof failure or success. An attempted LEAN_PATH append did not work. Root's missing-only six-object export, followed by the exact object observation, resolved it. Attempts002 and003 were elaboration failures at the real-power conversion and set-membership unfolding. Attempt004 is the sole whole-source success. All failure snapshots/commands/log hashes remain bound and remote; none receives success credit.

## Unit 163: actual rare probability under the native energy tilt

```lean
import Shao.C2.AuxiliaryProductC1Endpoint
import Shao.C2.AuxiliaryCenteredProductLaw
import Shao.C2.AuxiliarySourceGaussian

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryRareTiltProbability
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_rare_tilt_probability :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
          Integrable (fun z : ℝ => z ^ 2) nu →
          Integrable (fun z : ℝ => |z| ^ 3) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          ∀ (L s : ℝ), 0 ≤ L → 0 ≤ s →
            ∀ (n : ℕ) (x : ℝ), 1 ≤ x →
              s * (n : ℝ) ≤ L * x ^ 2 →
              4000000 * (1 + L) ^ 2 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 *
                (1 + x) ^ 6 ≤ (n : ℝ) →
              (768 / rhoStar) ^ 2 * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 *
                (1 + x) ^ 6 ≤ (n : ℝ) →
              let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
              let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
              let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
              P.real {v : Shao.Path n | 0 < Shao.energy v ∧
                a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ≤
                  C * Shao.standardNormalTail ((3 / 2) * x) := by

end Shao.C2.AuxiliaryRareTiltProbability
```

I read the entire production proof and the entire 20,444-byte actual type. Its C is before rhoStar, nu, L,s,n,x. The only numerical public conditions are the literal source time bound s*n≤L*x² and the two displayed rank bounds. The conclusion uses the native nu.tilted(−s*z²), its actual pi-product, positive actual raw energy, the exact sqrt((9/4)*x²−1) weak endpoint, and the genuine Gaussian tail at 3x/2. The full type has no supplied centered-law, event-implication, integrability, variance, or probability oracle.

All consumed declarations are read completely from their frozen exact interfaces; their existing qualified proof evidence is reused. The source and object bindings for these interfaces are explicit in producerInterfaces in full-review.json and the observations. The new interactions are as follows.

1. beta is the actual integral |z|³ dnu. Qualified AuxiliaryEnergyCentered proves beta≥1 from the true normalized second moment and finite third moment. It therefore supplies nonnegativity and strict positivity without adding beta as an independent parameter.
2. Qualified unit158 receives exactly hTime and the 4,000,000(1+L)² rank bound. Its output provides n>0, n≥4x², s*beta²≤1/128, actual mean drift, and the actual raw-to-centered weak endpoint implication for energy≥n/8. Its rho, mu, a, and y are definitionally the same as those in this proof. The new source does not assume that implication or a mean bound.
3. AuxiliaryEnergyCentered's small-parameter theorem yields IsProbabilityMeasure for the same native rho. Native tilted is the withDensity law with density exp(−s*z²)/(integral exp(−s*z²) dnu); its zero fallback is excluded by the already proved small-parameter probability output. No different normalized tilt is substituted.
4. Qualified unit159 yields chi=map(z−mu)rho, its actual probability, zero mean, finite square and cube, and actual sigmaSq=variance(id,rho) in [1/2,2], together with its own normalized eta budget≤48*beta*(1+y)^3/sqrt(n). The variance lower bound proves the strict second-moment premise of new161. The exact y=a−1/(100(1+x)) is in [1,2x] by the complete SourceEvent threshold interface. Its own rank-payment theorem uses the second displayed rank bound to give budget≤rhoStar/2≤rhoStar. All rhoStar conditions and n>0 are paid explicitly.
5. New161 is applied to that exact chi, its actual moments and mean, n,y, and eta. This gives the endpoint bound on Pc=pi chi. Qualified unit162's second component is equality of real probabilities for exactly this centered coordinate map and weak endpoint, for every y and every probability rho. Its rewritten left side is the literal B under P=pi rho. This is equality of distributions of the actual whole centered product, not an assertion that the centered variables retain law rho.
6. Qualified unit160 is applied with x≥1. The proof's two ring identities reconcile sqrt(9*x²/4−1) with sqrt((9/4)*x²−1), and 3*x/2 with (3/2)*x. Its bound is therefore the actual Ψ(y)≤12Ψ(3x/2), including x=1. Since C_endpoint>0, P(B)≤12*C_endpoint*Ψ(3x/2).
7. For the low-energy producer155, beta>0 makes 128*beta² strictly positive; s*beta²≤1/128 converts to s≤1/(128*beta²). Because L≥0, 4,000,000(1+L)²≥1,024. Multiplying by beta²(1+x)^6≥0 gives precisely its lower rank requirement. The producer's native product is the same P and its event is the weak low-energy A={energy≤n/8}, so it bounds P(A) by (8/3)Ψ(3x/2). Taking the weak low-energy event safely includes the source's strict low-energy region and its boundary.
8. A source-event sample either lies in A or has energy>n/8. In the latter case the unit158 implication sends its unchanged weak endpoint to B. The source event explicitly retains energy>0 even though this implication needs only the high-energy condition. Native probability monotonicity and union subadditivity give the universal C=8/3+12*C_endpoint>0. Equality boundaries, atoms, s=0, L=0, x=1, and centered zero-energy paths cause no division or event loss. n=0 is excluded by the paid rank condition, not a hidden binder restriction.

Unit161 changed only its proof bytes between the draft recorded at unit163 freeze and the final successful source. dependency-source-delta.json records the old and final hashes and unchanged frozen head. The final observation independently verifies the old and final heads identical. Unit163's original successful attempt001 and current receipt bind the final unit161 source and installed object; it does not consume failed unit161 proof evidence.

## Unit 166: original ceiling cutoff and both remaining ranks

```lean
import Shao.C2.AuxiliaryRareTiltProbability
import Shao.C2.AuxiliarySourceCutoffPayment

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Shao.C2.AuxiliaryOriginalCutoffRare
open MeasureTheory ProbabilityTheory

theorem auxiliary_original_cutoff_rare_probability :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ L : ℝ, 0 ≤ L →
          ∀ K : ℝ, 8000000 * (1 + L) ^ 2 ≤ K →
            2 * (768 / rhoStar) ^ 2 ≤ K →
            ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
              Integrable (fun z : ℝ => z ^ 2) nu →
              Integrable (fun z : ℝ => |z| ^ 3) nu →
              (∫ z : ℝ, z ∂nu) = 0 →
              (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
              ∀ s : ℝ, 0 ≤ s →
                ∀ x : ℝ, 1 ≤ x →
                  ∀ t n : ℕ,
                    Nat.ceil (K * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 * (1 + x) ^ 6) ≤ t →
                    (n = t ∨ n = t - 1) →
                    s * (t : ℝ) ≤ L * x ^ 2 →
                    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
                    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
                    let a : ℝ := Real.sqrt ((9 / 4) * x ^ 2 - 1)
                    P.real {v : Shao.Path n | 0 < Shao.energy v ∧
                      a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|} ≤
                        C * Shao.standardNormalTail ((3 / 2) * x) := by

end Shao.C2.AuxiliaryOriginalCutoffRare
```

I read the entire production proof and the entire 21,696-byte actual type. A single positive universal C is obtained from new163 before every parameter. The actual order is rhoStar, L, K, then auxiliary nu and its moment premises, s,x,t,n. Thus K is fixed once after rhoStar/L and before the auxiliary law, s,x,t,n. Requiring both finite lower bounds on K is compatible with choosing it once (for example their maximum); no impossible domain or law-dependent selection is hidden in a premise.

The beta in the cutoff is exactly integral |z|³ dnu. Its beta≥1 is discharged using the normalized second-moment interface, with no standalone beta premise. Qualified unit165's complete public interface is exactly the original Nat.ceil(K*beta²*(1+x)^6) cutoff at t, the alternative n=t or n=t−1 (natural truncated subtraction), and the literal time s*t≤L*x². The two K bounds are respectively 8,000,000(1+L)² and 2(768/rhoStar)². The qualified result gives cutoff≥4, n>0, n≥t/2, s*n≤L*x², and exactly the two new163 n-rank bounds. Thus the deletion case is covered without silently replacing t−1 by t or losing a factor two; t<4 cannot occur. New166 passes the last three paid facts directly to new163, preserving nu, native rho, pi-product, threshold, and event definitionally. The constant is unchanged.

The upstream163 source at this freeze is unchanged. Unit165 is reused with parent qualification SHA256 `4d8a0c300e837be64a9f2972735156defefae79939d41e3add8aae8ec599dc92` and independent review JSON `6ab5661af3fd2d0eb383a6a2eece26aba31a2f88730c61e0ec8e86384084ac8b`; that proof is not re-reviewed or re-executed. There is no original-law third-moment assumption. The source's finite-third-moment auxiliary preprocessing scope is explicit. The statement establishes its deterministic-rank rare probability only.

## Complete type, owner, proof, and axiom coverage

The exact owner maps derive three target modules, three public source theorems, three actual owned constants, and three actual theorems. There are zero private source theorems, zero generated theorems, zero global non-theorem values, and 50,495 total full actual-type bytes. All three actual definition-value exports are exactly empty (SHA256 of empty bytes). I read all three untruncated pp.all actual types, including every quantifier, universe, instance, local let and event target. The initial combined display was supplemented by individual untruncated reads of the 163 and166 exports; no missing output range is claimed as read. The complete production proof of each source is read, including all local have/let proofs.

All three OwnedAudit.lean sources are reviewed. Each enumerates env.constants.toList and uses getModuleIdxFor? plus the environment module-name index to select every constant owned by the target module, rather than selecting a namespace or just a public allowlist. The public list is only an additional coverage check. Every selected constant is passed to Lean.collectAxioms; all selected types and any defnInfo values are exported. The actual map has only one theorem in each module, so no unexported opaque/global value case exists here. Exported TARGET_DECL names exactly equal the owner map names. The current remote audit logs reconstruct the local type/value exports byte-for-byte.

The full pinned CollectAxioms source is read. For theorem, definition and opaque constants it recurses through both type and value, traverses used constants, and uses a seen cache only to avoid cycles/repetition. Imported declarations use axiom arrays computed from private checked environments at object export; this preserves transitive information across imports. getModuleIdxFor? reads const2ModIdx, and the exact toolchain Environment source is hash-bound. Each of these three actual owners has exactly [propext, Classical.choice, Quot.sound]. No sorryAx or new axiom is allowed. Production scans find no sorry, admit, axiom, unsafe or native_decide. This is transitive axiom evidence for the actual owners, not a lexical-only scan.

The original server kernel and axiom receipts are reused: unit161 attempt004, unit163 attempt001, unit166 attempt001, each kernel exit0 and audit exit0. Commands use the C12 heavy lock, CPU14–17, native -M8192 -j4, Lean v4.36.0-rc1, mathlib 807d3836b165983210ee2ecf3cd28f239436949c, and the accepted shared-v34 package view. Read-only observation confirms the branch author/c12-own-c1-budget-v71 and frozen base HEAD123547c9275f119c38975c95cd2dbc61d8bdf551. Existing mathlib local-change warnings are preserved as warnings; the relevant consumed native source bytes were independently compared with the pinned commit and matched. No original success is recompiled or re-audited.

## Physical bindings, prior evidence reuse, and release boundary

server-evidence-observation.json checks 661 exact remote source/object/receipt/freeze/snapshot/audit/type/value/qualified-interface bindings, including the root-exported accepted common closure; readonlyfinal-observation.json checks those same bindings plus the two original qualified C1 kernel/audit log hashes (663 bindings). All match. Both observe no Lean/lake process for these three released target modules. Every frozen head in all six archived target attempts matches its freeze, with UTF-8 without BOM and LF bytes (CRcount0). The current three sources, original objects, and installed objects are exact; no binaries or caches are copied into the local review. Final evidence retains structured exit/failure markers and remote log hashes; raw server logs stay remote.

The common C1 source is intentionally retained in its qualified root checkout. Root exported compiled objects only to C12; the source's absence in that lane checkout is not a missing mathematical dependency. The accepted root qualification, original author receipt/release/reviewer release, qualified owner map and full public type are bound. Root's export demonstrates 185 accepted closure modules, 179 pre-existing exact objects and six missing-only exports, with zero overwrite, source edit or compiler/audit invocation. The failed append hypothesis is not used as evidence of a successful import.

Seven sealed prior review packets are reused through their exact parent-acceptance hashes and sealed artifacts: auxiliary energy tilt150/151, centered moments152/153, low-energy154/155, centered event156/157, source parameters/own budget158/159, Gaussian/product/deletion160/162/164, and cutoff payment165. I read the complete consumed public interfaces and relevant definitions for the new uses; unchanged producer proofs are not replayed or re-reviewed. The complete fresh review here is restricted to new161/163/166 and their interactions. No p54 repair or external-result attribution is changed.

Some newly added dependencySourceSHA256 keys in the unit163/166 author receipts are Windows relative paths using backslashes; other keys use forward slashes. The observer explicitly interprets each as a relative project path by replacing backslashes with forward slashes before looking it up on Linux. Equal normalized keys must agree on their source hash, and every resulting path is freshly hash-verified. The parent raised this spelling issue before the seal, then explicitly confirmed retaining all original receipt/RELEASE bytes and their supplied hashes because this documented interpretation resolves the cross-platform lookup. No receipt/source/object/freeze or successful check was changed or replayed. This clarification concerns path spelling only, not a declaration or mathematical assumption.

The read-only query adaptations are recorded in query-mistakes.json: a local display SyntaxError; a source lookup that initially assumed the common source had also been copied to C12; and an excerpt pattern that omitted the Measure namespace. None is a mathematical or compiler result and none changed server/source state. The final native tilt excerpt is losslessly reused from a sealed primary-source observation only after its complete file hash freshly matches the same pinned source. The observer pattern is corrected for reproducibility. Review observations and validation are deterministic metadata work, not additional Lean gates.

The mathematical verdict is CORRECT for these frozen auxiliary statements. Their novelty or original-root completeness is not asserted. Full C2 rare suffix/marked Laplace bounds, inverse moments, weighted record and circular witness machinery, and final root assembly remain OPEN. The parent must read this entire report and independently validate exact source/receipt/seal bindings and coverage before issuing qualification. After validation, writer-release.json records this reviewer's source/reviewer/execution release, zero inflight work and zero heavy commands; ordinary final delivery ends this context's turn.
