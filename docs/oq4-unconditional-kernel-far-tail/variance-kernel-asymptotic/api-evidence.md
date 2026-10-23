# Pinned API and consumed-value evidence for the Kv adapter proposal

This packet is read-only source/API inspection plus a mathematical proposal.
It is not elaboration, kernel/object or independent-review evidence. No Lean,
import, object, toolchain, Git, build or cache command was run. No existing
source, proof, receipt, library snapshot or shared coordination file was edited.
The only new files belong to variance-kernel-asymptotic-author-v1/.

The local file library/lean-toolchain was read: leanprover/lean4:v4.36.0-rc1.
SERVER.md pins mathlib807d3836b165983210ee2ecf3cd28f239436949c. These are file
pins, not fresh runtime probes. All later Lean work remains server-only and
subject to the existing OQ4 CPU18–21/single-heavy lease. This author has no
Lean or implementation authority in this task.

## 1. Source bindings and old evidence reused

Original source proof01.md lines9–36 was read and hashed:
7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38.
Intake-only variance-kernel-asymptotic-next-math-notes-v1.md was read/hashed:
df83851de0913636d6275d34614a606c67527914c061ec7badcc968eebf09002.
It was not used as proof evidence.

The exact frozen154 formal contract and parent freeze were read completely:
bf1a80104cb1ee7812932127d7a54c274a0db7d8a3d900cc71a092b4f781fd6d and
d0a98bd623e6618e9246b9b5ea92a0f5b5ba0e6373c500d76bc69c1b5db0699d.
The LOCAL154 proof/implementation was NOT read. Its status is unqualified;
there is no accepted future object/hash in this proposal. The final import
must be bound to its actual qualified source/object before formal acceptance.

Accepted VarianceScaling.lean local source SHA256 is
f7e0b71c4a8ab372310c28e5ab5ceadc371eb00c7dccf2dca1a44cdf4cf70d21.
Existing saved object SHA256 is
62a5ab0048f6fcb7bdc1ab47c647eda477711fb35c3bb58ae6e77db0250c89ee,
at .lake/build/lib/lean/Shao/OQ4/VarianceScaling.olean. The latter is read
from library/verification/oq4-rademacher-lattice-shift-all/receipt.json,
provenance.old_build_artifacts_sha256; the matching source is in
provenance.frozen_oq4_source_sha256. That receipt SHA256 is
abc87069ca85fd8c329336957ac545fb4efa8a0fb3bb1002a02e3a1a43b8d2ce.
This is reuse of an accepted saved binding, not a new current-server object
observation or object command. The current v54 receipt's source map also
contains exactly the same VarianceScaling source SHA.

The existing finite-scaling author kernel/all14-owned axiom receipt is
drafts/oq4/scaling/receipt.md, SHA256
ded5a03c2f70cfb06f1f24b55d31ea91c11cf7298e84d25838d432437d62ffec.
The independent review's verdict/version/scope were read (not its whole old
proof review): drafts/oq4/review/variance-scaling-review-v1.md, CORRECT, SHA256
a4231653c8ccdff5e01bb321d0d869df9b87996e87798f20fd6cd48fb3e484ae.
The accepted library/verification/oq4/receipt.json, SHA256
e8cd903dd9991d00042185aa6841afca75bdccc4184480d9370a002ca5b0af00,
records source-bound target -o check exit0 and all-axiom audit exit0.
The old CPU0–3 commands in those archived receipts are historical evidence,
not current execution instructions. No old proof check was repeated.

The exact qualified scope is finite variance standardization, including n=0,
time0/weak endpoints, explicit moments and exact ratios. It does not supply
actual finite-product pushforward or long-time K/Kv. Reusing it does not close
any original research root.

## 2. Actual consumed scaling heads

The relevant actual heads and adjacent source fragments were inspected. The
whole accepted old proof/report was not re-reviewed and no old check replayed:

* VarianceScaling.lean23–28: path_variance_scaling {n} (a:Path n) (σ h:R)
  (hσ:0<σ) (_hh:0≤h) concludes the ALL-natural-k prefix identity, energy
  identity, and equivalence of all k≤n weak closed-strip inequalities.
* Lines89–96: standardized_third_moment_bound takes μ,Y,σ,M, lower σ≥1/2,
  M≥0, integrable |Y|³ and actual third≤M; concludes ∫|Y/σ|³≤8M.
  It is already called inside the next accepted theorem; we do not reprove
  or call it as a replacement for mapped-law transport.
* Lines117–119: sqrt_variance_parameters (v) (1/2≤v) (v≤2) gives
  sqrt(v)>0, sqrt(v)²=v, sqrt(v)≥1/2. The new upper bound sqrt(v)≤2 is
  proved in proof.md section3, not attributed to the old head.
* Lines127–146: sqrt_variance_standardization μ Y v M, both v bounds,
  M≥0, integrable Y,Y²,|Y|³, actual mean0/second=v/third≤M, gives
  original-measure integrability of Z=Y/sqrt(v), its square/absolute cube,
  mean0, second1, exact third=(σ⁻¹)³β and third≤8M. It does not assert
  these facts under ν.map g. New section4 pays that transfer explicitly.
* Lines162–166: sqrt_variance_scale_ratios N v h and both v bounds,h>0
  gives N/(h/sqrt(v))²=v*N/h² and N/(h/sqrt(v))³=sqrt(v)³*N/h³.
  No N>0, variance limit or other probabilistic premise occurs.

The exact new single-row call is sqrt_variance_standardization ν (fun x=>x)
v M hvlower hvupper hM0 hId hSq h3 hmean hsecond hthird. Here hId,hSq,hM0
are derived, not supplied extra public assumptions. The new mapped helper is
then invoked at f=id, square, and absolute cube.

## 3. Actual consumed project values and event APIs

These literal existing values were read; no new aliases are proposed:

    Shao.Path n := Fin n → ℝ
    Shao.prefixSum a k :=
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i
    Shao.closedStrip h := {a | ∀ k : ℕ, k ≤ n → |Shao.prefixSum a k| ≤ h}
    Shao.OQ4.RademacherScalarBounds.lambda := Real.pi ^ 2 / 8

Actual closedStrip source is Basic/ClosedSurvival.lean26–27, SHA256
bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f.
Actual path values and prefixSum_smul are in Basic/FinitePath.lean17–23,82–85.
Actual measurable_prefixSum (k:Nat):Measurable(fun a:Path n=>prefixSum a k)
is Probability/MeasurablePath.lean53–55, SHA256
827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41.

KilledPathLaw.lean26–32 gives measurableSet_shiftedClosedSurvival (n h z)
for actual {a|∀k,1≤k→k≤n→|z+prefixSum a k|≤h}. Lines248–249 give
shiftedClosedSurvival_eq_closedStrip n h hh for h≥0. These provide the
actual closedStrip measurable-set proof if convenient; the new proof can
also use the displayed countable intersection of measurable inequalities.
The source SHA256 is
1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f.

KilledBlockBounds.lean11–20, SHA256
cc46dc9257cc89d6e31139a60593a419d296fd5f691f10eb565d6310d9dd2408,
defines exactly:

    iidIntervalConcentration ν β Cq :=
      ∀ t:Nat, 1≤t → ∀ x:Real,
        (pi_(Fin t)ν).real {a|prefixSum a t∈Icc x (x+1)} ≤ Cq*β/sqrt(t)
    iidOneSidedSurvival ν β Cs :=
      ∀ t:Nat, 1≤t → ∀ d:Real, 0≤d →
        (pi_(Fin t)ν).real (Shao.closedUpper d) ≤ Cs*(d+β)/sqrt(t) ∧
        (pi_(Fin t)ν).real (lowerBlockSurvival d) ≤ Cs*(d+β)/sqrt(t).

Those predicates are kept literally on η_j and β'_j. The adapter never
changes their laws, bounds their old β_j instead, or calls them for t=0.
Their definitions are not an existence theorem for universal constants.

## 4. Pinned primary Mathlib source reads

Four completed source-only calls used existing tools/server.py transport,
command taskset -c18–21 python3 - with timeout60. Their exact request and
complete host-result pairs are api-map-*, api-pi-*, api-pi-namespace-*, and
api-pi-namespace-resolution-*. Each host result has exit_code0, empty stderr,
no ongoing session, and no uncertain execution. The host response itself is
preserved. No command was replayed. These are plain small text source reads,
not Lean/import/graph/object/toolchain probes or cache/build operations.

The first narrow search for a guessed map_pi spelling returned NO_MATCH and
was recorded. A source scan of map declarations in that SAME Pi.lean located
the actual pi_map_pi; the namespace-only read confirmed it is inside
MeasureTheory.Measure (namespace starts68/125). No guessed name is claimed
as an available API, and no characteristic-function/independence workaround
is needed. The saved independence excerpt is not consumed or imported.

All paths below are relative to the fixed read-only shared-v34 mathlib root.

* MeasureTheory/Constructions/Pi.lean386–389, SHA256
  bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef:

      lemma Measure.pi_map_pi {X Y : ι → Type*}
        {mX : ∀ i, MeasurableSpace (X i)} {μ : (i:ι)→Measure(X i)}
        [∀ i, MeasurableSpace (Y i)] {f : (i:ι)→X i→Y i}
        [∀ i, SigmaFinite ((μ i).map (f i))]
        (hf : ∀ i, AEMeasurable (f i) (μ i)) :
        (Measure.pi μ).map (fun x i=>f i (x i)) =
          Measure.pi (fun i=>(μ i).map(f i)).

  The surrounding finite-index assumptions are retained; take ι=Fin n,
  X_i=Y_i=Real, μ_i=ν,f_i=g. Mapped probability gives every required
  SigmaFinite instance. There is no n>0 hypothesis. Actual source lines390–399
  prove it by measurable rectangles and actual map evaluation; we use its
  accepted public result, not just the informal word independence.

* MeasureTheory/Function/L1Space/Integrable.lean355–357, SHA256
  d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759:

      integrable_map_measure
        (hg : AEStronglyMeasurable g (Measure.map f μ))
        (hf : AEMeasurable f μ) :
        Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ.

  Use its .mpr for the new actual mapped integrabilities. Measurable real
  tests supply AEStronglyMeasurable; g(x)=x/σ is measurable via
  measurable_id.div_const σ. No invertibility or positivity is needed in
  this generic transport helper.

* MeasureTheory/Integral/Bochner/Basic.lean1076–1078, SHA256
  66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670:

      integral_map (hφ : AEMeasurable φ μ)
        (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
        ∫y,f y ∂Measure.map φ μ = ∫x,f(φ x) ∂μ.

  This is the exact orientation used in standardized_law_moments.

* MeasureTheory/Measure/Typeclasses/Probability.lean124–141, SHA256
  00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b:
  its actual anonymous instance constructs IsProbabilityMeasure(map f μ)
  for probability μ. Also Measure.isProbabilityMeasure_map_iff
  (hf:AEMeasurable f μ) states probability(map f μ) iff probability μ.
  We prove g measurable before using either, and therefore do not use the
  definition's fallback branch for a nonmeasurable map.

* MeasureTheory/Measure/Map.lean166–172, SHA256
  7bae8f174146d4ef4055f79757c2a0a3af6a9090dda3d28ea17fbd54540e9593:
  Measure.map_apply_of_aemeasurable (hf:AEMeasurable f μ)
  (hs:MeasurableSet s) states (μ.map f)s=μ(f⁻¹'s).
  The measurable version Measure.map_apply is also present. Apply this to
  the actual F and actual standardized closedStrip, then apply toReal to
  the equality. No ENNReal subtraction or finite-product conditional law
  is used.

Existing saved148/150 primary excerpts are reused through
terminal-normalized-kernel-author-v1/api-evidence.md68–79 and the cited
brownian-terminal-kernel-block-author-v1/api-evidence.md. In particular
Integrable.mono'104–106, integrable_const166, Integrable.add420 and
integral_nonneg647–649 justify the two lower-moment/nonnegative-M helpers.
Metric.tendsto_atTop910–913 is the exact real epsilon/threshold criterion;
the scaled cubic proof uses it with the explicit majorant8*s_j.
The height/quadratic arguments use the definition of Tendsto to atTop and
eventual inequalities, not a guessed varying-variance continuity theorem.
No new limit API discovery or old check replay is needed.

## 5. Exhaustive proposed owned inventory and remaining gates

declarations.lean.txt is the only proposed formal inventory: eleven theorem
heads, eight private and three public, six exact imports, one namespace.
ZERO new def/abbrev/instance/structure/notation/macro values are proposed.
The three public heads are finite_product_standardization_map,
closedStrip_probability_standardization, and
varying_row_variance_closedStrip_relative_asymptotic. All others are private
helpers. Mathematical symbols in proof.md are proof-local notation only.
No implementation or theorem proof body is in the formal companion.

static-inventory.json records actual counted heads/imports, source hashes,
proposal-byte LF/CR counts, checked bindings and exact remaining scope.
checkpoint.json records actual author runtime/release and one next action.
Parent must FULL-read/freeze before implementation; the future source must
be UTF-8/LF before its first source-bound server gate. Any extra top-level
head/value/import or changed premise requires a substantive parent freeze.
The final complete independent review and kernel/all-owned transitive-axiom
receipt remain pending, as does actual154 qualification. Standard axioms
only: propext, Classical.choice, Quot.sound. The original roots remain OPEN.
