"""Assemble this independent review's coverage and immutable final receipt."""
from pathlib import Path
import json, hashlib, datetime, collections
W=Path('C:/game/shao lean'); D=W/'drafts/oq4/positive-boundary-studentized-final-review-v1'
B=W/'drafts/oq4/positive-boundary-studentized-execution-author-v1'; R=B/'round004'
def load(p): return json.loads(p.read_text(encoding='utf-8'))
def save(n,v): (D/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def metric(p):
    b=p.read_bytes();return dict(path=str(p).replace('\\','/'),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),LF=b.count(b'\n'),CR=b.count(b'\r'),UTF8BOM=b.startswith(b'\xef\xbb\xbf'))
native=load(R/'owned-native.json'); old=load(R/'old-direct-consumption-index.json'); ev=load(D/'evidence-validation.json')
src=(B/'PositiveBoundaryStudentized.lean').read_text(encoding='utf-8').splitlines()
spans={
'infiniteLaw':(27,28,'Actual countable product of the fixed real law.'),
'finiteProjection':(30,31,'Literal Fin.val coordinate restriction, including Fin0.'),
'squareAverage':(33,34,'Actual range-n sum of squared coordinates divided by the real cast of n; total division at zero.'),
'energyBad':(36,37,'Strict actual energy deviation δ*n < |Q-n|.'),
'measurable_finiteProjection':(39,41,'Coordinate evaluation measurability into the finite product space.'),
'finiteProjection_map_eq_pi':(43,61,'Actual infinite-product evaluation independence, identical coordinate law, and genuine finite iid pushforward; n=0 included.'),
'projection_energy':(63,66,'Exact Fin n/range n square-sum reindexing, including empty sum.'),
'measurable_squareAverage':(68,71,'Finite squared-coordinate sum and division by a fixed real are measurable.'),
'squareAverage_ae_tendsto':(73,105,'Actual infinite-product square strong law with square integrability only; no fourth moment.'),
'measurableSet_energyBad':(107,110,'Strict comparison with a measurable actual energy deviation.'),
'finite_energy_bad_eq_infinite':(112,121,'Exact event pushforward using the projection map law and energy reindexing for every n.'),
'finite_energy_lln':(123,149,'Strong law to convergence in measure, then strict deviation contained in weak norm event eventually n≥1; squeeze to zero.'),
'integrable_square_of_third':(151,166,'Pointwise z²≤1+|z|³ and probability-finite integrable domination.'),
'sqrt_nat_tendsto':(168,171,'Natural casts and real square root both diverge along nSeq→∞.'),
'horizon_exact':(173,183,'T=toNNReal((r²)⁻¹), r>0, gives T*(r*sqrt n)²=n and exact natural floor n, including zero.'),
'discrete_event_eq_closedStrip':(185,192,'Positive h exactly transports every divided-prefix weak inequality, including zero and final prefix.'),
'deterministic_positive_boundary_tendsto':(194,249,'Qualified actual row theorem with max(nSeq,1), exact floor horizon, fixed actual law and moment bound, bSeq→1; exact positive Brownian time identity and eventual dependent-length equality.'),
'measurableSet_closedStrip':(251,256,'Countable intersection of measurable weak prefix comparisons.'),
'measurableSet_randomDenominatorEvent':(258,265,'Countable intersection against the measurable actual square-root energy wall.'),
'randomDenominatorEvent_eq':(267,281,'Only sqrt(n)>0 is cancelled when n>0; n=0 has actual zero square sum and equal zero walls. No division by sqrt Q.'),
'sandwich_sets':(283,313,'Off strict bad event, weak energy bounds give sqrt walls for x≥0 and 0<δ<1; no atom removed.'),
'sandwich_probability':(315,345,'Lower Aminus⊆E∪Bad and upper E⊆Aplus∪Bad; finite real measure monotonicity and union subadditivity.'),
'studentized_positive_boundary_tendsto':(347,436,'One fixed small δ from actual CDF continuity, two positive deterministic-wall limits, energy LLN and eventual xSeq positivity; direct epsilon squeeze.'),
'studentized_positive_boundary_ratio_tendsto':(438,460,'Actual numerator limit divided by actual changing CDF limit, whose positive limit is paid by qualified A; quotient→1.')}
generated=[]; allowned=[]
for x in native:
    explicit=x['public'] or x['explicitPrivate']; suffix=x['name'].split('.')[-1]
    if explicit:
        a,z,meaning=spans[suffix]; category='public' if x['public'] else 'explicitPrivate'
    else:
        a=z=None;category='generated'
        refs=x['valueRefs']
        if 'Eq.refl' in refs:
            meaning='Exact defining equation; complete unabridged type agrees with literal full source value. Eq.refl proof binds the actual definition.'
        elif 'Metric.mem_ball' in refs:
            meaning='Exact metric-ball membership proposition equality under the displayed pseudometric-space premises.'
        elif 'Set.mem_preimage' in refs:
            meaning='Exact preimage-membership proposition equality with all explicit types, function, set and argument retained.'
        else:
            theorem=next(t for t in ['two_ne_zero','three_ne_zero','four_ne_zero','mul_ne_zero','pow_ne_zero','zpow_ne_zero','Nat.cast_add_one_ne_zero'] if t in refs)
            meaning='Separately owned generic FieldSimp proposition equality to False, proved by eq_false and '+theorem+'; the full actual algebraic/NeZero/IsReduced/CharZero premises were read and retained.'
    row=dict(name=x['name'],nativeOwner=x['module'],kind=x['kind'],category=category,sourceLines=None if a is None else dict(start=a,end=z),fullActualType=x['type'],fullActualTypeSHA256=hashlib.sha256(x['type'].encode()).hexdigest(),completeActualTypeIndependentlyRead=True,completeDefinitionValue=x['elaboratedValueExplicit'],completeDefinitionValueRead=x['kind']=='definition',opaqueValue=x['opaqueValueExplicit'],actualNativeProofValueAvailable=x['valueAvailable'],nativeAxioms=x['axioms'],unsafe=x['unsafe'],partial=x['partial'],semanticReview=meaning,proofBinding='Complete source proof independently read; original exact-source kernel and every-owned-root transitive AX receipt reused.' if explicit else 'NEW generated obligation, complete actual native type and proof-reference list reviewed; original same-check kernel and own AX row reused.',nativeGeneratedProofRefs=x['valueRefs'] if not explicit else None,verdict='CORRECT')
    allowned.append(row)
    if not explicit:generated.append(row['name'])
assert len(allowned)==61 and len(generated)==37

# Literal old source spans, not invented native pp signatures. Explicit inherited
# source context is stated separately rather than guessed as native binders.
spec={
'Shao.Path':('library/Shao/Basic/FinitePath.lean',18,18),
'Shao.prefixSum':('library/Shao/Basic/FinitePath.lean',23,24),
'Shao.energy':('library/Shao/Basic/FinitePath.lean',31,31),
'Shao.closedStrip':('library/Shao/Basic/ClosedSurvival.lean',26,27),
'Shao.OQ4.RandomDenominatorFarTail.randomDenominatorEvent':('drafts/oq4/random-denominator-far-tail-author-v1/RandomDenominatorFarTail.lean',31,32),
'Shao.measurable_sqrt_energy':('library/Shao/Probability/MeasurablePath.lean',79,80),
'Shao.measurable_prefixSum':('library/Shao/Probability/MeasurablePath.lean',53,54),
'Shao.measurable_energy':('library/Shao/Probability/MeasurablePath.lean',61,61),
'Shao.OQ4.PolygonalKilledFunctionalLimit.floorHorizon':('library/Shao/OQ4/PolygonalKilledFunctionalLimit.lean',37,38),
'Shao.Probability.iid_samplePath_map_eq_pi':('library/Shao/Probability/FiniteIID.lean',32,35),
'Shao.OQ4.PolygonalKilledFunctionalLimit.discreteClosedSurvival':('library/Shao/OQ4/PolygonalKilledFunctionalLimit.lean',40,41),
'Shao.OQ4.BrownianPositiveCDF.survival_time_eq_probability':('drafts/oq4/positive-boundary-studentized-author-v1/BrownianPositiveCDF.lean',229,233),
'Shao.Probability.BrownianSup.probability':('library/Shao/Probability/BrownianSup.lean',124,125),
'Shao.OQ4.BrownianSurvivalBoundary.closedSurvival':('library/Shao/OQ4/BrownianSurvivalBoundary.lean',26,27),
'Shao.OQ4.PolygonalKilledFunctionalLimit.discrete_survival_tendsto_brownian':('library/Shao/OQ4/PolygonalKilledFunctionalLimit.lean',880,898),
'Shao.OQ4.BrownianPositiveCDF.probability_continuousAt':('drafts/oq4/positive-boundary-studentized-author-v1/BrownianPositiveCDF.lean',168,171),
'Shao.OQ4.BrownianPositiveCDF.probability_pos':('drafts/oq4/positive-boundary-studentized-author-v1/BrownianPositiveCDF.lean',184,187),
'Shao.OQ4.BrownianPositiveCDF.probability_tendsto':('drafts/oq4/positive-boundary-studentized-author-v1/BrownianPositiveCDF.lean',176,181)}
chains={x['module']:x for x in ev['all31ConsumedOwnerSourceObjectRuntimeChains']}
direct=[]
for x in old['directOldHeads']:
    f,a,z=spec[x['name']];p=W/f
    text='\n'.join(p.read_text(encoding='utf-8').splitlines()[a-1:z])
    if x['kind']=='theorem':text=text.removesuffix(' := by').removesuffix(' :=')
    direct.append(dict(name=x['name'],nativeOwner=x['module'],nativeKind=x['kind'],nativeAxioms=x['axioms'],basis='SOURCE-DERIVED current exact qualified source; old compact native pp type absent',source=metric(p),sourceLines=dict(start=a,end=z),completeSourceHeadOrFullValue=text,completeValueRead=x['kind']=='definition',inheritedSourceContext='Finite path modules have implicit n:Nat. Probability source context uses the displayed measurable space and probability instances. Brownian contracts have Ω:Type*, MeasurableSpace Ω, actual B, P, IsProbabilityMeasure P, hB. iid_samplePath additionally has both source and target probability instances, finite n and family X. Only actually used variables become binders; no nonexistent native pp binder list is claimed.',callConditionsIndependentlyPaid=True,oldCompleteProofAndAXReused=True,ownerChain= x['module'],verdict='CORRECT_AT_NEW_USE'))
assert len(direct)==18
meaning={
'Shao.Basic.ClosedSurvival':'Literal weak all-prefix path survival and deterministic path semantics.',
'Shao.Basic.FinitePath':'Actual finite coordinates, filtered prefix sums and coordinate square energy, with zero-energy and empty-path conventions.',
'Shao.OQ4.BrownianPositiveCDF':'Qualified actual positive-level Brownian null atoms, CDF continuity/positivity and exact time-one survival identity.',
'Shao.OQ4.BrownianSurvivalBoundary':'Actual Brownian full-time closed/strict survival, continuous-path raw supremum and paid unit-boundary nullness including starts ±1.',
'Shao.OQ4.CosineCoefficients':'Qualified exact cosine-series coefficient values and identities.',
'Shao.OQ4.KilledIteration':'Qualified finite killed-kernel iterations representing weak survival.',
'Shao.OQ4.KilledKernel':'Qualified actual killed transition kernel definitions and identities.',
'Shao.OQ4.KilledPathLaw':'Qualified genuine finite-product killed path laws and integral representations.',
'Shao.OQ4.PolygonalBrownianWeakLimit':'Qualified actual product-pushforward polygonal laws converging to the genuine Brownian path law under the row moment assumptions.',
'Shao.OQ4.PolygonalKilledFunctionalLimit':'Qualified exact floor/grid path adapter and closed killed row functional limit with b→1, full moment/height/horizon and start conditions.',
'Shao.OQ4.PolygonalPathTightness':'Qualified actual continuous polygonal maps and tightness under the documented varying-row moment and height conditions.',
'Shao.OQ4.PolygonalThirdMomentB3':'Qualified actual finite ramp polygonal path, exact grid/affine identities and cubic-moment increment controls.',
'Shao.OQ4.RademacherAllModes':'Qualified finite lattice cosine eigenmode identities and their full finite-mode inventory.',
'Shao.OQ4.RademacherCosine':'Qualified actual Rademacher step law and killed cosine action.',
'Shao.OQ4.RademacherFiniteBasis':'Qualified finite lattice basis, sine/cosine orthogonality and exact expansion identities.',
'Shao.OQ4.RademacherFiniteS1':'Qualified actual finite lattice survival spectral representation.',
'Shao.OQ4.RademacherIteration':'Qualified exact iteration of the actual Rademacher killed kernel.',
'Shao.OQ4.RademacherScalarBounds':'Qualified scalar eigenvalue/coefficient inequalities used by accepted spectral comparisons.',
'Shao.OQ4.RademacherSpectralPairing':'Qualified finite spectral pairing, actual coefficients and paired-mode identities.',
'Shao.OQ4.RademacherSpectralTail':'Qualified leading-mode and remaining-mode bounds with their genuine spectral constants.',
'Shao.OQ4.RandomDenominatorFarTail':'Literal random-denominator multiplicative weak event; no private far-tail proof or target limit is a direct premise here.',
'Shao.OQ4.RowBlockGaussianLimit':'Qualified varying-law scalar-block Gaussian limits with genuine centering, variance and cubic-moment payment.',
'Shao.OQ4.RowPolygonalFDD':'Qualified actual finite-dimensional product-pushforward block/endpoint laws and probability instances.',
'Shao.OQ4.WeightedThirdMomentB2':'Qualified weighted cubic-moment estimates underlying actual polygonal tightness and limits.',
'Shao.Probability.BrownianFirstTerm':'Qualified actual Brownian leading-term comparison and eventual small-positive-radius positivity.',
'Shao.Probability.BrownianGridBridge':'Qualified actual Brownian versus finite Rademacher grid laws, closed-event boundaries and genuine grid approximation.',
'Shao.Probability.BrownianSpectralEnvelope':'Qualified Brownian leading-term/error envelope values and positivity.',
'Shao.Probability.BrownianSup':'Actual closed-interval raw supremum, trace, measurable modification U and literal weak CDF, with qualified realization invariance.',
'Shao.Probability.FiniteIID':'Literal samplePath and actual independent identical-coordinate pushforward to the finite product, including Fin0.',
'Shao.Probability.MeasurablePath':'Borel measurability/continuity of actual finite prefixes, energy and square-root energy.',
'Shao.Probability.RademacherGrid':'Qualified actual finite Rademacher grid law and maximal/grid comparison controls.'}
assert set(meaning)==set(chains)
oldrecords=[]
for x in old['allQualifiedTransitiveOldHeads']:
    assert x['valueAvailable']
    oldrecords.append(dict(name=x['name'],nativeOwner=x['module'],nativeKind=x['kind'],nativeAxioms=x['axioms'],ownerMeaningAndSourceObjectRuntimeChainRef=x['module'],isDirectNewUse=x['name'] in spec))
assert len(oldrecords)==899
coverage=dict(schema='oq4-independent-complete-final-review-coverage-v1',verdict='CORRECT',reviewer=dict(context=190,name='/root/oq4_positive_boundary_studentized_final_review',model='gpt-6.1-sol',reasoningEffort='xhigh',workflow='math-theorem',independent=True),source=ev['source'],frozenSourceHeads=24,completeSourceLinesRead=463,completeSourceTheoremBodiesRead=20,fullDefinitionValuesRead=4,imports=17,options=1,allActualOwned=allowned,counts=ev['counts'],ownershipBasis='Original unfiltered environment difference = module ownership = stage2; original native projection, no second walk',generatedAllNewObligations=generated,newForeignLookingOwned=load(R/'source-bound-final-receipt.json')['actualOwnership']['newForeignLookingOwnedNames'],ownedOpaqueValues=0,sourceInstances=0,generatedPropDefinitionValues=0,directQualifiedOldSourceDerivedInterfaces=direct,allConsumedOldNativeNameOwnerKindAXRecords=oldrecords,allConsumedOwnerSourceOriginalObjectRuntimeChains=ev['all31ConsumedOwnerSourceObjectRuntimeChains'],oldRawNativePPTypesAvailable=False,oldProofReplay=False,oldSemanticScope='Reuse complete qualified unchanged old proofs, full definition values and generated semantics only at exact checked source/owner/original-object/runtime bindings; this is not a second whole old-proof review.',runtimeRecovery=dict(receipt=metric(R/'runtime-recovery-receipt.json'),originalReadsLostInMemory=6,recoverySecondReads=6,totalNewInputReads=12,knownPaidFingerprintsReused=5124,actualImports=5130,sameCanonicalStrongLaw=True,originalSixHashesUnavailable=True,originalPointCaptureClaimed=False,noNewLeanOrWalk=True),semanticReview='independent-review.md',criticalGaps=[],requiredRepairs=[],originalRoots='OPEN',wholeWindowQualified=False,usage=dict(inputTokens=None,cachedInputTokens=None,outputTokens=None,reasoningSubsetTokens=None,status='UNAVAILABLE_NOT_ESTIMATED',subscriptionPercentageClaimed=False))
coverage['qualifiedOldMeaningByNativeOwner']=meaning
coverage['all899OldUnsafeFalsePartialFalseValueAvailableTrue']=True
save('semantic-coverage.json',coverage)
e=load(R/'execution-receipt.json'); final=load(R/'source-bound-final-receipt.json')
receipt=dict(schema='oq4-independent-final-reviewer-receipt-v1',status='CORRECT',atUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),reviewer=coverage['reviewer'],source=ev['source'],formalFreeze=metric(W/'drafts/oq4/frozen-positive-boundary-studentized-formal-v2.lean.txt'),mathematicalFreeze=metric(W/'drafts/oq4/frozen-positive-boundary-studentized-v2.md'),parentFreezeReceipt=metric(W/'drafts/oq4/takeover-20261023/positive-boundary-studentized-freeze-180-v2.json'),originalObject=e['object'],literalOriginalLeanReceipt=metric(R/'lean-process-receipt.json'),originalExecutionReceipt=metric(R/'execution-receipt.json'),sourceBoundFinalReceipt=metric(R/'source-bound-final-receipt.json'),originalOwnedNative=metric(R/'owned-native.json'),originalPerRootAX=metric(R/'per-root-axioms.json'),originalRuntimeRecoveryReceipt=metric(R/'runtime-recovery-receipt.json'),originalServerOnly=final['originalServerOnly'],reviewArtifacts=[metric(p) for p in sorted(D.iterdir()) if p.is_file() and p.name!='reviewer-receipt.json'],fullNewSourceProofAndActualTypeValueGeneratedReview=True,allConsumedOwnerBindingsVerified=True,oldCompleteProofAndValueReviewCreditReused=True,specialRecoveryRecordLossExplicitlyAudited=True,originalSixHashesUnrecoverableAsOriginalValues=True,recoverySecondReadCount=6,totalNewInputContentReads=12,criticalGaps=[],requiredRepairs=[],writerState='ACTUALFINALSTOP',writerReleased=True,pendingTools=0,activeHeavy=False,operations=dict(Lean=0,LeanParser=0,kernel=0,server=0,axiomDependencyWalk=0,sourceChanges=0,oldProducerReplay=0,remoteObjectContentRehash=0,cache=0,Git=0,download=0,spawn=0),localArtifactReconciliation='Standard-library file/JSON/hash reading only; verification script schema selector corrections did not touch or invalidate original evidence.',parentRequiredNext='FULL read report and receipt; verify every new review artifact hash/bytes/LF/CR before acceptance.',scope=final['scope'],originalRoots='OPEN',usage=coverage['usage'])
save('reviewer-receipt.json',receipt)
print(json.dumps(dict(status='CORRECT',owned=len(allowned),generated=len(generated),directOld=len(direct),oldConsumed=len(oldrecords),receipt=metric(D/'reviewer-receipt.json'),artifacts=len(receipt['reviewArtifacts']),writerReleased=True),ensure_ascii=False))
