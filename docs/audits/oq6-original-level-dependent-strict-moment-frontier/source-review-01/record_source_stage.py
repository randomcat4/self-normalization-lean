from pathlib import Path
from datetime import datetime, timezone
import json
import hashlib
import sys

ROOT=Path('C:/game/shao lean')
OUT=ROOT/'drafts/oq56/unit257/source-review-01'
AUTHOR=OUT.parent/'author-01'
def bind(p):
    b=Path(p).read_bytes()
    return {'path':Path(p).as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'LF':b.count(b'\n')}
def load(p):
    return json.loads(Path(p).read_text(encoding='utf-8'))
def save(name,data):
    (OUT/name).write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
now=datetime.now(timezone.utc).isoformat()
runtime={'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','freshContextRequested':True,
 'actualModel':None,'actualBackend':None,'actualEffort':None,
 'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None}}
operations={x:0 for x in ('Lean','lake','PP','AX','server','network','upload','Git','API','children','sidebar','Goal','schedule')}
source=bind(AUTHOR/'OriginalLevelDependentStrictMomentFrontier.lean')
if sys.argv[1]=='ack':
    verification=load(OUT/'SOURCE-STATIC-VERIFICATION.json')
    save('LOCAL-READ-NOTES.json',{
     'schema':'unit257-independent-local-read-notes-v1','atUTC':now,
     'displayFailuresRepaired':[
      'Initial combined AGENTS/REGISTRY output was truncated; authoritative latest AGENTS selected sections, REGISTRY rootThread/model/reasoning/phase and successor activation were then read separately. No mathematical source relied on truncated output.',
      'Initial optional REGISTRY .lanes.oq56 returned null; actual owner and Root5 checked against successor ACTIVATION and current rootThread, not inferred from null.',
      'Initial BINDING-TYPES sample tried .allPatternBindings[0].bindings[0], a nonexistent nested property; null-array display error. Corrected to flat allPatternBindings; all199 records then reconciled.',
      'Default python invocation hit WindowsApps Store alias: Python was not found; no script ran. Reused existing bundled dependencies/python/python.exe with -X utf8; independent static verification exited0.'
     ], 'sourceMutations':0,'oldSourceOrEvidenceMutations':0,'newLeanOrAxiomFailures':None,
     'staticVerificationActual':'PASS_SOURCE_ONLY','operations':operations})
    save('READ-ACK.json',{
     'schema':'unit257-independent-actual-complete-source-reading-ack-v1','atUTC':now,
     'role':'/root/oq56_unit257_review','ownerChat':'01a1822b-1815-7f21-a1af-2e0b15ee67a5',
     'currentRoot':'01a17d3c-6dfd-7cc0-94ed-35d758a423a5','source':source,
     'completeNewSourceReads':[[1,265],[266,540],[541,731]],
     'frozenHead':bind(OUT.parent/'freeze-01/FROZEN-HEAD.txt'),
     'frozenHeadCompleteRead':'Entire517LF declaration is byte-identical to fully-read source14-530; independently checked assembly and every source byte.',
     'freezePreambleClosingRouteActivationAndVersionAlignmentComplete':True,
     'authorReportRouteProofStaticInventoryComplete':True,
     'localTypesRHSAndScopes':verification['sourceDeclarations'],
     'patternCommandAndBindingFullTypeReview':[verification['bindingCommands'],verification['patternNames']],
     'allInventorySlicesIndependentlyRoundtrip':verification['sourceSlicesRoundtrip'],
     'allStaticProducerContractsApplicationsAndRepeatedContextsExact':True,
     'largeRepeatedContractReadMethod':'Complete qualified256 declaration, packet/consumer, and generic result types reconciled to fully-read source/contracts; exact repeated let contexts compared rather than duplicated into model context.',
     'completeGenericContractAndProofReads':[
       bind(ROOT/'library/Shao/OQ6/IIDSourceStrictMomentBudgets.lean'),
       bind(ROOT/'library/Shao/OQ6/NormalizedStrictMomentBudgets.lean'),
       bind(ROOT/'library/Shao/Basic/TruncationBudget.lean')],
     'completeOriginalSourceReads':[
       bind('C:/game/shao/current/oq56/inputs02/p51.md'),
       bind('C:/game/shao/current/oq56/inputs02/p54.md'),
       bind(ROOT/'coordination/integration-v149/original-t-relative-tail-cost-source-implication-review.md')],
     'qualified256EvidenceReportVerdictReleaseCompleteRead':True,
     'qualified256Source':bind(ROOT/'drafts/oq56/unit256/author-repair-01/OriginalLevelDependentLiteralWeightedConsumer.lean'),
     'qualified256FullMathematicalContractRead':'Complete statement reconciled against identical retained packets of new source and complete producer declaration; accepted old proof and7912LFactualTYPE reused without repeat complete review.',
     'qualified256OldActualTYPERead':False,'oldCompleteProofReviewRepeated':False,
     'targetedAcceptedAPIs':[
       {'file':'library/Shao/OQ6/OriginalSingleWitnessAnalyticStrictFrontier.lean','ranges':[[286,355],[355,431],[431,575]],'purpose':'Original g measurability/L2, integral-map/integrable-comp, normalized budget and eventual-event API only; its other m0 existence result never applied.'},
       {'file':'library/Shao/OQ6/ActualPhysicalCompactCDF.lean','ranges':[[23,37]],'purpose':'Exact original-mu normalized p-moment truncation contract used by IID generic.'},
       {'file':'library/Shao/OQ6/NormalizedAnalyticCostLimits.lean','ranges':[[173,241]],'purpose':'Complete bearing contract and field alignment used by normalized generic.'}],
     'skillsRead':['math-theorem/SKILL.md','math-theorem/references/prompt-library.md','math-theorem/references/openai-workflow.md','math-theorem/references/lean-verification.md','windows-shell7/SKILL.md'],
     'actualAllInputPayloadHashesVerified':True,'operations':operations,'runtime':runtime,
     'qualified':False,'machinePending':True,'actualOwnerCount':None,'actualTYPE':None,'actualVALUE':None,'actualAX':None,
     'authorityRetainedForSameContextMachineReview':True,'FINALWRITEWritten':False})
    print(json.dumps({'readACK':bind(OUT/'READ-ACK.json'),'notes':bind(OUT/'LOCAL-READ-NOTES.json')},ensure_ascii=False))
else:
    intervals=[
      [1,13,'imports/options/namespaces'],[14,23,'all original outer assumptions'],
      [24,34,'originalg/r/rho and one pre-n/z/epsilon/p/budget witness'],
      [35,289,'entire retained255 packet'],[290,401,'all current-z consumer model/coding/cost definitions'],
      [402,489,'entire49-field qualified256 consumer'],[490,530,'complete new originalp-moment strict frontier declaration'],
      [531,544,'proof entry and original-space projection measurability/L2'],
      [545,578,'qualified256 application/witness/retention/same measures'],
      [579,594,'same packet measurability and id:PtoP0'],
      [595,612,'original-mu IID budget instantiation'],[613,648,'two integral/L1 transfers and everydelta/Lsum equality'],
      [649,664,'nonnegativity/rate/zero-beta transfer'],[665,693,'exact moment window and same-normalization strict limits'],
      [694,726,'joint eventual strict budgets/Q/cost/cubic-slack with one k0'],[727,731,'closure/blanklines/namespaces']]
    assert intervals[0][0]==1 and intervals[-1][1]==source['LF']
    assert all(intervals[i][1]+1==intervals[i+1][0] for i in range(len(intervals)-1))
    save('SOURCE-COVERAGE.json',{
     'schema':'unit257-independent-source-semantic-coverage-v1','atUTC':now,'source':source,
     'completeSourceIntervals':intervals,'all731SourceLinesCovered':True,
     'full517LFFreezePreserved':True,'all196LFProofRead':True,
     'readACK':bind(OUT/'READ-ACK.json'),'staticVerification':bind(OUT/'SOURCE-STATIC-VERIFICATION.json'),
     'localDeclarationsFullHeadersRHSScopes':198,'patternCommands':22,'patternBoundFullTypes':199,'roundtripSlices':220,
     'producerContracts':3,'producerApplications':5,'allStaticInventoriesNotMachinePP':True,
     'inputBindings':load(OUT/'SOURCE-STATIC-VERIFICATION.json')['allBindings'],
     'mathRiskChecklist':{
      'singleM0BeforeAllNCurrentZEpsilonPBudget':True,'whole255And49Field256Retained':True,
      'pMomentOnlyOriginalMeasurableSpaceAndMu':True,'noExtraMu0pMomentHypothesis':True,
      'twoSameFunctionIntegralAndIntegrabilityTransfers':True,'everyDelta0EqualsDeltaOriginal':True,'L0EqualsLOriginal':True,
      'zeroBetaBranchAndPositiveBetaExactWindow':True,'cWindowStrictSlackAndConstants':True,
      'sameNuXiYepsilonActualEta':True,'eachCoordinateAndFiniteSumLimits':True,
      'oneCommonEventualK0ForEachPositiveTauDelta':True,'partialDenominatorsFullI':True,
      'noAllFiniteOrZeroSlackStrengthening':True,'p54RepairFixedClip1CounterexampleExternalAttributionPreserved':True},
     'findings':[],'sourceAccepted':True,'qualified':False,'machinePending':True,
     'actualOwnerCount':None,'actualTYPE':None,'actualVALUE':None,'actualAX':None,'operations':operations})
    save('SOURCE-VERDICT.json',{
     'schema':'unit257-independent-source-stage-verdict-v1','atUTC':now,
     'STATUS':'CORRECT','stage':'SOURCE_ONLY','sourceAccepted':True,'qualified':False,'machinePending':True,
     'source':source,'report':bind(OUT/'SOURCE-REPORT.md'),'coverage':bind(OUT/'SOURCE-COVERAGE.json'),
     'completeSourceToStatementProofReview':True,'authorReviewerSeparated':True,
     'additionalPremises':False,'criticalGaps':[],'nonblockingMathematicalIssues':[],
     'requestedFrozenStatementOrProofChange':False,
     'scope':'Same current-z canonical witness, original-mu p-moment strict budgets, exact original-to-coded truncation budget equality, same-normalized coordinate/sum limits and common eventual k0 jointly with qualified256 analytic costs and positive-slack cubic bound.',
     'actualUpperCurrentPhysicalExternalEngineCDFRelativeDCFullOQ56RootClosureClaimed':False,
     'fullOQ56':'OPEN','root':'OPEN',
     'kernel':'PENDING_PARENT_FIRST_NEW_NATIVE','actualOwnerCount':None,'actualTYPE':None,'actualVALUE':None,'actualAX':None,
     'sameContextFinalMachineReviewPending':True,'authorityRetainedForMachineReview':True,'FINALWRITEWritten':False,
     'runtimeStateAfterSourcePacket':'SOURCE_COMPLETE_WAITING_FOR_PARENT_NEW257_SAME_FIRST_OBJECT_MACHINE_MATERIAL_NOT_RUNNING_PROOF',
     'operations':operations,'runtime':runtime})
    payload=[p for p in OUT.iterdir() if p.is_file() and p.name!='SOURCE-MANIFEST.json']
    save('SOURCE-MANIFEST.json',{
     'schema':'unit257-independent-source-stage-manifest-v1','atUTC':now,'source':source,
     'payload':[bind(p) for p in sorted(payload)],'payloadCount':len(payload),
     'sourceAccepted':True,'qualified':False,'machinePending':True,'FINALWRITEWritten':False,
     'authorityRetainedForSameContextMachineReview':True,
     'actualOwnerCount':None,'actualTYPE':None,'actualVALUE':None,'actualAX':None})
    print(json.dumps({'STATUS':'SOURCE_CORRECT_MACHINE_PENDING','manifest':bind(OUT/'SOURCE-MANIFEST.json'),
      'report':bind(OUT/'SOURCE-REPORT.md'),'verdict':bind(OUT/'SOURCE-VERDICT.json'),'coverage':bind(OUT/'SOURCE-COVERAGE.json')},ensure_ascii=False))
