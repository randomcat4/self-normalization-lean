$ErrorActionPreference='Stop'
$reviewRoot='C:/game/shao lean/drafts/oq56/unit249/source-review-01'
$unitRoot='C:/game/shao lean/drafts/oq56/unit249'
$utf8=[System.Text.UTF8Encoding]::new($false,$true)
function ReadText([string]$p){$utf8.GetString([System.IO.File]::ReadAllBytes($p))}
function Bind([string]$p){$i=Get-Item -LiteralPath $p;@{path=$i.FullName.Replace('\','/');sha256=(Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash.ToLowerInvariant();bytes=$i.Length}}
function WriteJson([string]$name,$value){[System.IO.File]::WriteAllText($reviewRoot+'/'+$name,($value|ConvertTo-Json -Depth 30)+"`n",$utf8)}
$sourcePath=$unitRoot+'/author-01/OriginalSameWitnessPhysicalRelativeTailApplication.lean'
$source=Bind $sourcePath
if($source.sha256 -cne 'a81c0e0e50a16e3ee9ae06ef3d1ce8b82f4a0c6a97766320a1a529a2bfb245f5' -or $source.bytes -ne 240928){throw 'Reviewed source changed'}
$diagPath=$unitRoot+'/lead-execution-01/native-complete-diagnostic-projection.json'
$diag=(ReadText $diagPath)|ConvertFrom-Json -AsHashtable
$errorText=$diag['errors'][0]['completeMessage']
$errorHeader=$errorText.Split([string[]]@("`n`n"+[char]0x03A9+' :'),[StringSplitOptions]::None)[0]
$coverage=[ordered]@{
 schema='oq56-unit249-independent-complete-source-coverage-v1'
 atUTC=[DateTime]::UtcNow.ToString('o')
 role='/root/oq56_unit249_review'
 ownerChat='01a1822b-1815-7f21-a1af-2e0b15ee67a5'
 independent=$true
 neverAuthor=$true
 source=$source
 sourceLF=3824
 completeSourceToStatementProofReview=$true
 verdict='CRITICAL_GAPS'
 sourceAccepted=$false
 qualified=$false
 kernelChecked=$false
 axiomAudited=$false
 directReadSourceIntervalsInclusive=@(@(1,812),@(1520,1525),@(2232,2243),@(2945,2949),@(3201,3263),@(3511,3514),@(3749,3824))
 losslessRepeatedTypeIntervalsInclusive=@(
  @{name='hCg';source=@(813,1519);alreadyReadHead=@(38,744);context='N01'},
  @{name='hModel';source=@(1526,2231);alreadyReadHead=@(39,744);context='N01c'},
  @{name='hRetained248';source=@(2244,2944);alreadyReadHead=@(44,744);context='N01s'},
  @{name='hOldPayments248';source=@(2950,3200);alreadyReadHead=@(494,744);context='N01s'},
  @{name='hOldAtN248';source=@(3264,3510);alreadyReadHead=@(498,744);context='N03'},
  @{name='hOldAtCurrent248';source=@(3515,3748);alreadyReadHead=@(511,744);context='N04'}
 )
 normalizationRule='Only whitespace runs collapsed to one space and outer whitespace trimmed; all nonwhitespace characters and token boundaries preserved. Contexts restored separately; all unique proof text read.'
 allContextsRead=@('N00','N01','N01c','N01m','N01s','N02','N03','N04','N05','N06','N07')
 publicOrdinary=155
 optionalOrdinary=159
 allHave=28
 explicitlyTypedHave=27
 soleInferredHave='h248'
 allLexicalLet=730
 allLexicalLetI=8
 operativeLet=5
 operativeInstances=2
 frozenLetIntroductions=16
 choices=@{data=2;proofWitness=2;allChoose=4;chooseSpec=8}
 importedDefinitionTypesAndRHSRead=32
 originalSourcesReadComplete=@('C:/game/shao/current/oq56/inputs02/p51.md','C:/game/shao/current/oq56/inputs02/p54.md')
 APIContextReadComplete=$true
 APIContextLF=714
 originalP54RepairRetained=$true
 externalShaoZhouAttributionRetained=$true
 same248Witness=$true
 weightedFullPartialDeletedCostRetained=$true
 fixedRhoBeforeEventualN=$true
 genuinePaidPositiveAndNonempty=$true
 auxiliary236OnlyForNonempty=$true
 originalT0InR=$true
 physicalZeroBranchAndClosedEventRetained=$true
 psiDivision=$false
 costSmallnessPremiseAdded=$false
 rootOrCDFCompletionClaim=$false
 localCheck=Bind ($reviewRoot+'/LOCAL-BINDING-CHECK.json')
 authorExplanationFilesRead=$false
 reusedAcceptedProofs=@{unit248='Exact qualified evidence/source/public interface reused; old proof/TYPE/AX not replayed.';unit236='Exact qualified evidence and full public actual TYPE in API-CONTEXT reused; old proof/TYPE/AX not replayed.'}
 remainingUnreviewedUniqueSourceScope=@()
 newSuccessfulActualTYPERead=$false
 newRequiredVALUERead=$false
 newRecursiveAXRead=$false
 requestedModel='gpt-6.1-sol'
 requestedEffort='xhigh'
 actualBackend=$null
 actualModel=$null
 actualEffort=$null
 usage=@{input=$null;cachedInput=$null;output=$null;reasoningSubset=$null}
}
WriteJson 'COVERAGE.json' $coverage
$verdict=[ordered]@{
 schema='oq56-unit249-independent-source-verdict-first-sealed-version-v1'
 atUTC=[DateTime]::UtcNow.ToString('o')
 STATUS='CRITICAL_GAPS'
 source=$source
 sourceAccepted=$false
 qualified=$false
 completeIndependentSourceReview=$true
 mathematicalRoute='No further mathematical/source-fidelity gap found; submitted formal proof has the exact API mismatch below.'
 gaps=@(@{line=3768;column=6;fact='hPaymentLeOne';kind='FORMAL_API_UNIFICATION_FAILURE';sourceText='apply add_le_add_left';actualAPI='b <= c -> forall a, b+a <= c+a (AddRightMono)';requiredShape='A+B <= A+C';failure='The common summand is on the left, whereas this actual API adds its common summand on the right; the submitted apply does not unify.';diagnosticHeader=$errorHeader;messageSHA256=$diag['errors'][0]['messageSHA256']})
 nativeFailure=@{diagnostic=Bind $diagPath;actualRC=$diag['actualRC'];seconds=$diag['seconds'];receipt=$diag['receipt'];errorCount=$diag['errorCountDerived'];warningCount=$diag['warningCountDerived'];objectAfter=$diag['objectAfter'];allOwnedEnded=$diag['allOwnedEnded'];timedOut=$diag['timedOut'];preservationEqual=$diag['preservationEqual'];beforeAfterEqual=$diag['beforeAfterEqual'];ownershipIssue=$diag['ownershipIssue'];postError=$diag['postError'];cleanupEvents=$diag['cleanupEvents'];reviewerServerAccess=$false}
 changedProofOrStatementByReviewer=$false
 nextExactDependency='Same author minimal formal API repair; same independent role follows up on exact delta and then successful FIRSTO all actual owned TYPE/required VALUE/recursive AX. Old complete source coverage retained.'
 OQ56='OPEN'
 requestedModel='gpt-6.1-sol'
 requestedEffort='xhigh'
 actualModel=$null
 actualEffort=$null
 usage=@{input=$null;cachedInput=$null;output=$null;reasoningSubset=$null}
}
WriteJson 'VERDICT.json' $verdict
$inputs=@(
 $sourcePath,
 ($unitRoot+'/freeze-01/frozen-declaration.json'),
 ($unitRoot+'/freeze-01/FROZEN-PREAMBLE.txt'),
 ($unitRoot+'/freeze-01/FROZEN-HEAD.txt'),
 ($unitRoot+'/freeze-01/FROZEN-CLOSING.txt'),
 ($unitRoot+'/freeze-01/INTERFACE-INVENTORY.json'),
 ($unitRoot+'/freeze-01/NEW-RELATIVE-TAIL-CONTRACT.txt'),
 ($unitRoot+'/author-01/FACT-COORDINATES.json'),
 ($unitRoot+'/author-01/DECLARATION-COORDINATES.json'),
 ($unitRoot+'/author-01/MANIFEST.json'),
 ($unitRoot+'/author-01/lastzeroRELEASE.json'),
 ($unitRoot+'/parent-author-source-intake-01.json'),
 $diagPath,
 'C:/game/shao/current/oq56/inputs02/p51.md',
 'C:/game/shao/current/oq56/inputs02/p54.md',
 'C:/game/shao lean/drafts/oq56/unit248/qualified-evidence.json',
 'C:/game/shao lean/drafts/oq56/unit248/freeze-01/FROZEN-HEAD.txt',
 'C:/game/shao lean/drafts/oq56/unit236/qualified-evidence.json',
 'C:/game/shao lean/drafts/oq56/next-source/oq6-original-same-witness-physical-relative-tail-planned/author-stage1-01/API-CONTEXT.md',
 'C:/game/shao lean/drafts/oq56/next-source/oq6-original-same-witness-physical-relative-tail-planned/author-stage1-01/SOURCE-ROUTE.md'
)
$payloads=@('SOURCE-REVIEW.md','COVERAGE.json','VERDICT.json','LOCAL-BINDING-CHECK.json','check_local_bindings.ps1','finalize_source_stage.ps1')
$m=[ordered]@{
 schema='oq56-unit249-independent-source-stage-manifest-v1'
 atUTC=[DateTime]::UtcNow.ToString('o')
 role='/root/oq56_unit249_review'
 independent=$true
 STATUS='CRITICAL_GAPS'
 source=$source
 completeSourceReview=$true
 sourceAccepted=$false
 qualified=$false
 inputs=@($inputs|ForEach-Object {Bind $_})
 payloads=@($payloads|ForEach-Object {Bind ($reviewRoot+'/'+$_)})
 inputCountDerived=$inputs.Count
 payloadCountDerived=$payloads.Count
 releaseWrittenLast=$true
 noOldProofOrCheckReplay=$true
 requestedModel='gpt-6.1-sol'
 requestedEffort='xhigh'
 actualBackend=$null
 actualModel=$null
 actualEffort=$null
 usage=@{input=$null;cachedInput=$null;output=$null;reasoningSubset=$null}
}
WriteJson 'MANIFEST.json' $m
$release=[ordered]@{
 schema='oq56-unit249-independent-source-stage-sixzero-release-v1'
 atUTC=[DateTime]::UtcNow.ToString('o')
 role='/root/oq56_unit249_review'
 ownedRoot=$reviewRoot
 phase='COMPLETE_SOURCE_REVIEW_OF_FIRST_SEALED_VERSION'
 STATUS='CRITICAL_GAPS'
 source=$source
 manifest=Bind ($reviewRoot+'/MANIFEST.json')
 report=Bind ($reviewRoot+'/SOURCE-REVIEW.md')
 coverage=Bind ($reviewRoot+'/COVERAGE.json')
 verdict=Bind ($reviewRoot+'/VERDICT.json')
 sourceAccepted=$false
 qualified=$false
 stageWriterReleased=$true
 executionReleased=$true
 publicationReleased=$true
 childAuthorityReleased=$true
 sixZero=@{writers=0;heavyCommands=0;inflightExecution=0;pendingExternal=0;children=0;uncertainOperations=0}
 sixZeroScope='This review role only; all local tool commands returned; no claim about other lane/global/server process activity.'
 operations=@{Lean=0;lake=0;PP=0;AX=0;server=0;network=0;upload=0;Git=0;publication=0;children=0;Goal=0;schedule=0;sidebar=0}
 noFurtherWritesThisStage=$true
 contextRetainedForExplicitFollowup=$true
 nextExactDependency=$verdict.nextExactDependency
 requestedModel='gpt-6.1-sol'
 requestedEffort='xhigh'
 actualModel=$null
 actualEffort=$null
 usage=@{input=$null;cachedInput=$null;output=$null;reasoningSubset=$null}
}
WriteJson 'SOURCE-STAGE-RELEASE.json' $release
@{verdict='CRITICAL_GAPS';manifest=Bind ($reviewRoot+'/MANIFEST.json');report=Bind ($reviewRoot+'/SOURCE-REVIEW.md');coverage=Bind ($reviewRoot+'/COVERAGE.json');release=Bind ($reviewRoot+'/SOURCE-STAGE-RELEASE.json')}|ConvertTo-Json -Depth 5
