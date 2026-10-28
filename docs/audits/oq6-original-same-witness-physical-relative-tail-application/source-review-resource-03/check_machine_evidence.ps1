$ErrorActionPreference='Stop'
$reviewRoot='C:/game/shao lean/drafts/oq56/unit249/source-review-resource-03'
$unitRoot='C:/game/shao lean/drafts/oq56/unit249'
$evidence=$unitRoot+'/owner-evidence-01'
$utf8=[Text.UTF8Encoding]::new($false,$true)
function Load([string]$p){$utf8.GetString([IO.File]::ReadAllBytes($p))|ConvertFrom-Json -AsHashtable}
function Bind([string]$p){$i=Get-Item -LiteralPath $p;@{path=$i.FullName.Replace('\','/');bytes=$i.Length;sha256=(Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash.ToLowerInvariant()}}
function SHA([string]$s){[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($utf8.GetBytes($s))).ToLowerInvariant()}
function Same($a,$b){($a|ConvertTo-Json -Compress -Depth 15)-ceq($b|ConvertTo-Json -Compress -Depth 15)}
function Require([bool]$ok,[string]$why){if(-not$ok){throw $why}}
$m=Load ($evidence+'/actual-owned-metadata.json')
$s=Load ($evidence+'/native-kernel-and-all-owner-audit-summary.json')
$b=Load ($evidence+'/server-metadata-binding.json')
$n=Load ($unitRoot+'/lead-execution-03/native-complete-diagnostic-projection.json')
$ap=Load ($unitRoot+'/lead-execution-03/audit-preparation-projection.json')
$rows=$m['entries']
Require ($rows.Count-eq 1 -and $m['actualOwnerCount']-eq 1 -and $m['allTheoremCount']-eq 1 -and $m['nonTheoremCount']-eq 0 -and $m['nonTheoremFullValueCount']-eq 0) 'Owner count gap'
Require ($s['actualOwned']-eq$rows.Count-and$s['actualTheorems']-eq$m['allTheoremCount']-and$s['actualNonTheorems']-eq$m['nonTheoremCount']-and$m['sourceDeclaredCount']-eq 1-and$m['publicSourceTheoremCount']-eq 1) 'Summary/source actual owner count mismatch'
Require ($m['ownerDiscovery']-ceq 'actual env.getModuleIdxFor? anchor then ALL env.constants without namespace filter') 'Owner discovery scope gap'
$full='';$axes=@();$names=@()
foreach($r in $rows){
 $name=($r['components']|ForEach-Object {$_['value']})-join '.'
 Require ($name-ceq$r['name']-and$name-ceq$m['anchor']) 'Owner name gap'
 Require ($r['isTheorem']-and$r['constantKind']-ceq'thmInfo'-and$r['bodyExpressionPresent']-and$r['levelParams'].Count-eq 1-and$r['levelParams'][0]-ceq'u') 'Owner kind/body/universe gap'
 $expected=[ordered]@{}
 foreach($k in @('axioms','bodyExpressionPresent','components','constantKind','isTheorem','levelParams','name')){$expected[$k]=$r[$k]}
 $json=$r['rawOwnedJSON']|ConvertFrom-Json -AsHashtable
 Require (Same $expected $json) 'Raw JSON reconstruction gap'
 Require (-not$r.Contains('value')) 'Unexpected VALUE requirement'
 Require ($r['typeLines']-eq([regex]::Matches($r['type'],"`n")).Count-and$r['typeLines']-eq 15262) 'TYPE line count gap'
 $full+='OQ56_OWNED_JSON '+$r['rawOwnedJSON']+"`n"
 $full+='OQ56_OWNED_TYPE '+$r['name']+' : '+$r['type']
 $axes+=@($r['axioms']);$names+=$r['name']
}
$full+=$m['rawOwnedCountLine']
Require ($m['rawOwnedCountLine']-ceq"OQ56_OWNED_COUNT 1`n") 'Raw owner count line gap'
$rawSHA=SHA $full;$rawBytes=$utf8.GetByteCount($full)
Require ($rawSHA-ceq$m['rawStdoutSHA256']-and$rawSHA-ceq$b['rawStdoutSHA256']-and$rawSHA-ceq$s['ownedAudit01']['stdout']['sha256']-and$rawBytes-eq$m['rawStdoutBytes']-and$rawBytes-eq 2411259) 'Whole original stdout reconstruction gap'
Require ((Get-Item -LiteralPath ($evidence+'/actual-owned-values.txt')).Length-eq 0) 'Nonempty VALUE file'
$axisSet=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
foreach($ax in $axes){[void]$axisSet.Add($ax)}
Require ($axes.Count-eq 3 -and $axisSet.SetEquals([string[]]@('propext','Classical.choice','Quot.sound'))) 'Unexpected transitive axiom'
Require ((Same $m['source'] $s['source'])-and(Same $m['source'] $b['source'])-and(Same $m['object'] $s['object'])-and(Same $m['object'] $b['object'])-and(Same $m['object'] $ap['object'])) 'Source/object exact tuple join gap'
Require ((Same $m['auditReceipt'] $s['ownedAudit01']['receipt'])-and(Same $m['auditReceipt'] $b['auditReceipt'])-and(Same $s['native03']['receipt'] $b['nativeReceipt'])) 'Receipt join gap'
$localSource=Bind ($unitRoot+'/author-resource-03/OriginalSameWitnessPhysicalRelativeTailApplication.lean')
Require ($localSource.sha256-ceq$m['source']['sha256']-and$localSource.bytes-eq$m['source']['bytes']-and$localSource.sha256-ceq'19c3e659b538c19d7e73a55bcaec1dc6727b435665e215890cc6c219c88704a0') 'Current exact source gap'
Require ($s['native03']['actualExitCode']-eq 0-and$s['ownedAudit01']['actualExitCode']-eq 0-and$n['exit_code']-eq 0-and$n['sourceErrors']-eq 0-and$s['allOwnedProcessesEnded']-and$n['all_owned_group_ended']-and$b['allOwnedEnded']) 'Actual execution success/end gap'
Require ($s['ownedAudit01']['no_o']-and$s['ownedAudit01']['own_object_import']-and$s['native03']['beforeAfterExact']-and$s['ownedAudit01']['beforeAfterExact']-and$n['beforeAfterEqual']-and$n['preservation_equal']) 'Original object/protection gap'
Require (-not$n['timed_out']-and$null-eq$n['ownership_issue']-and$null-eq$n['post_error']-and$n['cleanup_events'].Count-eq 0-and$n['final_live_owned_members'].Count-eq 0) 'Timeout/cleanup/ownership/live process gap'
Require ((SHA $n['rawStdout'])-ceq$s['native03']['stdout']['sha256']-and$utf8.GetByteCount($n['rawStdout'])-eq$s['native03']['stdout']['bytes']-and(SHA $n['rawStderr'])-ceq$s['native03']['stderr']['sha256']) 'Native complete diagnostic/log hash gap'
$sourceWarningHeaders=@([regex]::Matches($n['rawStdout'],'(?m)^Shao/.+?:\d+:\d+: warning:.*$')|ForEach-Object {$_.Value})
Require ($sourceWarningHeaders.Count-eq 60-and$n['sourceWarnings']-eq 60-and$s['native03']['sourceWarnings']-eq 60) 'Warning count gap'
Require (-not$s['native03']['strictWrapperSuccess']-and-not$s['ownedAudit01']['strictWrapperSuccess']-and-not$n['success']) 'Warning-sensitive wrapper state was changed'
$report=[ordered]@{
 schema='oq56-unit249-independent-complete-machine-evidence-join-v1'
 atUTC=[DateTime]::UtcNow.ToString('o')
 source=$localSource
 serverSource=$m['source']
 FIRSTO=$m['object']
 firstSuccessfulAttempt=3
 oldNativeFailuresPreserved=@('native01 RC1 formal API/no object','native02 RC1 finite cap/no object')
 native=$s['native03']
 audit=$s['ownedAudit01']
 ownerDiscovery=$m['ownerDiscovery']
 actualOwnerNames=$names
 actualOwned=1
 actualTheorem=1
 actualNonTheorem=0
 actualTYPELines=15262
 requiredVALUECount=0
 requiredVALUEBytes=0
 bodyExpressionPresent=$true
 levelParams=@('u')
 allTransitiveAxioms=$axes
 allRecursiveAxiomsWhitelisted=$true
 metadataRawOwnedJSONReconstructionExact=$true
 completeOriginalAuditStdoutReconstructed=@{bytes=$rawBytes;sha256=$rawSHA;matchesBoundOriginal=$true;rawLogNotSaved=$true}
 exactSourceObjectAndReceiptTupleJoin=$true
 nativeDiagnosticFullStdoutAndStderrHashVerified=$true
 warningHeaders=$sourceWarningHeaders
 warningBreakdown=@{styleTryThis=@($sourceWarningHeaders|Where-Object {$_-match 'warning: Try this:'}).Count;unusedBinderName=@($sourceWarningHeaders|Where-Object {$_-match 'warning: Variable name'}).Count;tacticLinter=@($sourceWarningHeaders|Where-Object {$_-match 'warning: (Unused tactic linter:|Used `tac1)'}).Count;existingEnvironmentStderr=([regex]::Matches($n['rawStderr'],'(?m)^warning:')).Count}
 strictWrapperSuccessPreserved=$false
 FIRSTEMPTY=$s['native03']['FIRSTEMPTY']
 FIRSTEMPTYIsReturnedRunnerField=$s['native03']['FIRSTEMPTYIsReturnedRunnerField']
 allOwnedEnded=$true
 noOldProducerCheckReplay=$true
 localLeanOrServerExecution=$false
 sourceProofAndNovelTYPEReadingRecordedInFinalReview=$true
 notAnAutomaticQualificationDecision=$true
}
[IO.File]::WriteAllText($reviewRoot+'/MACHINE-EVIDENCE-CHECK.json',($report|ConvertTo-Json -Depth 24)+"`n",$utf8)
@{actualOwned=1;TYPElines=15262;VALUEbytes=0;transitiveAxioms=$axes;rawAuditBytes=$rawBytes;rawAuditSHA=$rawSHA;nativeRC=0;auditRC=0;warningCount=$sourceWarningHeaders.Count;join='PASS'}|ConvertTo-Json
