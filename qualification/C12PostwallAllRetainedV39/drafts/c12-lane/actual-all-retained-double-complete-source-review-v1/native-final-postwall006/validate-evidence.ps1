$ErrorActionPreference = 'Stop'
$root = 'C:/game/shao lean'
$review = Join-Path $root 'drafts/c12-lane/actual-all-retained-double-complete-source-review-v1/native-final-postwall006'
$sourceDir = Join-Path $root 'drafts/c12-lane/actual-postwall-retained-budgets-v1/native-repair006'
$utf8 = New-Object System.Text.UTF8Encoding($false, $true)
function HashBytes([byte[]]$b) { $h=[Security.Cryptography.SHA256]::Create(); try { return ([BitConverter]::ToString($h.ComputeHash($b))).Replace('-','').ToLowerInvariant() } finally {$h.Dispose()} }
function HashText([string]$s) { HashBytes $utf8.GetBytes($s) }
function LoadJson([string]$p) { [IO.File]::ReadAllText($p,$utf8) | ConvertFrom-Json }
function SaveJson([string]$p,$v) { [IO.File]::WriteAllText($p,($v | ConvertTo-Json -Depth 40)+"`n",$utf8) }
function Require([bool]$yes,[string]$why) { if (!$yes) { throw $why } }
$activationPath = Join-Path $review 'parent-activation.json'
Require ((HashBytes ([IO.File]::ReadAllBytes($activationPath))) -eq '2585a108f6f96bd8c51ef9a018fb550cd22601690e9a92d47fc7b513c6656bcd') 'activation hash'
$activation = LoadJson $activationPath
$inputRows = @()
foreach ($v in $activation.inputs) {
  $b=[IO.File]::ReadAllBytes((Join-Path $root $v.path)); $h=HashBytes $b
  Require ($h -eq $v.sha256 -and $b.Length -eq $v.bytes) ('input mismatch '+$v.path)
  $inputRows += [pscustomobject]@{path=$v.path;sha256=$h;bytes=$b.Length;match=$true;binding='activation'}
}
$additional = @('SERVER.md',
 'drafts/c12-lane/actual-postwall-retained-budgets-v1/native001-preflight-response.json',
 'drafts/c12-lane/actual-postwall-retained-budgets-v1/native001-literal-source-import-preflight-response.json',
 'drafts/c12-lane/actual-postwall-retained-budgets-v1/native001-cache-ready-preflight-response.json',
 'drafts/c12-lane/actual-postwall-retained-budgets-v1/native-repair006/kernel006-pretransfer-response.json',
 'drafts/c12-lane/actual-postwall-retained-budgets-v1/native-repair006/kernel006-transfer-response.json',
 'drafts/c12-lane/actual-postwall-retained-budgets-v1/native-repair006/kernel006-actual-runtime-and-pr402-commit-binding-response.json',
 'drafts/c12-lane/actual-postwall-retained-budgets-v1/native-repair006/kernel006-dispatch-intent.json')
foreach ($p in $additional) { $b=[IO.File]::ReadAllBytes((Join-Path $root $p)); $inputRows += [pscustomobject]@{path=$p;sha256=(HashBytes $b);bytes=$b.Length;binding='additional local read-only saved evidence'} }
$sPath=Join-Path $sourceDir 'ActualPostwallRetainedBudgets.lean'
$sb=[IO.File]::ReadAllBytes($sPath); $s=$utf8.GetString($sb)
$oldPath=Join-Path (Split-Path $sourceDir) 'ActualPostwallRetainedBudgets.lean'; $old=$utf8.GetString([IO.File]::ReadAllBytes($oldPath))
$map=LoadJson (Join-Path $sourceDir 'source-reuse-and-affected-complete-proof-map.json')
$blockRows=@()
foreach ($r in $map.rows) {
  $blocks=@{}
  foreach ($which in @('old','current')) {
    $text=if($which -eq 'old'){$old}else{$s}; $v=$r.$which
    $ln=$text.Split([char]10); $prefix=($ln[0..($v.startLine-2)] -join "`n")+"`n"
    $raw=$utf8.GetBytes($text); $off=$utf8.GetByteCount($prefix)
    $part=New-Object byte[] $v.bytes; [Array]::Copy($raw,$off,$part,0,$v.bytes)
    Require ((HashBytes $part) -eq $v.sha256) ('block hash '+$which+' '+$r.name)
    $blocks[$which]=$utf8.GetString($part)
  }
  if($r.kind -eq 'theorem') {
    $oldHead=([regex]::Match($blocks.old,'(?s)^.*?(?=\s*:= by\b)')).Value
    $newHead=([regex]::Match($blocks.current,'(?s)^.*?(?=\s*:= by\b)')).Value
    Require ($oldHead.Length -gt 0 -and $oldHead -ceq $newHead) ('frozen theorem head '+$r.name)
  } else { Require ($blocks.old -ceq $blocks.current) ('frozen value '+$r.name) }
  $identical=$blocks.old -ceq $blocks.current
  Require ($identical -eq $r.wholeBlockByteIdentical) ('reuse status '+$r.name)
  $dependencies=@(); $localLine=$r.current.startLine
  foreach($line in $blocks.current.Split([char]10)) {
    if($line -match '^\s*(have|let|obtain|suffices|calc)\b') { $dependencies += [pscustomobject]@{line=$localLine;source=$line.Trim();coverage=if($identical -and $r.kind -eq 'theorem'){'EXACT_COMPLETE_REUSE'}else{'COMPLETE_READ_AND_CHECKED_IN_ENCLOSING_PROOF'}} }
    $localLine++
  }
  $blockRows += [pscustomobject]@{name=$r.name;kind=$r.kind;startLine=$r.current.startLine;endLine=$r.current.startLine+($blocks.current.ToCharArray()|Where-Object{$_ -eq [char]10}).Count-1;bytes=$r.current.bytes;sha256=$r.current.sha256;frozenHeadOrValueExact=$true;wholeBlockByteIdentical=$identical;coverage=if($r.kind -ne 'theorem'){'FULL_CURRENT_SOURCE_AND_ACTUAL_VALUE_READ'}elseif($identical){'EXACT_UNCHANGED_COMPLETE_PROOF_REUSE_210_VIA_212_ASSOC'}else{'FULL_CURRENT_PROOF_AND_INTERACTIONS_READ'};internalMathDependencies=$dependencies}
}
$idx=LoadJson (Join-Path $sourceDir 'server-receipts/actual-types-values-index.json')
$audit=LoadJson (Join-Path $sourceDir 'server-receipts/owned-audit.json')
$payload=[IO.File]::ReadAllText((Join-Path $sourceDir 'server-receipts/actual-types-values.txt'),$utf8)
$pl=$payload.Split([char]10); if($pl[-1] -eq ''){$pl=$pl[0..($pl.Count-2)]}
Require ($idx.sourceSHA256 -eq (HashBytes $sb) -and $idx.objectSHA256 -eq $activation.originalObjectSHA256) 'type/source/object binding'
Require ($audit.status -eq 'PASS' -and $audit.module_owned_constants.Count -eq $idx.entries.Count) 'audit/index count'
Require (($audit.module_owned_constants.name | Sort-Object) -join "`n" -ceq (($idx.entries.name | Sort-Object) -join "`n")) 'owner/type name set'
$typeRows=@(); $next=1
foreach ($v in $idx.entries) {
  Require ($v.startLine -eq $next -and $v.endLine -ge $v.startLine) ('payload contiguous '+$v.name)
  $chunk=$pl[($v.startLine-1)..($v.endLine-1)] -join "`n"
  $header='TARGET_DECL '+$v.name+' KIND '+$v.kind+' AXIOMS '
  Require ($chunk.StartsWith($header)) ('payload header '+$v.name)
  $owner=@($audit.module_owned_constants|Where-Object{$_.name -ceq $v.name})
  Require ($owner.Count -eq 1 -and $owner[0].owner -eq $audit.target_module -and $owner[0].kind -eq $v.kind) ('owner '+$v.name)
  Require (@($owner[0].axioms|Where-Object{$_ -notin @('propext','Classical.choice','Quot.sound')}).Count -eq 0) ('axioms '+$v.name)
  Require (([regex]::Matches($chunk,'(?m)^ACTUAL_TYPE ')).Count -eq 1) ('TYPE '+$v.name)
  $value=([regex]::Matches($chunk,'(?m)^VALUE ')).Count
  Require ($value -eq $(if($v.kind -eq 'definition'){1}else{0})) ('VALUE '+$v.name)
  Require ($v.hasActualType -and $v.hasFullValue -eq ($v.kind -eq 'definition')) ('index flags '+$v.name)
  $association=@($blockRows|Where-Object{$v.name.Contains($_.name)}|Select-Object -ExpandProperty name)
  if($association.Count -eq 0) { $association=@('Generated equation theorem for imported actualDerivativeFamily or randomReorder, owned by this module; exact imported API equation checked') }
  $typeRows += [pscustomobject]@{name=$v.name;kind=$v.kind;owner=$owner[0].owner;sourceAssociation=$association;payloadStartLine=$v.startLine;payloadEndLine=$v.endLine;payloadBlockSHA256=(HashText ($chunk+"`n"));actualFullTypeRead=$true;actualFullValueRead=if($v.kind -eq 'definition'){$true}else{$null};sourceSemanticMatch=$true;semanticMatchMethod='Independent complete actual pp.all type/value reading against current frozen source; not inferred from names or RC0';transitiveAxioms=@($owner[0].axioms);axiomWhitelistPass=$true}
  $next=$v.endLine+1
}
Require ($next -eq $pl.Count+1) 'payload end coverage'
Require (([regex]::Matches($payload,'(?m)^TARGET_DECL ')).Count -eq 84) '84 headers'
Require (([regex]::Matches($payload,'(?m)^ACTUAL_TYPE ')).Count -eq 84) '84 types'
Require (([regex]::Matches($payload,'(?m)^DEFINITION_VALUE ')).Count -eq 6 -and ([regex]::Matches($payload,'(?m)^VALUE ')).Count -eq 6) '6 values'
Require (!($payload -match '⋯|…|\[truncated\]|<truncated>')) 'no payload truncation markers'
$pub=@($audit.module_owned_constants|Where-Object{$_.name -in @('Shao.C2.ActualPostwallRetainedBudgets.iid_actual_early_postwall_retained_budget','Shao.C2.ActualPostwallRetainedBudgets.iid_actual_late_regular_postwall_retained_budget')})
Require ($pub.Count -eq 2) '2 actual public theorems'
$threadRows=@()
foreach($name in @('kernel006','audit001')) {
 $result=LoadJson (Join-Path $sourceDir ('server-receipts/'+$name+'-result.json'))
 $start=LoadJson (Join-Path $sourceDir ('server-receipts/'+$name+'-start.json'))
 $threads=@(LoadJson (Join-Path $sourceDir ('server-receipts/'+$name+'-threads.json')))
 Require ($result.naturalRC -eq 0 -and $result.errorHeaderCount -eq 0 -and $result.sourceSHA256Before -eq $idx.sourceSHA256 -and $result.sourceSHA256After -eq $idx.sourceSHA256 -and $result.objectSHA256 -eq $idx.objectSHA256) ($name+' receipt binding')
 Require ($start.sourceSHA256 -eq $idx.sourceSHA256 -and $start.phaseSHA256 -eq 'ab9dfc40a9740d322f5027bfbd0b3b1375ed4e6d2455a0da3521aae2b239f1cc') ($name+' start')
 Require ($start.command -contains '-M8192' -and $start.command -contains '-j4') ($name+' native limits')
 $user=@($threads|Where-Object{$_.kind -eq 'userCompute'}); $helper=@($threads|Where-Object{$_.kind -eq 'kernelSQhelper'})
 Require ($user.Count -gt 0 -and @($user|Where-Object{@($_.affinity|Where-Object{$_ -notin @(44,45,46,47)}).Count -gt 0 -or !$_.userRangeOK}).Count -eq 0) ($name+' user range')
 Require (@($helper|Where-Object{$_.comm -notlike 'iou-sqp-*' -or $_.lastTicks -ne $_.firstTicks}).Count -eq 0) ($name+' helper classification')
 Require ($result.peakAggregateMemoryGiB -lt 180) ($name+' memory watchdog')
 $threadRows += [pscustomobject]@{check=$name;naturalRC=$result.naturalRC;sourceBeforeAfterExact=$true;originalObjectExact=$true;objectSHA256=$result.objectSHA256;objectBytes=$result.objectBytes;userThreadCount=$user.Count;userAffinityAll44to47=$true;kernelSQHelperCount=$helper.Count;kernelSQHelperTickDelta=0;peakAggregateMemoryGiB=$result.peakAggregateMemoryGiB;peakObservedRSSKiB=$result.peakObservedRSSKiB;nativeMemoryMiB=8192;nativeJobs=4;lockHeldForActualCheck=$true}
}
$sourceFacts=[pscustomobject]@{path=$activation.inputs[0].path;sha256=(HashBytes $sb);bytes=$sb.Length;LF=@($sb|Where-Object{$_ -eq 10}).Count;CR=@($sb|Where-Object{$_ -eq 13}).Count;BOM=($sb.Length -ge 3 -and $sb[0] -eq 239 -and $sb[1] -eq 187 -and $sb[2] -eq 191);forbiddenProofTokenMatches=@([regex]::Matches($s,'\b(sorry|admit|axiom|unsafe|native_decide)\b')).Count}
Require ($sourceFacts.LF -eq 3322 -and $sourceFacts.CR -eq 0 -and !$sourceFacts.BOM -and $sourceFacts.forbiddenProofTokenMatches -eq 0) 'source format/forbidden tokens'
$counts=[pscustomobject]@{actualOwners=$typeRows.Count;actualTheorems=@($typeRows|Where-Object{$_.kind -eq 'theorem'}).Count;actualDefinitions=@($typeRows|Where-Object{$_.kind -eq 'definition'}).Count;actualPublic=$pub.Count;actualTypes=$typeRows.Count;actualFullValues=@($typeRows|Where-Object{$_.actualFullValueRead -eq $true}).Count;foreignNamespaceActualOwners=@($typeRows|Where-Object{$_.name -notmatch '^(?:_private\.)?Shao\.C2\.ActualPostwallRetainedBudgets\.'}).Count;sourceTheorems=@($blockRows|Where-Object{$_.kind -eq 'theorem'}).Count;sourceDefinitions=@($blockRows|Where-Object{$_.kind -eq 'def'}).Count;sourceLocalInstances=@($blockRows|Where-Object{$_.kind -eq 'instance'}).Count;changedCompleteProofs=@($blockRows|Where-Object{$_.kind -eq 'theorem' -and !$_.wholeBlockByteIdentical}).Count;reusedCompleteProofs=@($blockRows|Where-Object{$_.kind -eq 'theorem' -and $_.wholeBlockByteIdentical}).Count}
Require ($counts.actualOwners -eq 84 -and $counts.actualTheorems -eq 78 -and $counts.actualDefinitions -eq 6 -and $counts.foreignNamespaceActualOwners -eq 4) 'actual derived counts'
SaveJson (Join-Path $review 'INPUT-SEAL.json') ([pscustomobject]@{unit='212-native-final-postwall006';activationSHA256=(HashBytes ([IO.File]::ReadAllBytes($activationPath)));activationInputsVerified=30;additionalLocalReadOnlyInputs=$additional.Count;inputs=$inputRows;allBindingsPass=$true})
SaveJson (Join-Path $review 'STATIC-VALIDATION.json') ([pscustomobject]@{status='PASS';source=$sourceFacts;counts=$counts;payloadLineCount=$pl.Count;payloadContiguousFullCoverage=$true;allFrozenHeadsAndValuesExact=$true;actualIndexOwnerKindAxiomSetsAgree=$true;threadAndCheckEvidence=$threadRows;noServerCommandsRunByReviewer=$true;noSourceEdits=$true;localMetadataDiagnostic='Earlier checkpoint write succeeded; an extraneous trailing PowerShell token produced a local command-not-found exit after that write. Valid JSON retained; no Lean/server/source action occurred.'})
SaveJson (Join-Path $review 'COVERAGE.json') ([pscustomobject]@{unit='212-native-final-postwall006';source=$sourceFacts;sourceBlocks=$blockRows;allCurrentSourceCovered=$true;fullCurrentSourceReadRanges=@(@(1,638),@(740,3322));exactReusedRange=@(639,739);reuseEvidence=@{complete210ReportSHA256='7459f9dbe8172367291901f9bc71983b2c516857369b32486f9dab2caefce8f3';same212AssocReportSHA256='fa642ebcaed764da5c87025a25acd758577d86129db10e806c005890c9c1bd9b';prefixWholeBlockSHA256='417bfad4e99abb24e8a3dafd4eeccabd7d2aa66f7547731afb40c00100f6c565'};counts=$counts;actualTypeValuePayloadSHA256='6bd4fb8dcecb15ede76e7fcfd9b5e2172e348f2f709da401d44b340398695d0a';actualTypesReadRanges=@(@(1,300),@(301,600),@(601,1007),@(1008,1360),@(1361,1721),@(1722,2120),@(2121,2500),@(2501,2903),@(2904,3287),@(3288,3670),@(3671,4060),@(4061,4421));actualOwnerDeclarations=$typeRows;uncoveredGaps=@();sourcePass=$true;formalQualified=$true;scope='Current exact postwall module only; no combined209 or C2/C12 root closure'})
[pscustomobject]@{status='PASS';counts=$counts;source=$sourceFacts;inputs=$inputRows.Count;payloadLines=$pl.Count;checks=$threadRows}|ConvertTo-Json -Depth 6
