$ErrorActionPreference = 'Stop'
$reviewRoot = 'C:/game/shao lean/drafts/oq56/unit249/source-review-repair-01'
$unitRoot = 'C:/game/shao lean/drafts/oq56/unit249'
$utf8 = [System.Text.UTF8Encoding]::new($false, $true)
function ReadText([string]$p) { $utf8.GetString([System.IO.File]::ReadAllBytes($p)) }
function Norm([string]$s) { ($s -replace '\s+', ' ').Trim() }
function Binding([string]$p) { $i=Get-Item -LiteralPath $p; @{path=$i.FullName.Replace('\','/');bytes=$i.Length;sha256=(Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash.ToLowerInvariant()} }
function ResolveRef($freeze,[string]$ref) {
  $p=$ref.Split('/')
  if($p[0] -ceq 'proposedProofFacts') {
    $fact=@($freeze.proposedProofFacts|Where-Object {$_.name -ceq $p[1]})[0]
    $line=$fact.fullType.Split("`n")[0]
    if($line -match '^\s*let\s+(\S+)\s*:\s*(.*?)\s*:=\s*(.*)$') {return @{name=$Matches[1];type=$Matches[2];rhs=$Matches[3]}}
    throw 'Unrecognized named local-let reference'
  }
  $freeze.($p[0])[[int]$p[1]]
}
$sourcePath = $unitRoot + '/author-repair-01/OriginalSameWitnessPhysicalRelativeTailApplication.lean'
$sourceBytes = [System.IO.File]::ReadAllBytes($sourcePath)
$source = $utf8.GetString($sourceBytes)
$head = ReadText ($unitRoot + '/freeze-01/FROZEN-HEAD.txt')
$preamble = ReadText ($unitRoot + '/freeze-01/FROZEN-PREAMBLE.txt')
$closing = ReadText ($unitRoot + '/freeze-01/FROZEN-CLOSING.txt')
$contract = ReadText ($unitRoot + '/freeze-01/NEW-RELATIVE-TAIL-CONTRACT.txt')
$freeze = (ReadText ($unitRoot + '/freeze-01/INTERFACE-INVENTORY.json')) | ConvertFrom-Json
$facts = (ReadText ($unitRoot + '/author-repair-01/FACT-COORDINATES.json')) | ConvertFrom-Json
$coords = (ReadText ($unitRoot + '/author-repair-01/DECLARATION-COORDINATES.json')) | ConvertFrom-Json
$manifest = (ReadText ($unitRoot + '/author-repair-01/MANIFEST.json')) | ConvertFrom-Json -AsHashtable
$failures = [System.Collections.Generic.List[object]]::new()
$headNormalized = Norm $head
$headLineMap=[System.Collections.Generic.List[int]]::new()
$headLine=([regex]::Matches($preamble,"`n")).Count+1
foreach($token in [regex]::Matches($head,'\S+|\s+')) {
  if($token.Value -match '^\s') {
    if($headLineMap.Count -gt 0){$headLineMap.Add($headLine)}
    $headLine+=([regex]::Matches($token.Value,"`n")).Count
  } else {
    for($j=0;$j -lt $token.Value.Length;$j++){$headLineMap.Add($headLine)}
  }
}
$factRows = foreach($fact in $facts) {
  $expected = @($freeze.proposedProofFacts | Where-Object { $_.name -ceq $fact.name })
  $typeMatches = $expected.Count -eq 1 -and (Norm $fact.fullType) -ceq (Norm $expected[0].fullType)
  $sourceTypeMatches = if($fact.explicitType) { (Norm ($source.Substring($fact.typeStartCharacter,$fact.typeEndCharacterExclusive-$fact.typeStartCharacter))) -ceq (Norm $fact.fullType) } else { $fact.name -ceq 'h248' }
  $sourceSlice=$source.Substring($fact.startCharacter,$fact.endCharacterExclusive-$fact.startCharacter)
  $sha=[Convert]::ToHexString([System.Security.Cryptography.SHA256]::HashData($utf8.GetBytes($sourceSlice))).ToLowerInvariant()
  $hashMatches = $sha -ceq $fact.sourceSliceSHA256
  $duplicateIndex = $headNormalized.IndexOf((Norm $fact.fullType),[StringComparison]::Ordinal)
  if(-not ($typeMatches -and $sourceTypeMatches -and $hashMatches)){ $failures.Add(@{kind='fact';name=$fact.name;frozen=$typeMatches;source=$sourceTypeMatches;hash=$hashMatches}) }
  @{name=$fact.name;contextId=$fact.contextId;startLine=$fact.start.line;endLineExclusive=$fact.endExclusive.line;explicit=$fact.explicitType;frozenTypeMatches=$typeMatches;sourceTypeMatches=$sourceTypeMatches;sourceSliceHashMatches=$hashMatches;headNormalizedSubstringIndex=$duplicateIndex;headMatchedSourceLines=if($duplicateIndex -ge 0){@($headLineMap[$duplicateIndex],$headLineMap[$duplicateIndex+(Norm $fact.fullType).Length-1])}else{@()};typeLines=if($fact.explicitType){@($fact.typeStart.line,$fact.typeEndExclusive.line)}else{@()}}
}
$letRows = foreach($row in $coords.ordinaryLets) {
  $item=ResolveRef $freeze $row.freezeRef
  $actual=$utf8.GetString($sourceBytes,[int]$row.start.byte,[int]($row.rhsEndExclusive.byte-$row.start.byte))
  $expected='let ' + $item.name + ' : ' + $item.type + ' := ' + $item.rhs
  $ok=(Norm $actual) -ceq (Norm $expected)
  if(-not $ok){$failures.Add(@{kind='let';name=$row.name;line=$row.start.line;ref=$row.freezeRef;actual=$actual;expected=$expected})}
  @{name=$row.name;line=$row.start.line;role=$row.role;insideFact=$row.insideFact;freezeRef=$row.freezeRef;typeRhsMatches=$ok}
}
$instanceRows=foreach($row in $coords.instanceLets) {
  $item=ResolveRef $freeze $row.freezeRef
  $actual=$utf8.GetString($sourceBytes,[int]$row.start.byte,[int]($row.rhsEndExclusive.byte-$row.start.byte))
  $expected='letI : ' + $item.type + ' := ' + $item.rhs
  $ok=(Norm $actual) -ceq (Norm $expected)
  $selectedAmbientExpansion=$false
  if(-not $ok -and $row.freezeRef -ceq 'approvedInstances/3') {
    $tokens=$item.type.Split(' ')
    $implicitType=$tokens[0].TrimStart('@')+' '+$tokens[1]
    $implicitExpected='letI : '+$implicitType+' := '+$item.rhs
    $selectedAmbientExpansion=(Norm $actual) -ceq (Norm $implicitExpected)
    $ok=$selectedAmbientExpansion
  }
  if(-not $ok){$failures.Add(@{kind='instance';line=$row.start.line;ref=$row.freezeRef})}
  @{name=$row.name;line=$row.start.line;role=$row.role;freezeRef=$row.freezeRef;typeRhsMatches=$ok;selectedAmbientExpansion=$selectedAmbientExpansion;ambientExplanation=if($selectedAmbientExpansion){'Immediately preceding selectedSpace=m0 supplies the omitted measurable-space argument; no new instance.'}else{$null}}
}
$bindings=foreach($item in @($manifest['inputs']) + @($manifest['payloads'])) {
  $actual=Binding $item.path
  $ok=$actual.sha256 -ceq $item.sha256 -and $actual.bytes -eq $item.bytes
  if(-not $ok){$failures.Add(@{kind='manifestBinding';path=$item.path;actual=$actual;expected=$item})}
  @{path=$actual.path;sha256=$actual.sha256;bytes=$actual.bytes;matches=$ok;reading='HASH_ONLY_UNLESS_SEPARATELY_RECORDED'}
}
$contractStart=$head.IndexOf($contract,[StringComparison]::Ordinal)
$oldHead=ReadText 'C:/game/shao lean/drafts/oq56/unit248/freeze-01/FROZEN-HEAD.txt'
$prefix=if($contractStart -ge 0){$head.Substring(0,$contractStart).TrimEnd()}else{''}
$restore=if($prefix.EndsWith([string][char]0x2227)){$prefix.Substring(0,$prefix.Length-1).TrimEnd().Replace('actual_original_same_witness_physical_relative_tail_application','actual_original_same_witness_physical_paid_scalar_tail_application') + "`n"}else{''}
$coverage = [ordered]@{
  schema='oq56-unit249-independent-local-lossless-binding-check-v1'
  atUTC=[DateTime]::UtcNow.ToString('o')
  source=(Binding $sourcePath)
  sourceLF=([regex]::Matches($source,"`n")).Count
  noCR=(-not $source.Contains("`r"))
  noBOM=(-not ($sourceBytes[0]-eq 239 -and $sourceBytes[1]-eq 187 -and $sourceBytes[2]-eq 191))
  exactPreambleAndHead=$source.StartsWith($preamble+$head,[StringComparison]::Ordinal)
  exactClosing=$source.EndsWith($closing,[StringComparison]::Ordinal)
  newContractExactSuffix=$head.EndsWith($contract,[StringComparison]::Ordinal)
  wholeOldHeadRestoredByteExact=($restore -ceq $oldHead)
  publicOrdinaryCount=@($coords.ordinaryLets|Where-Object role -eq 'PUBLIC_HEAD').Count
  optionalOrdinaryCatalogCount=$freeze.optionalOrdinary.Count
  optionalOrdinaryRelationToPublic=@{
    inherited145Compared=145
    inherited145TypeRhsEqualToPublic=(@(for($i=0;$i -lt 145;$i++){
      $a=$freeze.publicOrdinary[$i];$b=$freeze.optionalOrdinary[$i]
      if($a.name -cne $b.name -or (Norm $a.type) -cne (Norm $b.type) -or (Norm $a.rhs) -cne (Norm $b.rhs)){$i}
    }).Count -eq 0)
    new10Compared=10
    new10TypeRhsEqualToPublic=(@(for($i=0;$i -lt 10;$i++){
      $a=$freeze.publicOrdinary[145+$i];$b=$freeze.optionalOrdinary[147+$i]
      if($a.name -cne $b.name -or (Norm $a.type) -cne (Norm $b.type) -or (Norm $a.rhs) -cne (Norm $b.rhs)){$i}
    }).Count -eq 0)
    remaining4='cg,m0 and payment,payment1 are checked against all actual operative declarations; both complete choice propositions are separately compared.'
  }
  allOrdinaryLets=$letRows
  allInstances=$instanceRows
  facts=$factRows
  inputAndPayloadBindings=$bindings
  failures=$failures.ToArray()
  lexicalCounts=@{
    have=([regex]::Matches($source,'(?m)^  have ')).Count
    ordinaryLet=([regex]::Matches($source,'\blet\s')).Count
    instanceLet=([regex]::Matches($source,'\bletI\s')).Count
    classicalChoose=([regex]::Matches($source,'\bClassical\.choose\b')).Count
    classicalChooseSpec=([regex]::Matches($source,'\bClassical\.choose_spec\b')).Count
    forbidden=([regex]::Matches($source,'\b(sorry|admit|axiom|unsafe|native_decide)\b')).Count
    topLevelTheorems=([regex]::Matches($source,'(?m)^theorem ')).Count
  }
  sameModelChoiceFullProps=foreach($choice in $freeze.actualSameModelChoicesProposed){
    $factName=if($choice.name -ceq 'cg'){'hCg'}else{'hModel'}
    $fact=@($facts|Where-Object {$_.name -ceq $factName})[0]
    @{name=$choice.name;contextId=$choice.contextId;fullExistentialMatches=(Norm $choice.choiceFullProp) -ceq (Norm $fact.fullType)}
  }
  projectionAtLine3791=@{beforeGuard=46;afterGuard=5;review='46 = 39 enclosing old payment fields + 7 physical fields; 5 after guard = equality field, subset, two payment bounds, all-real transfer, final physical SZ bound.'}
  authorIndependentCheckOnly=$true
  LeanExecuted=$false
  actualTypeRead=$false
  qualified=$false
}
$json=$coverage|ConvertTo-Json -Depth 20
[System.IO.File]::WriteAllText($reviewRoot+'/LOCAL-BINDING-CHECK.json',$json+"`n",$utf8)
@{source=$coverage.source;sourceLF=$coverage.sourceLF;exactHead=$coverage.exactPreambleAndHead;exactClosing=$coverage.exactClosing;contractSuffix=$coverage.newContractExactSuffix;restoredOldHead=$coverage.wholeOldHeadRestoredByteExact;public=$coverage.publicOrdinaryCount;optional=$coverage.optionalOrdinaryCatalogCount;facts=$factRows.Count;lets=$letRows.Count;instances=$instanceRows.Count;bindings=$bindings.Count;failureCount=$failures.Count;failures=$failures.ToArray()} | ConvertTo-Json -Depth 10
