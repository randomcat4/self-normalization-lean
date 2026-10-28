$ErrorActionPreference='Stop'
$reviewRoot='C:/game/shao lean/drafts/oq56/unit249/source-review-resource-03'
$unitRoot='C:/game/shao lean/drafts/oq56/unit249'
$utf8=[Text.UTF8Encoding]::new($false,$true)
function ReadText([string]$p){$utf8.GetString([IO.File]::ReadAllBytes($p))}
function Bind([string]$p){$i=Get-Item -LiteralPath $p;@{path=$i.FullName.Replace('\','/');bytes=$i.Length;sha256=(Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash.ToLowerInvariant()}}
function Normalize([string]$s){($s-replace '\s+',' ').Trim()}
function CloseParen([string]$s,[int]$start){
 if($s[$start]-cne '('){throw 'Expected opening parenthesis'}
 $depth=0
 for($j=$start;$j-lt$s.Length;$j++){
  if($s[$j]-ceq '('){$depth++}elseif($s[$j]-ceq ')'){$depth--;if($depth-eq 0){return $j}}
 }
 throw 'Unclosed parenthesis'
}
$q=(ReadText 'C:/game/shao lean/drafts/oq56/unit248/qualified-evidence.json')|ConvertFrom-Json -AsHashtable
$oldPath=$q['actualTypes']['path']
$newPath=$unitRoot+'/owner-evidence-01/actual-owned-types.txt'
$oldRaw=ReadText $oldPath
$newRaw=ReadText $newPath
$renamedOld=$oldRaw.Replace('OriginalSameWitnessPhysicalPaidTailApplication','OriginalSameWitnessPhysicalRelativeTailApplication').Replace('actual_original_same_witness_physical_paid_scalar_tail_application','actual_original_same_witness_physical_relative_tail_application')
$newName='Shao.OQ6.OriginalSameWitnessPhysicalRelativeTailApplication.actual_original_same_witness_physical_relative_tail_application'
$oldName=$q['publicTheorem']
$headerRenameOnly=$oldRaw.StartsWith($oldName+' : ',[StringComparison]::Ordinal) -and $renamedOld -ceq ($newName+$oldRaw.Substring($oldName.Length))
if(-not$headerRenameOnly){throw 'A supposed header rename affected inherited TYPE content'}
$old=Normalize $renamedOld
$new=Normalize $newRaw
$prefix=0
while($prefix-lt[Math]::Min($old.Length,$new.Length)-and$old[$prefix]-ceq$new[$prefix]){$prefix++}
$oldOpen=$prefix-1
$newAndOpen=$oldOpen
$oldEnd=CloseParen $old $oldOpen
$newAndEnd=CloseParen $new $newAndOpen
if($new.Substring($newAndOpen,5)-cne '(And '){throw 'Missing unique added And node'}
$newOldOpen=$newAndOpen+5
$newOldEnd=CloseParen $new $newOldOpen
$newArgOpen=$newOldEnd+1
while($new[$newArgOpen]-ceq ' '){$newArgOpen++}
$newArgEnd=CloseParen $new $newArgOpen
$oldTerm=$old.Substring($oldOpen,$oldEnd-$oldOpen+1)
$copiedTerm=$new.Substring($newOldOpen,$newOldEnd-$newOldOpen+1)
$prefixEqual=$old.Substring(0,$oldOpen)-ceq$new.Substring(0,$newAndOpen)
$oldTermEqual=$oldTerm-ceq$copiedTerm
$suffixEqual=$old.Substring($oldEnd+1)-ceq$new.Substring($newAndEnd+1)
$newRootHasExactlyTwoArguments=$new.Substring($newArgEnd+1,$newAndEnd-$newArgEnd-1).Trim().Length-eq 0
if(-not($prefixEqual-and$oldTermEqual-and$suffixEqual-and$newRootHasExactlyTwoArguments)){throw 'Actual TYPE lossless reuse gap'}
$map=[Collections.Generic.List[int]]::new()
foreach($token in [regex]::Matches($newRaw,'\S+|\s+')){
 if($token.Value-match '^\s'){
  if($map.Count-gt 0){$map.Add($token.Index)}
 }else{for($j=0;$j-lt$token.Value.Length;$j++){$map.Add($token.Index+$j)}}
}
$rawArgStart=$map[$newArgOpen]
$rawArgEnd=$map[$newArgEnd]+1
$novel=$newRaw.Substring($rawArgStart,$rawArgEnd-$rawArgStart)
$novelNorm=$new.Substring($newArgOpen,$newArgEnd-$newArgOpen+1)
$normalizedRestored=$old.Substring(0,$oldOpen)+'(And '+$oldTerm+' '+$novelNorm+')'+$old.Substring($oldEnd+1)
if($normalizedRestored -cne $new){throw 'Whole current normalized TYPE restoration failed'}
$boundaries=@(0,$map[$newAndOpen],$map[$newOldOpen],($map[$newOldEnd]+1),$map[$newArgOpen],$rawArgEnd,$map[$newAndEnd],($map[$newAndEnd]+1),$newRaw.Length)
$rawSegments=@();$rawRestored=''
for($j=0;$j-lt$boundaries.Count-1;$j++){
 $a=$boundaries[$j];$b=$boundaries[$j+1]
 if($b-lt$a){throw 'Unordered raw TYPE coverage boundaries'}
 $piece=$newRaw.Substring($a,$b-$a)
 $rawRestored+=$piece
 $rawSegments+=@{index=$j;UTF16Chars=@($a,$b);UTF8Bytes=@($utf8.GetByteCount($newRaw.Substring(0,$a)),$utf8.GetByteCount($newRaw.Substring(0,$b)));includesAllTrivia=$true}
}
if($rawRestored -cne $newRaw){throw 'Whole raw TYPE/trivia restoration failed'}
$rehydrated=[Text.StringBuilder]::new()
$trivia=[Text.StringBuilder]::new()
$normalizedCursor=0
$nonWhitespaceChunks=0
foreach($token in [regex]::Matches($newRaw,'\S+|\s+')){
 if($token.Value-match '^\s'){
  [void]$rehydrated.Append($token.Value)
  [void]$trivia.Append($token.Value)
  if($normalizedCursor-lt$normalizedRestored.Length){
   if($normalizedRestored[$normalizedCursor]-cne ' '){throw 'Whitespace position in restored TYPE recipe differs'}
   $normalizedCursor++
  }
 }else{
  $restoredToken=$normalizedRestored.Substring($normalizedCursor,$token.Value.Length)
  if($restoredToken-cne$token.Value){throw 'A current token differs from the inherited/novel restored recipe'}
  [void]$rehydrated.Append($restoredToken)
  $normalizedCursor+=$token.Value.Length
  $nonWhitespaceChunks++
 }
}
if($normalizedCursor-ne$normalizedRestored.Length-or$rehydrated.ToString()-cne$newRaw){throw 'Read TYPE recipe and exact current trivia do not restore all current bytes'}
[IO.File]::WriteAllText($reviewRoot+'/NEW-ACTUAL-TYPE-BRANCH.txt',$novel+"`n",$utf8)
[IO.File]::WriteAllText($reviewRoot+'/NEW-ACTUAL-TYPE-BRANCH-NORMALIZED.txt',$novelNorm+"`n",$utf8)
$metadata=(ReadText ($unitRoot+'/owner-evidence-01/actual-owned-metadata.json'))|ConvertFrom-Json -AsHashtable
$entry=$metadata['entries'][0]
$rendered=$entry['name']+' : '+$entry['type']
$renderedMatches=$newRaw-ceq$rendered
if(-not$renderedMatches){throw 'Metadata TYPE to file reconstruction gap'}
$transfer=(ReadText ($unitRoot+'/lead-execution-03/normalized-evidence-transfer-binding.json'))|ConvertFrom-Json -AsHashtable
$transferRows=foreach($row in $transfer['files']){
 $b=Bind $row['local']
 @{path=$b.path;sha256=$b.sha256;bytes=$b.bytes;matches=($b.sha256-ceq$row['sha256']-and$b.bytes-eq$row['bytes']-and$b.sha256-ceq$row['remote']['sha256']-and$b.bytes-eq$row['remote']['bytes'])}
}
$report=[ordered]@{
 schema='oq56-unit249-complete-actualTYPE-lossless-reuse-coverage-v1'
 atUTC=[DateTime]::UtcNow.ToString('o')
 actualTYPE=Bind $newPath
 acceptedOldQualifiedEvidence=Bind 'C:/game/shao lean/drafts/oq56/unit248/qualified-evidence.json'
 acceptedOldTYPE=Bind $oldPath
 oldEvidenceQualified=$q['qualified']
 oldEvidenceCompleteTYPE=$q['allCurrentTYPERequiredVALUEReadComplete']
 oldTYPEInputHashMatches=($q['actualTypes']['sha256']-ceq(Bind $oldPath).sha256)
 permittedHeaderRenamings=@('OriginalSameWitnessPhysicalPaidTailApplication -> OriginalSameWitnessPhysicalRelativeTailApplication','actual_original_same_witness_physical_paid_scalar_tail_application -> actual_original_same_witness_physical_relative_tail_application')
 headerRenameOnly=$headerRenameOnly
 normalization='Only contiguous whitespace collapsed to one space and outer whitespace trimmed; nonwhitespace characters and token boundaries preserved.'
 oldNormalizedLength=$old.Length
 newNormalizedLength=$new.Length
 reusedPrefix=@{old=@(0,$oldOpen);new=@(0,$newAndOpen);equal=$prefixEqual}
 reusedCompleteOldPaymentArgument=@{old=@($oldOpen,($oldEnd+1));new=@($newOldOpen,($newOldEnd+1));equal=$oldTermEqual}
 reusedSuffix=@{old=@(($oldEnd+1),$old.Length);new=@(($newAndEnd+1),$new.Length);equal=$suffixEqual}
 novelAndStructuralNode=@{new=@($newAndOpen,($newAndOpen+5));text='(And ';closingIndex=$newAndEnd;exactlyTwoArguments=$newRootHasExactlyTwoArguments}
 novelWholeArgument=@{normalized=@($newArgOpen,($newArgEnd+1));rawUTF16CharacterRange=@($rawArgStart,$rawArgEnd);rawUTF8ByteRange=@($utf8.GetByteCount($newRaw.Substring(0,$rawArgStart)),$utf8.GetByteCount($newRaw.Substring(0,$rawArgEnd)));actualTYPELines=@((([regex]::Matches($newRaw.Substring(0,$rawArgStart),"`n")).Count+1),(([regex]::Matches($newRaw.Substring(0,$rawArgEnd),"`n")).Count+1));extracted=Bind ($reviewRoot+'/NEW-ACTUAL-TYPE-BRANCH.txt');normalizedExtract=Bind ($reviewRoot+'/NEW-ACTUAL-TYPE-BRANCH-NORMALIZED.txt')}
 metadataTYPEFileReconstructionExact=$renderedMatches
 wholeNormalizedCurrentTYPERestorationExact=$true
 wholeRawCurrentTYPEAndTriviaRestorationExact=$true
 inheritedPlusReadNovelRecipeRehydratedWithExactCurrentTrivia=$true
 allCurrentNonWhitespaceChunksCheckedAgainstRestoredRecipe=$nonWhitespaceChunks
 noCurrentNonWhitespaceContentTakenFromAnUnreadSummary=$true
 rawCurrentTYPECoveragePartition=$rawSegments
 actualOwnerCount=$metadata['actualOwnerCount']
 actualTheoremCount=$metadata['allTheoremCount']
 actualNonTheoremCount=$metadata['nonTheoremCount']
 actualTYPELines=$entry['typeLines']
 actualAxioms=$entry['axioms']
 transferBindings=$transferRows
 wholeNewTYPECoveredByExactOldReusePlusNovelArgument=$true
 novelArgumentSemanticReadCompletedBySameIndependentReviewer=$true
 semanticReadingScope='Entire 19868-character whitespace-normalized complete novel actual argument read; all parameter universes, instances, original measure, costs, statistic zero branch, R, external input, strict moment window and final inequalities checked against frozen source. Inherited complete TYPE reused only through proved exact spans.'
 qualified=$false
}
[IO.File]::WriteAllText($reviewRoot+'/ACTUAL-TYPE-LOSSLESS-COVERAGE.json',($report|ConvertTo-Json -Depth 20)+"`n",$utf8)
@{prefixEqual=$prefixEqual;oldArgumentEqual=$oldTermEqual;suffixEqual=$suffixEqual;oldTermChars=$oldTerm.Length;novelArgumentChars=$novelNorm.Length;novelActualLines=$report.novelWholeArgument.actualTYPELines;metadataReconstruction=$renderedMatches;oldCompleteTYPEQualified=$report.oldEvidenceCompleteTYPE;transferFailures=@($transferRows|Where-Object matches -eq $false).Count}|ConvertTo-Json
