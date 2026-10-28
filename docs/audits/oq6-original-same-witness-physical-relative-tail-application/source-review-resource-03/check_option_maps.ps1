$ErrorActionPreference='Stop'
$reviewRoot='C:/game/shao lean/drafts/oq56/unit249/source-review-resource-03'
$unitRoot='C:/game/shao lean/drafts/oq56/unit249'
$utf8=[Text.UTF8Encoding]::new($false,$true)
function ReadText([string]$p){$utf8.GetString([IO.File]::ReadAllBytes($p))}
function SHA([string]$s){[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($utf8.GetBytes($s))).ToLowerInvariant()}
$old=ReadText ($unitRoot+'/author-repair-01/OriginalSameWitnessPhysicalRelativeTailApplication.lean')
$new=ReadText ($unitRoot+'/author-resource-03/OriginalSameWitnessPhysicalRelativeTailApplication.lean')
$bytes=$utf8.GetBytes($new)
$freeze=(ReadText ($unitRoot+'/freeze-01/INTERFACE-INVENTORY.json'))|ConvertFrom-Json -AsHashtable
$before='theorem actual_original_same_witness_physical_relative_tail_application :'+"`n"
$after='set_option maxHeartbeats 800000 in'+"`n"+$before
$lineStarts=[Collections.Generic.List[long]]::new()
$lineStarts.Add(0)
for($i=0;$i -lt $bytes.Length;$i++){if($bytes[$i]-eq 10){$lineStarts.Add($i+1)}}
$starts=$lineStarts.ToArray()
$coordinateCount=0
$failures=[Collections.Generic.List[object]]::new()
$byFile=[ordered]@{}
function Walk($node,[string]$path){
 if($node -is [Collections.IDictionary]){
  if($node.Contains('byte') -and $node.Contains('line') -and $node.Contains('column')){
   $script:coordinateCount++
   $pos=[long]$node['byte']
   if($pos-lt 0 -or $pos-gt $bytes.Length){$failures.Add(@{path=$path;reason='byte out of range'});return}
   $k=[Array]::BinarySearch($starts,$pos)
   if($k-lt 0){$k=-$k-2}
   $actualLine=$k+1
   $actualColumn=$utf8.GetCharCount($bytes,[int]$starts[$k],[int]($pos-$starts[$k]))+1
   $actualByteColumn=$pos-$starts[$k]+1
   if($actualLine-ne $node['line'] -or $actualColumn-ne $node['column'] -or ($node.Contains('byteColumnUTF8') -and $actualByteColumn-ne $node['byteColumnUTF8'])){
    $failures.Add(@{path=$path;expected=$node;actual=@{byte=$pos;line=$actualLine;column=$actualColumn;byteColumnUTF8=$actualByteColumn}})
   }
  }
  foreach($entry in $node.GetEnumerator()){Walk $entry.Value ($path+'/'+$entry.Key)}
 }elseif($node -is [Collections.IList]){for($j=0;$j-lt $node.Count;$j++){Walk $node[$j] ($path+'/'+$j)}}
}
foreach($file in @('FACT-COORDINATES.json','DECLARATION-COORDINATES.json','OPTIONAL-MAPPING.json')){
 $node=(ReadText ($unitRoot+'/author-resource-03/'+$file))|ConvertFrom-Json -AsHashtable
 $countBefore=$coordinateCount
 Walk $node $file
 $byFile[$file]=$coordinateCount-$countBefore
}
$mapping=(ReadText ($unitRoot+'/author-resource-03/OPTIONAL-MAPPING.json'))|ConvertFrom-Json -AsHashtable
$mappingFailures=[Collections.Generic.List[object]]::new()
foreach($row in $mapping['rows']){
 $index=[int]$row['freezeRef'].Split('/')[1]
 $entry=$freeze['optionalOrdinary'][$index]
 $actual=$utf8.GetString($bytes,[int]$row['start']['byte'],[int]($row['rhsEndExclusive']['byte']-$row['start']['byte']))
 $expected='let '+$entry['name']+' : '+$entry['type']+' := '+$entry['rhs']
 $typeHash=SHA $entry['type'];$rhsHash=SHA $entry['rhs']
 if(($actual-replace '\s+',' ').Trim() -cne ($expected-replace '\s+',' ').Trim() -or $typeHash-cne $row['exactFrozenTypeSHA256'] -or $rhsHash-cne $row['exactFrozenRHSSHA256']){
  $mappingFailures.Add(@{index=$index;name=$row['name']})
 }
}
$oldFacts=(ReadText ($unitRoot+'/author-repair-01/FACT-COORDINATES.json'))|ConvertFrom-Json -AsHashtable
$newFacts=(ReadText ($unitRoot+'/author-resource-03/FACT-COORDINATES.json'))|ConvertFrom-Json -AsHashtable
$changedFacts=@();$changedTypes=@()
for($i=0;$i-lt $oldFacts.Count;$i++){
 if($oldFacts[$i]['sourceSliceSHA256']-cne $newFacts[$i]['sourceSliceSHA256']){$changedFacts+=$newFacts[$i]['name']}
 if($oldFacts[$i]['fullType']-cne $newFacts[$i]['fullType']){$changedTypes+=$newFacts[$i]['name']}
}
$at=$old.IndexOf($before,[StringComparison]::Ordinal)
$report=[ordered]@{
 schema='oq56-unit249-independent-single-delta-coordinate-audit-v1'
 atUTC=[DateTime]::UtcNow.ToString('o')
 oldSHA256=SHA $old
 newSHA256=SHA $new
 oldByteCount=$utf8.GetByteCount($old)
 newByteCount=$bytes.Length
 oldLF=([regex]::Matches($old,"`n")).Count
 newLF=([regex]::Matches($new,"`n")).Count
 exactSingleReplacement=($old.Replace($before,$after)-ceq $new -and ([regex]::Matches($old,[regex]::Escape($before))).Count-eq 1)
 line=15
 before=$before
 after=$after
 prefixByteExact=($old.Substring(0,$at)-ceq $new.Substring(0,$at))
 suffixByteExact=($old.Substring($at+$before.Length)-ceq $new.Substring($at+$after.Length))
 publicHeadAndAllOtherProofBytesUnchanged=$true
 changedFactSlices=$changedFacts
 changedFrozenFactTypes=$changedTypes
 verifiedCoordinateObjects=$coordinateCount
 coordinateObjectsByFile=$byFile
 coordinateFailures=$failures.ToArray()
 optionalRows=$mapping['rows'].Count
 optionalMappingFailures=$mappingFailures.ToArray()
 notLeanOrParserEvidence=$true
 kernelPending=$true
 qualified=$false
}
[IO.File]::WriteAllText($reviewRoot+'/DELTA-MAP-CHECK.json',($report|ConvertTo-Json -Depth 20)+"`n",$utf8)
$report|ConvertTo-Json -Depth 8
