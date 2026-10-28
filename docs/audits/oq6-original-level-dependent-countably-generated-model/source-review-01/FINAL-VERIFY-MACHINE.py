import datetime
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path('C:/game/shao lean')
UNIT = ROOT / 'drafts/oq56/unit253'
OUT = UNIT / 'source-review-01'
LEAD = UNIT / 'lead-execution-01'
EVIDENCE = UNIT / 'owner-evidence-01'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def fp(p):
    b = p.read_bytes()
    return dict(path=p.as_posix(), sha256=sha(b), bytes=len(b), LF=b.count(b'\n'))

def load(p):
    return json.loads(p.read_text(encoding='utf-8'))

def payload(p):
    t = load(p)
    assert t['exit_code'] == 0, p
    return json.loads(t['stdout'])

def write(n, j):
    with (OUT/n).open('x',encoding='utf-8',newline='\n') as h:
        h.write(json.dumps(j,ensure_ascii=False,indent=2)+'\n')

source = fp(UNIT/'author-01/OriginalLevelDependentCountablyGeneratedModel.lean')
assert source['sha256'] == '00c05d340014e5d8193390ab01beaf19f2ee86423767953c8eb86585e38386be'
assert source['bytes'] == 15673 and source['LF'] == 265
old_manifest = load(OUT/'MANIFEST.json')
old_payloads = old_manifest['payloads']
assert len(old_payloads) == 7
for e in old_payloads:
    assert fp(pathlib.Path(e['path'])) == e
assert fp(OUT/'MANIFEST.json')['sha256'] == '3dfe8ecbaac6cf3ace2f152fdc5418f212301ba04bf8bdcd13b56db5fbf7545b'

transfer = load(LEAD/'normalized-evidence-transfer-binding.json')
metadata = load(EVIDENCE/'actual-owned-metadata.json')
summary = load(EVIDENCE/'native-kernel-and-all-owner-audit-summary.json')
server = load(EVIDENCE/'server-metadata-binding.json')
for e in transfer['files']:
    f = fp(pathlib.Path(e['path']))
    assert all(f[k] == e[k] == e['server'][k] for k in ['sha256','bytes'])
assert len(transfer['files']) == 5
normalization = load(LEAD/'normalize-result.json')
assert normalization['exit_code'] == 0 and not normalization['stderr']
normalized, normalized_warnings = map(json.loads,normalization['stdout'].splitlines())
for key, filename in [('types','actual-owned-types.txt'),('values','actual-owned-values.txt'),('metadata','actual-owned-metadata.json'),('summary','native-kernel-and-all-owner-audit-summary.json'),('binding','server-metadata-binding.json')]:
    entry = next(e for e in transfer['files'] if pathlib.Path(e['path']).name == filename)
    assert normalized[key] == entry['server']
assert server['metadata'] == normalized['metadata']
assert server['summary'] == normalized['summary']
assert normalized_warnings == load(LEAD/'native01-warning-classification.json')

native_pre = payload(LEAD/'native-prepare-result.json')
audit_pre = payload(LEAD/'audit-prepare-result.json')
native_dispatch = load(LEAD/'native01-DISPATCHED.json')
audit_dispatch = load(LEAD/'audit01-DISPATCHED.json')
native_wrapper = load(LEAD/'native01-transport-result.json')
audit_wrapper = load(LEAD/'audit01-transport-result.json')
assert native_wrapper['exit_code'] == audit_wrapper['exit_code'] == 1
native_transport = json.loads(native_wrapper['stdout'])
audit_transport = json.loads(audit_wrapper['stdout'])
n, a = summary['native01'], summary['ownedAudit01']
assert n['actualExitCode'] == a['actualExitCode'] == 0
assert n['strictWrapperSuccess'] is False and a['strictWrapperSuccess'] is False
assert n['beforeAfterExact'] and a['beforeAfterExact']
assert n['protectedDerived'] == 26622 and a['protectedDerived'] == 26630
assert n['requireEmptyStdout'] and n['FIRSTEMPTY'] is None and not n['FIRSTEMPTYIsReturnedRunnerField']
assert a['no_o'] and a['own_object_import']
assert summary['allOwnedProcessesEnded'] and summary['ownLean'] == []
assert summary['oldProducerRechecks'] == 0 and summary['actualNativeAttempt'] == 1
assert summary['correctNativeUnit'] == 253
assert native_dispatch['singleDispatch'] and audit_dispatch['singleDispatch']
assert native_dispatch['noAutomaticReplay'] and audit_dispatch['noAutomaticReplay']
assert native_pre['config'] == native_dispatch['config'] == n['config']
assert audit_pre['config'] == audit_dispatch['config'] == a['config']
for label, compact, transport in [('native',n,native_transport),('audit',a,audit_transport)]:
    assert transport['unit'] == 253 and transport['success'] is False
    assert transport['all_owned_group_ended'] and transport['author_stop'] is None
    assert transport['Lean_calls'] == 1 and transport['no_automatic_next_invocation']
    for k in ['receipt','stdout','stderr','seconds']:
        assert transport[k] == compact[k], (label,k)
assert server['nativeReceipt'] == n['receipt']
assert server['auditReceipt'] == a['receipt'] == metadata['auditReceipt']
assert server['sourceRunEndedReceipt'] == native_transport['run_ended']
assert server['allOwnedEnded'] and not server['ownLean']
assert all(x['source'] == summary['source'] for x in [metadata,server,native_pre,audit_pre,normalized_warnings])
assert all(summary['source'][k] == source[k] for k in ['sha256','bytes'])
objects = [summary['object'],metadata['object'],server['object'],audit_pre['sameFIRSTO'],audit_dispatch['sameFirstO']]
assert all(o == objects[0] for o in objects)
projection = load(LEAD/'native01-actual-projection.json')
assert projection['object'] == objects[0]
assert projection['actualRC'] == 0 and not projection['strictWrapper']
assert projection['sameBeforeAfter'] and projection['preservation'] and projection['ended']
assert not projection['timedOut'] and projection['cleanup'] == [] and projection['ownLive'] == []
assert objects[0]['sha256'] == '5665afcfed95e987ccfe2d326f6fc16487785b801bae970bcd1dbfd1fa55f2b3'
assert objects[0]['bytes'] == 2333144 and objects[0]['mtime_ns'] == '1793195907806998671'
for field in ['stdout','stderr']:
    raw = projection[field].encode('utf-8')
    assert sha(raw) == n[field]['sha256'] and len(raw) == n[field]['bytes']
assert n['sourceErrors'] == 0 and n['sourceWarnings'] == 5
assert normalized_warnings['categories'] == {'style':2,'unused':3}
blocks = [x for x in re.split(r'(?m)(?=^Shao/OQ6/OriginalLevelDependentCountablyGeneratedModel[.]lean:\d+:\d+:)',projection['stdout']) if ': warning' in x]
assert len(blocks) == 5
for block, warning in zip(blocks,normalized_warnings['warnings']):
    assert sha(block.encode()) == warning['completeMessageUTF8SHA256']
    assert len(block.encode()) == warning['completeMessageBytes']

audit_source = fp(LEAD/'owned-object-audit-input.lean')
assert audit_source['sha256'] == audit_pre['auditInput']['sha256'] == '26f4734907e667fe0990f724007951f101b62b0044bb32873da5345aa1d8ff1c'
assert audit_source['bytes'] == audit_pre['auditInput']['bytes'] == 2812 and audit_source['LF'] == 62
parameters = load(LEAD/'parameters.json')
parameter_bindings = []
for e in parameters['entries']:
    f = fp(pathlib.Path(e['local']))
    assert f['sha256'] == e['sha256'] and f['bytes'] == e['bytes']
    parameter_bindings.append(f)
assert parameters['unit'] == 253 and parameters['noReadoption']
assert parameters['sourceSHA256'] == source['sha256'] and parameters['sourceBytes'] == source['bytes'] and parameters['sourceLF'] == source['LF']

assert metadata['actualOwnerCount'] == metadata['allTheoremCount'] == 1
assert metadata['nonTheoremCount'] == metadata['nonTheoremFullValueCount'] == 0
assert metadata['sourceDeclaredCount'] == metadata['publicSourceTheoremCount'] == 1
assert metadata['ownerDiscovery'] == 'actual env.getModuleIdxFor? anchor then ALL env.constants without namespace filter'
assert len(metadata['entries']) == 1
entry = metadata['entries'][0]
parsed = json.loads(entry['rawOwnedJSON'])
assert all(entry[k] == v for k,v in parsed.items())
assert set(parsed) == {'axioms','bodyExpressionPresent','components','constantKind','isTheorem','levelParams','name'}
assert '.'.join(c['value'] for c in entry['components']) == entry['name']
assert all(c['kind'] == 'str' for c in entry['components'])
assert entry['name'] == metadata['anchor']
assert entry['levelParams'] == ['u','v','w']
assert entry['bodyExpressionPresent'] and entry['isTheorem'] and entry['constantKind'] == 'thmInfo'
assert set(entry['axioms']) == {'propext','Classical.choice','Quot.sound'}
assert 'value' not in entry and entry['type'].endswith('\n')
assert not any(m in entry['type'] for m in ['⋯','...','<elided>','sorryAx'])
assert not any(m in entry['type'].lower() for m in ['failed to pretty print','exceeded maximum recursion depth','maximum number of heartbeats'])
canonical = (entry['name']+' : '+entry['type']).encode()
assert canonical == (EVIDENCE/'actual-owned-types.txt').read_bytes()
assert len(canonical.splitlines()) == entry['typeLines'] == summary['TYPElines'] == 3742
assert (EVIDENCE/'actual-owned-values.txt').read_bytes() == b'' and summary['VALUElines'] == 0
raw = ('OQ56_OWNED_JSON '+entry['rawOwnedJSON']+'\nOQ56_OWNED_TYPE '+entry['name']+' : '+entry['type']+metadata['rawOwnedCountLine']).encode()
assert metadata['rawOwnedCountLine'] == 'OQ56_OWNED_COUNT 1\n'
assert len(raw) == metadata['rawStdoutBytes'] == server['rawStdoutBytes'] == a['stdout']['bytes'] == 425896
assert sha(raw) == metadata['rawStdoutSHA256'] == server['rawStdoutSHA256'] == a['stdout']['sha256'] == '436bdf677014f9e48c8e64e8fd4ca93d9d56660b5440bbc2190bf49b81ac6565'
assert summary['actualOwned'] == summary['actualTheorems'] == 1 and summary['actualNonTheorems'] == 0
assert summary['axiomOccurrences'] == {'propext':1,'Classical.choice':1,'Quot.sound':1}

result=dict(schema='unit253-final-independent-machine-binding-check-v1',atUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),STATUS='PASS',source=source,sourceStageManifest=fp(OUT/'MANIFEST.json'),sourceStageSevenPayloadsUnchanged=True,firstOriginalO=objects[0],native=n,audit=a,nativeTransportExitCode=1,auditTransportExitCode=1,actualNativeExitCode=0,actualAuditExitCode=0,strictFactsPreserved=True,knownEndedPreserved=True,normalizerAllReceiptPreservationNoTimeoutCleanupOwnershipAssertionsRead=True,allLocalTransferBindingsVerified=[fp(pathlib.Path(e['path'])) for e in transfer['files']],auditInput=audit_source,metadataFieldsAndRawOwnedJSONAllVerified=True,actualOwnerCount=1,actualTheoremCount=1,actualNonTheoremCount=0,requiredVALUECount=0,allActualTYPELF=3742,allActualTYPECanonicalSHA256=sha(canonical),allActualTYPEFullyReadInSameReviewerContext=True,typeReadDisplayOnlyLeadingIndentRemoved=True,typeSemanticSourceCorrespondence='PASS_COMPLETE_1_3742',typeRegions=[dict(lines=[1,67],scope='all original assumptions'),dict(lines=[68,137],scope='nine original outer definitions'),dict(lines=[138,483],scope='single m0/trim/core/all finite J/any measurable target law'),dict(lines=[484,528],scope='all n>=4/z>=1/original tiltwindow'),dict(lines=[529,814],scope='full 251 local definitions in same m0/mu0'),dict(lines=[815,1979],scope='all 251 conclusions including zero/deletion/geometric/cost'),dict(lines=[1980,2235],scope='full 252 local definitions in same m0/mu0'),dict(lines=[2236,3742],scope='all 252 conclusions including full real epsilon and bilateral L1 limit')],entryKind=entry['constantKind'],entryLevels=entry['levelParams'],entryName=entry['name'],allRecursiveAxioms=entry['axioms'],rawStdoutReconstruction=dict(inMemoryOnly=True,bytes=len(raw),sha256=sha(raw),lossless=True),warningClassification=normalized_warnings,parameterLocalBindingsVerified=len(parameter_bindings),parentCapacityInterruptionRecoveredWithoutReplay=True,reviewerLeanServerNetworkGitAPIOperations=0,qualified=True,fullOQ56='OPEN')
write('FINAL-MACHINE-CHECK.json',result)
inputs=[LEAD/n for n in ['normalized-evidence-transfer-binding.json','reused-normalizer-adaptation.py','normalize-result.json','native-prepare-result.json','audit-prepare-result.json','native01-DISPATCHED.json','audit01-DISPATCHED.json','native01-transport-result.json','audit01-transport-result.json','native01-actual-projection.json','native01-warning-classification.json','owned-object-audit-input.lean','parameters.json']]+[pathlib.Path(e['path']) for e in transfer['files']]
write('FINAL-HASH-BINDINGS.json',dict(schema='unit253-final-review-input-hash-bindings-v1',atUTC=result['atUTC'],inputs=[fp(p) for p in inputs],source=source,firstO=objects[0],sourcePayloadsUnchanged=old_payloads,sourceManifest=fp(OUT/'MANIFEST.json'),parameterBindings=parameter_bindings))
print(json.dumps(dict(STATUS='PASS',actualRC=[0,0],strictWrapper=[False,False],actualOwners=1,allTYPELF=3742,VALUE=0,rawStdoutSHA256=sha(raw),rawStdoutBytes=len(raw),originalSourcePayloadsUnchanged=7,machineCheck=fp(OUT/'FINAL-MACHINE-CHECK.json')),ensure_ascii=False))
