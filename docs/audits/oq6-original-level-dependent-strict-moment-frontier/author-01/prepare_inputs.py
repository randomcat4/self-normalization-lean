from pathlib import Path
import hashlib, json
from datetime import datetime, timezone

root = Path('C:/game/shao lean')
out = root/'drafts/oq56/unit257/author-01'
def bind(p):
    b=p.read_bytes()
    return {'path':p.as_posix(),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'LF':b.count(b'\n')}
def save(name,x):
    (out/name).write_bytes((json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
expected={
 'drafts/oq56/unit257/freeze-01/frozen-declaration.json':('1638ec2044887cd2c81851a8910d5e0062ef1909d589081e203356d00ea1bae0',1995),
 'drafts/oq56/unit257/freeze-01/FROZEN-HEAD.txt':('2dc9f8a5c0e192638d9b8907c0ab5f66f8877d3b62962d087299c899115a26d0',35639),
 'drafts/oq56/unit257/freeze-01/ACTIVATION.json':('dc4ecf409e6b90a56e254769649c18be7250e60f069d4e48d1a2409cfae9050e',2257),
 'drafts/oq56/unit257/parent-qualified256-version-alignment.json':('69d9d85ef87bb4b600712d0a9f0b9d15e11b2c4bbdacda8723a944a0e9e51da2',2040),
 'drafts/oq56/unit256/qualified-evidence.json':('e052e31d745497938fa02c8f5875ea9904331a7a0a7ff93011dda97b000882c0',9469),
 'drafts/oq56/unit256/author-repair-01/OriginalLevelDependentLiteralWeightedConsumer.lean':('bbab19f1d8c091b81e3c06e7cfbc0dcc3c6acb16ce39261d0f08b2dc3ac1efcf',66823),
 'drafts/oq56/unit256/source-review-01/FINAL-REPORT.md':('e49f979337823631064e9cdb9e7d988a74bec9525c2052609ad53df168e11e1b',12613),
 'drafts/oq56/unit256/source-review-01/FINAL-VERDICT.json':('2688658bb9888b86ba1c2f726ae76865ae3758f173600b31b758cd95abf3b2b7',5730),
 'drafts/oq56/unit256/source-review-01/FINALWRITE.json':('d1bfcae488bb94c6192f38cef60ff14c2de77479966a67348d49878a1c8f1e83',3327),
}
inputs=[]
for rel,(sha,size) in expected.items():
    item=bind(root/rel)
    assert item['sha256']==sha and item['bytes']==size,item
    item['expectedBindingVerified']=True
    inputs.append(item)
extra=[
 root/'drafts/oq56/unit257/freeze-01/FROZEN-PREAMBLE.txt',
 root/'drafts/oq56/unit257/freeze-01/FROZEN-CLOSING.txt',
 root/'drafts/oq56/unit257/freeze-01/SOURCE-ROUTE.md',
 root/'library/Shao/OQ6/IIDSourceStrictMomentBudgets.lean',
 root/'library/Shao/OQ6/NormalizedStrictMomentBudgets.lean',
 root/'library/Shao/OQ6/OriginalSingleWitnessAnalyticStrictFrontier.lean',
 root/'library/Shao/Basic/TruncationBudget.lean',
 Path('C:/game/shao/current/oq56/inputs02/p51.md'),
 Path('C:/game/shao/current/oq56/inputs02/p54.md'),
 root/'coordination/integration-v149/original-t-relative-tail-cost-source-implication-review.md',
]
inputs += [bind(p) for p in extra]
save('INPUT-BINDINGS.json',{'schema':'unit257-author-input-bindings-v1','inputs':inputs})
save('READ_ACK.json',{
 'schema':'unit257-author-actual-complete-reading-ack-v1','atUTC':datetime.now(timezone.utc).isoformat(),
 'role':'/root/oq56_unit257_author','ownerChat':'01a1822b-1815-7f21-a1af-2e0b15ee67a5',
 'completeReads':['257 full preamble/head/closing/route/freeze/activation and qualified256-version-alignment',
   'qualified repaired256 complete 1053LF source; qualified-evidence; complete final report/verdict/last release',
   'IIDSourceStrictMomentBudgets entire contract and proof',
   'NormalizedStrictMomentBudgets entire contract and proof',
   'p51 full text','p54 full text','v149 original-T relative-tail/cost source implication full report'],
 'targetedReads':['OriginalSingleWitnessAnalyticStrictFrontier original g measurability/L2 and original-law integral transportation/projection-budget/joint eventual proof API, not its independent witness conclusion',
   'TruncationBudget scalar definition/nonnegative/continuous/quadratic bound',
   'SERVER.md complete; TEAM current integration/mechanical review constraints; REGISTRY current root/oq56 owner/model/lease; oq56 status current 256qualification/257activation',
   '256 author deterministic inventory scripts for source-only adaptation'],
 'skills':['math-theorem with prompt-library/openai-workflow/lean-verification','windows-shell7','windows-gbk-utf8'],
 'sameM0BeforeAllNCurrentZEpsilonPBudget':True,'qualified256Source':'bbab19f1d8c091b81e3c06e7cfbc0dcc3c6acb16ce39261d0f08b2dc3ac1efcf',
 'oldActualTYPEReread':False,'oldProofReviewCommissioned':False,'oldLeanAXReplay':False,
 'requestedModel':'gpt-6.1-sol','requestedEffort':'xhigh','freshContextRequested':True,
 'actualModel':None,'actualBackend':None,'actualEffort':None,
 'usage':{'input':None,'cachedInput':None,'output':None,'reasoningSubset':None},
 'LeanLakePPAXServerNetworkUploadGitAPIChildrenSidebarGoalScheduleOperations':0,
 'localReadTruncationsRepaired':['257 head overlap270-339 reread; 256source read1-260/261-520/521-800/801-1053; p51 full disjoint/overlap slices; old frontier targeted missed lines reread'],
 'pureStaticAuthor':True,'actualTYPE':None,'actualVALUE':None,'actualAX':None,'fullOQ56':'OPEN'
})
print(json.dumps({'verifiedInputBindings':len(inputs),'readACK':bind(out/'READ_ACK.json')},ensure_ascii=False))
