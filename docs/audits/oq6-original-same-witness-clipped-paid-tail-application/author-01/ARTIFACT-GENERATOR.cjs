/* Pure local unit247 source/artifact authoring. No Lean, network, child or process API. */
'use strict';
const fs = require('fs');
const crypto = require('crypto');
const path = require('path');
const root = 'C:/game/shao lean';
const own = root + '/drafts/oq56/unit247/author-01';
const base = root + '/drafts/oq56/unit247';
const read = p => fs.readFileSync(p, 'utf8');
const sha = b => crypto.createHash('sha256').update(b).digest('hex');
const bind = p => ({path: p, sha256: sha(fs.readFileSync(p)), bytes: fs.statSync(p).size});
const assert = (p, msg) => { if (!p) throw new Error(msg); };
const put = (name, s) => {
  const p = path.resolve(own, name);
  assert(p.startsWith(path.resolve(own) + path.sep), 'ownership');
  assert(!s.includes('\r') && !s.startsWith('\uFEFF'), 'UTF8 no BOM LF');
  fs.writeFileSync(p, s, 'utf8');
};
const json = (name, v) => put(name, JSON.stringify(v, null, 2) + '\n');
const activationPath = base + '/implementation-activation-01/ACTIVATION.json';
assert(!fs.existsSync(own+'/lastzeroRELEASE.json'),'FINALWRITE already sealed; no further author writes');
const activation = JSON.parse(read(activationPath));
assert(bind(activationPath).sha256 === 'ed955f81f097872adc2c7a5d58f88b9c020fe1ce2221fe2b8731028cf12bb63f', 'activation');
assert(activation.inputs.length === 55, 'input count');
for (const i of activation.inputs) {
  const b = bind(i.path);
  assert(i.sha256 === b.sha256 && i.bytes === b.bytes, 'immutable input changed: ' + i.path);
}
const supplementPath=base+'/lead-nat-order-api-freeze-01/FROZEN-API-SUPPLEMENT.json';
assert(bind(supplementPath).sha256==='660a22aa20fed39767bab4a1382a86a62d5f866383f252cda2a3a55f0c4d55c6','Nat API supplement');
const supplement=JSON.parse(read(supplementPath));
const supplementInputs=[bind(supplementPath),supplement.primaryRead,supplement.ambientRead,supplement.completeDeclarations];
for(const i of supplementInputs){const b=bind(i.path);assert(i.sha256===b.sha256&&i.bytes===b.bytes,'Nat supplement input');}
const provisionalPath=own+'/PROVISIONAL-SOURCE-831b25e1.txt';
if(!fs.existsSync(provisionalPath)) {
  const prior=read(own+'/OriginalSameWitnessClippedPaidTailApplication.lean');
  assert(sha(prior)==='831b25e1c03689603aa062b86780377700fac0cf26df35f004bce71aa8f0aab2','prior authored source');
  put('PROVISIONAL-SOURCE-831b25e1.txt',prior);
}
const release = JSON.parse(read(activation.priorStage1ExclusiveWriterRelease.path));
assert(release.FINALWRITE && release.noFurtherWritesAfterThisRelease &&
  Object.values(release.sixZero).every(x => x === 0), 'old author final zero release');
const inv = JSON.parse(read(base + '/freeze-01/INTERFACE-INVENTORY.json'));
const pre = read(base + '/freeze-02/FROZEN-PREAMBLE.txt');
const head = read(base + '/freeze-02/FROZEN-HEAD.txt');
const close = read(base + '/freeze-02/FROZEN-CLOSING.txt');
const initial = read(base + '/freeze-02/FROZEN-INITIAL-INTRO.txt');
const call = read(base + '/freeze-03/FROZEN-H246-CALL.txt');
const facts = inv.proofFactTypeDictionary;
const dedent = s => {
  const a = s.trim().split('\n');
  const n = Math.min(...a.slice(1).filter(x => x.trim()).map(x => x.search(/\S/)));
  return a[0] + '\n' + a.slice(1).map(x => x.slice(n)).join('\n');
};
const unparen = s => s.trim().startsWith('(') ? s.trim().slice(1, -1).trim() : s.trim();
const splitAnd = s => {
  const out = []; let depth = 0; let start = 0;
  for (let i = 0; i < s.length; ++i) {
    if ('([{'.includes(s[i])) ++depth;
    if (')]}'.includes(s[i])) --depth;
    assert(depth >= 0, 'delimiter underflow');
    if (s[i] === '∧' && depth === 0) { out.push(s.slice(start, i).trim()); start = i + 1; }
  }
  assert(depth === 0, 'delimiter tail'); out.push(s.slice(start).trim()); return out;
};
const universal = unparen(facts.hUniversal246.type);
const uniPointStart = universal.indexOf('(∀ i : Fin n, Measurable[mAugLocal');
assert(uniPointStart > 0, 'universal point marker');
const uniLetsStart = universal.indexOf('let mN :');
const uniLets = universal.slice(uniLetsStart, uniPointStart);
const uniPoint = universal.slice(uniPointStart);
const uniConj = splitAnd(uniPoint);
const payment = unparen(facts.hPayment246.type);
const paymentAtN = payment.slice(payment.indexOf('4 ≤ n ∧'));
const payPointStart = paymentAtN.indexOf('Measurable[mN₀, borel ℝ] V0 ∧');
const payLetsStart = paymentAtN.indexOf('let mN :');
const payLets = paymentAtN.slice(payLetsStart, payPointStart);
const payPoint = paymentAtN.slice(payPointStart);
const payConj = splitAnd(payPoint);
const newPayPoint = head.slice(head.indexOf('        Measurable[mN₀, borel ℝ] V0 ∧', head.indexOf('      (∀ (Cenv'))).trim().slice(0,-1);
const newPayConj = splitAnd(newPayPoint);
const propContext = inv.declarationContexts;
const actualPublicTypePath = root + '/drafts/oq56/unit246/normalized-owner-evidence-02/public-full-type.txt';
const dictPath = root + '/drafts/oq56/unit246/lead-final-type-packet-01/TYPE-LOSSLESS-DICTIONARY.json';
const dict = JSON.parse(read(dictPath));
const expand = t => typeof t === 'string' ? [t] : dict.dictionary[t.ref].flatMap(expand);
const tokens = dict.main.flatMap(expand);
assert(tokens.length === dict.triviaBeforeEachExpandedToken.length, 'dictionary token count');
const roundtrip = tokens.map((t,i) => dict.triviaBeforeEachExpandedToken[i]+t).join('') + dict.trailingTrivia;
assert(roundtrip === read(root + '/drafts/oq56/unit246/normalized-owner-evidence-01/actual-owned-types.txt'), 'dictionary exact round trip');
const actualPublicType = read(actualPublicTypePath);
const publicLabel = 'Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application : ';
assert(roundtrip.startsWith(publicLabel + actualPublicType), 'complete actual public prefix binding');
const producerHead = inv.declarationContexts.producer246CompleteHead;
assert(facts.h246.type.trim() === read(base + '/freeze-03/EXPECTED-H246-PROP.txt').trim(), 'exact expected producer Prop');
assert(inv.ordinaryBindings.length === 141 && inv.optionalProofOrdinaryCount === 145 && inv.instanceInventory.length === 6 && Object.keys(facts).length === 33, 'approved inventory');
if (process.argv.includes('--inspect')) {
  console.log(JSON.stringify({inputs:55, roundtripExact:true, actualPublicTypeBytes:Buffer.byteLength(actualPublicType),
    ordinary:141, optional:145, instances:6, facts:33,
    universalConjuncts:uniConj.map((x,i)=>({index:i+1,first:x.split('\n')[0]})),
    paymentConjuncts:payConj.map((x,i)=>({index:i+1,first:x.split('\n')[0]})),
    newPaymentConjuncts:newPayConj.length}, null, 2));
  process.exit(0);
}
const indent = (s, n) => s.split('\n').map(x => ' '.repeat(n)+x).join('\n');
const proj = (name, i, total) => name + '.2'.repeat(i-1) + (i < total ? '.1' : '');
assert(uniConj.length === 71 && payConj.length === 38 && newPayConj.length === 39, 'derived conjunct counts');
assert(uniConj[67].includes('projectionV n g') && uniConj[69].includes('∃ k0 : ℕ'), 'universal selected projections');
assert(newPayConj.slice(0,37).every((x,i)=>x===payConj[i]) && newPayConj[38]===payConj[37], 'old payment conjunctions retained');
const at512 = s => s.replace(/\bC0\b/g, '512');
const tailClause = unparen(uniConj[69]);
const jointMarker = '∃ k0 : ℕ, ';
const jointAll = tailClause.slice(tailClause.indexOf(jointMarker)+jointMarker.length);
assert(jointAll.startsWith('∀ (k : ℕ), k0 ≤ k →'), 'complete joint all cutoff');
const jointPoint = jointAll.slice(jointAll.indexOf('→')+1).trim();
assert(splitAnd(jointPoint).length === 20, 'joint twenty clauses');
const wholeJointAllType = at512(uniLets + jointAll);
const uniCall = '(hUniversal246 n hPaymentAtN.1 (512 : ℝ) (by norm_num) z (by linarith only [hz]))';
const tailAtInput = '(' + proj(uniCall,70,71) + ' C1 C2 C3 C4 hSZcBudget hz hzMomentWindow)';
const publicRows = inv.ordinaryBindings;
const paymentRows = publicRows.filter(x=>x.scope.startsWith('newPayment:') || x.new === true);
assert(paymentRows.length === 47, 'payment public mirror count');
const factLines = [];
const packageLines = [];
const ordinaryLines = [];
let source = pre + head + ' := by\n' + initial + call + '  intro g r v rho β cWindow\n';
const lineNow = () => source.split('\n').length;
const add = s => { source += s; };
const have = (name, proof, level=2, actualName=name) => {
  const type = facts[name].type;
  const start = lineNow();
  add(' '.repeat(level) + 'have ' + actualName + ' :\n' + indent(type.trim(),level+4) + ' :=\n' + indent(proof,level+2) + '\n');
  factLines.push({frozenName:name,name:actualName,type,sourceStartLine:start,sourceEndLine:lineNow()-1});
};
have('hCg', 'h246.2.2.2.2.2.2');
ordinaryLines.push({name:'cg',startLine:lineNow()}); add('  let cg : ℝ := Classical.choose hCg\n');
have('hcgpos','(Classical.choose_spec hCg).1');
have('hModel','(Classical.choose_spec hCg).2');
ordinaryLines.push({name:'m₀',startLine:lineNow()}); add('  let m₀ : MeasurableSpace Ω := Classical.choose hModel\n');
have('hm₀','Classical.choose (Classical.choose_spec hModel)');
have('hCountableGeneration','Classical.choose (Classical.choose_spec (Classical.choose_spec hModel))',2,'hcg');
add('  refine ⟨h246.1, h246.2.1, h246.2.2.1, h246.2.2.2.1,\n' +
    '    h246.2.2.2.2.1, h246.2.2.2.2.2.1, cg, hcgpos, m₀, hm₀, hcg, ?_⟩\n' +
    '  intro μ₀\n' +
    '  letI : MeasurableSpace Ω := m₀\n' +
    '  letI : @MeasurableSpace.CountablyGenerated Ω m₀ := hcg\n');
have('hμ₀Probability','(Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hModel))).1');
have('hUniversal246','(Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hModel))).2.1');
have('hPayment246','(Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hModel))).2.2');
add('  refine ⟨hμ₀Probability, hUniversal246, ?_⟩\n' +
    '  intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv\n' +
    '  refine (hPayment246 Cenv aenv t0 Menv hCenv haenv ht0 hMenv).mono ?_\n' +
    '  intro n\n');
const atNStart = lineNow();
add('  refine fun (hPaymentAtN :\n' + indent(paymentAtN,6) + ') => ?_\n');
packageLines.push({name:'hPaymentAtN',type:paymentAtN,sourceStartLine:atNStart,sourceEndLine:lineNow()-1,
  kind:'Exact whole per-n producer payment proposition, explicit logical implication binder'});
add('  refine ⟨hPaymentAtN.1, ?_⟩\n' +
    '  intro w hW hWR hSq hSqBound hEnv z hz hzWindow\n');
for(let i=0;i<paymentRows.length;i+=10) add('  intro ' + paymentRows.slice(i,i+10).map(x=>x.name).join(' ')+'\n');
const ppStart = lineNow();
add('  have hPointPayment :\n' + indent(payPoint,6) + ' :=\n' +
    '    hPaymentAtN.2 w hW hWR hSq hSqBound hEnv z hz hzWindow\n');
packageLines.push({name:'hPointPayment',type:payPoint,sourceStartLine:ppStart,sourceEndLine:lineNow()-1,
  kind:'Exact whole38-conjunct fixed n/w/z producer payment result'});
have('hNumeratorPayment',proj('hPointPayment',37,38));
have('hSecondPayment',proj('hPointPayment',33,38));
have('hZeroPayment',proj('hPointPayment',34,38));
have('hZeroTransport',proj(uniCall,68,71));
have('hOriginalZeroPayment','by\n  rw [← hZeroTransport]\n  exact hZeroPayment');
add('  refine ⟨\n' + payConj.slice(0,37).map((_,i)=>'    '+proj('hPointPayment',i+1,38)+',').join('\n') +
    '\n    ?_, '+proj('hPointPayment',38,38)+'⟩\n' +
    '  intro C1 C2 C3 C4 hSZcBudget hzMomentWindow\n');
have('hClippedLower',tailAtInput+'.1');
const eventStart = lineNow();
add('  have hClippedEventual :\n'+indent(facts.hClippedEventual.type,6)+' := by\n'+
    '    intro τ hτ\n' +
    '    exact Exists.imp\n' +
    '      (fun (k0 : ℕ) (hJointAll :\n' + indent(wholeJointAllType,10) + ') =>\n'+
    '        fun (k : ℕ) (hk : k0 ≤ k) => '+proj('(hJointAll k hk)',20,20)+')\n'+
    '      ('+tailAtInput+'.2 τ hτ)\n');
factLines.push({frozenName:'hClippedEventual',name:'hClippedEventual',type:facts.hClippedEventual.type,
  sourceStartLine:eventStart,sourceEndLine:lineNow()-1});
packageLines.push({name:'hJointAll',type:wholeJointAllType,sourceStartLine:eventStart+4,
  sourceEndLine:lineNow()-2,kind:'Complete twenty-conjunct same-k producer result under its complete literal512 let telescope; logical Exists.imp premise only'});
have('hPaidLower','by\n  linarith only [hClippedLower, hOriginalZeroPayment]');
const toleranceStart = lineNow();
add('  have hUpperWithTolerance :\n'+indent(facts.hUpperWithTolerance.type,6)+' := by\n    intro τ hτ\n');
have('hClippedCutoff','hClippedEventual τ hτ',4);
have('hPaymentEventuallyAtTau','hNumeratorPayment τ hτ',4);
have('hPaymentCutoff','Filter.eventually_atTop.mp hPaymentEventuallyAtTau',4);
ordinaryLines.push({name:'kClipped',startLine:lineNow()}); add('    let kClipped : ℕ := Classical.choose hClippedCutoff\n');
ordinaryLines.push({name:'kPayment',startLine:lineNow()}); add('    let kPayment : ℕ := Classical.choose hPaymentCutoff\n');
have('hClippedAll','Classical.choose_spec hClippedCutoff',4);
have('hPaymentAll','Classical.choose_spec hPaymentCutoff',4);
have('hCommonClippedLe','Nat.le_of_add_right_le (Nat.le_refl (kClipped + kPayment))',4);
have('hCommonPaymentLe','Nat.le_of_add_left_le (Nat.le_refl (kClipped + kPayment))',4);
have('hClippedAtCommon','hClippedAll (kClipped + kPayment) hCommonClippedLe',4);
have('hPaymentAtCommon','hPaymentAll (kClipped + kPayment) hCommonPaymentLe',4);
have('hPaidUpperApprox','by\n  dsimp only [E, E2] at hPaymentAtCommon hSecondPayment\n  linarith only [hClippedAtCommon, hPaymentAtCommon, hSecondPayment, hOriginalZeroPayment]',4);
add('    exact hPaidUpperApprox\n');
factLines.push({frozenName:'hUpperWithTolerance',name:'hUpperWithTolerance',type:facts.hUpperWithTolerance.type,
  sourceStartLine:toleranceStart,sourceEndLine:lineNow()-1});
const upperStart = lineNow();
add('  have hPaidUpper :\n'+indent(facts.hPaidUpper.type,6)+' := by\n'+
    '    exact Classical.byContradiction (fun (hUpperFailed :\n'+indent(facts.hUpperFailed.type,8)+') => by\n');
factLines.push({frozenName:'hUpperFailed',name:'hUpperFailed',type:facts.hUpperFailed.type,
  sourceStartLine:upperStart+2,sourceEndLine:lineNow()-1});
have('hUpperGapPositive','by\n  linarith only [hUpperFailed]',6);
const gap = inv.inlineOrdinaryExpressionsNotNamedData[1];
have('hUpperAtGap','hUpperWithTolerance ('+gap+') hUpperGapPositive',6);
add('      linarith only [hUpperGapPositive, hUpperAtGap])\n');
factLines.push({frozenName:'hPaidUpper',name:'hPaidUpper',type:facts.hPaidUpper.type,
  sourceStartLine:upperStart,sourceEndLine:lineNow()-1});
have('hPaidContract','⟨hPaidLower, hPaidUpper⟩');
add('  exact hPaidContract\n' + close);
const sourceName = 'OriginalSameWitnessClippedPaidTailApplication.lean';
put(sourceName,source);
json('SOURCE-STRUCTURE.json', {schema:'oq56-unit247-deterministic-source-structure-v1',
  inputsVerified:55, publicOrdinary:141, optionalApproved:145, instanceApproved:6,
  frozenPropRecords:33, universalConjuncts:71, retainedPaymentConjuncts:38,
  outputPaymentConjuncts:39, jointProducerConjuncts:20, pureLogicalPackages:packageLines,
  namedFacts:factLines, ordinaryChoiceCoordinates:ordinaryLines,
  source:bind(own+'/'+sourceName), kernelChecked:false, axiomAudited:false});
console.log(JSON.stringify({source:bind(own+'/'+sourceName),LF:source.split('\n').length-1,
  namedFrozenFactWrites:factLines.length+1, pureLogicalPackaging:packageLines.length,
  mirrorCount:7+paymentRows.length, optionalUsed:7+paymentRows.length+4,
  kernelChecked:false,axiomAudited:false},null,2));
const lineAt = index => source.slice(0,index).split('\n').length;
const escapeRE = s => s.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
const whitespaceRE = s => s.split(/\s+/).map(escapeRE).join('\\s*');
const sourceBinding = bind(own+'/'+sourceName);
const priorProof=read(provisionalPath);
const restoredProof=source.replace('Nat.le_of_add_right_le (Nat.le_refl (kClipped + kPayment))','by omega')
  .replace('Nat.le_of_add_left_le (Nat.le_refl (kClipped + kPayment))','by omega');
assert(restoredProof===priorProof,'exact two-line proof-internal delta');
json('PROOF-DELTA.json',{schema:'oq56-unit247-before-finalwrite-two-line-direct-order-replacement-v1',
  provisional:bind(provisionalPath),final:sourceBinding,supplementInputs,
  changedLines:[
    {fact:'hCommonClippedLe',fullProp:facts.hCommonClippedLe.type,old:'by omega',
      new:'Nat.le_of_add_right_le (Nat.le_refl (kClipped + kPayment))',
      sourceLine:lineAt(source.indexOf('Nat.le_of_add_right_le (Nat.le_refl (kClipped + kPayment))'))},
    {fact:'hCommonPaymentLe',fullProp:facts.hCommonPaymentLe.type,old:'by omega',
      new:'Nat.le_of_add_left_le (Nat.le_refl (kClipped + kPayment))',
      sourceLine:lineAt(source.indexOf('Nat.le_of_add_left_le (Nat.le_refl (kClipped + kPayment))'))}],
  reverseOnlyTwoLinesRecoversPriorByteExact:true,publicAndAllFactTypesContextsInstancesOptionsExact:true,
  reason:'Lead-frozen existing Nat APIs avoid broad arithmetic tactic for the two unchanged frozen common-sum order Props. Reflexive sum bound is the core Nat reflexivity proof, with no named premise or data.',
  beforeAnyIndependentOrMachineGate:true,LeanCalls:0});
const rootParams = propContext.originalParameters;
const globalContext = rootParams + '\n' + propContext.globalSixResultLets;
const actualContexts = {...propContext};
for (const key of ['selectedPaymentContext','paymentExternalContext','paymentTauContext',
  'paidCutoffChoiceContext','paidChosenCutoffsContext','failedPaidUpperContext']) {
  actualContexts[key] = actualContexts[key].replace('(n : ℕ) (hn : 4 ≤ n)',
    '(n : ℕ)\n(hPaymentAtN :\n'+paymentAtN+')');
}
actualContexts.producerLogicalPaymentAtN = propContext.selectedModelContext + '\n' +
  '(Cenv aenv t0 Menv : ℝ)\n(hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)\n' +
  '(ht0 : 0 < t0) (hMenv : 0 ≤ Menv)\n(n : ℕ)\n';
actualContexts.producerLogicalJointAll = actualContexts.paymentTauContext + '(k0 : ℕ)\n';
const initialEnd = source.indexOf(initial)+initial.length;
const callStart = source.indexOf(call,initialEnd);
assert(callStart===initialEnd, 'exact initial call order');
const sourceTailStart = pre.length+head.length;
const sourceBody = source.slice(sourceTailStart);
const before = (text,row) => {
  const pat = new RegExp('let\\s+'+escapeRE(row.name)+'\\s*:\\s*'+whitespaceRE(row.type)+'\\s*:=\\s*'+whitespaceRE(row.rhs),'g');
  const matches = [...text.matchAll(pat)];
  assert(matches.length>0,'binding context not found '+row.name);
  return text.slice(0,matches[matches.length-1].index);
};
const claimedPublic = new Set();
const publicOrdinary = publicRows.map((row,index)=>{
  const pat = new RegExp('let\\s+'+escapeRE(row.name)+'\\s*:\\s*'+whitespaceRE(row.type)+'\\s*:=\\s*'+whitespaceRE(row.rhs),'g');
  const matches = [...head.matchAll(pat)].filter(m=>!claimedPublic.has(m.index));
  const paymentScope = row.scope.startsWith('newPayment:') || row.new === true;
  const universalScope = !paymentScope && index>=7;
  const m = paymentScope ? matches[matches.length-1] : matches[0];
  assert(m,'public binding matched '+index+' '+row.name); claimedPublic.add(m.index);
  let fullContext;
  if(index<6) fullContext=before(globalContext,row);
  else if(index===6) fullContext=before(propContext.selectedModelContext,row);
  else if(paymentScope) fullContext=before(propContext.selectedPaymentContext,row);
  else if(['J','mDel','Cdel','pX','pR'].includes(row.name)) {
    const deletedStart = head.indexOf('          let J : Type :=');
    fullContext = propContext.selectedUniversalContext + '\n(k : ℕ) (i : Fin n)\n' + head.slice(deletedStart,m.index);
  } else fullContext=before(propContext.selectedUniversalContext,row);
  const mirrored = index<7 || paymentScope;
  const introPattern = new RegExp('^  intro ([^\\n]*\\b'+escapeRE(row.name)+'[^\\n]*)$','m');
  const introLine = row.name==='μ₀' ? lineAt(source.indexOf('  intro μ₀\n')) :
    (index<6 ? lineAt(source.indexOf('  intro g r v rho β cWindow\n')) :
      mirrored ? lineAt(source.indexOf('  intro '+paymentRows.slice(Math.floor(paymentRows.findIndex(x=>x===row)/10)*10,
        Math.floor(paymentRows.findIndex(x=>x===row)/10)*10+10).map(x=>x.name).join(' ')+'\n')) : null);
  return {...row,publicOccurrence:index+1,completeEnclosingParameterContext:fullContext,
    sourceDeclaration:{path:sourceBinding.path,startLine:lineAt(pre.length+m.index),
      endLine:lineAt(pre.length+m.index+m[0].length),fullType:row.type,fullRHS:row.rhs},
    mirrorUsed:mirrored,mirrorSourceLine:introLine,
    proofMirrorActualContext:mirrored && paymentScope ? before(actualContexts.selectedPaymentContext,row) : fullContext,
    optionalStatus:mirrored?'USED exact public let intro':'UNUSED as a live proof mirror; public result retained in complete producer package',
    universalScope,paymentScope};
});
assert(claimedPublic.size===141,'public source binding coverage');
const optionalOrdinary = [
  ...publicOrdinary.map(r=>({...r,kind:'public-let-mirror'})),
  ...inv.soleExistingWitnessSelections.map(r=>({...r,kind:'sole-immediate246-witness',mirrorUsed:true,
    sourceLine:ordinaryLines.find(x=>x.name===r.name).startLine})),
  ...inv.newProofLocalOrdinaryData.map(r=>({...r,kind:'new-frozen-natural-cutoff',mirrorUsed:true,
    enclosingParameterContext:actualContexts[r.completePropContextRef],
    sourceLine:ordinaryLines.find(x=>x.name===r.name).startLine})),
];
assert(optionalOrdinary.length===145 && optionalOrdinary.filter(x=>x.mirrorUsed).length===58,'optional actual count');
const factByFrozen = new Map(factLines.map(x=>[x.frozenName,x]));
const actualFacts = Object.fromEntries(Object.entries(facts).map(([name,row])=>{
  const written = factByFrozen.get(name);
  const start = name==='h246' ? lineAt(callStart) : lineAt(source.indexOf(
    name==='hUpperFailed' ? '(hUpperFailed :' : 'have '+(written?.name||name)+' :',sourceTailStart));
  return [name,{...row,name:written?.name||name,used:true,
    type:name==='h246'?read(base+'/freeze-03/EXPECTED-H246-PROP.txt').trim():row.type,
    enclosingParameterContext:actualContexts[row.completePropContextRef],
    fullExplicitAnnotation:name!=='h246',onlyApprovedInferredPropException:name==='h246',
    sourceStartLine:start,sourceEndLine:written?.sourceEndLine||lineAt(callStart+call.length)-1,
    sourceBinding,actualNameMapping:name==='hCountableGeneration'?
      'Approved full CountablyGenerated Prop is named hcg so the exact frozen selected-instance RHS hcg is retained. No additional fact/assumption.':null}];
}));
for(const p of packageLines) {
  p.sourceStartLine=lineAt(source.indexOf(p.name==='hPointPayment'?'have hPointPayment :':'('+p.name+' :',sourceTailStart));
  p.enclosingParameterContext=p.name==='hPaymentAtN'?actualContexts.producerLogicalPaymentAtN:
    p.name==='hJointAll'?actualContexts.producerLogicalJointAll:actualContexts.selectedPaymentContext;
  p.newDataAssumptionsOrMathematicalInterface=false;
  p.fullExplicitAnnotation=true;
}
const actualInstances=inv.instanceInventory.map(r=>({...r,used:r.name!=='augmentedProductSpace',
  enclosingParameterContext:actualContexts[r.completePropContextRef],
  actualProofInstalls:r.name==='selectedSpace'||r.name==='selectedCountableGeneration'?
    [{path:sourceBinding.path,line:lineAt(source.indexOf(r.name==='selectedSpace'?
      '  letI : MeasurableSpace Ω := m₀':'  letI : @MeasurableSpace.CountablyGenerated Ω m₀ := hcg',sourceTailStart)),
      fullType:r.type,fullValue:r.rhs}]:[],
  actualStatus:r.name==='augmentedProductSpace'?'UNUSED optional proof letI; complete public/type-local instance scopes retained':
    'USED exact frozen type/value/scope; no added local instance'}));
const contextArtifact={schema:'oq56-unit247-author-full-actual-prop-contexts-v1',atUTC:new Date().toISOString(),
  status:'COMPLETE AUTHOR SOURCE; INDEPENDENT SOURCE/KERNEL/AX GATES PENDING',module:inv.module,
  publicTheorem:inv.publicTheorem,source:sourceBinding,activation:bind(activationPath),
  completeFrozenPublicHead:head,completeOriginalParameters:rootParams,completeResultType:inv.completeResultType,
  exactSourceContextRule:'Full source is bound by SHA; coordinates identify actual lexical scope. Context strings include every ordinary type/RHS and proof dependency used in the recorded Prop. Repeated complete contexts are intentionally retained.',
  declarationContexts:actualContexts,publicOrdinary,optionalOrdinary,
  ordinaryCount:{public:141,optionalApproved:145,optionalUsed:58,optionalUnused:87,
    usedPublicMirrors:54,soleExistingWitnesses:2,newNaturalCutoffs:2,newUnfrozenData:0},
  proofFactTypeDictionary:actualFacts,proofFactRecords:33,all33FrozenFactsUsed:true,
  pureLogicalWholeProducerPackages:packageLines,
  logicalOnlyBoundVariables:[
    {name:'k0',type:'ℕ',RHS:null,scope:'Exists.imp universally bound witness from frozen producer joint existential; no choice or fresh selector',sourceLine:packageLines[2].sourceStartLine,
      enclosingParameterContext:actualContexts.paymentTauContext},
    {name:'k',type:'ℕ',RHS:null,scope:'Universal frozen all-k consequence under Exists.imp',
      enclosingParameterContext:actualContexts.producerLogicalJointAll+'(hJointAll :\n'+wholeJointAllType+')\n'},
    {name:'hk',type:'k0 ≤ k',RHS:null,scope:'Explicit full Prop lambda premise from frozen all-k consequence',
      enclosingParameterContext:actualContexts.producerLogicalJointAll+'(hJointAll :\n'+wholeJointAllType+')\n(k : ℕ)\n'},
  ],
  fullExistingAssumptionBindersIn:head,
  instanceInventory:actualInstances,approvedInstanceCount:6,usedOptionalInstanceCount:5,
  newLocalInstances:0,actualExplicitProofInstanceInstalls:2,
  APIImplicitInstanceArguments:inv.APIImplicitInstanceArguments,
  typeLocalLetRestatementRule:'Whole hCg/hModel/hUniversal246/hPayment246 and three logical packages restate only frozen producer lets/scopes; hJointAll uses the literal C0=512 specialization. They are not additional live ordinary data mirrors, choices, assumptions or helper interfaces.',
  noUnfrozenOrdinaryOrMathematicalInterface:true,
  kernelChecked:false,axiomAudited:false,independentSOURCEReviewPending:true,
  requestedModel:'gpt-6.1-sol',requestedEffort:'xhigh',actualModel:null,actualBackend:null,actualEffort:null,
  usage:{input:null,cachedInput:null,output:null,reasoningSubset:null}};
json('ACTUAL-PROP-CONTEXTS.json',contextArtifact);
const forbidden=[...source.matchAll(/\b(sorry|admit|axiom|unsafe|native_decide)\b|#eval!/g)].map(x=>x[0]);
assert(forbidden.length===0,'forbidden proof token');
assert(source.startsWith(pre+head+' := by\n'+initial+call),'frozen prefix');
assert(source.endsWith(close),'frozen closing');
assert([...source.matchAll(/^set_option /gm)].length===1 && source.includes('set_option autoImplicit false'),'options');
assert([...sourceBody.matchAll(/^\s*have\s+\S+\s*:=/gm)].length===1,'sole inferred named fact');
assert([...sourceBody.matchAll(/^ {2,4}let\s+\S+\s*:/gm)].length===4,'only four live choices');
assert([...sourceBody.matchAll(/^ {2}letI\s*:/gm)].length===2,'exact optional instance installs');
const actualNamed=Object.values(actualFacts).filter(x=>x.used).length;
assert(actualNamed===33,'all frozen named facts accounted');
const producerRecovered=head.replace(inv.completeNewData,'').replace(inv.completeNewContract,'')
  .replace('actual_original_same_witness_clipped_paid_scalar_tail_application','actual_original_same_witness_clipped_scalar_tail_application');
const producerActualSource=read(root+'/drafts/oq56/unit246/author-01/OriginalSameWitnessClippedTailApplication.lean');
const producerActualHead=producerActualSource.slice(producerActualSource.indexOf('theorem actual_original_same_witness_clipped_scalar_tail_application'),
  producerActualSource.indexOf(' := by\n'));
assert(producerRecovered===producerActualHead,'whole producer source result recovery');
const compatibility={schema:'oq56-unit247-author-static-compatibility-v1',atUTC:new Date().toISOString(),source:sourceBinding,
  activation:bind(activationPath),all55ImmutableInputsVerified:true,stage1FinalWriteSixZeroVerified:true,
  frozenPreambleExact:true,frozenHeadExact:true,frozenOriginalPi16InitialIntroExact:true,
  frozenH246CallExactBeforeGlobalMirrors:true,onlyH246InferredFact:true,completeExpectedH246PropExact:true,
  frozenClosingExact:true,wholeQualified246RecoveredAfterOnlyNewDataContractAndNameRemoval:true,
  publicOrdinaryCount:141,optionalOrdinary:{approved:145,used:58,unused:87},
  frozenPropRecords:33,allFrozenPropsUsed:true,pureLogicalWholeProducerPackages:3,
  instances:{approved:6,used:5,unused:1,explicitProofInstalls:2,newUnfrozen:0},
  twoNewNatCutoffs:{names:['kClipped','kPayment'],exactTypesRHSChoicePropsScopes:true},
  sameOnceCgM0Mu0MAugNuActualEta:true,sameClipping1:true,sameCBudget:true,
  bothOriginalWindowsAndConditionalExternalInputRetained:true,
  universalConjunctsRetainedDirectly:71,oldPaymentConjunctsRetained:38,newPaidPaymentConjuncts:1,
  completeProducerJointConjunctsLogicallyProjected:20,
  lowerMinusLiteralPayment:true,upperPlusLiteralThreePayment:true,
  toleranceElimination:'Real order only at literal positive quarter-gap; no probability or error limit used',
  fullOriginalWeightedSourceCostLiteral:true,noUnfrozenOrdinaryInterface:true,
  noProofOptionChanges:true,forbiddenTokensFound:forbidden,UTF8NoBOM:true,CR:0,LF:source.split('\n').length-1,
  producerPublicTypeLosslessRoundTrip:true,producerPublicType:bind(actualPublicTypePath),
  oldHelperTYPEPrinterFailuresSupersededByQualifiedCoverageOnly:true,
  producerQualificationConsumed:activation.qualifiedImmediateProducer,
  primaryAPIBindingsAlreadyFrozen:inv.primaryAPIBindings,
  supplementalExistingNatAPIs:supplementInputs,proofDelta:bind(own+'/PROOF-DELTA.json'),
  noLocalLeanKernelPPAxiomOrServerCommand:true,noNetworkUploadGitAPIOrChildren:true,
  staticChecksAreNotLeanElaborationOrIndependentReview:true,
  qualified:false,kernelChecked:false,axiomAudited:false,independentSOURCEReviewPending:true};
json('COMPATIBILITY.json',compatibility);
json('LOCAL-VALIDATION.json',{schema:'oq56-unit247-author-local-static-validation-v1',atUTC:new Date().toISOString(),
  source:sourceBinding,all55BindingsVerified:true,allHeaderAndInstanceAndOrdinaryChecks:true,
  namedPropsExplicitExceptFrozenH246:true,wholeResultLogicalProjectionStructureVerified:true,
  deterministicAuthoringValidatorCorrections:[{stage:'producer publicTYPE prefix binding',
    observed:'The public-full-type.txt omits the theorem name label present in actual-owned-types.txt; initial local validator incorrectly expected an identical beginning.',
    correction:'Compare the exact theorem label plus full public type with the original audit prefix; dictionary full-byte round trip is unchanged and exact.',
    LeanCommand:false,sourceEffect:false},
    {stage:'live data count',observed:'An initial regular expression also counted complete public lets inside explicitly typed frozen Prop restatements.',
      correction:'Count only the actual two/four-space live proof let declarations; all type-local frozen restatements remain inventoried separately.',LeanCommand:false,sourceEffect:false}],
  sourceBytesNotMechanicallyElaborated:true,LeanCalls:0,serverCalls:0,networkCalls:0,children:0});
json('PRODUCER-READING.json',{schema:'oq56-unit247-qualified-producer-interface-consumption-v1',
  producerQualification:activation.qualifiedImmediateProducer,producerBinding:activation.qualifiedProducerInterfaceBinding,
  fullPublicType:bind(actualPublicTypePath),dictionary:bind(dictPath),
  all318DictionaryEntriesAndCompletePublicMainRead:true,
  exactDictionaryRoundTripToOriginalAudit:true,exactTheoremLabelPlusPublicTypePrefix:true,
  fullPublicUnelidedTypeBytes:2000145,universalConjuncts:71,paymentConjuncts:38,
  helperCoverage:bind(root+'/drafts/oq56/unit246/normalized-owner-evidence-02/TYPE-coverage.json'),
  qualifiedOldHelperReviewsReusedWithoutRepeat:true,helperFailurePlaceholdersAreNotTypes:true,
  localLeanOrServerPublicTYPEReplay:false,newMathematicalAssumptions:false});
const report=`# Unit247 complete author source

STATUS: COMPLETE REVIEWABLE AUTHOR SOURCE; independent full source-to-statement/proof review and lead server native/FIRSTO/all-owner transitive-axiom/current full-type gates remain pending. No machine or independent qualification is claimed by this author.

The source is ${sourceBinding.path}, SHA256 ${sourceBinding.sha256}, ${sourceBinding.bytes} bytes and ${source.split('\n').length-1} LF. It uses UTF-8 without BOM and contains no CR. The frozen preamble, entire freeze02 public head, original Pi16 initial introduction, freeze03 exact h246 call before global let introductions, and namespace closing are byte-exact. All55 activation inputs and prior Stage1 final-write six-zero release were verified before the actual first-write ACK. No producer bytes, old evidence, shared source or resource state were changed.

## Full mathematical route

Invoke the complete qualified immediate246 theorem exactly once with the original Ω/mΩ/μ/h and all original measurability, L², symmetry, centering, unit projection second moment, p-window/moment and positive cBudget inputs. After its six literal global lets, project the complete cg existential, select cg once, project the complete dependent model existential and select m₀ once. Obtain its proof witnesses hm₀ and hcg, retain the identical trimmed μ₀, and install only the two already frozen selected-space and CountablyGenerated instances. The approved hCountableGeneration full Prop is locally named hcg solely to retain the exact instance RHS. No new mathematical fact or instance is added by that naming.

The entire71-conjunct universal branch is returned directly as hUniversal246. The eventual-n payment branch is strengthened by Filter.Eventually.mono for the SAME eventual n. The complete per-n producer result is explicitly typed as hPaymentAtN; its4≤n projection is used inline. Thus the n cutoff remains before w,z, external scalar constants/input and strict moment-window proof. No new n cutoff, uniform k rate, model, measure, coding family, factor, coordinate selector or probability instance is selected.

At fixed original admissible w,z in the original remainder window, introduce exactly the frozen47 payment lets, including the new literal512 T0, original L0 sum and fully expanded original weighted sourceCost0. The whole38-conjunct fixed-n payment result is explicitly typed as hPointPayment. Every old conjunct, including both limsup inequalities and every payment/convergence/measurability statement, is reconstructed by its exact conjunction projection. Only the new frozen conditional paid-tail clause is inserted before the old final limsup-to-payment clause.

The exact246 universal zero transport is specialized at literal512, with0≤512 and0≤z derived from the existing z≥1 premise. It gives ν.real Z equal to the original P projection-zero event. Its existing ν.real Z≤payment yields the original projection-zero payment. The exact246 clipped lower bound subtracts that original zero event; real linear order therefore proves the new normal lower expression minus the SAME literal payment.

For any fixed external C1..C4, supplied ScalarShaoZhouFiniteCostTailInput at cBudget and original strict moment window, the full246 joint eventual-k result is projected logically to its upper inequality. The bound witness k0 remains bound by Exists.imp; there is no extra Classical.choose or new witness selection. hJointAll has its complete20-conjunct Prop and full literal512 universal let telescope written explicitly, so the original joint package and all its contexts are covered without an inferred shorthand predicate.

For τ>0, choose only kClipped and kPayment, with their complete frozen choice Props/RHS/scopes. The payment cutoff is obtained from the pinned Filter.eventually_atTop theorem applied to the retained numerator payment at δ=τ. The inline sum kClipped+kPayment is above each cutoff. At that identical sum the clipped upper is bounded by normalUpper + numeratorError + secondError + originalZeroError + τ. NumeratorError≤payment+τ, secondError≤payment and originalZeroError≤payment give normalUpper+3*payment+2*τ. E and E2 are unfolded definitionally only at this real arithmetic step. If the final τ-free upper failed, its literal positive quarter-gap would be an allowed τ and would contradict that bound by real linear order. No probability limit, vanishing error assertion or continuity/CDF argument is used.

## Exact interface and source reading

The approved counts are141 public ordinary occurrences,145 optional live proof data,6 exact instance entries and33 named Prop records. This implementation uses54 public mirrors plus the sole cg/m₀ selections and two natural cutoffs:58 optional data used,87 unused. All33 frozen fact types are explicitly annotated except the sole exact h246 call inference exception. Three additional names hPaymentAtN, hPointPayment and hJointAll only restate entire already frozen producer/result Props; they add no ordinary data, assumptions or substantive mathematical interface. Their full types/contexts/source coordinates are recorded. Existing theorem-input hypotheses and logical all-k binders remain in their complete frozen types; hk has an explicit k0≤k Prop annotation.

The qualified246 actual public fullTYPE was read using the complete318-entry dictionary and full current public main portion. The dictionary expands byte-for-byte to the original all-owner audit text; removing only its exact theorem-name label exposes the exact2000145-byte public-full-type.txt prefix. The two historical helper pretty-printer failure messages are preserved and are not treated as types. Their already qualified complete DAG/source review coverage is reused through TYPE-coverage.json and the producer qualification; no unchanged producer proof/helper review or server audit was replayed.

All141 public type/RHS/scope rows,145 optional used/unused rows,6 exact instance type/value/scopes,33 actual full Prop contexts and the three logical-package contexts are in ACTUAL-PROP-CONTEXTS.json. Source coordinates and the bound complete source provide the exact lexical context. COMPATIBILITY.json and LOCAL-VALIDATION.json record deterministic byte/interface/count checks, including the corrected local publicTYPE-label comparison. These checks do not constitute Lean elaboration or independent proof review.

Before final release the lead supplied a four-file hash-bound supplement with full pinned core Nat order heads/bodies/ambient. The two unchanged hCommonClippedLe/hCommonPaymentLe proof lines now use Nat.le_of_add_right_le / Nat.le_of_add_left_le on Nat reflexivity of the same inline sum, replacing only the two provisional omega lines. The provisional831b25e1 source bytes are preserved in PROVISIONAL-SOURCE-831b25e1.txt. PROOF-DELTA.json records both exact line replacements and verifies that reversing those two lines recovers the provisional source byte-for-byte. No public declaration, ordinary binding, fact type, instance, assumption, option, import, cutoff or choice changed. Both versions precede any independent or machine gate.

## Scope, evidence boundary and next dependency

The result is a finite conditional fixed512/clipping1 paid-tail application for the actual original clipped statistic, with the SAME witnesses, original product-envelope payment, both original windows and explicit external Shao–Zhou input. The original p54 projection-zero repair remains paid. The complete original246 result is retained. This source does not prove existence of the external scalar input, quantitative smallness of sourceCost0, vanishing exceptional probabilities, unclipped/physical-statistic identification, CDF/atom/no-atom passage, S11/S15/DC completion or any original OQ56/root closure. Those obligations remain OPEN.

No local Lean, kernel/PP/AX command, server/SSH request, upload, network request, Git/API publication, child context, cache/environment/shared write was executed. The toolchain consumed from the existing curated pin is leanprover/lean4:v4.36.0-rc1 and mathlib807d3836b165983210ee2ecf3cd28f239436949c. Actual checking remains lead-only on the designated server after complete independent SOURCE acceptance. Acceptance must bind the exact new source, first successful original object, every actual owned type/value and transitive axioms to the qualified independent review. Reuse unchanged qualified producer evidence.

The exact next dependency is independent complete SOURCE review of this247 artifact, then lead newnative and same-FIRSTO allactualAX/current completeTYPE join if accepted. This bounded author role releases all writer/execution/child authority in its final-write lastzeroRELEASE.json and performs no further writes after that release.

Requested model/effort: gpt-6.1-sol/xhigh. This context exposes no independently verifiable backend/model/effort or token counters; actual fields and input/cached-input/output/reasoning-subset counts are null, without inferred subscription allocation.
`;
put('REPORT.md',report);
json('CHECKPOINT.json',{schema:'oq56-unit247-author-compact-checkpoint-v1',atUTC:new Date().toISOString(),
  ownerChat:activation.ownerChat,role:activation.role,ownedRoot:own,status:'AUTHOR_COMPLETE_READY_FOR_FRESH_INDEPENDENT_SOURCE_REVIEW',
  source:sourceBinding,publicOrdinary:141,optionalApproved:145,optionalUsed:58,instances:6,PropRecords:33,
  proofRoute:'whole246; same512 model; original zero payment; two frozen k cutoffs; common inline sum; real quarter-gap tolerance elimination',
  nextExactDependency:'Fresh independent complete SOURCE review -> lead newnative -> sameFIRSTO allactualAX/current completeTYPE -> qualified final join',
  kernelChecked:false,axiomAudited:false,qualified:false,
  activeWriter:1,heavyCommands:0,inflightExecution:0,pendingExternal:0,children:0,uncertainOperations:0,
  finalReleasePending:true,requestedModel:'gpt-6.1-sol',requestedEffort:'xhigh',actualBackend:null,actualModel:null,actualEffort:null,
  usage:{input:null,cachedInput:null,output:null,reasoningSubset:null}});
json('SOURCE-STRUCTURE.json', {schema:'oq56-unit247-deterministic-source-structure-v1',
  inputsVerified:55,supplementInputsVerified:4,publicOrdinary:141,optionalApproved:145,instanceApproved:6,
  frozenPropRecords:33,universalConjuncts:71,retainedPaymentConjuncts:38,outputPaymentConjuncts:39,
  jointProducerConjuncts:20,pureLogicalPackages:packageLines,namedFacts:factLines,
  ordinaryChoiceCoordinates:ordinaryLines,source:sourceBinding,kernelChecked:false,axiomAudited:false});
const brackets=[];
for(const c of source){if('([{'.includes(c))brackets.push(c);if(')]}'.includes(c)){
  assert('([{'.indexOf(brackets.pop())===')]}'.indexOf(c),'source delimiter order');}}
assert(brackets.length===0,'source delimiter final');
console.log(JSON.stringify({actualContexts:bind(own+'/ACTUAL-PROP-CONTEXTS.json'),compatibility:bind(own+'/COMPATIBILITY.json'),
  allInputs:55,public:141,optional:145,used:58,instances:6,props:33,qualified:false},null,2));
