const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const root = __dirname;
const work = 'C:/game/shao lean';
const freeze = path.join(work, 'drafts/oq56/unit248/freeze-01');
const read = p => fs.readFileSync(p, 'utf8');
const json = p => JSON.parse(read(p));
const hash = b => crypto.createHash('sha256').update(b).digest('hex');
const bind = p => { const b = fs.readFileSync(p); return { path: p.replaceAll('\\', '/'), sha256: hash(b), bytes: b.length }; };
const put = (name, obj) => fs.writeFileSync(path.join(root, name), JSON.stringify(obj, null, 2) + '\n');
const sourcePath = path.join(root, 'OriginalSameWitnessPhysicalPaidTailApplication.lean');
const source = read(sourcePath);
const sourceBinding = bind(sourcePath);
const inv = json(path.join(freeze, 'INTERFACE-INVENTORY.json'));
const activationPath = path.join(work, 'drafts/oq56/unit248/implementation-activation-01/ACTIVATION.json');
const activation = json(activationPath);
const now = new Date().toISOString();
const facts = Object.fromEntries(inv.frozenProofFacts.map(x => [x.name, x]));
const knownModel = {requestedModel:'gpt-6.1-sol', requestedEffort:'xhigh', actualBackend:null, actualModel:null, actualEffort:null,
  usage:{input:null, cachedInput:null, output:null, reasoningSubset:null}};
const operations = {Lean:0,lake:0,kernel:0,PP:0,AX:0,server:0,network:0,upload:0,Git:0,API:0,children:0};
const normalize = s => s.replace(/\s+/g, ' ').trim();
const indent = (s, n) => {
  const ls = s.replace(/\r\n/g, '\n').replace(/^\n+|\n+$/g, '').split('\n');
  const base = Math.min(...ls.filter(l => l.trim()).map(l => l.match(/^ */)[0].length));
  return ls.map(l => ' '.repeat(n) + l.slice(base)).join('\n');
};
const position = offset => ({byteOffset:Buffer.byteLength(source.slice(0,offset)), line:source.slice(0,offset).split('\n').length,
  column:offset-source.lastIndexOf('\n',offset-1)});
const locate = (needle, required=true) => {
  const p = source.indexOf(needle);
  if (p < 0) { if(required) throw Error('Source coordinate missing: '+needle.slice(0,90)); return null; }
  return {start:position(p), end:position(p+needle.length)};
};
const lines = source.split('\n');
const haveDeclarations = [];
let offset=0;
for (let n=0;n<lines.length;n++) {
  const m=lines[n].match(/^( *)have ([^ :]+)(?: :| :=)/);
  if (m) haveDeclarations.push({name:m[2],indent:m[1].length,offset,line:n+1});
  offset += lines[n].length+1;
}
const haveByName = Object.fromEntries(haveDeclarations.map(x => [x.name,x]));
const requiredFacts = inv.frozenProofFacts.map(f => {
  if(f.name==='h247') return {...f,contextId:'C00',actualBinding:locate(read(path.join(freeze,'FROZEN-H247-CALL.txt')).trimEnd()),
    actualFullExpectedProp:read(path.join(freeze,'EXPECTED-H247-PROP.txt')), solePermittedInferredProp:true,
    expectedPropSameAsFreeze:normalize(f.fullType)===normalize(read(path.join(freeze,'EXPECTED-H247-PROP.txt')))};
  if(f.name==='hStudentizerWindow') return {...f,contextId:'C08',actualBinding:locate('intro hStudentizerWindow'),
    introducedFromCompleteExplicitGuard:true, fullType:f.fullType};
  const decl=haveByName[f.name];
  if(!decl) throw Error('Frozen fact absent '+f.name);
  const header=' '.repeat(decl.indent)+'have '+f.name+' :\n'+indent(f.fullType,decl.indent+4)+' :=';
  if(!source.startsWith(header,decl.offset)) throw Error('Full frozen type differs for '+f.name);
  const contextId = ['hrSymm','hRhoNonneg','hCg'].includes(f.name)?'C01':
    ['hcgpos','hModel'].includes(f.name)?'C02': ['hm₀','hcg'].includes(f.name)?'C03':
    ['hRetained247','hμ₀Probability','hPaymentAll247'].includes(f.name)?'C04':
    f.name==='hPaymentAtN247'?'C05':f.name==='hClippedCurrentBounds'||f.name==='hNewPhysicalWhole'?'C06':
    ['hLiteralComparison','hClosedUpperDiff','hClosedLowerDiff'].includes(f.name)?'C08':'C07';
  return {...f,contextId,actualBinding:locate(header),completeExplicitTypeInSource:true,
    precedingProofFactNames:haveDeclarations.filter(x=>x.line<decl.line).map(x=>x.name)};
});
if(requiredFacts.some(f=>f.name==='h247'&&!f.expectedPropSameAsFreeze))throw Error('Expected h247 fullProp differs');
const paymentNames=[...inv.completeContexts.paymentOrdinaryContext.matchAll(/^\s*let (?!I\b)([^ :\n]+)\s*:/gm)].map(x=>x[1]);
const headerText=read(path.join(freeze,'FROZEN-HEAD.txt'));
const preamble=read(path.join(freeze,'FROZEN-PREAMBLE.txt'));
const closing=read(path.join(freeze,'FROZEN-CLOSING.txt'));
const initialIntro=read(path.join(freeze,'FROZEN-INITIAL-INTRO.txt'));
const exactCall=read(path.join(freeze,'FROZEN-H247-CALL.txt'));
const originalTelescope=headerText.slice(headerText.indexOf('  ∀'),headerText.indexOf('    let g'));
const paymentQuantifiers=inv.completeContexts.eventualPaymentQuantifiers;
const currentType=facts.hPaymentAtN247.fullType.slice(facts.hPaymentAtN247.fullType.indexOf('        let mN'));
const extraFacts=[
  {name:'hAllAtN247',fullType:'4 ≤ n ∧\n'+facts.hPaymentAtN247.fullType,contextId:'C05',kind:'pure logical entire producer conjunction input'},
  {name:'hn',fullType:'4 ≤ n',contextId:'C05',kind:'projection of producer input'},
  {name:'hAtCurrent247',fullType:currentType,contextId:'C06',kind:'complete fixed-n current-z producer package'},
  {name:'hDisagreementSubset',fullType:'Ephysical ⊆ H1sourceᶜ',contextId:'C08',kind:'frozen conclusion projection'},
  {name:'hDisagreementMono',fullType:'P.real Ephysical ≤ P.real H1sourceᶜ',contextId:'C08',kind:'frozen conclusion projection'},
  {name:'hDisagreementPayment',fullType:'P.real Ephysical ≤ payment1',contextId:'C08',kind:'frozen conclusion projection'},
  {name:'hUpperComparison',fullType:'∀ t : ℝ, |P.real {ζ : Fin n → Ω | t ≤ Tphysical ζ} - P.real {ζ : Fin n → Ω | t ≤ T0 ζ}| ≤ P.real Ephysical',contextId:'C08',kind:'frozen all-real conclusion projection'},
  {name:'hLowerComparison',fullType:'∀ t : ℝ, |P.real {ζ : Fin n → Ω | Tphysical ζ ≤ t} - P.real {ζ : Fin n → Ω | T0 ζ ≤ t}| ≤ P.real Ephysical',contextId:'C08',kind:'frozen all-real conclusion projection'}
].map(x=>({...x,actualBinding:x.name==='hAllAtN247'?locate('(hAllAtN247 :'):locate('have '+x.name+' :'),completeExplicitTypeInSource:true}));
const contexts=[
  {id:'C00',parent:null,text:originalTelescope,role:'exact original sixteen binder groups; original mΩ/μ; before h247'},
  {id:'C01',parent:'C00',text:inv.completeContexts.global247,fullProofInputs:['h247'],role:'exact six original global lets'},
  {id:'C02',parent:'C01',text:'let cg : ℝ := Classical.choose hCg\n',fullProofInputs:['hCg'],role:'sole cg from the single producer'},
  {id:'C03',parent:'C02',text:'let m₀ : MeasurableSpace Ω := Classical.choose hModel\n',fullProofInputs:['hcgpos','hModel'],role:'sole m₀ and proof witnesses from the same hModel'},
  {id:'C04',parent:'C03',text:'let μ₀ : @Measure Ω m₀ := μ.trim hm₀\nletI : MeasurableSpace Ω := m₀\nletI : MeasurableSpace.CountablyGenerated Ω := hcg\n',fullProofInputs:['hm₀','hcg'],role:'same selected model, entire universal71 retained'},
  {id:'C05',parent:'C04',text:'(Cenv aenv t0 Menv : ℝ)\n(hCenv : 0 ≤ Cenv) (haenv : 0 ≤ aenv)\n(ht0 : 0 < t0) (hMenv : 0 ≤ Menv)\n(n : ℕ)\n',
    fullProofInputs:['hPaymentAll247'],fixedNLogicalInputFullType:'4 ≤ n ∧\n'+facts.hPaymentAtN247.fullType,role:'same old eventual set, no new cutoff'},
  {id:'C06',parent:'C05',text:paymentQuantifiers.slice(paymentQuantifiers.indexOf('          ∀ (w'))+'\n'+inv.completeContexts.paymentOrdinaryContext,
    fullProofInputs:['hn','hPaymentAtN247'],role:'same fixed n,w,z, complete47 lets, original39 retained'},
  {id:'C07',parent:'C06',text:inv.completeContexts.newExtensionLets+'\nletI : MeasurableSpace (Fin n → Ω) := mN\nletI : @IsProbabilityMeasure (Fin n → Ω) mN P := (inferInstance : @IsProbabilityMeasure (Fin n → Ω) mN P)\n',
    role:'four frozen new lets; isolated original sample proof block'},
  {id:'C08',parent:'C07',text:'(hStudentizerWindow : 1 + rho ≤ Real.sqrt (n : ℝ))\n',role:'explicit guard only; no automatic eventual assertion'},
  {id:'C09',parent:'C08',text:'(t : ℝ)\n',role:'all real closed thresholds, no sign or atom premise'},
  {id:'C10',parent:'C08',text:'(C1 C2 C3 C4 : ℝ)\n(hSZcBudget : Shao.OQ6.NormalizedIntegrableTailAssembly.ScalarShaoZhouFiniteCostTailInput.{u} cBudget C1 C2 C3 C4)\n(hzMomentWindow : β = 0 ∨ (0 < β ∧ z ≤ cWindow * Real.rpow β (-1 / p) * Real.rpow (n : ℝ) ((p - 2) / (2 * p))))\n',
    role:'original external theorem input and original strict-moment window'}
];
const publicLets=[...headerText.matchAll(/\blet ([^ :\n]+)\s*:/g)];
if(publicLets.length!==inv.publicOrdinary.length)throw Error('Public ordinary occurrence count mismatch');
const ordinary=inv.publicOrdinary.map((x,index)=>{
  if(publicLets[index][1]!==x.name)throw Error('Public ordinary name/order differs '+x.name);
  const directIntro=/^global /.test(x.scope)?locate('intro g r v rho β cWindow'):
    /sole selected m₀ before/.test(x.scope)?locate('let μ₀ : @Measure Ω m₀ := μ.trim hm₀'):
    /newPayment:|Payment branch ONLY/.test(x.scope)?locate('intro '+paymentNames.join(' ')):
    /LAST added conjunction/.test(x.scope)?locate('intro Tphysical H1source payment1 Ephysical'):null;
  const at=preamble.length+publicLets[index].index;
  return {...x,retainedInPublicStatement:true,usedByComplete247Retention:!/LAST added conjunction/.test(x.scope),
    publicStatementCoordinate:position(at),actualProofIntroduction:directIntro,
    directOrdinaryIntroductionUsed:directIntro!==null,newOrdinaryInterface:false};
});
const choiceOrdinary=inv.optionalOrdinary.slice(-2).map(x=>({...x,actualBinding:locate('let '+x.name+' : '+x.type+' := '+x.rhs),sameProducerOnly:true}));
const approvedInstances=inv.approvedInstances.map(x=>({...x,used:x.name!=='augmentedProductSpace',
  actualDisposition:x.name==='augmentedProductSpace'?'unused optional local instance':
  ['selectedSpace','selectedCountableGeneration','originalSampleSpace','originalSampleProbability'].includes(x.name)?'explicit local instance at frozen scope':
  x.name==='finiteIndex'?'existing finite instance in exact public RHSs':'original telescope instance retained'}));
put('ACTUAL-PROP-CONTEXTS.json',{
  schema:'oq56-unit248-full-actual-source-Prop-ordinary-instance-contexts-v1',atUTC:now,source:sourceBinding,
  independent:false,sourceAccepted:false,qualified:false,kernelPending:true,
  completeUniqueContexts:contexts,contextExpansionRule:'Expand parent chain in order; fullProofInputs resolve case-sensitively to full types below. No omitted mathematical premise.',
  fullFrozenPropositions:requiredFacts,additionalPureLogicalPackages:extraFacts,
  publicOrdinary:ordinary,approvedOptionalOrdinary:inv.optionalOrdinary,actualSameModelChoices:choiceOrdinary,
  approvedInstances,APIImplicitInstances:inv.APIImplicitInstances,
  allPublicOrdinaryTypeRHSScopeRetained:true,soleInferredProp:'h247',allOtherSubstantiveFactsExplicitlyTyped:true,
  proofIntroductoryCoordinates:{original16:locate(initialIntro.trimEnd()),global6:locate('intro g r v rho β cWindow'),payment47:locate('intro '+paymentNames.join(' ')),physical4:locate('intro Tphysical H1source payment1 Ephysical')},
  actualHaveDeclarations:haveDeclarations.map(({offset,...x})=>x),
  countsDerived:{publicOrdinary:ordinary.length,approvedOptionalOrdinary:inv.optionalOrdinary.length,frozenProps:requiredFacts.length,
    additionalPureLogicalPackages:extraFacts.length,approvedInstanceRows:approvedInstances.length,usedApprovedInstanceRows:approvedInstances.filter(x=>x.used).length,
    APIImplicitRows:inv.APIImplicitInstances.length,actualDataChoices:choiceOrdinary.length,paymentLetIntroductions:paymentNames.length,newNatCutoffs:0},
  countsMeaning:'Frozen semantic occurrence/optional-cap inventory, not regex counts of repeated type-local lets or Lean actual constants.',...knownModel,operations
});

const inputChecks=activation.inputs.map(x=>{const b=bind(x.path);return{...b,exact:b.sha256===x.sha256&&b.bytes===x.bytes};});
if(inputChecks.length!==72||inputChecks.some(x=>!x.exact))throw Error('A bound input changed');
const reconstructedDeclaration=preamble+headerText+closing;
const candidateDeclaration=read(path.join(freeze,'CANDIDATE-DECLARATION.lean'));
const prefix=preamble+headerText+' := by\n';
if(reconstructedDeclaration!==candidateDeclaration)throw Error('Frozen declaration constituents differ');
if(!source.startsWith(prefix)||!source.endsWith(closing))throw Error('Frozen head/preamble/closing not exact');
if(!source.includes(initialIntro)||!source.includes(exactCall))throw Error('Frozen intro/call differs');
if(source.indexOf(exactCall)>source.indexOf('intro g r v rho β cWindow'))throw Error('Producer call after global lets');
if(/\b(sorry|admit|axiom|unsafe|native_decide)\b/.test(source))throw Error('Forbidden proof token');
if(/kClipped|kPayment/.test(source))throw Error('Old live cutoffs introduced');
if(source.charCodeAt(0)===0xfeff||source.includes('\r'))throw Error('Source encoding defect');
if([...source.matchAll(/^theorem /gm)].length!==1)throw Error('Public declaration count differs');
const opening={'(':')','[':']','{':'}','⟨':'⟩'};
const closingChars=new Set(Object.values(opening));
const stack=[];
for(const c of source.replace(/\/\*[\s\S]*?\*\//g,'').replace(/--[^\n]*/g,'')){
  if(opening[c])stack.push(opening[c]);
  else if(closingChars.has(c)&&stack.pop()!==c)throw Error('Textual delimiter mismatch '+c);
}
if(stack.length)throw Error('Textual delimiters unclosed');
put('LOCAL-VALIDATION.json',{
  schema:'oq56-unit248-local-byte-structure-checks-only-v1',atUTC:now,source:sourceBinding,
  status:'PASS_LOCAL_TEXT_AND_BINDING_CHECKS_ONLY',all72InputsExact:true,inputChecks,
  activation:bind(activationPath),frozenDeclaration:bind(path.join(freeze,'frozen-declaration.json')),
  frozenPreambleHeadClosingByteExact:true,reconstructedProspectiveDeclarationExact:true,
  original16IntroByteExact:true,singleH247CallByteExact:true,callBeforeGlobalsAndChoices:true,
  explicitFrozenHaveTypesDerived:requiredFacts.filter(x=>x.completeExplicitTypeInSource).length,
  allOther31FrozenSubstantiveFactsExplicitIncludingGuard:true,guardAntecedentIntroducedExactly:true,
  noForbiddenProofTokens:true,noOldLiveCutoffs:true,noNewNatCutoff:true,onePublicTheorem:true,textualDelimiterBalance:true,
  UTF8NoBOM:true,LFOnly:true,sourceLF:source.split('\n').length-1,
  kernelChecked:false,axiomAudited:false,qualified:false,sourceAccepted:false,
  limitation:'These deterministic checks do not parse, elaborate, compile or certify Lean or the mathematics.',operations
});
put('COMPATIBILITY.json',{
  schema:'oq56-unit248-complete-frozen-source-compatibility-v1',atUTC:now,source:sourceBinding,
  freeze:bind(path.join(freeze,'frozen-declaration.json')),activation:bind(activationPath),
  exactPreambleHeadClosing:true,original16BinderGroups:true,publicOrdinary:ordinary.length,optionalOrdinaryCap:inv.optionalOrdinary.length,
  frozenPropRows:requiredFacts.length,approvedInstanceRows:approvedInstances.length,APIImplicitRows:inv.APIImplicitInstances.length,
  sameCgAndM0ChoicesOnly:choiceOrdinary,whole247Universal71Retained:true,whole247Payment39Retained:true,newPublicPackageClauses:8,
  producerQualification:activation.qualifiedImmediateProducer,producerSourceSHA256:'6f64eb0d74346cf03f5eac8832cc39f377b0fb3ac50007200bdf11eefdc4ecaf',
  producerFIRSTOSHA256:'e926c6395aab6d532d9024dbabeb630e1ede634c277ab0167df0dbaf934701ca',producerNativeRC:0,producerAuditRC:0,
  reusedQualifiedInterfaces:[197,210,220,247],independent235237239Selectors:0,qualified239MainConsumed:false,
  newModel:false,newLaw:false,newNatCutoff:false,newSignOrAtomOrWindowAssumption:false,
  studentizerGuard:'Explicit 1 + rho ≤ sqrt n remains an antecedent; never asserted automatically.',
  sameFixedNPaymentAtOne:true,sameCgPayment1:true,sameMu0NuEta:true,
  exactPhysicalBranch:'if sqrt(centeredSq)=0 then 0 else (projectionW+residualStatisticD)/sqrt(centeredSq)',
  sourceFidelity:['original h/μ/g/r/v/rho/n','literal weighted sourceCost0 including partial deleted exponents and n-2 deletion','both original moment and remainder windows','clipping level1 fixed independently of current z','p54 repair retained','external Shao-Zhou attribution retained'],
  outsideScope:['external SZ existence/proof','sourceCost0 smallness','payment/error absorption','Gaussian relative error or CDF limit','atoms/noatom estimates or zero-denominator probability removal','full S11/S15/DC/OQ56/root closure'],
  independent:false,sourceAccepted:false,qualified:false,kernelPending:true,operations,...knownModel
});
put('LOCAL-TOOLING-HISTORY.json',{
  schema:'oq56-unit248-local-author-tooling-corrections-v1',atUTC:now,
  entries:[
    {kind:'platform interruption',record:'C:/game/shao lean/drafts/oq56/unit248/capacity-interruption-01/OBSERVATION.json',resumedSameRole:true,proofResult:null},
    {kind:'local interpreter unavailable',attempt:'python -c read-only JSON inspection',result:'Python was not found / Windows Store alias',resolution:'Used existing Node executable; installed nothing; no mathematical command.'},
    {kind:'local metadata selection',result:'PowerShell case-insensitive hCg/hcg selection produced excessive output and a bounded Substring exception',resolution:'Case-sensitive exact-name selection and Node object keys; no input bytes changed.'},
    {kind:'local source generator syntax error',attempt:1,result:'SyntaxError: missing ) after argument list in unused phHave function',resolution:'Removed unused function before successful generation; no Lean command or external operation.'},
    {kind:'local evidence writer syntax error',attempt:1,result:'SyntaxError: Unexpected token ) in context slicing',resolution:'Removed the extra parenthesis; no Lean command or external operation.'},
    {kind:'local inventory lexical guard',result:'An ASCII word-boundary exclusion mistakenly skipped ordinary Iη, reporting144 rather than145 rows',resolution:'Recognize literal let-plus-space directly; letI has no space. All145 frozen names and their order are now compared exactly. Source and mathematical premises unchanged.'},
    {kind:'unsealed draft formatting',result:'Initial local draft indentation/preamble newline preservation was corrected before any source-bound Lean gate',resolution:'Exact literal preamble/head/closing and typed local block validated in final source; no frozen input changed.'}
  ],failedLeanAttempts:0,uncertainExternalOperations:0,operations
});

const report=`# Unit248 complete author handoff

Status: COMPLETE_SOURCE_DRAFT_KERNEL_PENDING. This is an author candidate, not independent certification. The entire frozen declaration is implemented as one theorem in OriginalSameWitnessPhysicalPaidTailApplication.lean. No Lean, lake, kernel, pretty-printer, axiom, server, network, upload, Git, API or child operation was performed by this author. SourceAccepted=false, qualified=false, kernelPending=true.

The exact frozen preamble, full public head, original sixteen input groups and closing are retained. The sole 222-byte h247 call precedes all six global lets and all witness selection. The only two data choices are cg := Classical.choose hCg and m₀ := Classical.choose hModel, where both existential propositions are complete, explicitly typed projections of that one producer. The proof witnesses hm₀ and hcg are taken from the same model. μ₀ is exactly μ.trim hm₀. No independent 235, 237 or 239 selector is consumed. The original ν, normalization a/s and actual η family remain in the complete producer package.

The accepted247 proof was not reread or rechecked. Its qualification3259f836, source6f64eb0d, FIRSTOe926c639, native actualRC0, same-original-object audit actualRC0 and independent finalM5d71e4ed/release281d7514 are reused by hash. The complete actual current public TYPE was read through the318-entry lexical dictionary and431-line current main. Expanding the dictionary with every original trivia token independently restored all2,074,284 bytes to SHA256d2c1a11a exactly. TYPE247-RESTORATION.json records this local reconstruction. No PP/kernel/AX was invoked.

Proof route:

1. Preserve the six global conclusions, the entire71-clause universal package and the entire39-clause payment package. Apply only Eventually.mono to the old eventual set. Thus the same n and the same old fixed-n producer quantify over every admissible w and z; no natural-number cutoff is introduced.
2. From current1≤z and z≤remainderWindowScale Ktail t0*n^(1/6), derive1≤the same window. Specialize the same hPaymentAtN247 to the same w and level1. Its seventh component supplies original-mN H1 measurability and its sixteenth supplies P.real(H1 complement)≤payment1. Only one_mul is simplified. The exponential term exp(-cg*n) uses exactly the same cg.
3. Original symmetry of h and real additive algebra give symmetry of literal r. rho is nonnegative by sqrt. Ktail is nonnegative from its squareTailScale lower branch and Menv≥0. Qualified197 bounded_remainder_small_window at y=1, the actual originalUpper and originalRows bounds, and projectionGood membership give V>0 and |centeredDelta|≤1/32. The absolute-value lower inequality then gives centeredDelta≥-1/2.
4. Under the public antecedent1+rho≤sqrt n only, apply qualified210 literal_clippedCentered_comparison_on_projectionGood at512/rho/1. All its premises are supplied explicitly. This gives equality of clipped and actual delta, positivity and literal equality of the two denominators, and T0=Tphysical with the original centeredSq-zero branch. Consequently the exact disagreement event is contained in H1 complement and its original-P real measure is at most payment1.
5. In an isolated original-sample block, install only original mN and the probability instance of the literal original product P. Apply qualified220 to original Ω/mΩ/μ/h, the same n, source z=0 and C0=512. Its eleventh/twelfth components give global measurability of T0/Tphysical. All parameters and the full220 result are explicitly typed. No selected/reduced/augmented measure is substituted for original P. Equality-set measurability gives the exact disagreement measurable.
6. For every real t, measurable closed upper/lower events are direct preimages of Ici/Iic. If T0=Tphysical, membership agrees, so each literal symmetric difference is contained in the disagreement event. The pinned finite-measure abs_measureReal_sub_le_measureReal_symmDiff theorem followed by original-P monotonicity proves both absolute differences≤P.real(Ephysical)≤payment1. This includes equality thresholds and atoms; no continuity or atom-free assumption is used.
7. At the current z, retain the exact247 conditional Shao–Zhou bounds with the same cBudget, original strict moment window, L0 and full weighted sourceCost0. Combine their lower and upper inequalities with the two sides of the absolute comparison at t=z. Pure real order arithmetic gives normalLower-payment_z-payment1≤Pphysical(z)≤normalUpper+3*payment_z+payment1. No sign of sourceCost0 or normalLower, cost-smallness, error absorption or new source theorem existence is needed or claimed.

The original remainder window and strict moment window remain distinct and unchanged. The actual deleted normalization n-2, original weighted full/deleted integrals and fixed clipping1 are retained by the complete producer type. The p54 correction and external Shao–Zhou attribution are preserved. This does not establish externalSZ existence, a quantitative sourceCost0 bound, vanishing/absorbed payments, Gaussian-relative error, CDF passage, atom/noatom estimates, final zero-denominator removal, full S11/S15/DC/OQ56 or any root closure.

ACTUAL-PROP-CONTEXTS.json contains every full frozen proposition, source coordinates, all complete unique context layers,145 public ordinary type/RHS/scope rows,147 optional-cap rows including only the two approved data choices,8 instance-cap rows and5 implicit API rows. Additional names are explicitly typed pure logical whole packages or projections of frozen conclusions. These counts describe the frozen semantic inventory, not the count of repeated type-local lets in the generated source, actual Lean constants or machine receipts. No mathematical interface gap was found in this author pass. Elaboration and machine checks remain unperformed.

LOCAL-VALIDATION.json records local byte and textual checks only: all72 bindings exact; frozen declaration reconstruction exact; one public theorem; no forbidden escape/proof tokens; no kClipped/kPayment or new Nat cutoff; UTF8 without BOM and LF; balanced textual delimiters; full typed fact headers. Local tooling corrections and the capacity interruption are preserved in LOCAL-TOOLING-HISTORY.json and the original/new runtime ACKs. They are not mathematical proof failures or quota-exhaustion evidence.

Next exact dependency: the OQ56 lead independently intakes this sealed author packet, assigns a fresh complete source-to-statement/proof reviewer, and only after that source review conducts designated-server native and same-FIRSTO all-actual TYPE/required VALUE/transitive axiom gates. The author retains no continuing writer or execution authority after lastzeroRELEASE.json.

Requested model gpt-6.1-sol, effort xhigh. Actual backend/model/effort and separate input/cached-input/output/reasoning-subset usage are unknown/null. No token/subscription allocation inference is made.
`;
fs.writeFileSync(path.join(root,'REPORT.md'),report,'utf8');
put('CHECKPOINT.json',{
  schema:'oq56-unit248-complete-author-compact-checkpoint-v1',atUTC:now,role:activation.role,ownerChat:activation.ownerChat,
  status:'COMPLETE_SOURCE_DRAFT_READY_FOR_FRESH_INDEPENDENT_SOURCE_REVIEW',source:sourceBinding,
  exactFreeze:activation.exactFreeze,all72BindingsExact:true,sourceComplete:true,mathematicalInterfaceGap:null,
  kernelPending:true,qualified:false,sourceAccepted:false,authorIndependent:false,
  actualRuntime:'LOCAL_COMPLETION_SEALING_THEN_FINALWRITE_SIXZERO_RELEASE',heavy:0,inflight:0,pendingExternal:0,children:0,uncertainOperations:0,
  nextExactDependency:'Lead exact-source intake; fresh independent complete source-to-statement/proof review; then lead-only server native and same-FIRSTO allactual TYPE/requiredVALUE/transitiveAX. No oldproducer replay.',
  operations,...knownModel
});
console.log(JSON.stringify({source:sourceBinding,fullFrozenFacts:requiredFacts.length,publicOrdinary:ordinary.length,
  optionalOrdinary:inv.optionalOrdinary.length,haveDeclarations:haveDeclarations.length,all72BindingsExact:true,
  localTextValidation:'PASS',independent:false,qualified:false,kernelPending:true}));
