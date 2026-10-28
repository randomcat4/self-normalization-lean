"""Local textual inventory only; deliberately contains no Lean/server runner."""
from __future__ import annotations

from bisect import bisect_left
from datetime import datetime, timezone
import hashlib
import json
import re
from pathlib import Path

ROOT = Path("C:/game/shao lean")
OUT = ROOT / "drafts/oq56/unit249/author-01"
FREEZE = ROOT / "drafts/oq56/unit249/freeze-01"
SOURCE_PATH = OUT / "OriginalSameWitnessPhysicalRelativeTailApplication.lean"
SOURCE_BYTES = SOURCE_PATH.read_bytes()
S = SOURCE_BYTES.decode("utf-8")
I = json.loads((FREEZE / "INTERFACE-INVENTORY.json").read_bytes())
F = json.loads((FREEZE / "frozen-declaration.json").read_bytes())
FACTS = json.loads((OUT / "FACT-COORDINATES.json").read_bytes())
FACT_MAP = {x["name"]: x for x in FACTS}
P = I["publicOrdinary"]
O = I["optionalOrdinary"]
NOW = datetime.now(timezone.utc).isoformat()


def flat(s):
    return "".join(s.split())


def binding(p):
    p = Path(p)
    b = p.read_bytes()
    return {"path": p.as_posix(), "sha256": hashlib.sha256(b).hexdigest(), "bytes": len(b)}


def coord(pos):
    prefix = S[:pos]
    last_line = prefix.rsplit("\n", 1)[-1]
    return {"byte": len(prefix.encode("utf-8")), "line": prefix.count("\n") + 1,
            "column": len(last_line) + 1, "byteColumnUTF8": len(last_line.encode("utf-8")) + 1}


def write_json(name, data):
    (OUT / name).write_bytes((json.dumps(data, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))


def split_and(text):
    stack = []
    segments = []
    last = 0
    close = {')': '(', ']': '[', '}': '{'}
    for k, c in enumerate(text):
        if c in '([{':
            stack.append(c)
        elif c in close:
            assert stack and stack.pop() == close[c], (k, c)
        elif c == '∧' and not stack:
            segments.append(text[last:k].strip())
            last = k + 1
    assert not stack
    segments.append(text[last:].strip())
    return segments


PREAMBLE = (FREEZE / "FROZEN-PREAMBLE.txt").read_bytes()
HEAD = (FREEZE / "FROZEN-HEAD.txt").read_bytes()
CLOSING = (FREEZE / "FROZEN-CLOSING.txt").read_bytes()
HEAD_END = len((PREAMBLE + HEAD).decode("utf-8"))
assert SOURCE_BYTES.startswith(PREAMBLE + HEAD)
assert SOURCE_BYTES.endswith(CLOSING)
assert b'\r' not in SOURCE_BYTES and not SOURCE_BYTES.startswith(b'\xef\xbb\xbf')

inputs = []
for p in [FREEZE / "frozen-declaration.json"] + [Path(x["path"]) for x in F["files"]]:
    inputs.append(binding(p))
for row in F["files"]:
    assert binding(row["path"])["sha256"] == row["sha256"]
    assert binding(row["path"])["bytes"] == row["bytes"]
for item in [F["activation"], F["qualified248"], F["stage1Manifest"], F["parentIntake"], F["closingCorrection"]]:
    b = binding(item["path"])
    assert b["sha256"] == item["sha256"] and b["bytes"] == item["bytes"]
    inputs.append(b)
for p in [
    ROOT / "drafts/oq56/unit248/author-repair-02/OriginalSameWitnessPhysicalPaidTailApplication.lean",
    ROOT / "drafts/oq56/unit248/freeze-01/FROZEN-HEAD.txt",
    ROOT / "drafts/oq56/next-source/oq6-original-same-witness-physical-relative-tail-planned/author-stage1-01/SOURCE-ROUTE.md",
    ROOT / "drafts/oq56/next-source/oq6-original-same-witness-physical-relative-tail-planned/author-stage1-01/API-CONTEXT.md",
    ROOT / "AGENTS.md", ROOT / "SERVER.md", ROOT / "coordination/TEAM.md",
]:
    inputs.append(binding(p))
assert binding(ROOT / "drafts/oq56/unit248/author-repair-02/OriginalSameWitnessPhysicalPaidTailApplication.lean")["sha256"] == "50cc9872e1d6148e4a81f0d49da391a1b4b749b682c91b4ba347ae22bad00433"
old_head = (ROOT / "drafts/oq56/unit248/freeze-01/FROZEN-HEAD.txt").read_text(encoding="utf-8")
inherited_types = {x["name"]: flat(x["fullType"]) in flat(old_head)
                   for x in I["proposedProofFacts"] if len(x["fullType"]) > 1000}
assert all(inherited_types.values())

positions = [k for k, c in enumerate(S) if not c.isspace()]
compact = ''.join(S[k] for k in positions)
cursor = {}
ordinary = []
instances = []
fact_type_end = {}


def location_role(pos):
    if pos < HEAD_END:
        return "PUBLIC_HEAD", None
    for row in FACTS:
        if row["explicitType"] and row["typeStartCharacter"] <= pos < row["typeEndCharacterExclusive"]:
            return "FROZEN_FACT_TYPE_ONLY", row["name"]
    return "OPERATIVE_PROOF", None


def match_end(pos, pattern):
    k = bisect_left(positions, pos)
    assert compact.startswith(pattern, k), (coord(pos), pattern[:60])
    return positions[k + len(pattern) - 1] + 1


for m in re.finditer(r'(?m)^[ \t]*(?P<keyword>letI|let)[ \t]+(?:(?P<name>[^\s:]+)[ \t]+)?(?=:)', S):
    pos = m.start('keyword')
    role, fact = location_role(pos)
    start = coord(pos)
    if m['keyword'] == 'letI':
        candidates = []
        for j, row in enumerate(I['approvedInstances']):
            patterns = [flat('letI : ' + row['type'] + ' := ' + row['rhs'])]
            if row['name'] == 'selectedCountableGeneration':
                # The freeze's own letI spelling uses the preceding selectedSpace
                # instance; its full explicit ambient type is the approved row.
                patterns.append(flat('letI : MeasurableSpace.CountablyGenerated Ω := hcg'))
            for pat in patterns:
                if compact.startswith(pat, bisect_left(positions, pos)):
                    candidates.append((j, row, pat))
        assert len(candidates) == 1, (start, candidates)
        j, row, pat = candidates[0]
        end = match_end(pos, pat)
        instances.append({"keyword": "letI", "name": row['name'], "role": role,
                          "insideFact": fact, "start": start, "rhsEndExclusive": coord(end),
                          "freezeRef": f"approvedInstances/{j}", "type": row['type'], "rhs": row['rhs']})
        continue
    group = role if fact is None else role + '/' + fact
    minimum = cursor.get(group, 94 if fact in {'hOldPayments248', 'hOldAtN248', 'hOldAtCurrent248'} else 0)
    candidates = []
    for j, row in enumerate(P):
        if j + 1 <= minimum:
            continue
        pat = flat('let ' + row['name'] + ' : ' + row['type'] + ' := ' + row['rhs'])
        if compact.startswith(pat, bisect_left(positions, pos)):
            candidates.append((j + 1, j, row, pat))
    if role != 'OPERATIVE_PROOF' and candidates:
        ordinal, j, row, pat = min(candidates, key=lambda x: x[0])
        cursor[group] = ordinal
        ref = f'publicOrdinary/{j}'
        name = row['name']
        end = match_end(pos, pat)
    elif fact == 'hAbsorption236':
        pat = flat('let cWindow : ℝ := min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))')
        end = match_end(pos, pat)
        name, ordinal, ref = 'cWindow', None, 'proposedProofFacts/hAbsorption236/fullType/local-let'
    elif role == 'OPERATIVE_PROOF':
        matches = []
        for j, row in enumerate(O):
            pat = flat('let ' + row['name'] + ' : ' + row['type'] + ' := ' + row['rhs'])
            if compact.startswith(pat, bisect_left(positions, pos)):
                matches.append((j, row, pat))
        assert len(matches) == 1, (start, [x[0] for x in matches])
        j, row, pat = matches[0]
        end = match_end(pos, pat)
        name, ordinal, ref = row['name'], row.get('publicOccurrence'), f'optionalOrdinary/{j}'
    else:
        raise AssertionError((start, name, fact))
    ordinary.append({"keyword": "let", "name": name, "role": role, "insideFact": fact,
                     "start": start, "rhsEndExclusive": coord(end),
                     "publicOccurrence": ordinal, "freezeRef": ref})

public_rows = [x for x in ordinary if x['role'] == 'PUBLIC_HEAD']
assert len(public_rows) == 155
assert [x['publicOccurrence'] for x in public_rows] == list(range(1, 156))
assert len(ordinary) == 730
assert len(instances) == 8
operative_lets = [x for x in ordinary if x['role'] == 'OPERATIVE_PROOF']
assert [x['name'] for x in operative_lets] == ['cg', 'm₀', 'μ₀', 'payment', 'payment1']
assert len([x for x in instances if x['role'] == 'OPERATIVE_PROOF']) == 2

fact_headers = list(re.finditer(r'(?m)^  have ([^\s:]+)', S))
assert len(fact_headers) == 28 and {m[1] for m in fact_headers} == set(FACT_MAP)
explicit_types = {}
for row in FACTS:
    if row['explicitType']:
        explicit_types[row['name']] = flat(S[row['typeStartCharacter']:row['typeEndCharacterExclusive']]) == flat(row['fullType'])
assert len(explicit_types) == 27 and all(explicit_types.values())

intro_ordinary = []
intro_sets = [
    ('  intro g r v rho β cWindow', range(1, 7), 'N01'),
    ('  intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv cPaid', [146], 'N02'),
    ('  intro mN P N ξ0 D1 L0 sourceCost0 Tphysical R', range(147, 156), 'N05'),
]
for line, ordinals, context in intro_sets:
    start = S.index(line)
    for ordinal in ordinals:
        row = P[ordinal - 1]
        token_match = re.search(r'(?<!\S)' + re.escape(row['name']) + r'(?!\S)', line)
        assert token_match
        pos = start + token_match.start()
        intro_ordinary.append({"name": row['name'], "kind": "INTRO_OF_FROZEN_LET",
                               "start": coord(pos), "endExclusive": coord(pos + len(row['name'])),
                               "contextId": context, "freezeRef": f'publicOrdinary/{ordinal-1}',
                               "type": row['type'], "rhs": row['rhs']})
assert len(intro_ordinary) == 16

choices = []
for m in re.finditer(r'Classical\.choose\b', S):
    pos = m.start()
    containing = next((x['name'] for x in FACTS if x['startCharacter'] <= pos < x['endCharacterExclusive']), None)
    if containing is None:
        selected = next(x for x in operative_lets if x['start']['byte'] <= len(S[:pos].encode('utf-8')) < x['rhsEndExclusive']['byte'])
        name = selected['name']
        choice = next(x for x in I['actualSameModelChoicesProposed'] if x['name'] == name)
        choices.append({"name": name, "kind": "DATA_CHOICE_SAME248", "start": coord(pos),
                        "fullType": choice['type'], "rhs": choice['rhs'],
                        "contextId": choice['contextId'], "fullExistentialFreezeRef": f'proposedProofFacts/{"hCg" if name == "cg" else "hModel"}',
                        "declarationStart": selected['start'], "declarationEndExclusive": selected['rhsEndExclusive']})
    else:
        assert containing in {'hm₀', 'hcg'}
        choices.append({"name": containing, "kind": "PROOF_WITNESS_SAME_HMODEL", "start": coord(pos),
                        "fullType": FACT_MAP[containing]['fullType'],
                        "freezeRef": f'proposedProofFacts/{containing}',
                        "notAdditionalDataSelection": True})
assert len(choices) == 4 and sum(x['kind'] == 'DATA_CHOICE_SAME248' for x in choices) == 2

aux_n_pos = S.index('intro n hAuxAtN') + len('intro ')
aux_fact_pos = S.index('intro n hAuxAtN') + len('intro n ')
filter_line = 'n hOldAtNRaw248 hPaidAtN hGuardAtN hAbsorptionAtN'
filter_start = S.index(filter_line)
actual_cwindow = 'min (1 : ℝ) (Real.sqrt t0 / (2 : ℝ))'
absorb_predicate = (
    f'4 ≤ n ∧ (1 : ℝ) ≤ ({actual_cwindow}) * Real.rpow (n : ℝ) (1 / 6 : ℝ) ∧\n'
    f'∀ z : ℝ, (1 : ℝ) ≤ z → z ≤ ({actual_cwindow}) * Real.rpow (n : ℝ) (1 / 6 : ℝ) →\n'
    '(6 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) +\n'
    '  (2 : ℝ) * Real.exp (-cg * (n : ℝ)) +\n'
    '  (8 : ℝ) * Real.exp (-Real.sqrt (n : ℝ) / (2 : ℝ)) ≤\n'
    '  Real.exp (-(t0 / (2 : ℝ)) * Real.rpow (n : ℝ) (1 / 3 : ℝ)) * Shao.standardNormalTail z')
aux_predicate = absorb_predicate.replace('t0', '((2 * cPaid) ^ (2 : ℕ))')
internal_binders = [
    {"name": "n", "type": "ℕ", "start": coord(aux_n_pos), "scope": "hPaidNonemptyEventually proof; dummy eventual argument; no cutoff choice"},
    {"name": "hAuxAtN", "type": aux_predicate, "start": coord(aux_fact_pos), "scope": "predicate of qualified236 specialized at inline (2*cPaid)^2; existing predicate pattern only"},
]
patterns = {
    'n': ('ℕ', 'N03'),
    'hOldAtNRaw248': (FACT_MAP['hOldAtN248']['fullType'], 'N03'),
    'hPaidAtN': ('4 ≤ n ∧ (1 : ℝ) ≤ cPaid * Real.rpow (n : ℝ) (1 / 6 : ℝ)', 'N03'),
    'hGuardAtN': ('1 + rho ≤ Real.sqrt (n : ℝ)', 'N03'),
    'hAbsorptionAtN': (absorb_predicate, 'N03'),
}
for name, (typ, context) in patterns.items():
    offset = re.search(r'(?<!\S)' + re.escape(name) + r'(?!\S)', filter_line).start()
    internal_binders.append({"name": name, "type": typ, "start": coord(filter_start + offset),
                             "contextId": context, "scope": "filter_upwards destructures exactly four preexisting eventual predicates; no new interface"})
threshold_start = S.index('fun x hx => hx')
internal_binders += [
    {"name": "x", "type": "ℝ", "start": coord(threshold_start + 4), "scope": "threshold witness for Filter.eventually_atTop; N02"},
    {"name": "hx", "type": "1 + rho ≤ x", "start": coord(threshold_start + 6), "scope": "existing threshold implication argument; N02"},
]

old_current = FACT_MAP['hOldAtCurrent248']['fullType']
old_current_body = old_current[old_current.index('        Measurable[mN'):]
fields40 = split_and(old_current_body)
physical = fields40[-1].strip()[1:-1].strip()
start8 = re.search(r'(?m)^\s*\(1 : ℝ\) ≤ remainderWindowScale', physical).start()
fields8 = split_and(physical[start8:])
guard = fields8[-1].strip()[1:-1].strip()
consequence = guard[guard.index('→') + 1:].strip()
fields6 = split_and(consequence)
assert (len(fields40), len(fields8), len(fields6)) == (40, 8, 6)
assert fields6[-1].startswith('(∀ (C1 C2 C3 C4 : ℝ)')
assert 'payment - payment1' in fields6[-1] and '3 * payment + payment1' in fields6[-1]

delimiter_stack = []
closing = {')': '(', ']': '[', '}': '{'}
for pos, c in enumerate(S):
    if c in '([{': delimiter_stack.append(c)
    elif c in closing: assert delimiter_stack and delimiter_stack.pop() == closing[c], coord(pos)
assert not delimiter_stack
forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', S)
assert not forbidden
producer = 'Shao.OQ6.OriginalSameWitnessPhysicalPaidTailApplication.actual_original_same_witness_physical_paid_scalar_tail_application'
assert S.count(producer) == 1
assert S.index(producer) < S.index('  intro g r v rho β cWindow') < S.index('  let cg :') < S.index('  let m₀ :')
assert len(re.findall(r'(?m)^theorem\s', S)) == 1

textual_checks = {
    "schema": "oq56-unit249-local-textual-checks-not-elaboration-v1", "atUTC": NOW,
    "source": binding(SOURCE_PATH), "UTF8NoBOM": True, "LFOnly": True,
    "preambleByteExact": True, "publicHeadByteExact": True, "closingByteExact": True,
    "publicOrdinary155ExactOrderAndRHS": True, "optionalOrdinaryFrozen159": len(O),
    "all730LexicalOrdinaryLetOccurrencesMapped": True,
    "all8ExistingInstanceLetOccurrencesMapped": True,
    "all27ExplicitFactTypesExactModuloWhitespace": explicit_types,
    "soleInferredProp": "h248", "all28HaveRowsPresentExactlyOnce": True,
    "allLargeInheritedTypesSubstringsOfQualified248HeadModuloWhitespace": inherited_types,
    "dataChoices": 2, "proofWitnessChoices": 2, "newNatCutoffChoices": 0,
    "producer248Calls": 1, "producerCallBeforeAllGlobalLetsAndDataChoices": True,
    "physicalProjectionFieldCounts": [40, 8, 6], "physicalProjectionRightStepsBeforeGuard": 46,
    "physicalProjectionRightStepsAfterGuard": 5,
    "allDelimiterStacksEmpty": True, "forbiddenProofTokens": forbidden,
    "newTopLevelHelpers": 0, "newStructures": 0, "newInstances": 0,
    "sourceTheorems": 1, "LeanParsingOrElaborationPerformed": False,
    "notMathematicalIndependentReview": True, "notKernelEvidence": True,
}
write_json('TEXTUAL-CHECKS.json', textual_checks)

fact_summary = [{k: v for k, v in row.items() if k not in {'fullType'}} for row in FACTS]
write_json('DECLARATION-COORDINATES.json', {
    "schema": "oq56-unit249-exhaustive-source-coordinate-map-v1", "source": binding(SOURCE_PATH),
    "coordinateConvention": "UTF8 byte offset zero based; line, codepoint column and UTF8 byte column one based; end is exclusive",
    "ordinaryLets": ordinary, "instanceLets": instances, "facts": fact_summary,
    "proofOrdinaryIntroductionsOfFrozenLets": intro_ordinary,
    "allClassicalChooseOccurrences": choices,
    "chooseSpecOccurrences": [coord(m.start()) for m in re.finditer(r'Classical\.choose_spec\b', S)],
    "internalPatternBindings": internal_binders,
    "otherOriginalBinderIntroductions": [
        {"sourceLine": line, "start": coord(S.index(line)), "fullContextFreezeRef": context}
        for line, context in [
            ('  intro Ω mΩ μ hμProbability h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp cBudget hcBudget', 'completeUniqueContexts/N00'),
            ('  intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv cPaid', 'completeUniqueContexts/N02'),
            ('  intro w hW hWR hSq hSqBound hEnv z hz hzPaidWindow', 'completeUniqueContexts/N04'),
            ('  intro C1 C2 C3 C4 hSZcBudget hzMomentWindow', 'completeUniqueContexts/N07'),
        ]],
    "typeOnlyBindingPolicy": "Repeated let/letI in explicitly copied frozen Prop types are recorded as type bindings; they are not fresh operative models or selectors.",
})

payload_names = [
    'OriginalSameWitnessPhysicalRelativeTailApplication.lean',
    'SOURCE-ROUTE.md', 'AUTHOR-PROOF.md', 'FACT-COORDINATES.json',
    'DECLARATION-COORDINATES.json', 'TEXTUAL-CHECKS.json',
    'generate_unit249.py', 'build_manifest.py',
]
payloads = [binding(OUT / name) for name in payload_names]
manifest = {
    "schema": "oq56-unit249-frozen-full-implementation-author-v1", "atUTC": NOW,
    "role": "/root/oq56_unit249_author", "ownerChat": "01a1822b-1815-7f21-a1af-2e0b15ee67a5",
    "rootCoordinator": "01a17d3c-6dfd-7cc0-94ed-35d758a423a5",
    "ownedRoot": OUT.as_posix(), "unit": 249,
    "module": "Shao.OQ6.OriginalSameWitnessPhysicalRelativeTailApplication",
    "publicTheorem": "Shao.OQ6.OriginalSameWitnessPhysicalRelativeTailApplication.actual_original_same_witness_physical_relative_tail_application",
    "STATUS": "PROVED_UNCHECKED_COMPLETE_FROZEN_IMPLEMENTATION",
    "proofStatus": "PROVED", "proofStatusQualifier": "author complete proof; NOT kernel checked",
    "sourceComplete": True, "sourceAccepted": False, "independent": False,
    "qualified": False, "kernelChecked": False, "kernelPending": True, "axiomAudited": False,
    "source": binding(SOURCE_PATH), "sourceLF": S.count('\n'), "sourceUTF8NoBOM": True,
    "sourceLFOnly": True, "preambleHeadClosingByteExact": True,
    "frozenDeclaration": binding(FREEZE / 'frozen-declaration.json'),
    "inputCountDerived": len(inputs), "inputs": inputs,
    "payloadCountDerivedExcludingManifestAndLastRelease": len(payloads), "payloads": payloads,
    "allInputsAndPayloadsHashBound": True,
    "frozenCounts": F['constraints'],
    "actualDerivedCounts": {
        "publicOrdinary": len(public_rows), "optionalOrdinaryCatalog": len(O),
        "allLexicalOrdinaryLetOccurrencesIncludingTypeCopies": len(ordinary),
        "allLexicalInstanceLetOccurrencesIncludingTypeCopies": len(instances),
        "operativeOrdinaryLetDeclarations": len(operative_lets),
        "operativeIntroOfFrozenOrdinaryLet": len(intro_ordinary),
        "operativeExistingInstances": sum(x['role'] == 'OPERATIVE_PROOF' for x in instances),
        "haveRows": len(FACTS), "explicitFullTypeHaveRows": len(explicit_types), "permittedInferredPropHaveRows": 1,
        "dataChoices": 2, "proofWitnessChoicesFromSameExistential": 2,
        "newNatCutoffs": 0, "newTopLevelHelpers": 0, "newSelectors": 0,
        "newStructures": 0, "newInstances": 0,
    },
    "allActualLetHaveInstanceChoiceCoordinates": {
        "exhaustiveBoundLedger": binding(OUT / 'DECLARATION-COORDINATES.json'),
        "fullFrozenFactTypeCoordinateLedger": binding(OUT / 'FACT-COORDINATES.json'),
        "haveRowsWithExactSourceCoordinatesAndFreezeMapping": fact_summary,
        "operativeOrdinaryLetsWithExactSourceCoordinatesAndFreezeMapping": operative_lets,
        "operativeIntroOfFrozenLetsWithExactCoordinatesAndFreezeMapping": intro_ordinary,
        "operativeInstances": [x for x in instances if x['role'] == 'OPERATIVE_PROOF'],
        "allChoiceOccurrences": choices,
        "internalPatternBindingsRecorded": True,
        "typeOnlyRepeatedLetOccurrencesRecorded": True,
    },
    "qualificationReuse": {
        "qualified248Evidence": F['qualified248'],
        "qualified248Source": binding(ROOT / 'drafts/oq56/unit248/author-repair-02/OriginalSameWitnessPhysicalPaidTailApplication.lean'),
        "producer248Invocations": 1, "sameCGAndM0Only": True,
        "noOldProofOrTYPEOrAXReplay": True,
        "qualified236ExactInterfaceAndEvidence": I['source236QualifiedEvidence'],
        "236ActualT0Use": "fee absorption and positivity",
        "236InlineSquaredParameterUse": "only common-window nonemptiness",
    },
    "semanticScope": F['semanticScope'], "newAssumptions": False,
    "weightedFullAndDeletedSourceCostUnchanged": True, "externalSZUnchanged": True,
    "originalPhysicalZeroBranchUnchanged": True, "rhoFixedBeforeCommonEventualN": True,
    "noPsiDivisionOrCostSmallness": True, "fullOQ56": "OPEN", "CDFRootClosure": False,
    "readingFrontier": {
        "fullPublicHeadAndNewContractRead": True, "allUniqueNewContextsAndNewFactTypesRead": True,
        "repeatedLargeFactTypesComparedAgainstFullyReadQualified248PublicHead": inherited_types,
        "allImportedDefinitionTypesAndRHSReadFromFrozenInventory": 32,
        "fullOldProofReReview": False,
        "oldSourceReading": "hash binding and limited witness/projection implementation idioms only; not a new complete review",
        "originalP51P54": "source route/semantic qualification inherited from immutable stage1 and qualified248; no new claim of rereading full originals",
    },
    "localTextualValidation": binding(OUT / 'TEXTUAL-CHECKS.json'),
    "nextExactDependency": "Fresh qualified independent complete249 SOURCE/proof review, then lead-designated server native and same-first-original-object all-actualTYPE/requiredVALUE/transitiveAX. No old248/236 proof/TYPE/AX replay.",
    "operations": {x: 0 for x in ['Lean', 'lake', 'kernel', 'PP', 'AX', 'server', 'network', 'upload', 'Git', 'publicationAPI', 'children']},
    "operationsClarification": "Local file tools and collaboration ACK used; API zero refers external publication/API operations, not the local tool transport.",
    "requestedModel": "gpt-6.1-sol", "requestedEffort": "xhigh",
    "actualBackend": None, "actualModel": None, "actualEffort": None,
    "usage": {x: None for x in ['input', 'cachedInput', 'output', 'reasoningSubset']},
}
write_json('MANIFEST.json', manifest)
print(json.dumps({"status": manifest['STATUS'], "source": manifest['source'],
                  "counts": manifest['actualDerivedCounts'], "inputCount": len(inputs),
                  "payloadCount": len(payloads), "Lean": 0}, ensure_ascii=False))
