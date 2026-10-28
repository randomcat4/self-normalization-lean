from pathlib import Path
import datetime, hashlib, json

root = Path('C:/game/shao lean')
f = root / 'drafts/oq56/unit256/freeze-01'
f.mkdir(parents=True, exist_ok=False)
previous = root / 'drafts/oq56/unit255/freeze-01/FROZEN-HEAD.txt'
current = previous.read_text(encoding='utf-8')
old = root / 'library/Shao/OQ6/OriginalLiteralWeightedConsumer.lean'
old_text = old.read_text(encoding='utf-8')
old_head = 'theorem ' + old_text.split('theorem ', 1)[1].split(' := by', 1)[0]
boundary = '      IsProbabilityMeasure μ₀ ∧\n'
assert current.count(boundary) == old_head.count(boundary) == 1
prefix, packet = current.split(boundary, 1)
prefix = prefix.replace('actual_original_level_dependent_canonical_cost_packet',
                        'actual_original_level_dependent_literal_weighted_consumer')
sequence = old_head.split(boundary, 1)[1]
q = '      ∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)\n          (z : ℝ) (hz : 0 ≤ z),\n'
assert sequence.count(q) == 1 and sequence.count('C0 rho 1') == 4
sequence = sequence.replace(q,
    '      ∀ (n : ℕ) (hn : 4 ≤ n)\n'
    '          (z : ℝ) (hz : 1 ≤ z)\n'
    '          (hwindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))),\n')
sequence = sequence.replace('C0 rho 1', '512 rho z')
assert 'C0' not in sequence
bound = ('64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) *\n'
         '            (1 + rho) * (1 + z) ^ 3 / Real.sqrt (n : ℝ)')
sequence = sequence.rstrip() + ' ∧\n        0 ≤ sourceCost0 ∧\n        sourceCost0 ≤\n          ' + bound + ' ∧\n'
sequence += ('        (∀ δ : ℝ, 0 < δ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →\n'
             '          sourceCostη k ≤\n            ' + bound.replace('\n            ', '\n              ') + ' + δ)\n')
# Both clauses share the single original m0/trim-mu0 selected by unit255.
assert packet.startswith('      ∀ ')
wrapped_packet = packet.replace('      ∀ ', '      (∀ ', 1).rstrip() + ') ∧\n'
head = prefix + boundary + wrapped_packet + sequence
assert (wrapped_packet.replace('      (∀ ', '      ∀ ', 1)[:-4] + '\n') == packet
preamble = '''import Shao.OQ6.OriginalLevelDependentCanonicalCostPacket
import Shao.OQ6.LiteralDeletedWeightedCosts
import Shao.OQ6.NormalizedRemainderEnvelope

set_option autoImplicit false
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology MeasureTheory
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLevelDependentLiteralWeightedConsumer
noncomputable section

'''
closing = '\nend\n\nend Shao.OQ6.OriginalLevelDependentLiteralWeightedConsumer\n'
route = '''# 第256单元冻结路线：保留同一模型的当前层级完整费用极限

最外层原假设与255完全相同。同一个m₀在所有n/current-level/ε之前选择。第一合取逐字保留255的整个forall n/y/ε当前canonical/bare/weighted packet；第二合取才给同一个m₀、μ₀下每个n/z的实际编码序列及费用极限。这样后续预算或事件消费者不会被迫另选一个可能不兼容的模型。第一包比较阈值仍为任意实数；第二包当前z同时供给预算和权重，固定512 rho z。

只在255 qualified并释放后激活作者。调用255一次取m₀与整包，把整包直接保留为第一合取。第二合取按已接受228 OriginalLiteralWeightedConsumer完整结构，取ε(k)=1/(8√n(k+1))，在同一255合同各ε(k)处取得实际ν/q/Y/η/删除因子。ν与q不依赖ε，但每次实际归一参数/η/factor必须来自该k的合同，不能从k=0复用变化的归一量。

用相同eval/q运输给原ξ的均值0/L²/总能量1及Y的量化误差。当前A=|D|、B=B_z及真实删除量的裸L1来自255。已接受LiteralDeletedWeightedCosts.literal_deleted_weighted_cost_limits及NormalizedRemainderEnvelope.actual_normalized_remainder_envelope_spec只要求这些输入；使用原来的H=(1+V)(√n+z√(1+B))、删H、K=4√n、M=KεH、真signed Q、Anew=A+M和真实删除差Δ。不能替换为粗糙混合四矩包络，不能把weighted L1反推bare L1。

同一保测id与q把完整/部分权重的极限送回原P；每个部分项仍除完整Iη(k)，禁止部分归一。保留228原有所有归一η性质、M/Anew/B因子、retained删除因子、signed差L1、全/部分积分/比值极限、sourceCost和compactCost极限。当前正分母/zeroV convention保持。

在同一255原费用界下补充sourceCost0非负和显式三次界。由sourceCostη→sourceCost0给每个δ>0最终sourceCostη≤该界+δ；不能声称每个有限k都有未留余量的同一个界。此处没有引入费用小性前提或新增p矩。

原p51/p54范围、Root固定clip1三次费用反例及Shao–Zhou外部归属保留。后续仍需同一模型上的原p矩严格budget、actual upper-event和true physical付款联合、外部源引擎及relative-tail/CDF/DC消费；fullOQ56/root OPEN。本冻结不实现证明，不执行Lean/服务器/网络/API，不增加作者或调度。
'''

def write(name, content):
    assert '\r' not in content and content.endswith('\n')
    with (f / name).open('xb') as out:
        out.write(content.encode('utf-8'))

for name, text in [('FROZEN-PREAMBLE.txt', preamble), ('FROZEN-HEAD.txt', head),
                   ('FROZEN-CLOSING.txt', closing), ('SOURCE-ROUTE.md', route)]:
    write(name, text)

def fp(path):
    data = path.read_bytes()
    return {'path': path.as_posix(), 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}

record = {
    'schema': 'oq56-unit256-exact-currentlevel-literal-weighted-consumer-freeze-v1',
    'atUTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'leadOwner': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
    'module': 'Shao.OQ6.OriginalLevelDependentLiteralWeightedConsumer',
    'publicDeclaration': 'actual_original_level_dependent_literal_weighted_consumer',
    'preamble': fp(f/'FROZEN-PREAMBLE.txt'), 'head': fp(f/'FROZEN-HEAD.txt'),
    'closing': fp(f/'FROZEN-CLOSING.txt'), 'route': fp(f/'SOURCE-ROUTE.md'),
    'headLF': head.count('\n'), 'oldQualified228Source': fp(old),
    'bearing255Frozen': fp(root/'drafts/oq56/unit255/freeze-01/frozen-declaration.json'),
    'whole255AllEpsilonPacketLiteralRetained': True, 'sameWitnessRequired': True,
    'extraPremisesAllowed': False, 'authorActivated': False,
    'qualified255RequiredBeforeActivation': True,
    'publicTheoremCount': 1, 'noTopLevelHelpersDefsInstances': True,
    'allPartialDenominatorsFullNormalizer': True, 'fullOQ56': 'OPEN'
}
write('frozen-declaration.json', json.dumps(record, ensure_ascii=False, indent=2)+'\n')
print(json.dumps({'freeze': fp(f/'frozen-declaration.json'), 'head': record['head'],
                  'headLF': record['headLF'], 'all255PacketLiteralRetained': True}, ensure_ascii=False))
