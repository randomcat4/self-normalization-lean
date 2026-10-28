from pathlib import Path
import datetime, hashlib, json, re

root = Path('C:/game/shao lean')
freeze = root / 'drafts/oq56/unit255/freeze-01'
old = root / 'library/Shao/OQ6/OriginalClippedCanonicalCostPacket.lean'
text = old.read_text(encoding='utf-8')
head = 'theorem ' + text.split('theorem ', 1)[1].split(':= by', 1)[0]
head = head.replace('actual_original_clipped_canonical_cost_packet',
                    'actual_original_level_dependent_canonical_cost_packet')
old_quantifier = '      ∀ (n : ℕ) (hn : 4 ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)\n'
assert head.count(old_quantifier) == 1
head = head.replace(old_quantifier,
    '      ∀ (n : ℕ) (hn : 4 ≤ n)\n'
    '          (y : ℝ) (hy : 1 ≤ y)\n'
    '          (hywindow : y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)))\n')
assert head.count('C0 rho 1') == 4
head = head.replace('C0 rho 1', '512 rho y')
head = re.sub(r'\bB1del\b', 'Bdelete', head)
head = re.sub(r'\bB1\b', 'B', head)
assert 'C0' not in head

weighted = '''        let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => gcoord i (O i ζ)
        let S0 : (Fin n → Ω) → ℝ := fun ζ =>
          ∑ j : Fin n, (y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
        let S0delete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
          ∑ j ∈ Finset.univ.erase i, (y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
        let Sν : (Fin n → Ω × ℝ) → ℝ := fun x =>
          ∑ j : Fin n, (y * ξ j x - (y * ξ j x) ^ 2 / 2)
        let Sνdelete : (Fin n → Ω × ℝ) → Fin n → ℝ := fun x i =>
          ∑ j ∈ Finset.univ.erase i, (y * ξ j x - (y * ξ j x) ^ 2 / 2)
        let fullTest0 : (Fin n → Ω) → ℝ := fun ζ => y * A ζ + y ^ 2 * B ζ
        let deleteTest0 : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
          min |y * ξ0 i ζ| 1 * (|A ζ - Adel ζ i| + y * |B ζ - Bdelete ζ i|)
        let fullTestν : (Fin n → Ω × ℝ) → ℝ := fun x => fullTest0 (q x)
        let deleteTestν : (Fin n → Ω × ℝ) → Fin n → ℝ := fun x i => deleteTest0 (q x) i
        let Ioriginal : ℝ := ∫ ζ : Fin n → Ω, Real.exp (S0 ζ) ∂P
        let Ireduced : ℝ := ∫ ζ : Fin n → Ω, Real.exp (S0 ζ) ∂P₀
        let Icoded : ℝ := ∫ x : Fin n → Ω × ℝ, Real.exp (Sν x) ∂ν
        let costOriginal : ℝ :=
          ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) +
            ∑ i : Fin n, ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P) / Ioriginal
        let costReduced : ℝ :=
          ((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) +
            ∑ i : Fin n, ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) / Ireduced
        let costCoded : ℝ :=
          ((∫ x, fullTestν x * Real.exp (Sν x) ∂ν) +
            ∑ i : Fin n, ∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) / Icoded
'''
marker = '        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧\n'
assert head.count(marker) == 1
head = head.replace(marker, weighted + marker)
extra = ''' ∧
        (∀ x : Fin n → Ω × ℝ, Sν x = S0 (q x)) ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), Sνdelete x i = S0delete (q x) i) ∧
        0 < Ioriginal ∧ Ireduced = Ioriginal ∧ Icoded = Ioriginal ∧
        0 < Ireduced ∧ 0 < Icoded ∧
        Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P ∧
        (∀ i : Fin n,
          Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P) ∧
        Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P₀ ∧
        (∀ i : Fin n,
          Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P₀) ∧
        Integrable (fun x => fullTestν x * Real.exp (Sν x)) ν ∧
        (∀ i : Fin n,
          Integrable (fun x => deleteTestν x i * Real.exp (Sνdelete x i)) ν) ∧
        (∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) =
          ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P ∧
        (∫ x, fullTestν x * Real.exp (Sν x) ∂ν) =
          ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P ∧
        (∀ i : Fin n,
          (∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) =
            ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P) ∧
        (∀ i : Fin n,
          (∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) =
            ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P) ∧
        costReduced = costOriginal ∧ costCoded = costOriginal ∧
        0 ≤ costOriginal ∧ 0 ≤ costReduced ∧ 0 ≤ costCoded ∧
        costOriginal ≤
          64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
            (1 + y) ^ 3 / Real.sqrt (n : ℝ) ∧
        costReduced ≤
          64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
            (1 + y) ^ 3 / Real.sqrt (n : ℝ) ∧
        costCoded ≤
          64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
            (1 + y) ^ 3 / Real.sqrt (n : ℝ)
'''
head = head.rstrip() + extra
preamble = '''import Shao.OQ6.OriginalLevelDependentCanonicalCoding
import Shao.OQ6.OriginalLevelDependentWeightedSourceCost
import Shao.OQ6.OriginalLevelDependentCorrectionEnvelope
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical symmDiff
open Shao.OQ5.P51

namespace Shao.OQ6.OriginalLevelDependentCanonicalCostPacket

noncomputable section

'''
closing = '\nend\n\nend Shao.OQ6.OriginalLevelDependentCanonicalCostPacket\n'
core = head.replace(weighted, '').split('        (∀ ξ : Fin n → Ω, 0 ≤ A ξ', 1)[0]
bare = core[core.index('        let J :'):core.index(marker)]
core = core.replace(bare, '')
assert core.endswith('≤ p0) ∧\n')
core = (core[:-3] + '\n').replace('actual_original_level_dependent_canonical_cost_packet',
                                'actual_original_level_dependent_canonical_normalized_coding')
assert core == (root/'drafts/oq56/unit254/freeze-01/FROZEN-HEAD.txt').read_text(encoding='utf-8')

def write_new(name, content):
    assert '\r' not in content and content.endswith('\n')
    with (freeze / name).open('xb') as handle:
        handle.write(content.encode('utf-8'))

for name, value in [('FROZEN-PREAMBLE.txt', preamble), ('FROZEN-HEAD.txt', head),
                    ('FROZEN-CLOSING.txt', closing)]:
    write_new(name, value)

route = '''# 第255单元冻结路线：同一当前层级编码与真实费用运输

本单元把254完整canonical合同、当前512 rho y裸费用和250完整/逐坐标删除加权费用放在同一m₀、P₀、ν、q、η见证中。m₀在全部n/y/ε之前选择；原始产品可测L²/逐点对称/中心化/投影二矩1以外不增加前提。比较阈值z仍任意实数；当前权重/预算使用y≥1及原tilt window。固定clip1三次费用已被Root二点模型否定，不允许恢复。

先调用最终qualified254一次，不能用第二个独立模型替换m₀。原252在原μ/P上的完整未加权D/J/A/B/删除量L1与全局界和250当前y加权费用直接用原前提实例化；不从加权L1反推裸L1。原mΩ实例显式传入，绝不把μ₀下积分投影偷偷等同μ下投影。

从254真实删除三元组及可测截面τ(ζ)i=(ζi,1/2)取得Ddel/Jdel/Bdelete的mN₀可测性。按已接受OriginalClippedCanonicalCostPacket完整路线，利用对称残差 incident row=√n(n−1)(D−Ddel)及J=row平方和/(n−2)²，得到当前J/B可测，保留真实删除系数与所有裸费用。

原id:(mN,P)→(mN₀,P₀)保测由hm₀与254 map-id构造；同一q:(ν→P₀)保测。先证mN₀下全/删除加权函数可测，使用MeasurePreserving.integrable_comp及integral_map运输原P的完整250合同到P₀和ν。Sν=S0∘q及删除权重逐点对应；所有删除项分母均是完整Ioriginal/Ireduced/Icoded，不能换成部分归一因子。输出原、缩减、编码三费用精确相等、正完整分母、全/删除weighted L1及同一显式三次界。

这是基底ξ费用运输，尚不是η校正费用的极限。后续需252 H/M/κ/真实signed差L1包与228全/部分weight连续极限机制，固定n/y下exp(weight)≤exp(n/2)、cap≤1，无需混合四矩；再对齐严格预算231、实际upper-events232及物理坏事件付款。Shao–Zhou外部输入、p54仅收敛/统一上界修复继续保留。fullOQ56/root OPEN。

所有冻结字节在作者之前形成；仅在254新源完整独审/同首O机器证据qualified并释放后激活255作者。冻结阶段没有Lean/服务器/API/作者运行。禁止增删假设、sorry/admit/axiom/unsafe/native_decide；不创建顶层辅助定义/实例，唯一公共定理。若接口实际不成立报告精确缺口，不得静改。
'''
write_new('SOURCE-ROUTE.md', route)

def fp(path):
    data = path.read_bytes()
    return {'path': path.as_posix(), 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}

record = {
    'schema': 'oq56-unit255-exact-currentlevel-canonical-costpacket-freeze-v1',
    'atUTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'leadOwner': '01a1822b-1815-7f21-a1af-2e0b15ee67a5',
    'module': 'Shao.OQ6.OriginalLevelDependentCanonicalCostPacket',
    'publicDeclaration': 'actual_original_level_dependent_canonical_cost_packet',
    'preamble': fp(freeze/'FROZEN-PREAMBLE.txt'), 'head': fp(freeze/'FROZEN-HEAD.txt'),
    'closing': fp(freeze/'FROZEN-CLOSING.txt'), 'route': fp(freeze/'SOURCE-ROUTE.md'),
    'headLF': head.count('\n'), 'oldAcceptedSource': fp(old),
    'bearing254Candidate': fp(root/'drafts/oq56/unit254/author-01/OriginalLevelDependentCanonicalCoding.lean'),
    'bearing250Qualified': fp(root/'drafts/oq56/unit250/qualified-evidence.json'),
    'bearing252Qualified': fp(root/'drafts/oq56/unit252/qualified-evidence.json'),
    'canonical254FullContractLiteralPreserved': True, 'sameWitnessRequired': True,
    'allPartialDenominatorsFullNormalizer': True, 'currentClipYIndependentComparisonZ': True,
    'extraPremisesAllowed': False, 'authorActivated': False,
    'qualified254RequiredBeforeActivation': True, 'publicTheoremCount': 1,
    'noTopLevelHelpersDefsInstances': True, 'fullOQ56': 'OPEN'
}
write_new('frozen-declaration.json', json.dumps(record, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'freeze': fp(freeze/'frozen-declaration.json'),
                  'head': record['head'], 'headLF': record['headLF'],
                  'canonical254LiteralPreserved': True}, ensure_ascii=False))
