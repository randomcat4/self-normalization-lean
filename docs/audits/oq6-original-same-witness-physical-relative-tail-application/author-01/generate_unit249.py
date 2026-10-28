"""Deterministic local source assembly from the immutable unit249 freeze.

This script writes only the assigned author-01 directory.  It neither invokes
Lean nor contacts a server.  The mathematical implementation is the explicit
proof text below; the large frozen local types are copied without abbreviation.
"""
from __future__ import annotations

import hashlib
import json
import re
import textwrap
from pathlib import Path

ROOT = Path("C:/game/shao lean")
OUT = ROOT / "drafts/oq56/unit249/author-01"
FREEZE = ROOT / "drafts/oq56/unit249/freeze-01"
OUT.mkdir(parents=True, exist_ok=True)
INVENTORY = json.loads((FREEZE / "INTERFACE-INVENTORY.json").read_bytes())
FACTS = {row["name"]: row for row in INVENTORY["proposedProofFacts"]}
PARTS: list[str] = []
FACT_SPANS: list[dict] = []


def add(s: str) -> None:
    PARTS.append(s)


def typed(name: str, proof: str) -> None:
    typ = FACTS[name]["fullType"]
    start = sum(len(x) for x in PARTS)
    add("  have " + name + " :\n")
    type_start = sum(len(x) for x in PARTS)
    add(textwrap.indent(textwrap.dedent(typ).rstrip(), "      ") + " :=\n")
    type_end = sum(len(x) for x in PARTS) - len(" :=\n")
    proof_start = sum(len(x) for x in PARTS)
    add(textwrap.indent(textwrap.dedent(proof).strip(), "    ") + "\n")
    FACT_SPANS.append({
        "name": name,
        "contextId": FACTS[name]["contextId"],
        "startCharacter": start,
        "endCharacterExclusive": sum(len(x) for x in PARTS),
        "typeStartCharacter": type_start,
        "typeEndCharacterExclusive": type_end,
        "proofStartCharacter": proof_start,
        "fullType": typ,
        "explicitType": True,
        "freezeFact": "proposedProofFacts/" + name,
    })


add((FREEZE / "FROZEN-PREAMBLE.txt").read_bytes().decode("utf-8"))
add((FREEZE / "FROZEN-HEAD.txt").read_bytes().decode("utf-8"))
add(" := by\n")
add("  intro Ω mΩ μ hμProbability h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp cBudget hcBudget\n")
start_h248 = sum(len(x) for x in PARTS)
add("  have h248 :=\n")
add("    Shao.OQ6.OriginalSameWitnessPhysicalPaidTailApplication.actual_original_same_witness_physical_paid_scalar_tail_application\n")
add("      μ h hh hh2 hhsymm hcenter hprojectionsecond p hp2 hp3 hgp cBudget hcBudget\n")
FACT_SPANS.append({
    "name": "h248", "contextId": "N00", "startCharacter": start_h248,
    "endCharacterExclusive": sum(len(x) for x in PARTS),
    "fullType": FACTS["h248"]["fullType"], "explicitType": False,
    "freezeFact": "proposedProofFacts/h248",
    "inferencePermission": INVENTORY["solePermittedInferredProp"],
})
add("  intro g r v rho β cWindow\n")
typed("hCg", "h248.2.2.2.2.2.2")
add("  let cg : ℝ := Classical.choose hCg\n")
typed("hcgpos", "(Classical.choose_spec hCg).1")
typed("hModel", "(Classical.choose_spec hCg).2")
add("  let m₀ : MeasurableSpace Ω := Classical.choose hModel\n")
typed("hm₀", "Classical.choose (Classical.choose_spec hModel)")
typed("hcg", "Classical.choose (Classical.choose_spec (Classical.choose_spec hModel))")
add("  let μ₀ : @Measure Ω m₀ := μ.trim hm₀\n")
add("  letI : MeasurableSpace Ω := m₀\n")
add("  letI : MeasurableSpace.CountablyGenerated Ω := hcg\n")
typed("hRetained248", "Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hModel))")
typed("hμ₀Probability", "hRetained248.1")
typed("hOldPayments248", "hRetained248.2.2")
add("  refine ⟨h248.1, h248.2.1, h248.2.2.1, h248.2.2.2.1, h248.2.2.2.2.1, h248.2.2.2.2.2.1,\n")
add("    cg, hcgpos, m₀, hm₀, hcg, hμ₀Probability, hRetained248.2.1, hOldPayments248, ?_⟩\n")
add("  intro Cenv aenv t0 Menv hCenv haenv ht0 hMenv cPaid\n")
typed("hTailScalePos", "(Shao.OQ6.BoundedProductEnvelopeTails.bounded_scales_pos Menv hMenv).2.2.2.2.2")
typed("hRemainderScalePos", "(remainderWindowScale_bounds\n  (Shao.OQ6.BoundedProductEnvelopeTails.tailScale Menv) t0 hTailScalePos.le ht0).1")
typed("hAbsorption236", "Shao.OQ6.OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed\n  t0 cg ht0 hcgpos")
typed("hAbsScalePos", "hAbsorption236.1")
typed("hPaidPositive", "lt_min hRemainderScalePos hAbsScalePos")
typed("hPaidLeBoth", "⟨min_le_left _ _, min_le_right _ _,\n  (min_le_right _ _).trans (min_le_left _ _)⟩")
typed("hAuxWindowEq", """
by
  calc
    min (1 : ℝ) (Real.sqrt ((2 * cPaid) ^ (2 : ℕ)) / (2 : ℝ)) =
        min (1 : ℝ) ((2 * cPaid) / (2 : ℝ)) := by
      rw [Real.sqrt_sq (x := 2 * cPaid) (by positivity)]
    _ = min (1 : ℝ) cPaid := by congr 1 <;> ring
    _ = cPaid := min_eq_right hPaidLeBoth.2.2
""")
typed("hPaidNonemptyEventually", """
by
  refine Filter.Eventually.mono
    (Shao.OQ6.OriginalExceptionalTailAbsorption.eventually_original_exceptional_payment_absorbed
      ((2 * cPaid) ^ (2 : ℕ)) cg (by positivity) hcgpos).2 ?_
  intro n hAuxAtN
  exact ⟨hAuxAtN.1, by simpa only [hAuxWindowEq] using hAuxAtN.2.1⟩
""")
typed("hSqrtNatAtTop", "Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))")
typed("hStudentizerEventually", "hSqrtNatAtTop.eventually\n  (Filter.eventually_atTop.2 ⟨1 + rho, fun x hx => hx⟩)")
add("  refine ⟨hPaidPositive, ?_⟩\n")
add("  filter_upwards [hOldPayments248 Cenv aenv t0 Menv hCenv haenv ht0 hMenv,\n")
add("    hPaidNonemptyEventually, hStudentizerEventually, hAbsorption236.2] with\n")
add("    n hOldAtNRaw248 hPaidAtN hGuardAtN hAbsorptionAtN\n")
typed("hOldAtN248", "hOldAtNRaw248")
add("  refine ⟨hOldAtN248.1, hGuardAtN, hPaidAtN.2, ?_⟩\n")
add("  intro w hW hWR hSq hSqBound hEnv z hz hzPaidWindow\n")
typed("hOldAtCurrent248", """
hOldAtN248.2 w hW hWR hSq hSqBound hEnv z hz
  (hzPaidWindow.trans (mul_le_mul_of_nonneg_right hPaidLeBoth.1
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
""")
add("  intro mN P N ξ0 D1 L0 sourceCost0 Tphysical R\n")
add("  let payment : ℝ := (3 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) + Real.exp (-cg * (n : ℝ)) +\n")
add("    (4 : ℝ) * Real.exp (-(z * Real.sqrt (n : ℝ)) / (2 : ℝ))\n")
add("  let payment1 : ℝ := (3 : ℝ) * Real.exp (-boundedPolylogMomentOrder t0 n) + Real.exp (-cg * (n : ℝ)) +\n")
add("    (4 : ℝ) * Real.exp (-Real.sqrt (n : ℝ) / (2 : ℝ))\n")
typed("hFeeIsDoublePaymentOne", "by\n  dsimp only [payment1]\n  ring")
typed("hPaymentLeOne", """
by
  dsimp only [payment, payment1]
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hz (Real.sqrt_nonneg (n : ℝ))]
""")
typed("hDoublePaymentAbsorbed", """
by
  rw [← hFeeIsDoublePaymentOne]
  exact hAbsorptionAtN.2.2 z hz
    (hzPaidWindow.trans (mul_le_mul_of_nonneg_right hPaidLeBoth.2.1
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
""")
typed("hLowerLoss", "by linarith only [hPaymentLeOne, hDoublePaymentAbsorbed]")
typed("hUpperLoss", "by linarith only [hPaymentLeOne, hDoublePaymentAbsorbed]")
add("  intro C1 C2 C3 C4 hSZcBudget hzMomentWindow\n")
# The complete old-current package has40 top-level conjuncts; its40th is the
# physical package.  That package's8th field is the guard implication; the
# consequence has6 fields and its6th is the original externalSZ paid tail.
physical_projection = "hOldAtCurrent248" + ".2" * (39 + 7)
typed("hPhysicalPaidBounds", f"({physical_projection} hGuardAtN).2.2.2.2.2\n  C1 C2 C3 C4 hSZcBudget hzMomentWindow")
typed("hRelativeBounds", """
by
  constructor
  · calc
      Shao.standardNormalTail z *
          (Real.exp (-C1 * L0) * (1 - C2 * sourceCost0) - R) =
          Shao.standardNormalTail z * Real.exp (-C1 * L0) *
            (1 - C2 * sourceCost0) - R * Shao.standardNormalTail z := by ring
      _ ≤ Shao.standardNormalTail z * Real.exp (-C1 * L0) *
            (1 - C2 * sourceCost0) - payment - payment1 := by
          linarith only [hLowerLoss]
      _ ≤ P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} := hPhysicalPaidBounds.1
  · calc
      P.real {ζ : Fin n → Ω | z ≤ Tphysical ζ} ≤
          Shao.standardNormalTail z * Real.exp (C3 * L0) *
            (1 + C4 * sourceCost0) + 3 * payment + payment1 := hPhysicalPaidBounds.2
      _ ≤ Shao.standardNormalTail z * Real.exp (C3 * L0) *
            (1 + C4 * sourceCost0) + 2 * (R * Shao.standardNormalTail z) := by
          linarith only [hUpperLoss]
      _ = Shao.standardNormalTail z *
          (Real.exp (C3 * L0) * (1 + C4 * sourceCost0) + 2 * R) := by ring
""")
add("  exact hRelativeBounds\n")
add((FREEZE / "FROZEN-CLOSING.txt").read_bytes().decode("utf-8"))

SOURCE = "".join(PARTS)
assert "\r" not in SOURCE
assert not SOURCE.startswith("\ufeff")
assert len(FACT_SPANS) == 28
assert {x["name"] for x in FACT_SPANS} == set(FACTS)
(OUT / "OriginalSameWitnessPhysicalRelativeTailApplication.lean").write_bytes(SOURCE.encode("utf-8"))


def coord(pos: int) -> dict:
    prefix = SOURCE[:pos]
    return {"byte": len(prefix.encode("utf-8")),
            "line": prefix.count("\n") + 1,
            "column": len(prefix.rsplit("\n", 1)[-1]) + 1}


for row in FACT_SPANS:
    row["start"] = coord(row["startCharacter"])
    row["endExclusive"] = coord(row["endCharacterExclusive"])
    row["sourceSliceSHA256"] = hashlib.sha256(SOURCE[row["startCharacter"]:row["endCharacterExclusive"]].encode("utf-8")).hexdigest()
    if row["explicitType"]:
        row["typeStart"] = coord(row["typeStartCharacter"])
        row["typeEndExclusive"] = coord(row["typeEndCharacterExclusive"])
        row["proofStart"] = coord(row["proofStartCharacter"])
(OUT / "FACT-COORDINATES.json").write_bytes((json.dumps(FACT_SPANS, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
print(json.dumps({"sourceBytes": len(SOURCE.encode("utf-8")),
                  "sourceSHA256": hashlib.sha256(SOURCE.encode("utf-8")).hexdigest(),
                  "LF": SOURCE.count("\n"), "facts": len(FACT_SPANS),
                  "LeanInvocations": 0}, ensure_ascii=False))
