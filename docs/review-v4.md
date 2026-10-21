# Independent semantic review v4

Authors: ordered_selection (OrderedSelection, Lindley, LindleyLaw) and deletion_inequality (DeletionNumeric, Deletion, ClosedSurvival), gpt-6.1-sol xhigh. Reviewer c12_blind_review_v4 used a fresh context independent of both authors, only source declarations/proofs and necessary existing imports, without source-paper or intent documents. Each file received complete declaration translation before proof review. Primary compared translations with the frozen source statements.

All six frozen source hashes below received CORRECT source-level review. Actual kernel results are separately recorded in receipt-v4.json.

- Shao/Basic/OrderedSelection.lean: 4b6a4e86583455813c59ce0a64754416a01913b442047abd5c581699ac6a70b6
- Shao/Basic/DeletionNumeric.lean: 725b90e3e8e63e311906d506b77f16f5976959b9a680080215415110e74927fe
- Shao/Basic/Deletion.lean: 2bb43cdec4e7ccce21e0ca2981d1ca4178d791970c0b983665653543bee69687
- Shao/Basic/Lindley.lean: 81c0b9cea36513e456c4867dd0478a370eb4ef881c8aff9f0bab69009136eef7
- Shao/Basic/ClosedSurvival.lean: bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f
- Shao/Probability/LindleyLaw.lean: e661e493559b19537800ba432538aa053bd6ce742ddf2d0571bd152a4bcbea25

OrderedSelection: 5 definitions, 13 public theorems. Ascending rank/cutoff and sums are correct for all k, empty selection included. The positive threshold t>0 is necessary: a negative singleton distinguishes maxWithZero from the nonempty upper maximum.

DeletionNumeric: 2 public theorems, real nonnegative j,q,r and x>0,j<x^2. Two-term Cauchy–Schwarz is derived by a squared determinant identity; q=0/r=0 are valid.

Deletion: 2 aliases, 8 public theorems. Prefix and true energy split; deleted-prefix Cauchy–Schwarz uses at most J.card coordinates. The final theorem concerns the actually ordered compressed sample. Zero retained energy yields a nonempty all-zero weak crossing; otherwise the threshold is strictly positive and the empty prefix cannot manufacture the hit. Set inclusion has the original quantifiers and contains no iid or mean-zero premise.

Lindley: 3 definitions, 7 public theorems. W is a real recursive definition, not a maximum abbreviation. Reverse head/tail indexing and induction are correct for every k<=n including0. Compiler-generated executable name _unsafe_rec is not a source unsafe declaration or proof bypass; the logical definition uses Nat.brecOn and all audited theorem dependencies satisfy the whitelist.

ClosedSurvival: 2 definitions, 12 public theorems. Time0 is checked separately; strip membership supplies nonnegative wall. Adjacent-prefix difference gives the coordinate bound. Ordered single deletion uses the exact original cutoff and correct negative-part sign; n=1 deletion to empty is covered, with nonempty upper maximum explicitly guarded.

LindleyLaw: 1 public theorem. Fixed reversal preserves finite iid law; the measurable observable is the pair(maxWithZero, actual energy). Deterministic identities rewrite the reversed side as (Wn,Q), and IdentDistrib.symm gives the intended orientation. n=0 and zero energy are permitted. No pathwise equality, independence from Q, or extra moment assertion is made.
