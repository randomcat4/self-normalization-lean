# Shared path/probability scope v4

Sources at randomcat4/shao@35d4580b61e22e7145f47730045a09874ef93259:
- current/c12/supplement.tex: b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd; deletion lemma/proof and Lindley reversal at lines126–142,1390–1403,368–405.
- current/oq4/energy01.md: 2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6; E3 closed strip coordinate bound.
- current/oq4/b01/proof01.md: 7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38; single-coordinate deletion in section4.

43 new public theorems across six modules. OrderedSelection implements the increasing enumeration of any retained Finset, actual compressed energy, both directions of the prefix correspondence and the positive-threshold nonempty-prefix bridge. DeletionNumeric and Deletion prove the source event inclusion for every deterministic real path, J.card<n, x>0 and J.card<x^2, with all zero-energy cases included and no probability assumptions.

ClosedSurvival explicitly includes time0 and uses closed <= walls. It supplies abs/upper maximum bridges, coordinate |a_i|<=2h, and the ordered single-deletion upper survival bound d+max(-a_i,0), including deletion to an empty path. This is distinct from the strict complement of weak crossing.

Lindley is the genuine bounded recursion W0=0, W(k+1)=max(0,Wk+a_k), k<=n. It proves Wn=maxWithZero(reversePath a), including n=0; reversal preserves actual energy. LindleyLaw proves the joint IdentDistrib((Wn,Q),(maxWithZero,Q)) under the previously frozen measurable finite-iid assumptions, with both probability measures explicit. No centering, moment, nonatomicity or positive-energy assumption is added. It does not assert pathwise Wn=maxWithZero.

Complete C1/C2/OQ3/OQ4/OQ56 roots remain OPEN. Truncation conditional laws, telescoping, quantitative estimates and external theorem closures are not supplied by this milestone.
