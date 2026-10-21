# C1/C2 shared foundations: frozen scope v1

Owner: primary orchestrator. Authorized by the user on 2026-10-21 after explicit scope alignment. Earlier source-repository catalog-only instructions remain historical; the new authorization applies to this separate Lean repository.

## Objects and quantifiers

A path of length n is an arbitrary function Fin n → ℝ. No centering, independence, distribution, symmetry, density, atomlessness or moment hypothesis is imposed on a deterministic path. S_k sums precisely those coordinates i with i.val < k. Q_k sums their actual squares. Q is the sum of squares of all n coordinates. S_0 = Q_0 = 0. Prefix functions saturate at n for k > n.

A one-sided maximum requires n > 0 and uses 1 ≤ k ≤ n, excluding k = 0. The lower maximum is the upper maximum of the negated path. The absolute maximum must be proved to equal the maximum of |S_k| on the same times. A separate maximum includes time zero and must agree with max 0 M+.

## Intended conclusions

1. Finite sums and true energy: nonnegativity; Q = 0 iff every coordinate is zero; negation and scaling identities; precise maximum bounds and crossing witnesses.
2. Primitive crossings are weak multiplication inequalities x * sqrt(Q) ≤ M, for every real x. Strict survival is M < x * sqrt(Q), the exact complement. Equality is a hit. All-zero paths belong to every primitive crossing, including x > 0; they never survive strictly.
3. Normalized endpoint and upper maximum are defined to be zero on Q = 0. Quotient comparisons are used only when Q > 0. For t > 0, the normalized strict CDF set is the disjoint union of the raw multiplication strict set and the zero-energy set. With Q > 0 and t > 0, adjoining time zero does not change strict upper survival.
4. C2: double hit is the intersection of upper and lower weak crossings. Absolute weak crossing is their union. Absolute strict survival is their intersection of strict survivals. Negation exchanges upper and lower events.
5. Formal boundary witnesses cover a single negative step at threshold zero, a positive step at equality, levels greater than one, and arbitrary all-zero paths.

## Source and semantic audit

Source repository randomcat4/shao, commit 35d4580b61e22e7145f47730045a09874ef93259. Source files are byte-preserved on the server.

- current/c12/main.tex SHA256 beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
- current/c12/supplement.tex SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd

Source anchors: main.tex 149–167 (statistics, maxima, weak crossing and zero sample); 301–310 (strict CDF events); 595–607 (positive-threshold reflected event and Q > 0); 1153–1155 (double hit); 1552–1564 (two-sided inclusion–exclusion).

An independent reviewer first translates actual Lean declarations and their definitions without access to this intent contract. The primary compares that translation to this source. Compilation alone is not a semantic audit. Any material declaration change must be reviewed again.

## Acceptance

Every delivered declaration is checked by the pinned Lean kernel on the server. No sorry/admit, custom axioms, native_decide or unsafe bypass. Print transitive axiom dependencies of all exported project theorems; only propext, Classical.choice and Quot.sound are permitted. Bind receipts to the precise code commit, source hashes, lockfile and toolchain. Check only changed code and affected imports during iteration. No local Lean builds or repeats of passed preparation tests.

## Non-claims

This milestone does not prove the quantitative C1/C2 probability theorems, establish iid/measurability/conditional-law interfaces, prove the Lindley reversal identity, or solve the 124 unified mechanism. A maximum including zero is not yet claimed to be a Lindley process. External candidate formalization repositories are not dependencies or certified inputs.
