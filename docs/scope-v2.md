# Shared probability interfaces: frozen scope v2

Authorized 2026-10-21 as the next milestone in the user's whole-corpus formalization plan. The v1 path/event definitions and theorem statements remain unchanged.

## Measurability

For every n, the path space is Fin n → ℝ with its standard product measurable/topological structure. Prove measurability of actual prefixes and final energy, extrema (with n > 0 for nonempty-prefix extrema), all primitive weak/strict event sets and zero energy. Prove measurability of the zero-defined normalized endpoint and upper maximum, their strict CDF sets, and C2 double crossing. Optional continuity results must use the same genuine definitions. No probability law or moment restriction is needed.

## Finite iid and deterministic reindexing

For an arbitrary measurable sample space Ω, probability measures μ on Ω and ν on ℝ, and coordinatewise measurable X : Fin n → Ω → ℝ, assume iIndepFun X μ and IdentDistrib (X i) id μ ν for every i. Prove that the sample path has law Measure.pi (fun _ => ν). The common law may have nonzero mean and arbitrary moments. Include n = 0.

For any fixed permutation e of Fin n, the original and reindexed sample paths have identical distributions. Consequently any measurable observable of the path and any measurable path event have identical pushforward laws/probabilities under that reindexing. This is a distributional assertion; a path's maximum need not agree pointwise with its permuted maximum. No sample-dependent permutation, conditional permutation reveal, truncation-conditioned law, or Lindley identity is claimed here.

## Source and review

Source commit 35d4580b61e22e7145f47730045a09874ef93259, current/c12/main.tex:149–180 and 548–608; supplement.tex:S.2; assessment C12-01. Full exact manuscript hashes are in scope-v1.md. Fixed Lean/mathlib and dependency lock are inherited unchanged. Independent statement/definition review and server kernel/axiom checks are required before a ready PR. No local Lean builds and no duplicate old preparation checks.

## Separate OQ5 activity

This milestone also records a source-linked dependency contract for the original fixed-law OQ5 counterexample. That document is planning/source analysis only. It does not count as a Lean proof of the counterexample or cover the stronger later p52/p53 constructions.
