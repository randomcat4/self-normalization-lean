# Delivery plan

## Repositories and authority

Use two private repositories in total: existing shao for source manuscripts/history and shao-lean for formal statements, proofs, fixed dependencies and server verification receipts. C1 and C2 share one Lean library. Workers use isolated worktrees, not separate repositories. Source files are referenced by exact source commit and SHA256 instead of copied wholesale.

## Milestones

1. Finite paths, genuine energy, event algebra, C1 normalization and C2 two-sided consumers. Current implementation milestone.
2. Finite iid laws, fixed permutations and independent copies; event measurability and distribution transport.
3. Truncated budget and ordered deletion, independently after their interfaces are frozen.
4. Conditional truncation, exact product conditional laws and moment/mixture formulas. Recentring has a distinct energy.
5. Separate C1 reversal/Lindley and C2 permutation-reveal consumers. No assertion of a unified 124 mechanism.

Each milestone has a source-linked statement contract, independently read declarations, kernel checks and a reviewable PR. Update a draft when checked substantive work is ready, with a target checkpoint every 1–2 hours of active work; do not manufacture empty commits. The checkpoint is a project practice, not a claim about a published prover protocol. No background recurring automation is configured.

## Team

Primary coordinates semantics, dependencies, integration and publication. Two gpt-6.1-sol xhigh authors own disjoint files. A third fresh gpt-6.1-sol xhigh context audits actual declarations and proofs without relying on author explanations. Changes are not accepted by majority vote; concrete objections must be resolved.

## Compute

Server quota: 40 CPU cores and 200 GiB RAM. Initial planning envelope: three workers × 24 GiB, integration 16 GiB, system/cache 24 GiB = 112 GiB; this is a capacity estimate, not a measured footprint. Model inference is external, so no GPU or local model allocation is required. Begin with at most three single-module Lean checks concurrently and one integration build at a time; raise concurrency only using measured demand. Do not raise it above 140 GiB, defer new heavy jobs around 160 GiB, investigate task-owned jobs near 180 GiB/OOM. Keep toolchain and fixed dependencies shared, project build outputs separate. A single writer populates dependency caches. Initial disk budget 100–120 GB; retain at least 150 GB free where practical.

## Deliverables and reuse

GitHub receives source, lockfiles, source mappings, concise review and verification receipts. The local fallback receives the same curated outputs if GitHub becomes unavailable. Toolchains, .lake, oleans, installers, raw logs, scratch searches and credentials stay out. All heavy checks run on the server. Reuse unchanged environment and module evidence; changes require only the changed objects and affected downstream checks, plus the actual integrated project entrypoint at a milestone.
