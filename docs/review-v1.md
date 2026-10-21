# Independent semantic and proof review

Reviewer: fresh gpt-6.1-sol xhigh context, separate from both authors. The reviewer received only the actual Lean definitions, statements and proofs, not the manuscript or intent contract, and did not run builds. Initial blind translation was followed by a proof review and a final review of changed proof bodies. Verdict: CORRECT for these local declarations; no blocking issues. The primary compared that blind translation against docs/scope-v1.md and the cited manuscript passages and found it aligned with the limited milestone.

## Independent findings

Path is genuinely Fin n → ℝ; prefixes sum coordinates with i.val < k; energy sums actual squares. One-sided maxima use exactly 1..n, may be negative, and require n > 0. The separate maximum including zero uses 0..n. The absolute maximum is characterized and attained as a maximum of |S_k|, not merely named that way. Energy zero is equivalent to all coordinates zero. Maximum scaling is only claimed for nonnegative scale; sums and squared energies allow any real scale.

Weak multiplication events include equality and the all-zero path for every real threshold. Strict survival is their exact complement. Quotient transformations require positive energy. At positive thresholds the normalized strict event contains the extra zero-energy set, disjoint from raw strict survival. Including time zero is harmless for positive thresholds but changes the negative singleton event at zero threshold, which is formally witnessed.

Double crossing means an intersection of two maximum conditions, not ordered or distinct-time hits. Absolute crossing is their union. CDF names refer to strict deterministic path sets; endpoint versions use absolute endpoint values. No probability theorem or distribution comparison is present. Negative thresholds and collapsed zero-energy walls have the literal algebraic meaning rather than two separated geometric barriers.

## Final reviewed source SHA256

- Shao/Basic/FinitePath.lean: 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb
- Shao/Basic/Events.lean: 58a243902a660defc28e8a0625a93f6098a1d80c770037460f205ee615799a3a
- Shao/C1/Normalization.lean: fef196ff1358ca597a4ddeec652d537744be62c77e0e5829b63c61283c12734d
- Shao/C2/TwoSided.lean: 125cb4f9b13e05fed36118f9c614b4aad76c3ef912b0c153d3fa94fff0400cf4
- Shao/Checks/Boundaries.lean: 351ff11513ea34f1b743dec0f5ef0f91e43337dfa47d87be677b778ad06560f0

The independent review is not a kernel certificate. Server build and transitive axiom checks are recorded separately. Subsequent changes invalidate the corresponding source-bound review.
