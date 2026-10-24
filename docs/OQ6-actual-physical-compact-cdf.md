# Actual centered physical compact CDF/tail bounds and genuine moment rate

This milestone connects the already qualified uncentered row-statistic CDF engine to the true centered physical jackknife statistic. The supplied uniform scalar Shao–Zhou input hSZ remains an ordinary UNPROVED theorem parameter. Its existence is not claimed.

## Exact mathematical scope

For the original countably generated probability space and degree-two iid sample, assume a jointly measurable, symmetric, centered, jointly L2 kernel h with actual projection g(o)=integral h(o,t) dμ(t) and projection second moment one. Put r(o,t)=h(o,t)-g(o)-g(t), v=integral r², and s=1+sqrt(v). The statistic uses the actual pair average U and actual centered jackknife variance R², with T=sqrt(n)*U/sqrt(R²) when R²>0 and T=0 otherwise. Projection energy, uncentered denominator and centered physical variance remain distinct.

The exact module proves three public theorems:

- `normalized_observation_truncation_budget_le_rpow_moment`: for a genuine measurable L2 observation g, genuine integrable |g|^p, 2≤p≤3, n≥1 and y≥0, the actual normalized truncation budget L is integrable and satisfies both L≤β(1+y)^p*n/(sqrt(n))^p and L≤β(1+y)^p/n^((p-2)/2), with β=integral |g|^p. The proof transfers the actual normalized observation law; no moment comparison is assumed.
- `actual_physical_compact_cdf_tail_bounds_nonnegative`: there exists c>0 before n and x such that for all n≥3 and 0≤x≤1, all four strict/weak CDF and upper-tail absolute errors are bounded by C*(L_tau+16*4097*(1+tau)*s/sqrt(n))+2*exp(-c*n)+(1/8+33104*s)/sqrt(n)+12/n. Here tau=x/sqrt(1+c_n*x²), c_n=4*(n-1)/(n-2)², and L_tau is the genuine truncation integral at tau. The witness is min of the qualified147/169 exponential constants.
- `actual_physical_compact_cdf_tail_rpow_rate`: with the additional genuine projection p-moment and 2<p≤3, there exists K>0 before n/x such that all four physical errors are at most K*(β/n^((p-2)/2)+s/sqrt(n)). The proof uses K=131112*C+33117+2/c. No β≥1 or asymptotic sample-size hypothesis is added.

Exact measurable complements and the zero-at-zero convention retain equality and zero atoms. The deterministic zero matrix supplies the compact threshold range without an Inhabited Ω premise. The two actual exponential payments and finite-n transport cost are retained transparently, including any overlap in their event bounds.

## Exact-source evidence

Source SHA256 d264ae1c1f04cee3b43ec5e44829a5986574d70f30615f7bdeb1f1bfab2a14ae; 26260 UTF-8 bytes,570 LF lines. All3 frozen headers and43 typed values remain exact; autoImplicit is false and the default heartbeat is unchanged. The retained full original independent review plus complete9+2 compiler-directed repair-delta review covers all final source bytes. No mathematical assumption, import, constant or quantifier order changed during repairs.

Designated-server complete kernel receipt7bd7137172618a91a78822c32678ea59792ed999b4714f8d81ee8f010c01945f directly exits0,7.202782416716218 seconds. It checks BOTH147/169 imports and the entire170 proof interaction. Produced object SHA256 c907a0e8730cae485e8e6614f4fb3aa5f839687cb748b71f2706b9cb7c7a0dfb,3118176 bytes. All3391 protected physical records were preserved; Git stayed exact, owned processes ended, no timeout or actual compiler error occurred.

The import-only actual-owner audit receipt18e29d9d8c8e9e7570d5151d06085b5d71d7b4c3fbe87289deb4a8a46aa46b89 directly exits0,5.390159383416176 seconds, with all3401 protected records preserved. Actual ownership derives13 TYPEs=3 public source+10 generated,0 private source,756 TYPE lines/51481 TYPE bytes,0 non-theorem FULLVALUE obligations. The qualified independent reviewer literally read every entire actual TYPE and every kind/component/level/body flag and recursive axiom list. Recursive AX occurrences are13 propext+4 Classical.choice+4 Quot.sound=21, with no other dependency. Owner selection has no namespace filter.

Twelve existing stdout linter/deprecation warnings and the known134-byte Lake notice are retained. Strict wrapper success remains false; the direct kernel/object/audit/preservation/process gates pass. Both genuine failed source versions and receipts remain archived and are not relabeled as successful. Parent acceptance reused exact successful receipts without another Lean run.

Pinned environment: Lean4.36.0-rc1; mathlib807d3836b165983210ee2ecf3cd28f239436949c. All Lean runs used the designated server, CPU22–25, native8192MiB and j4, under the lane lock. No local Lean/build/cache write or full rebuild was used.

## Unpaid scope

Negative or growing thresholds, relative Gaussian tails, p54 concentration/strict margins/conditional obligations, scalar input proof/existence and novelty/priority remain unpaid. The invalid arbitrary polynomial conditional standardized p-moment convergence claim is not used. Original OQ56/C12 root groups remain OPEN; OQ3 stays PAUSED_BY_USER and separate limited OQ4 acceptance is unchanged. This PR is stacked on PR337 and performs no merge or root acceptance.
