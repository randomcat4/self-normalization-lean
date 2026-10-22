# Independent review of v35 public-theorem manifest coverage

STATUS: **CORRECT**

This review covers only the bounded parser fix and the exact public theorem roster in the frozen four-module integration tree. It adds no mathematical proof acceptance. A separate root-requested path-precision clarification in the M report preserves its mathematical verdict and checked evidence.

## Parser change

The original [public_theorems.py](<C:/game/shao lean/library/scripts/public_theorems.py>) has SHA256 `b11b92a18a49b7ea6278dc4ab72659fdd09422db9696e7e3b1c1754c1f129389`. The candidate [public_theorems.py](<C:/game/shao lean/coordination/integration-v35/public_theorems.py>) has SHA256 `f5566e8a84d418b3944de6b8c7d78936748dbcbddb9194b23200db1c0f89e073` and exactly matches the integration workspace's script.

The diff contains one comment update at line 8 and one executable change at line 12: trimming a declaration line changes from `.rstrip()` to `.strip()`. Namespace, section, end, and theorem matching all receive the same trimmed line. The anchored theorem pattern is unchanged, and still does not match `private theorem`.

Leading whitespace is valid before a Lean declaration. The frozen `BrownianSpectralEnvelope.lean:69` starts with a space before `theorem rademacher_eventual_firstTerm_envelope`. The old parser omits it; the new parser includes it without changing any Lean bytes.

## Exact roster verification

I independently scanned the actual remote source trees in memory, without running the generator in write mode. The v34 baseline has 1,739 names under both old and new parsing; its expected list matches that roster. The v35 tree has 1,746 under the old parser and **1,747** under the fixed parser. The sole name made newly visible by the fix is `Shao.Probability.BrownianSup.rademacher_eventual_firstTerm_envelope`.

The full difference between v35 and the baseline is exactly the following eight public theorems, all in namespace `Shao.Probability.BrownianSup`. Every baseline name is preserved. There are no duplicates, private theorem names, or other additions in the generated manifest.

| Source | Actual source line | Public theorem | Expected-file line |
|---|---:|---|---:|
| `Shao/Probability/RademacherGrid.lean` | 174 | `rademacher_max_fourth_tail` | 1469 |
| `Shao/Probability/RademacherGrid.lean` | 316 | `rademacher_coarse_comparison` | 1466 |
| `Shao/Probability/BrownianGridBridge.lean` | 436 | `rademacher_coarse_tendsto_brownian_grid` | 1467 |
| `Shao/Probability/BrownianGridBridge.lean` | 511 | `brownian_dyadic_grid_tendsto_probability` | 1460 |
| `Shao/Probability/BrownianSpectralEnvelope.lean` | 69 | `rademacher_eventual_firstTerm_envelope` | 1468 |
| `Shao/Probability/BrownianFirstTerm.lean` | 112 | `actual_brownian_firstTerm_envelope` | 1459 |
| `Shao/Probability/BrownianFirstTerm.lean` | 143 | `actual_brownian_firstTerm` | 1458 |
| `Shao/Probability/BrownianFirstTerm.lean` | 154 | `actual_brownian_eventually_positive` | 1457 |

The four remote source files retain exactly the frozen hashes:

| Source | SHA256 |
|---|---|
| `Shao/Probability/RademacherGrid.lean` | `abb08df1b17a154ab6a8a8c59fda06eadec6a44009c89d02c8f2aeedbd4acaac` |
| `Shao/Probability/BrownianGridBridge.lean` | `98741686b236686ea72d9d6b9c44dced7b6f1036528942bb7bf69154972bd5e9` |
| `Shao/Probability/BrownianSpectralEnvelope.lean` | `97e1a9f13d2b86874b94df93540d3355dcc38dac8dff81ad3a823ded68396fc7` |
| `Shao/Probability/BrownianFirstTerm.lean` | `f4faa8c89016aea74dd16c8ea0dc359213390413d3ab0faff234dd98d0a87c6a` |

The freeze-set file `coordination/integration-v35/frozen-sources.json` hashes to `824c7f3416e6c43685b93c8162c80541a09ea241cf6ac9a07c9dd631dc49353a`.

## Integration expected file and existing gate

The integration `verification/expected-public-theorems.txt` hashes to `90c6b2b232616fec4d757ce8c3a93992405f2301e1f2247793930ef6d223f370` and matches the complete sorted 1,747-name generated roster. All eight additions are present at the exact lines above. The old expected file hashes to `9be576dec6aa62a0e86b0159aac2f9db97efd650bb746f4111178735b8e34e59`.

The existing integration receipt observed during this read-only review reports **PASS**. Its frozen snapshot contains the same parser and expected-file hashes. Its versions, manifest, build, theorem-audit, all-declarations, module-coverage, and diff-check commands all record exit 0.

I also checked the existing theorem-audit and owned-declaration logs directly: all eight public names occur in both. The theorem log reports `COVERED_PUBLIC_THEOREMS 1747` and `AUDITED_THEOREMS 2853`. Its SHA256 is `1afc93b22f71e23fe2710d7db973ec7ed70dda834407ff57e94b456dbbf3bf10`; the owned-declaration log SHA256 is `5776f9d6cb4ce3650eca05743f944c5b6f4f4a703b8c0f4ce3ae5e251458b9ae`. This establishes that the corrected expected roster is actually consumed by the existing coverage gate.

No Lean command, cache change, source change, Git mutation, manifest write, or process modification was performed by this reviewer. Server inspection used the existing shared connection and CPU10–13. This coverage task writes only `manifest-review.md/json`; the additional root-requested M report correction merely names the private overlay that produced the earlier Git-status observation. The M mathematical verdict and checked evidence remain unchanged.

**No issue found.** The bounded parser fix correctly repairs current-tree theorem coverage while preserving all baseline public names and all frozen Lean source bytes.
