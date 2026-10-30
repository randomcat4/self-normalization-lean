# unit285 pinned primary API trace

All primary files are bound to mathlib `807d3836b165983210ee2ecf3cd28f239436949c`; the parent records working bytes equal to pinned git-show bytes. Local hashes and byte counts were independently verified before use. Line numbers below identify original primary sources, not source excerpts rewritten by the author. Complete used declarations/proofs and variable environments were read; whole unrelated files are not claimed semantically reviewed.

| Candidate use | Exact pinned source and declaration | Conditions checked |
| --- | --- | --- |
| T01 quadratic remainder | next285-parent-api-02/Mathlib/Analysis/SpecialFunctions/Exp.lean:38 `Complex.exp_bound_sq` | x=0, z=(u:Complex); norm z=abs u<=1; full original norm remainder bound |
| Real part of remainder | unit285/parent-api-04/Mathlib/Analysis/Complex/Norm.lean:45 `Complex.re_le_norm` | Arbitrary complex remainder; its real part is bounded by its norm |
| Cast and real exponential | unit285/parent-api-04/Mathlib/Analysis/Complex/Exponential.lean:192 `Complex.ofReal_exp`, :198 `Complex.exp_ofReal_re` | The implementation uses exp_ofReal_re directly; both conversion statements and proofs were read |
| Complex real norm | unit285/parent-api-04/Mathlib/Analysis/Complex/Norm.lean:105 `Complex.norm_real` | Norm of a real cast is its real norm; norm_eq_abs and sq_abs give u^2 |
| Actual f and f^2 integrability | unit284/parent-api-01/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:155 `Integrable.of_mem_Icc` | nu finite from probability; hf AE measurable; f in [-B,B]; f^2 in [0,B^2] AE |
| Integrable polynomial | same Integrable.lean `integrable_const`, `Integrable.add`, :1028 `Integrable.const_mul` | Finite nu; actual previous integrability, constants 1,t,t^2 |
| Exponential integrability | next285-parent-api-01/Mathlib/Probability/Moments/Basic.lean:500 `integrable_exp_mul_of_mem_Icc` | Finite measure, AE measurable real variable, AE finite interval; arbitrary real parameter |
| Legitimate integral comparison/linearity | unit284/parent-api-02/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:239 `integral_add`, :288 `integral_const_mul`, :662 `integral_mono_ae` | Actual integrability of every summand and comparison function; actual AE pointwise bound; hmean/hsecond |
| Final scalar exponential | unit285/parent-api-04/Mathlib/Analysis/Complex/Exponential.lean:633 `Real.add_one_le_exp` | Unconditional real s=t^2*v; add_comm only rewrites 1+s |
| Actual Pi probability | unit283/parent-api-02/Mathlib/MeasureTheory/Constructions/Pi.lean:311 `Measure.pi.instIsProbabilityMeasure` | Fintype iota; every factor nu probability; instance includes empty products |
| AE coordinate transport | same Pi.lean:425 `Measure.tendsto_eval_ae_ae` | Finite iota, factor measures sigma-finite (probability); used only as filter-eventually transport |
| Coordinate distribution | same Pi.lean:402 `measurePreserving_eval` | Each factor probability; evaluation measurable, map_eq exactly nu |
| Actual coordinate independence | unit283/parent-api-06/Mathlib/Probability/Independence/Basic.lean:895 `iIndepFun_pi` | Fintype iota, arbitrary measurable spaces, probability factors, measurable f -> AE measurable f; no StandardBorel or Nonempty premise |
| Coordinate MGF map | next285-parent-api-01/Mathlib/Probability/Moments/Basic.lean:215 `mgf_map` | Evaluation AE measurable; exp(z*f) AE strongly measurable for its map measure; function composition is actual coordinate f |
| Independent exponential integrability | same Moments/Basic.lean:347 `iIndepFun.integrable_exp_mul_sum` | Finite P, actual iIndepFun, measurable coordinates, all exp(z*X_i) integrable; s=univ, including empty |
| Finite product of MGFs | same Moments/Basic.lean:379 `iIndepFun.mgf_sum` and full preceding mgf_sum-zero proof | Actual iIndepFun and all coordinate functions measurable, s=univ; explicit local function-sum equality supplied |
| Product monotonicity | same Moments/Basic.lean `mgf_nonneg`; unit285/parent-api-05/Mathlib/Algebra/Order/GroupWithZero/Basic.lean:513 `pow_le_pow_left₀` | Base mgf>=0; T01 gives base inequality; exponent m is arbitrary natural, including zero |
| Exponential of m terms | unit285/parent-api-04/Mathlib/Analysis/Complex/Exponential.lean:234 `Real.exp_nat_mul` | Arbitrary real z^2*v, arbitrary natural m; final exponent equality by ring |
| Real square root | unit285/parent-api-05/Mathlib/Analysis/Real/Sqrt.lean:143 `Real.sqrt_nonneg`, :177 `Real.sq_sqrt` | a=m*v>=0 and q>=0 supply a*q>=0; no strict positivity needed |
| Upper Chernoff | next285-parent-api-01/Mathlib/Probability/Moments/Basic.lean:430 `measure_ge_le_exp_mul_mgf` | Finite P, t>=0, actual exp(t*S) integrability; threshold 2*d |
| Lower Chernoff | same Moments/Basic.lean:452 `measure_le_le_exp_mul_mgf` | Finite P, -t<=0, actual exp(-t*S) integrability; threshold -(2*d) |
| Real-measure comparison/null/union | unit285/parent-api-03/Mathlib/MeasureTheory/Measure/Real.lean:40 `measureReal_eq_zero_iff`, :88 `measureReal_mono`, :137 `measureReal_union_le` | P probability ensures all relevant measures finite; null follows from actual AE zero; strict event inclusion is proved |
| Scalar exponential positivity/monotonicity | unit285/parent-api-04/Mathlib/Analysis/Complex/Exponential.lean:284 `Real.exp_pos`, :317 `Real.exp_le_exp` | Arbitrary real exponents; final exponent comparison is checked from t*d=q and t^2*a<=q |

Supporting standard scalar arithmetic, finite sum/product rewriting, measurability composition/absolute value, finite Filter.eventually_all, ae_iff and tactic infrastructure come from the four unchanged frozen imports. The source uses no unknown private declaration, unqualified new producer or hidden original-consumer hypothesis. Primary files merely supplied but not used as mathematical dependencies are explicitly marked in READING-COVERAGE.json.
