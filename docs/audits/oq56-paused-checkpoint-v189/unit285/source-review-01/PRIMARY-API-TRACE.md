# unit285 独立实际主接口审查

所有条目均按绑定的原始文件字节阅读其完整 HEAD/body 与相关环境。PRIMARY-API-CONTEXTS.json 保存每条实际原文片段、完整文件 SHA256/bytes、原始行号和独立条件检查；这里汇总候选使用点。pin 的外部来源依据为绑定父记录，本 reviewer 另行独立核验本地 bytes/hash，没有服务器、Git 或网络操作。

| 原始接口 | 候选行 | 独立条件核对 |
| --- | --- | --- |
| Complex.exp_bound_sq | 41-46 | x=0 and real-cast z=u; norm bound from abs u<=1. |
| Complex.re_le_norm | 42-46 | Arbitrary complex remainder; its real part<=its norm. |
| Complex.norm_real | 41-46 | Real cast norm is real norm=absolute value. |
| Complex.exp_ofReal_re | 44-46 | Real part of exp real-cast is actual real exp; no extra premise. |
| Complex.exp_zero | 41-46 | Simplifies original remainder and norm coefficient at x=0. |
| Real.exp_zero | 118 | Actual exp0=1 used by q0 simplification. |
| Real.exp_add | 227,236 | Unconditional exponent product equality. |
| Real.exp_nat_mul | 186-190 | Arbitrary real exponent and natural m including zero. |
| Real.exp_pos | 226,235 | All real exponents have strictly positive exponential. |
| Real.exp_le_exp | 228,237 | Strict monotonicity gives equivalent scalar exponent inequality. |
| Real.add_one_le_exp | 74-75 | Unconditional real scalar bound, applied to t^2*v. |
| Integrable.of_mem_Icc | 25-36 | Real AE finite interval, AEMeasurable and finite probability measure. |
| integrable_const | 48-65 | Probability implies finite measure; constant1. |
| Integrable.add | 48-49,61-64 | Actual summand integrability and continuous real addition. |
| Integrable.const_mul | 48-49,61-64 | Real normed ring and actual f/f2 integrability. |
| integral_add | 59-65 | Both additions carry actual Integrable witnesses. |
| integral_const_mul | 61-65 | RCLike real scalar identity. |
| integral_const | 65 | Real constant integral is nu.real(univ)*constant; probability mass1. |
| integral_mono_ae | 69-70 | Both real functions integrable and actual AE inequality. |
| ProbabilityTheory.mgf | 68,147-190 | Definition is actual exponential Bochner integral. |
| mgf_nonneg | 185 | Actual MGF integral nonnegative, no integrability loophole used. |
| mgf_map | 160-171 | AEMeasurable evaluation and AEStronglyMeasurable exp(z*f) under map. |
| integrable_exp_mul_of_mem_Icc | 37-38,152-157 | Finite measure, AE measurable real variable, AE interval; arbitrary real parameter. |
| iIndepFun.integrable_exp_mul_sum | 158-159 | Finite P, true independence, all coordinates measurable and each exponential integrable. |
| iIndepFun.mgf_sum | 172-179 | True independent measurable coordinates; full base/induction proof includes empty sum/product. |
| measure_ge_le_exp_mul_mgf | 220-228 | Finite P,t>=0,actual exp(t*S) integrable,threshold2d. |
| measure_le_le_exp_mul_mgf | 229-237 | Finite P,-t<=0,actual exp(-t*S) integrable,threshold-2d. |
| Measure.pi | 85,92 | Genuine finite product on arbitrary measurable factors. |
| Measure.pi.instIsProbabilityMeasure | 97-99 | Every factor nu probability; no Nonempty index premise. |
| Measure.pi_of_empty | boundary audit | Actual empty Pi is a Dirac probability; candidate need not branch. |
| measurePreserving_eval | 163-164 | Every factor probability; eval measurable and map exactly nu. |
| Measure.tendsto_eval_ae_ae | 124-126,144-146 | Sigma-finite factors inferred from probability; transports AE statements only. |
| iIndepFun_pi | 142-143 | Finite index and probability factors, same measurable f on every coordinate. |
| pow_le_pow_left₀ | 184-185 | Nonnegative lower base and base bound, natural exponent including0. |
| Real.sqrt_nonneg | 192 | Every real argument; no strict a>0 needed. |
| Real.sq_sqrt | 193-194 | a*q>=0 from a>=0,q>=0. |
| measureReal_eq_zero_iff | 137-138 | Relevant P set finite because P probability. |
| measureReal_mono | 116,250-251 | Containing set finite because P probability. |
| measureReal_union_le | 252-253 | All actual events; finite P additionally available. |

范围说明：Pi、Independence、Integrable 和 Bochner 文件虽然位于 unit283/284 的 primary-api 目录，候选实际导入的只是四条冻结 Mathlib 模块；没有依赖未qualified283/284证明。ExpDeriv、IntegrableExpMul、Group/Arithmetic 和 Analysis/Complex/Basic 是已验 hash 的供给输入，非此候选的新增主数学依赖。
