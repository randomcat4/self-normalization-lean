# 同一原 Brownian 路径的初始完成恒等式

原来源 main cn:initial、1038–1076 的 Gaussian 端点/桥分解，后续紧域联合比较直接消费者。本单元消费已服务器核验、在独立终审中的实际桥律和桥/端点联合乘积律，不把 Brownian 概率或独立性作为前提。

冻结原始全域a,v∈R的精确声明与唯一透明值见frozen.lean.txt。initialSurvival在BridgeNoise×R上定义为实际连续函数g(t)+tw的一致范数<a，闭单位区间紧且非空使它等价于全部时间严格绝对值<a；并非有限网格或闭墙近似。连续范数的开下水平集给Borel可测性。

对任意真实桥噪声概率律ν，集合S的实质量经有界可测indicator1、Bochner Fubini换积分次序，得到product_real_section。initialSurvival的每个固定w截面逐项恰为strictInterval a 0 1 w；因此真实product初始生存质量就是正态w下的intervalCompletion积分。端点闭半线w≤v只在同一截面乘其indicator，保留等号与所有离散比较统计原子；不需要边界零测假设。

给定原IsBrownianReal B P，已建立的全时间同时AE身份gω(t)=B_t(ω)−tB1(ω)逐路径给gω(t)+tB1(ω)=B_t(ω)。原全时间严格生存事件因而AE等于同一个(bridgeNoiseB,B1)的initialSurvival逆像。用真实HasLaw将该概率传到bridgeLaw.prod(N01)，再用上述Fubini身份得两个原Brownian概率恒等式。原过程及原P不换，不从单时刻AE非法推出不可数同时AE。

此处只闭合真实初始Gaussian期望识别，不证明离散端点的Kolmogorov/BV误差预算、terminal/overshoot预算或整个cn:initial两条CR比较，更不关闭C1/C2原根。零宽区间事件为空，所有声明仍有效；半直线核a0一律置零的原约定保留为单独消费者范围。
