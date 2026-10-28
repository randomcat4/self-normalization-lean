# 第256单元精确证明路线

本路线对应冻结head7951013304c2f42406971387ea8749955c0c44fa5e56c604d9ef587cd0d0a6ac以及源556ba5b0dc475e4881e3e91a774b2f22961bd3526683b6356ae1c3061f9598a1。完整证明在PROOF-BODY.txt，所有中间对象的完整类型、RHS、源位置与词法范围在LOCAL-CONTEXTS/BINDING-TYPES；此文件给逐段数学依赖。

| 冻结输出 | 实际证明来源与条件 |
|---|---|
| 一次选择m₀，在全部n/y/ε前 | qualified255原定理调用一次，取m₀/hm₀/hcg/整包；首合取直接hfor |
| 相同P₀、ν、q及原sourceCost0界 | 同hfor于当前n/z和ε0，packet内固定量定义不含ε |
| ε正、小且趋0 | n≥4给√n>0；显式倒数序列与one_div_add极限；K=4√n |
| ξ可测、L²、mean0、energy1 | 原ξ0由hgcoord与coordinate评价；同q保测拉回L²与积分，二矩逐项求和 |
| Ylocal/Y可测与ε误差 | 同μ₀的四进制scalar编码；quantized_observation_spec于每个ε(k) |
| 当前η的归一化/独立/能量/正分母 | 每个k重新应用同hfor，不复用η0或s0 |
| H/Hdelete裸L¹与Anew/删除Anew | literal_deleted_weighted_cost_limits；仅同ξ二矩、Y误差及A/B/真实删除量裸L¹ |
| 完整三元因子 | 当前hfactorK分别恢复M/Anew/B，组合产品可测三元组 |
| 真实删除三元因子 | 当前Fdel恢复Ddel/Jdel/Bdelete；当前retained factor恢复原ξ保留平方和Uret；组合Mdelete、|Ddel|+Mdelete和Bdelete |
| signed阈值精确等式 | 当前hfor的任意实比较z分支，原W/D/V及当前D2全保留 |
| 真Qε包络及L¹趋0 | actual_normalized_remainder_envelope_spec用当前B；Dη−D1=Qε，4ε√n=Kε；有限∫H与ε→0夹逼 |
| 真Δ等式/上界/积分界 | 逐点展开Δ=M−Mdelete；两项非负及L¹，积分三角界 |
| 全及partial weighted积分/比值极限 | 通用加权consumer；全Iη归一；经id和q的同目标函数积分law送回原P |
| compact删除费用/Lcompact/compactCost极限 | 连续cap min(|η|,(1+z)⁻¹)及原ξ截断费用；同一积分law送回原P |
| sourceCost0非负/三次界 | 同ε0的qualified255 original费用字段；当前B=512rho z |
| 任意δ>0最终η费用≤三次界+δ | sourceCostη→sourceCost0，取Iio(sourceCost0+δ)的邻域；再接sourceCost0界 |

使用的外部/既有结论均为KNOWN_QUALIFIED_INPUT；本证明新增的是上述同见证当前层级参数连接和明确删除因子的组合。hSubtypeSum、Δ代数、积分law、ε和eventual界是PROVED_HERE的内部局部步骤。没有OPEN或等价原题被藏作辅助前提。

零边界：n≥4排除√n和原n−1/n−2分母退化；每个ε(k)>0；z≥1蕴含通用consumer所需z≥0；D2≥−1/2来自同255包；原projectionV=0时clipped统计量定义为0，编码Vη=0时除零统计量为0。原physical分母与这些零事件不同，本单元不作其概率付款。

计量、源码与审查边界：原观测μ始终是原投影/残差定义的测度；μ₀仅是同一次trim。所有full/partial分母为完整I，所有真实删除量保留原n系数。不存在clip1替换、混合四矩推理、weightedL¹倒推bareL¹、重新选择m₀、为全k固定η0因子或无余量逐k三次界。

本作者交付后父线进行完整新源码独审及新源首次kernel/同首O allactualTYPE/requiredVALUE/递归AX。旧255/228及通用consumer的已qualified原O/TYPE/AX只按精确hash复用。原p矩strictbudget、actualupper、physicalpayments、外部SZ、CDF/relative/DC/fullOQ56/root继续OPEN。
