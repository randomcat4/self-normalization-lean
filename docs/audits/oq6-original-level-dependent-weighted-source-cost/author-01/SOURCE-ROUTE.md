# Unit250 作者证明说明

状态：`PROVED_CANDIDATE`，数学推导完整；Lean 内核、实际生成接口和传递公理检查均 `PENDING_SERVER`，新鲜独立完整复核 `PENDING`。本目录不是已接受结果。作者任务请求模型 `gpt-6.1-sol`、推理强度 `xhigh`；实际运行模型/强度和各项用量对本上下文不可见，记为 null。

冻结对象是 `Shao.OQ6.OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost`，freeze-01/frozen-declaration.json 的 SHA256 为 `a26f0a109e8f06fd03c4326ecd868ed882ae40f84a927c172b67e567ac8166de`，4352 字节。声明、前导、结尾逐字节保留。只有这一条公有定理；全部新增辅助事实在该证明局部，不新增顶层声明、选择器、数据或实例。

## 1. 原文与语义

完整已读原始 p51.md（17326 字节，SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`）和 p54.md（6045 字节，SHA256 `e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`）。p51 S10 的预算是

`B_z = C0*((1+rho)*z/sqrt(n) + J/((1+rho)*z*sqrt(n)))`，

其中原始 `J = sum_j psi_j^2/(n-2)^2`；S13 的删一量保持原 n 的全部系数，只抹去 incident edges。S14 的 full/partial 指数、cap 和原始 D/Ddeleted 均逐字面保留。本命题只证明这一原始 level-dependent 解析费用，不涉及 unit249 的 clipping1 费用。

p54 修正 p51 S6 的过强条件 p 矩变化率：只允许统一有界与收敛，不能声称任意多项式速率。本证明没有使用任何 p 矩、变化率、截断模型、混合 g²r²、高阶矩、标准 Borel 或新包络假设。原始概率引擎和集中接口仍归属 Shao–Zhou（2016）；本有限解析桥不证明其外部定理、存在性或尾概率结论。

## 2. 全部记号来自同一个原始核

`g(o)=integral_y h(o,y)`；`r(o,y)=h(o,y)-g(o)-g(y)`；`v=integral r²`；`rho=sqrt(v)`；`N=sqrt(n)`；`P=mu^n`。原始随机变量 `ξ0_i=g(O_i)/N`。保留原始 D、原始 deleted D、B、deleted B、fullTest、deletedTest、S、Sdelete 与归一化积分 I。

仅为局部证明令 `L=sum_j psi_j²`，`Ldelete_i=sum_j psiDeleted_ij²`，`K=(n-2)²`，`Q=(1+rho)*z*N`，`A=(1+rho)*z/N`，`denA=(1+rho)*z*(n²*N)`，`k=C0/(K*Q)`，`kA=(4*C0)/denA`。这些不是新模型或随机量选择。

`n>=4` 给 n>0、N>0、K>0、n²>0；rho>=0 和 z>=1 给 Q>0、A>=0、denA>0，且 `denA=n²*Q`。包括 C0=0、rho=0 的边界都允许。

## 3. 分母桥与删一差的完整推导

由 `n>=4`，

`4*(n-2)²-n² = 3*(n-4)²+8*(n-4) >= 0`。

因此 n²<=4K。乘 C0>=0 和 Q>0，再作正分母交叉相乘，得到

`0 <= k=C0/(KQ) <= (4*C0)/(n²Q)=kA`。

引用已接受 `residualEnergyJ_eq_rowSqSum`，原 full J 精确等于 L/K；原 deleted J 按原定义精确等于 Ldelete/K。因此

`B = C0*A+k*L`，`Bdelete_i=C0*A+k*Ldelete_i`。

与已接受 SourceAnalyticCost 在同 mu/h/n/z、系数 4*C0 的预算完全一致的局部包络为

`BA=(4*C0)*A+kA*L`，`BAdelete_i=(4*C0)*A+kA*Ldelete_i`。

L 为平方和，故 L>=0。由 C0<=4C0、A>=0 和 k<=kA，得到 B<=BA。差分必须单独证明：先精确消去两预算中同一个确定项 C0*A，得到

`|B-Bdelete_i|=k*|L-Ldelete_i|`；

同样消去 BA 的确定项后，

`|BA-BAdelete_i|=kA*|L-Ldelete_i|`。

因为绝对值非负，k<=kA 精确给 `|B-Bdelete_i|<=|BA-BAdelete_i|`。这里没有由 B/Bdelete 分别支配推导差支配，没有假设行能量差有固定符号。

## 4. 同一个正归一化积分

令 `φ(o)=z*(g(o)/N)-(z*(g(o)/N))²/2`，`m=integral exp φ`。g 产品积分的可测性由 hh 的 stronglyMeasurable/integral_prod_right' 接口导出，r 由可测函数相减得到。φ 可测。

已接受 `QuadraticTilt.weight_bounds` 给逐点 `0<exp φ<=exp(1/2)`；常数在概率测度可积，非负有界支配给 exp φ 可积。对同一 mu 和同一 φ 应用已接受 `finite_observation_product_tilt`，得到原始 `I=integral exp(S)=m^n>0`。有限乘积中的常数 m 的乘积正是 m^n。φ 与原 S 的 summand 定义相等。

SourceAnalyticCost 所用的相位 `(z/N)*g` 与原始 `z*(g/N)` 通过域代数恒等式相等；只重写这一等式，不替换全/部分指数或归一化积分。证明中的 hscale 显式记录该恒等式，hSource 的标准乘除简化在所有出现处实行相同代数改写。

## 5. 唯一已接受解析生产者调用

`SourceAnalyticCost.actual_quadratic_source_analytic_cost` 只在 hSource 中调用一次，使用同一个 mu/h、原全部核假设、n>=3（由 n>=4 推出）、同 z/window 和非负 4*C0。hSource 完整保留生产者的四个输出：full 加权可积、所有 deleted 加权可积、归一化费用恒等式、三次上界。生产者使用的 m^n 通过第4节的精确 hNorm 改写为同一个 I。

其接受上界在系数 4*C0 时正是冻结右端：

`64*exp(1/2)^4*(1+4*C0)*(1+rho)*(1+z)^3/sqrt(n)`。

原生产者证明和既有 TYPE/AX 证据按精确 SHA 复用，不在本任务重审或重跑。

## 6. 原始加权可积性与积分比较

所有可测性都直接从原 r 的可测性、坐标投影和有限和推导。incident-erased 矩阵的每项按固定有限索引分支为 0 或同一 r 项；full 和 deleted pair sum、row sum、row square sum 均可测。B/Bdelete 的可测性由第3节精确仿射公式导出；D/Ddelete 的绝对值通过原定义的有限 pair sum 导出。cap 是连续的 min/absolute-value 组合；S/Sdelete 是有限可测和。因此 full/deleted 加权原始 integrands 具有真实可测性，未从积分存在反推可测性。

z>=0、B>=0、平方和、绝对值、cap>=0 和正指数共同给原始两个 integrands 逐点非负。用 B<=BA，得到 full integrand 支配；用单独已证的 deleted difference 支配、相同非负 cap/z 和相同正的部分指数，得到每个 deleted integrand 支配。已接受的相应 source integrand 真正可积，`Integrable.mono'` 在已证明的可测性和点态 norm 支配下给原始所有 integrands 可积。

以 `integral_mono` 对 full 及每个 deleted 项积分，再对 Fin n 求和。得到原始非负分子 <= 已接受 source 分子。两者除同一个 I>0，原始 sourceCost 非负且 <= sourceCostA；再接生产者冻结右端，完成全部五项合取。

## 7. 验证边界与非主张

只进行本地文本/字节/结构静态检查。没有本地 Lean，没有服务器或网络操作，没有上传、Git、API、发布或新上下文。本候选尚无新源内核/公理收据，不得标记 kernel PASS 或 accepted。没有尾、CDF、固定 clipping1 三次费用、eventual window、DC、external SZ 或完整 OQ56 闭合结论。

本源唯一顶层定理的候选证明应由另一新鲜上下文做完整 source-to-statement/proof 审查，并由 lane lead 在服务器执行新源 kernel 与同第一成功对象的 all-actual-owner 传递公理审计。标准白名单仍是 propext、Classical.choice、Quot.sound。
