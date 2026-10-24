# 初始完成误差装配及零能量损失

来源 main.tex 1038–1076 cn:initial，supplement.tex3914–3965的S.8.2/S.8.4归属边界。三个完整声明先冻结再实现，所有原量词与假设未变。Q只要求可测且几乎处处非负，W只要求AE可测，没有假设Q严格正。

zero_energy_removal 对任意0≤f≤1可测函数，先证明f(W)可积。以s={Q>0}分解原积分，删除部分的非负积分≤P.real(s补集)；由Q≥0几乎处处，s补集与{Q=0}几乎处处相等，故删去Q=0成本≤P.real{Q=0}。它没有假设W在Q=0上取任何特定值，也不丢弃零能量原子。

边际与闭阈值联合装配均取真实W推前μ=P.mapW，用AE可测性证明μ为概率律。原域闭CDF差前提逐点等价于μ的闭CDF差，不把目标期望差或路径概率差写入前提。消费EndpointCDFTransfer的2δ误差，再用已合格同一原B/PB的Gaussian积分身份，把标准正态期望识别成真实Brownian生存或生存∧B1≤v概率。两项最终误差均≤2δ+P(Q=0)。联合遮罩精确≤v，W有原子时仍覆盖。所有桥概率/积分使用bridgeLaw B PB，没有另造无关耦合。

对原文最终CR范围，仍需把δ和P(Q=0)按实际有限iid/self-normalized变量界定，并保留Pinelis2011复述Shao标量界的外部来源；本模块不宣称该外部估计已形式化，不宣称C1/C2根闭合，也不支付terminal/overshoot预算。正时间核商/光滑性及supplement全部半线a=0置零约定仍属其他范围。

attempt001/002失败分别为闭CDF事件隐式参数展开及概率推前API命名，源码/日志保留；attempt003 kernel PASS。使用服务器固定版本、CPU14–17/c12-heavy.lock/-M8192-j4，复用旧成功对象，未重编旧producer或改缓存。全所属AX审计沿用Established工具按实际module owner；没有仅看公开名。
