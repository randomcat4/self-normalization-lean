# 实际有限路径初始完成：零能量原子的CDF支付

来源 main.tex1038–1076 cn:initial及supplement3914–4025 cn:zero/cn:scalar。实际统计量使用已接受 Shao.C1.normalizedEndpoint 和真正 Shao.energy=∑z_i²，未替换为方差/中心化能量；零能量时端点严格按源定义取0。四个完整头实现前冻结。

明确方法偏离（结论和假设不扩大）：源cn:zero用截断能量U的Chebyshev界独立证明P(Q=0)≤CR；本单元在已经明确给出的闭CDF差δ输入下，利用端点零原子≤2δ来支付Q=0。一般原子界以任意参考律ρ在指定点x无原子为条件，由闭、开CDF两界及μ(Iio x)+μ{x}=μ(Iic x)得到。标准正态在0无原子是库证明的结论。{Q=0}⊆{W=0}由真实normalizedEndpoint零能量值推出，故P(Q=0)≤2δ。没有假设Q=0概率小或把目标路径误差写入前提，也没有引入三阶/更高矩。

实际有限路径的边际/闭阈值联合完成误差遂≤4δ，消费已合格InitialCompletionError的2δ+P(Q=0)和Shao.energy非负/可测性。P是任意明确有限路径概率律，因而覆盖iid产品律；独立、同分布、中心性只用于尚未形式化的外部标量δ=CR输入，不是本次误差传递需要的隐藏条件。所有n包括0、a/v实数及≤v闭阈值保留；n=0时CDF输入本身不可能任意小，未作退化参数假设。

外部Pinelis2011式(1.10)/(1.7)复述Shao的截断标量界仍未形式化；独立cn:zero的16R证明也不被本替代支付路线冒充。C1/C2原根、三域/telescope、terminal/overshoot和核光滑性仍OPEN。

attempt001因缺少当前工作树中的旧MeasurablePath对象停止；按v71 baseline-reuse逐一验证5个旧源/对象后，仅新增4个只读叶符号链接，无旧producer重编。accepted-dependencies-v71.json记录精确map源/object/hash。attempt002仅剩显式Iio参数推断失败，原源保留；attempt003内核及全所属AX PASS，8实际owner=8定理，4公开，0非定理值。按实际module owner全选，未仅扫public。
