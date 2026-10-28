# HD293 source-bound scope

将已合格GV真实平滑密度与实际Hermite有符号参考的uniform pointwise误差转换为加权测试积分误差。泛型接口输入真实概率rho=Lebesgue.withDensity(ofReal k)、可测非负k、可测有符号reference、全局有界可测且Lebesgue真L1的f、逐点|k-reference|<=delta及非负C/delta，输出f在rho真L1、f*k与f*reference在Lebesgue真L1以及真实积分误差<=delta*∫|f|。不要求reference非负/概率/全局L1，不将sup误差直接在全平面Lebesgue积分；只使用明确可积f。误差premise是已生产的密度sup误差接口，不冒充原律期望误差或完整根定理。

后续实际同E小胞消费者必须从GV/HC取得真实密度/参考/原律数据，并从真实小胞support/weight/volume导出所需f全L1及∫|f|界，不可将其当无条件免费结论。当前单元无新旧OQ3数学模块直接依赖，只用同一固定mathlib的withDensity转换与Bochner积分；全部L1先于积分差/单调性成立。完整新证明/实际TYPE/局部值及同首OAX仍需独立终审。

原严格beta/p54/Song外部归属/反例与历史归档限制保留；原正面root/B-D/物理重建/胞求和/外区仍OPEN。
