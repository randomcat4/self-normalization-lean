# unit187 repair01 的完整改变证明审阅

STATUS: CORRECT

本文件与原独立 source-review.md（SHA7435d3ca6f8957b913288e08109689097e007275190d7abad32277158e78aedb）结合，覆盖新源全部声明与证明。原源5c711507…的native01确实RC1、无对象，原审阅的数学候选判断不改写成编译通过。现源1e5a32cc…仅5个proof body改变；6定义与另外3定理整段字节相同，原完整审阅按精确字节复用。

已完整读取原10个错误及所有相关警告的stdout/stderr、修复delta、diagnostic-disposition、freeze-comparison和actual-scopes，并独立验证12payload与16inputs全部哈希。

**signLeft_isometry（41–60）**：完整重读。唯一变化去掉不用的hsi等式名；cases s i把符号两值直接代入，平方恒1。后续真实Euclidean平方范数、非负性、差兼容性与全距离等距保持完整有效，无新增数据。

**ghostMatrix_envelope（81–101）**：完整重读。对角用默认simpa[ghostMatrix]真正消掉if True并与mul_self_nonneg匹配。异索引以当前ite_eq_right化简；第三次三角界的abs_add替换为现有abs_add_le，恰好|a+b|≤|a|+|b|，未弱化结论。四个hR和三次三角界仍给乘积W_iW_j，零权重/字面对角保留。

**swapSample_measurePreserving（103–125）**：完整重读。false分支的pairSwap固定值经δ/η转换为既有Prod.swap；true分支为既有id；change只转换命题内的原冻结函数，不初始化新数据。最终map目标显式展开原pairedLaw与swapSample为Measure.pi和逐坐标原lambda，使pi_map_pi结果匹配。hμ仍按实际hmap重写取得SigmaFinite，无额外local instance或测度。

**ghostMatrix_ae_envelope（127–196）**：完整重读。开头unfold pairedLaw，所有Prop helper中同一源测度写成其已冻结的Measure.pi(fun _=>ν.prodν)值。这样实际概率因子提供所需IsFiniteMeasure；既未假定结论，也未添加letI/新测度/新假设。四个异索引joint map、每个投影可测、边缘ν、独立组合及QMP.ae与两层有限交完整保留；本次实际TYPE仍以原pairedLaw表述，外层AE z的作用域完整。

**ghost_row_norm_law（198–256）**：完整重读。固定索引if以当前ite_eq_left/right化简；第四角的两个snd投影增加明确Measurable期望类型。hentry所绑定i/j可见，每个show内部的z仅在其lambda内可见、互不泄漏；是先前冻结的sndObservation(i/j)值，没有匿名数据helper。随后u的有限行和、平方和、sqrt连接、真欧氏范数可测性与map_map/map_congr全链完整有效。声明14头/6完整值、34授权表达式与全部实质作用域不变。

这些修复都是实际诊断对应的证明表达/类型转换与基础三角界名称修复；没有新数学前提或外部结果。native02和同对象审计均实际RC0，支付了原仅静态推断而未通过的elaboration层。最终接受只绑定修复源，旧失败永久保留。
