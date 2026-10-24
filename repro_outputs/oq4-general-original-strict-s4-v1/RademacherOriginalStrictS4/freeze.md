# 原 AE iid 实际严格 S4：完整冻结与数学证明

原 spectrum01.md 第4节严格边界在固定 Rademacher 律上应保持真实能量和实际布朗分母。新模块冻结1个定义 sourceQ 与2个定理，无额外头，全部量词/宇宙/定义值见 frozen-interface.lean.txt；冻结时无实现。body-local have/let允许。样本空间ΩX与布朗空间ΩB宇宙独立；原空间只给概率测度、正下标AE iid同分布，不增加完备性、普通可测性或矩假设。

sourceQ 分子是既有 sourceStrictEvent 的原空间实际概率，墙为 (h/√n)√sourceEnergy，sourceEnergy 来自真实有限平方和；分母是给定B/P/hB的实际弱布朗上确界概率(h/√n)，不是自由尾函数。X0未使用。

第一定理对所有n与所有实h成立。先用已接受source_strict_probability将真实原空间自归一化事件概率传到规范有限向量事件。n=0时两个严格正前缀条件均为空条件，旧zero_time分别给概率1，无需解释h/0。n>0时√n>0；同一规范full-measure支持集上V(v)=√n，所以(h/√n)V(v)=h。因此两个真实规范事件AE相等，用measure_congr及ENNReal.toReal得到所需概率。此步骤不把AE事件等价提升成全样本集合相等，也不把零时刻改成包含零前缀的严格事件。

第二定理取规范generalstrictS4的共同正尾部与两个极限。第一定理给sourceQ与规范Q逐k精确相等，直接传递真实自归一化比值与对数/标准化极限。h→∞给最终h>0，在该尾部qualified source_ceil_boundary_bridge给真实确定有限和事件概率=strictP。于是原自归一化、原确定事件两种实际概率同时正，且比值最终相等；后两项极限由最终相等传递。所有参数与scale2/scale3假设保持原样，早期n0/h非正均允许，不声称全序列比值正。

GeneralStrictS4 的精确源935753f4已经服务器内核/所有owned递归公理首成功；冻结时尚未独立终审。后续新鲜独立完整终审必须将该规范证明与本原空间传输一起覆盖，接受前两者都须CORRECT；不把未完成的review当成资格。所有原根仍OPEN。真正后继是应用严格generalS4到字面临界尺度，另证严格相位的整列近似/极限点，不复用弱相位的整数端点值。
