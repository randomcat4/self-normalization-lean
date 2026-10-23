# 实际 future/noise Fourier 乘积声明冻结

根完整核对四项声明（两个实际定义/两个定理），冻结 candidate SHA256 727d51ec39a93b31288b65c5f174cf196bc402dcafbf1494c6fa1981bca1c415，源supplement2343–2353、main613–620。实际核是原H_y在规范iid路径的真实和/原平方和及真实完整噪声律上的正移位平均，实际变换保留负单位频率相位。正移位贡献正特征相位，所得次序 Hhat*Xi*phi^m 正确，不能替换二次项或中心化原平方和。

条件仅接受的实际law/probability、h3、正方差、有界支撑，用于真实噪声概率律；不增加gamma≤2h、均值0、自由变换或假定乘积式。先用真实平移Lebesgue可积性与Tonelli/Fubini支付交换，再消费实际iid特征函数幂和实际Xi积分身份。m=0、y=0及全实u/v保留。

授权 /root/common_highfreq_author 在原独立树追加 Shao/Probability/SourceFutureNoiseFourier.lean，直接开始实现，保持既有centered/power/kernel源冻结。暂定kernel精确接口可消费推进，联合接受前其唯一完整审查须CORRECT；若依赖变动只核受影响delta。此单位只交付实际核的可积性与精确乘积式，不声称反演、平滑微分、marknorm、区域积分或C1/C2概率链闭合。之后mathlib反演2π重标定须显式支付。

复用既有服务器树、缓存、脚本与root-heavy.lock，Lean仅CPU10–13固定版本参数；新增源一次独立完整source-to-statement/proof/actualtype/definition审查和内核/所属传递公理门。
