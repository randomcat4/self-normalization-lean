# OQ4 反射与BE/SP到真实S/AC输入冻结 v1

源 current/oq4/b01/proof01.md §3 的“same assertion holds for −Y”及独立闭区间AC后果，衔接已冻结FiniteSurvivalLaplace与现有KilledBlockBounds的实际iidOneSidedSurvival/iidIntervalConcentration接口。

ν为任意ℝ Borel概率测度，ν⁻=map(x↦−x)ν，β≥1、C_BE≥0。实际普通和CDF输入只对ν给出：∀自然t≥1、∀实x，
|Π_t(ν).real{a | prefixSum a t/sqrt(t)≤x}−standardNormalCDF x|≤C_BE β/sqrt(t)。

冻结目标：

1. 真实有限产品反射law：Π_t(ν⁻)=map(a↦−a)Π_t(ν)，所有t包括0；真实prefixSum在反射下变号，closedLower/BoundaryOccupation.lowerBlockSurvival与公共closedUpper的反射原像精确对应，不删除零时刻或任何原子。
2. 由唯一ν-CDF输入证明ν⁻满足同一全t/x CDF误差、同一β与C_BE。需证明实际标准正态Φ的反射恒等式，并用其连续性（已有1-Lipschitz）从≤的CDF误差推出<版本再反射。不能假设ν无原子、不能直接把P(X<a)换成P(X≤a)，也不另加ν⁻-BE前提。
3. 唯一额外概率输入是ν与ν⁻各自的**源原始Spitzer形式**：全部L>0、0<s<1的实际最大值Laplace和式=exp(实际正部普通和Laplace和式)。不声称由ν的SP自动推出ν⁻的SP，也不假设所需S、非增性、可和性或等价生成式。复用FiniteSurvivalLaplace得到对全部自然t≥1,d≥0，ν真实闭上侧与闭下侧生存概率均≤C_S(d+β)/sqrt(t)，其中
   C_S=sqrt(2) exp(6+3C_BE)。
   证明现有iidOneSidedSurvival ν C_S β谓词，而非新造抽象事件接口。
4. 从同一ν-CDF输入及β≥1（无额外矩假设）证明对全部t≥1、实x，ν真实Π普通和落在闭[x,x+1]的概率≤C_q β/sqrt(t)，C_q=1+2C_BE，并供应现有iidIntervalConcentration ν C_q β谓词。可复用IntervalConcentration的任意law闭CDF界，不得使用“仅当β为某第三矩才成立”的高层接口而暗增矩条件。
5. 明确证明C_q,C_S非负，输出这两个实际谓词的联合接口，供已有KilledBlockBounds调用。常数只依赖C_BE；若外部BE取数值通用常数，它们才是通用数值常数。β在此仍是明确BE参数，未来调用者可取实际第三绝对矩并用已审矩定理供应β≥1。

拟Shao/OQ4/ReflectedSurvival.lean。不直接证明外部BE或任一SP，无新公理；无条件S/AC/O0、B1、长时间K/Kv、能量分母与完整OQ4仍OPEN。保持全部原子、t=1,d=0、全零路径；不更改公共定义或任何既审源。
