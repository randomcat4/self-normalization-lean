# OQ4 Rademacher 谱链第一有限叶：真实弱闭一步主余弦特征对冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

来源：固定commit35d4580b61e22e7145f47730045a09874ef93259的oq4/c01/spectrum01.md，SHA256b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b，原11–34行S1的严格弱组件。只读intake980f873ce9b94b373b169a31d1cbfe4e708af7ac9147e55b2cfc039a62e3689d不是认证。本叶与E1/E2/E3独立，拟新Shao/OQ4/RademacherCosine.lean，仅本线namespace/模块，不改公共Basic/Probability定义。

## 真实law、参数与事件合同

实际ν_R固定为ℝ Borel上的二点测度

ν_R=((1/2:ℝ≥0∞) • Measure.dirac (1:ℝ))
    +((1/2:ℝ≥0∞) • Measure.dirac (-1:ℝ))。

允许在Shao.OQ4内透明命名，或使用已有完全相同的实际library对象并内部证明等式；不得把概率性、对称性、余弦系数或所需特征对设为新的前提。

固定m:ℕ且1≤m，h:ℝ满足(m:ℝ)≤h<(m:ℝ)+1；H=(m:ℝ)+1，a=Real.pi/(2*H)，ρ=Real.cos a。实际整数状态r:ℤ满足−(m:ℤ)≤r≤m。状态实嵌入为(r:ℝ)，弱闭域是Set.Icc(-h)h，吸收格点是±H，不能把其写成±h。

使用既有实际killedKernel ν_R h、Kcos ν_R a h和既有真实product路径/生存law。killedKernel为平移后限制到闭区间的真实次概率核，不是条件存活后归一化转移。不得另造一个具有目标谱的抽象矩阵/核代替实际对象。

## 冻结有限结论

1. 内部证明实际ν_R是概率测度，并给实际一步闭核的二点行测度公式：

killedKernel ν_R h (r:ℝ)
= (if |r+1|≤m then (1/2:ℝ≥0∞) • dirac ((r+1:ℤ):ℝ) else0)
+ (if |r−1|≤m then (1/2:ℝ≥0∞) • dirac ((r−1:ℤ):ℝ) else0)。

这里条件是整数绝对值/整数m比较，精确识别弱闭全整数状态I_m；实现中允许等价的两个实闭条件，但必须内部证明在给定r,m,h下与整数条件等价。出界质量直接丢失，不补回。

2. 对真实余弦测试y↦cos(a*y)，供应其在实际killedKernel ν_R h (r:ℝ)下的真正可积性；使用已有bounded-kernel接口合法，不增加积分可交换性或有限性前提。

3. 证明源主特征对的一步实际身份

Kcos ν_R a h (r:ℝ)=ρ*cos(a*(r:ℝ))，

并以既有killedKernel_integral_cos或等价正式定理接到真实核的实积分

∫y cos(a*y)d(killedKernel ν_R h (r:ℝ))=ρ*cos(a*(r:ℝ))。

4. 给所用a与ρ的真实0<a<π/2、0<ρ<1（可与主身份合并）。这些只是同一冻结参数的有限附属事实，不冒称谱隙/完整谱。

可提供可测有界实测试f的一步积分helper以承接真实二点行，但不能把主结论弱化成自由cosineCoefficient ν_R a=cos a。主结论始终是实际被杀闭核。公开Lean条数最终实际测量，不机械按本条目数计为独立原始义务。

## 边界、整数性与不可扩展解释

r必须整数；对任意实起点z∈[-h,h]，可达coset为z+ℤ且吸收点一般不对称，不能把同一主特征对扩大到所有实起点。该整数性是原Rademacher零起点状态的真实约束，不是新分布条件。

m≥1保留原h≥1范围；h=m的弱闭端点和任意m≤h<m+1全部包含。r=±m时向外一步到±(m+1)，正是cos(±π/2)=0处；向内质量仍1/2，r=m−1或−m+1走到±m的闭边界质量保留。不加无原子/非格点/aperiodicity条件。正负r和所有整数状态均须覆盖。

本叶不带时间n，不证明有限n的主函数迭代、不建立完整矩阵谱/正交基/有限谱求和S1，不删负/零模态，不证明S2–S4、4/π、Brownian基准、K/Kv或锋利窗口分类。既有一般killedMass与closedStrip/iid真实概率桥可引用，不因一步特征对就给生存质量一个未经证明的谱值。n=0空路径和0≤h<1退化范围仍由原事件约定保留，后继若涉及这些范围必须另写接口，首叶不以ρ>0覆盖它们。

严格事件不属于本冻结。只在整数h时弱边界吸收shift为+1、严格为0；一般实h分别floor(h)+1和ceil(h)，不能用两个固定实shift替代原源。

## 执行与验收

冻结后证明实例不得改measure、量词、参数、弱闭事件或把整数r扩大为实数。先匿名完整数学proof，再全新独立关键缺口审查，后续Lean实施需lead明确scratch/canonical窗口。所有Lean/重计算只指定server；作者唯一emit；独立no-o/fullsource所有getModuleIdxFor?none无名字过滤、全部冻结旧OQ4真实共存；父全owner+namespace标准三公理门。禁sorry/admit/newaxiom/unsafe/native_decide。不改公共/root/cache/锁/Git，所有原完整根仍OPEN。
