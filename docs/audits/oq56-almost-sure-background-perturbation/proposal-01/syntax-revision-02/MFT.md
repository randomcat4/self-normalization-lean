# unit280 数学忠实性表（提案，未冻结/未检查）

| 项目/接口 | 精确对象与量词 | 来源/条件 | 边界与未声明事项 |
|---|---|---|---|
| Ω、μ、n | 任意 Ω 的可测空间，μ 概率；每个固定 n:ℕ；实际 Pₙ=Measure.pi(Fin n→μ) | p41 iid；父设计280 | 无非原子或标准 Borel；事件覆盖 n=0/1，小 n 不造分母结论 |
| D01 共同事件 | 固定 n/r/w 后一个 E；∀坐标权重非负，∀i≠j 真实 r(xᵢ,xⱼ) 受 w(xᵢ)w(xⱼ) 控制 | p41 PE 为 μ.prod μ-AE；hw 为 μ-AE | i≠j 与 xᵢ≠xⱼ 不混同；原 r 对角任意，不换成零 |
| T01 私有坐标对 | 对每个 i,j:Fin n，i≠j 时 pair map MeasurePreserving Pₙ (μ.prod μ) | Mathlib 全独立 pi 恒等坐标、双独立 map_prod、求值边缘 | 不以“独立”一句话省略推前；n=0 无可取指标；无 Ω 相等可测要求 |
| T02 AE 共同事件 | hw/hr⇒∀ᵐx∂Pₙ,x∈E | 单坐标/对坐标 QMP 拉回 AE，有限合取 | 不增加 r/w 可测前提；也不从 AE 推 E 可测；不作不可数 AE 交 |
| T03 事件可测 | Measurable(uncurry r)、Measurable w⇒MeasurableSet E | 函数复合、实数绝对值/乘积/序关系，有限交 | μ 不参与；对角索引约束为 univ；不声称任意 AE 谓词可测 |
| T04 概率一 | 同样可测条件与 AE 条件⇒Pₙ(E)=1 ∧ Pₙ.real(E)=1 | T02 null complement、T03、Pₙ total mass1、toReal1 | 普通可测概率事件接口；不是样本选择规则或所选统计量的可测性 |
| D02/T05 异常残差和 | x∈E 后∀v:Fin n→ℝ ∀B，|F_A|≤ℓ²/2 | 精确合格278 T12，rₓ/wₓ直接代入 | 不要求对称、n≥4 或 B 非空；A=univ\B，半系数保留 |
| D02/T05 行差 | 同一 x、全部 v/B；4≤n⇒∀i∈B，行差绝对值≤ℓ wᵢ/(n-2) | 精确合格278 T13 | 仅 B 内行，不是全部 i；原 n-2；B 空时量化空 |
| D02/T05 中心化范数 | 同一 x、全部 v/B；4≤n、3≤card B⇒范数差≤ℓ sqrt(Qw)/(n-2) | 精确合格278 T19，原对象/独审复用 | 系数1；允许 Qb=0、sB=0；无除 sB；不是物理 m=3 推广 |
| T06 同一样本 forall B | 一个 Pₙ-AE 包：x∈E ∧∀v∀B 三界 | T02 后逐点 T05 | 不先固定B再偷偷交换量词；∀v 也在事件内点态导出 |
| 实际来源 g | 任意 g:Ω→ℝ，v(i)=g(xᵢ) | 只需有限点态代入 | 不要求均值0/方差1/可测；没有因此宣称统计量概率事件可测 |
| 样本选择 B | 任意 S:(Fin n→Ω)→Finset(Fin n)，每个 x∈E 取 B=S(x) | D02 的逐样本 forallB | 不声称 S 可测；不声称选择后的条件法则或尾概率接口 |
| 对称/分子恒等式 | 本提案不纳入278 T10 | p41(4) 若未来真需须显式点态对称 | AE 对称不能默换处处；无无关恒等式包装 |
| 物理尺度 | backgroundRow denominator n-2；hB residual scale(cardB-2)/(n-2) | p41 §2；278 固定值 | 279 未合格不消费；B→Fin(cardB) 与物理 m≥4 分离 |
| 定义组装语法 | 两最终proposed HEAD末尾各直接含唯一 :=，裸RHS保持不变；head+LF+RHS直接拼接 | ASSEMBLED-DEFINITIONS.txt；pureTypedHEAD仅作说明 | 无额外separator组件；两完整定义的 := token各恰好一次；数学签名不变 |
| 证明/证据状态 | 8提案HEAD、2固定RHS、完整数学路线 | ACT十二输入/额外sourcefp封存；已有278精确证据复用 | 本单元SOURCEAccepted=false、kernelChecked=false、qualified=false；文本guard非内核 |
| 原根与原αp | 条件投影/均值方差/交互/rareblock/PE-R/PE-L/NR/DC/root OPEN | p41/p51原域；αp=2(p-2)/(2p-1) | 不以共同AE事件声明概率尾结论，不从276任意α条件窗偷换无条件结论 |

独立审查状态：尚未委任/完成。本作者的边界核对不是独立审查。未来实际 Lean/AX 仅可由已授权 owner 在指定服务器完成；本次未调用。
