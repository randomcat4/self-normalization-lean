# OQ4 从显式 S/AC 到真实块界及有限 D8 冻结 v1

源 current/oq4/b01/proof01.md §5–§8 O0/R3/R4/D8。组合已证真实有限iid路径law、反向分块BoundaryOccupation、解析平均残差及条件核递推。目标消除R3/R4作为单独假设，但明确保留尚未形式化的S与AC真实概率输入。

ν为ℝ Borel概率测度，id/y²/|y|³真实可积，均值0、二阶矩1。β=∫|y|³dν，0≤β≤M且M≥0。Cq,Cs≥0。Π_t=ν的t维有限乘积law，U_t(d)=Shao.closedUpper d，L_t(d)={a|-a∈U_t(d)}。

明确概率前提：

- 每个自然t≥1及实x有Π_t.real{a|prefixSum a t∈[x,x+1]}≤Cq β/sqrt(t)；
- 每个自然t≥1及实d≥0有Π_t.real(U_t(d))≤Cs(d+β)/sqrt(t)，且Π_t.real(L_t(d))≤Cs(d+β)/sqrt(t)。

没有生存条件下独立性前提，也没有密度/无原子条件。上述是实际分布概率上界，不能替换成未定义的抽象S/AC常数。

令h≥3、m=⌊h²⌋₊。实际核P、作用U_n、φ=principalCosine h、r=实际cosineResidual、F/G及归一化量沿用已审定义。定义明确常数

C_layer=12 Cq Cs M(1+M)，
E=π³M/48+2π C_layer(1+2M)，A=2Cs，B=2Cs M。

冻结结论：

1. 对每个|z|≤h及自然j，实际κ=(P^m)(z)满足κ.real(boundaryLayer(h−|·|,j))≤(C_layer/h²)(j+1)。逐j由S/AC在首/末半块的真实输入导出，不能当作新增假设。
2. 对每个|z|≤h，真实块平均满足U_m|r|(z)≤E/h³。所有被积函数真实可积，κ质量≤1及AE支持必须来自实际核；不能仅把任意κ的旧定理改名为本结论。
3. 对每个|z|≤h，G_m(z)≤Aφ(z)+B/h。证明真实闭生存蕴含与起点符号对应的一侧生存；用m≥h²/2从S支付，再用闭域余弦下界(h−|z|)/h≤φ(z)（含两个端点）得到显示常数。不得假设φ在全实轴非负。
4. 若另有π(1+M)≤h、m≤N以及R=exp(π²)下的有限小系数条件(AR)(ER/h³)N+BR/h≤1/2，令H=2(1+AR)R，则对实际源起点|z|≤h：所有k≤N有0≤Ghat_k(z)≤H，所有m≤k≤N有|Fhat_k(z)−Fhat_m(z)|≤(ER/h³)(k−m)H。这里两块输入由1–3真正供应，再调用已审KernelAbsorption，不能重新作为假设塞入最终声明。

这些常数显式依赖M,Cq,Cs；只有S/AC另给固定数值Cq,Cs后才可统一称源C_M。ν原子、不对称、任意大跳，h=3、N=m及零允许参数均保留。无需第四矩/有界支持/非格点假设。

拟Shao/OQ4/KilledBlockBounds.lean。该单元认证从明确S/AC到实际O0/R3/R4块界及条件有限D8的约化，不证明S/AC本身、B1初值、Brownian近似、终端4/π、长时间K/Kv、E1-E6或OQ4。所有根保持OPEN，不改既审源或共同定义。
