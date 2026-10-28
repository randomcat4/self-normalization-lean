# Unit249 完整数学证明说明

状态：**PROVED（作者给出了完整证明；未经内核检查）**。

冻结命题及全部前提是 freeze-01/FROZEN-HEAD.txt。正文的形式源码逐字保留这个
公开声明，前导及关闭匿名 noncomputable section 的结尾也逐字保留。以下说明
只展开新增证明；旧248已合格证明作为公开定理消费，不重新证明。

在冻结的原16组外层对象和假设下，先调用248一次。其原六个全局定义为 g、
r=h-g-g、原 residual 二阶积分 v、rho=sqrt(v)、原 p 阶矩 β、原 strict-moment
cWindow。原六项全局结论直接传递。由同一个248结果选择正 cg，随后选择原
可数生成子可测结构 m₀，并取得 hm₀:m₀≤mΩ 及 hcg。定义相同的 μ₀=μ.trim hm₀。
保留的解析/编码整包、原费用整包和新分支的所有概率与积分都因此使用同一个
模型；本证明没有另行选择 cg、可测结构、coding witness、概率律或 n 截断。

现在固定 Cenv,aenv,t0,Menv 及冻结的非负/正性条件。记

`K=tailScale Menv`，
`a=remainderWindowScale K t0`，
`b=min 1 (sqrt(t0)/2)`，
`cPaid=min a b`。

这些记号在本说明中只用于阅读，形式源码没有另加 K、a、b 普通 let。
既有 bounded_scales_pos 给出 K>0；既有 remainderWindowScale_bounds 给出
a>0；236在原 t0、同 cg 上的第一字段给出 b>0。因此 cPaid>0，且
cPaid≤a、cPaid≤b≤1。

将236应用到正参数 `(2*cPaid)^2` 和同一个 cg。由于 cPaid>0，平方参数严格
正；又由 Real.sqrt_sq，`sqrt((2*cPaid)^2)=2*cPaid`。因此该次236的窗口
尺度 `min 1 (sqrt((2*cPaid)^2)/2)` 正好等于 cPaid。只提取它的非空窗口字段，
得到 eventually `4≤n` 且 `1≤cPaid*n^(1/6)`；该次236的费用字段没有使用。

rho 在原模型建立时已经固定。平方根在实数 atTop 的趋向与自然数到实数
atTop 的趋向复合，给出 `sqrt(n)→atTop`。因此实数 atTop 中的阈值集合
`{x | 1+rho≤x}` 拉回后，得到 eventually `1+rho≤sqrt(n)`。这个论证不需要
后置 rho，不需要 rho 统一有界，也没有额外使用 rho 非负。

相交下列四个 eventual 谓词：旧248整包、刚取得的非空 paid 窗口、固定 rho
studentizer guard、236在原 t0/cg 上的费用吸收。交集仍是 eventual 集合。
这一步在后置 w 和 z 之前完成，所以给出冻结命题要求的共同 n 集合。

固定该集合内的 n，再给任意满足冻结条件的 w 及
`1≤z≤cPaid*n^(1/6)`。由于 `n^(1/6)≥0`，cPaid≤a 和 cPaid≤b 分别推出
`z≤a*n^(1/6)` 与 `z≤b*n^(1/6)`。在前一个窗口上，旧248给出其原物理整包；
在后一个窗口上，236给出

`6*exp(-q)+2*exp(-cg*n)+8*exp(-sqrt(n)/2) ≤ R*Psi(z)`，

其中 `q=boundedPolylogMomentOrder t0 n`，
`R=exp(-(t0/2)*n^(1/3))`。最终 R 仍用原 t0，未用辅助平方参数。

令形式源码中许可的两个普通标量别名为

`payment=3*exp(-q)+exp(-cg*n)+4*exp(-(z*sqrt(n))/2)`，
`payment1=3*exp(-q)+exp(-cg*n)+4*exp(-sqrt(n)/2)`。

上式左端精确等于 `2*payment1`。由 z≥1 和 sqrt(n)≥0 得
`sqrt(n)≤z*sqrt(n)`，取负并除以正数2后次序反向；指数函数单调，于是
`payment≤payment1`。所以

`payment+payment1≤2*payment1≤R*Psi(z)`，

`3*payment+payment1≤4*payment1≤2*(R*Psi(z))`。

这些是冻结的 hFeeIsDoublePaymentOne、hPaymentLeOne、hDoublePaymentAbsorbed、
hLowerLoss、hUpperLoss。没有以费用界反推成本符号，也没有除 Gaussian tail。

现在给任意冻结外部标量 C1,C2,C3,C4、原外部 Shao–Zhou 有限成本输入以及原
strict-moment 窗口备选。共同 eventual 集合已给 studentizer guard，因此可以
消费248同一物理整包的 guarded 物理尾界。它使用原样的 mN/P、D1、ξ0、L0、
完整 full/deleted 指数加权 sourceCost0 和

`Tphysical(ζ)=if sqrt(centeredSq n g r ζ)=0 then 0 else
  (projectionW n g ζ+residualStatisticD n r ζ)/sqrt(centeredSq n g r ζ)`。

该整包的最后物理字段给出

`Psi*exp(-C1*L0)*(1-C2*sourceCost0)-payment-payment1 ≤ P(Tphysical≥z)`，

`P(Tphysical≥z) ≤ Psi*exp(C3*L0)*(1+C4*sourceCost0)+3*payment+payment1`。

用下损失界，第一式左边向下放宽到
`Psi*exp(-C1*L0)*(1-C2*sourceCost0)-R*Psi`；实数分配律将它改写成
`Psi*(exp(-C1*L0)*(1-C2*sourceCost0)-R)`。用上损失界，第二式右边向上放宽到
`Psi*exp(C3*L0)*(1+C4*sourceCost0)+2*(R*Psi)`；分配律将它改写成
`Psi*(exp(C3*L0)*(1+C4*sourceCost0)+2*R)`。这恰是冻结新分支的上下界。

边界和量词核对：z=1和paid右端等号都被非严格不等式覆盖；paid窗口最终含1；
共同 n 同时满足4≤n和原 guard。原模型的零分母分支仍是逐样本0，没有改成
零测约定；闭上尾事件与 standardNormalTail 的既有定义没有混同；外部 SZ
始终作为原明确输入；sourceCost0 未改变权重、删除索引或512/rho/1常数。无需
`1-C2*sourceCost0` 非负、无需成本小、无需 Psi 正性或除法。beta=0 的原备选
由旧 producer 负责且原样传递。本单元没有宣布其余原题依赖闭合。

形式源码中的长 `.2` 投影只解包既有合取：旧 current 整包40字段的最后一项，
其物理整包8字段的最后 guard，及 guard 后6字段的最后 SZ 费用尾界。相应
40/8/6结构由确定性文本分层核对登记，属于定位辅助，不是 Lean 通过证据。
