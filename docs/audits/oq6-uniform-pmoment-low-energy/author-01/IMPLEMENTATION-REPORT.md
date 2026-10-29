# Unit265 U0：统一p矩到显式低能量生产者实现

状态：`IMPLEMENTED_SOURCE_REVIEW_PENDING; NOT_KERNEL_CHECKED; NOT_QUALIFIED`。

本轮严格实现lead冻结的U0唯一声明`Shao.OQ6.UniformPMomentLowEnergy.actual_uniform_pmoment_low_energy`。原候选通用物理引擎与U1/U2/U3均未实施。没有改动数学前提、冻结声明、proposal/ACK/READY、library或共享实现；没有运行Lean/AX、工具链探测、服务器、网络、Git/API、发布或子代理。完整SOURCE独立接收之前不得开始机器检查。

## 一、授权、阅读与精确字节

完整读取并核验实施激活`implementation-ACTIVATION.json`，SHA256 `aea38711bbecb529ec72b517c07b3f977f4f5db88e7e2513e5bd63d1727b4f54`／4350B；冻结元数据`freeze-01/frozen-declaration.json`，SHA256 `b2b3f954c79eb1515318c5ddae8e881016ac889825544cbb571474f3a42b6b48`／2283B。其10个输入均完成哈希/字节核验。实际READ_ACK先写并封存，再完整读入精确HEAD/PREAMBLE/CLOSING和两份承重源。

本轮已完整读取`ConditionalStandardizedLowEnergy.lean`的447行与`OriginalLowEnergyTail.lean`的320行。前者分1–225、226–447两段，后者分1–160、161–320两段；没有将早前提案阶段的片段阅读当成全文。两份完整源仍为激活绑定的`6158a684…`／20659B及`77b67bfe…`／14282B。使用既有证明中可核验的标量/积分/有限乘积/Markov推导结构；没有重新审判旧源的TYPE、AX或kernel证据，也没有试图将有额外条件化假设的旧定理直接冒充本泛型声明。

新源为`author-01/UniformPMomentLowEnergy.lean`，SHA256 `8d6897dc939cd5e5e07e3d29f8a262b7942536bc41042a47052f1d8a5d7b6d32`／14730B／308LF。`PROOF.txt`为12423B／261LF，从`:= by`开始。源严格等于以下四个原始字节段顺序拼接：

| 区段 | 源行 | 字节数 | 字节区间，零起点左闭右开 |
| --- | --- | --- | --- |
| 原冻结PREAMBLE | 1–11 | 340 | [0,340) |
| 原冻结HEAD | 12–45 | 1926 | [340,2266) |
| 本轮完整PROOF | 46–306 | 12423 | [2266,14689) |
| 原冻结CLOSING | 307–308 | 41 | [14689,14730) |

`SPLICE-STATIC-CHECK.json`记录完整四段SHA256、字节区间、精确原始组装和静态格式检查。新源及PROOF均严格UTF-8无BOM、CR0/LF、单终LF。没有在冻结片段间增加空白或改动选项。

## 二、共同数值见证与完整证明路线

冻结量词先固定`p,B`，其中`2<p≤3,B≥1`，并在全部模型量词之前定义

\[
q=p/2,\qquad t_B=(1/(4B))^{2/(p-2)},\qquad c_g=t_B/4.
\]

源49–88行先证明全部数值结论，包括`1<q≤3/2`、`0<tB≤1`、`0<cg`，以及

\[
B t_B^{q-1}=1/4,\qquad B t_B^q=t_B/4.
\]

前一个身份用`(2/(p−2))(q−1)=1`与正底数实幂规则得到；后一个用`tB^q=tB^(q−1)*tB`得到。所有这些证明均在源157行引入`Ω,μ,g`之前完成。没有选取依赖当前分布的截断见证，也没有依赖单模型的最终阈值。

源100–147行建立纯标量不等式

\[
e^{-z}\le1-z+z^{q'}\qquad(z\ge0,\ 1\le q'\le2).
\]

`z=0`直接按正指数实幂化简。`z>0`先由`1+z≤exp(z)`及正数相乘得到`exp(−z)≤1/(1+z)`。若`z≤1`，使用

\[
(1+z)^{-1}=1-z+z^2/(1+z)\le1-z+z^2\le1-z+z^{q'};
\]

若`z>1`，使用`z≤z^(q')`和`exp(−z)≤1`。这一推导只使用实数指数的单调性，不调用高阶矩假设。

随后源157行才引入任意可测空间、原概率法则μ和g。全部模型前提逐字来自冻结HEAD：g可测、`MemLp g 2 μ`、`Eg²=1`、`|g|^p`可积以及`E|g|^p≤B`。没有新增均值零、条件化、指数矩、四阶矩或结论性概率前提。

定义`f=exp(−tB*g²)`及其真实原法则积分L。源158–171行用`0≤f≤1`与概率测度得到f可测、可积及L非负。源172–199行将上述标量不等式应用于`z=tB*g²`，并用

\[
(t_Bg^2)^q=t_B^q|g|^p
\]

得到点态上界`f≤1−tB*g²+tB^q*|g|^p`。其右端可积，仅需g²和`|g|^p`可积。源200–231行逐项积分，以`Eg²=1`、`E|g|^p≤B`及`B*tB^q=tB/4`得到

\[
L\le1-t_B+t_B^qE|g|^p\le1-3t_B/4.
\]

源232–234行再用`1+x≤exp(x)`推出`L≤exp(−3tB/4)`。所有积分都在当前实际μ上，没有改成编码/辅助law。

## 三、全部有限样本量，包括零样本

源236行引入任意自然数n及冻结定义的实际乘积测度`P=μ^n`、能量`S=Σg_i²`和`F=exp(−tB*S)`。源239–246行建立P为概率测度、S/F可测和闭低能量事件`E={S≤n/2}`可测。

源247–269行使用有限和的指数乘法身份和Bochner有限乘积积分定理，得到F可积及

\[
F(\zeta)=\prod_{i\in\mathrm{Fin}(n)}f(\zeta_i),\qquad
\int F\,dP=L^n.
\]

源270–279行对非负L使用自然数幂单调性，再由指数幂身份得到

\[
\int F\,dP\le e^{-3t_Bn/4}.
\]

令正数`ε=exp(−tB*n/2)`。在闭事件`S≤n/2`上，由`tB>0`得到`ε≤F`，所以源281–294行以非负F的Markov积分界支付

\[
\varepsilon\,P(E)\le\int F\,dP\le e^{-3t_Bn/4}.
\]

源295–304行只除以严格正的ε，得到

\[
P\{S\le n/2\}\le e^{-t_Bn/4}=e^{-c_gn}.
\]

该推导从未除以n，也没有假设`n>0`。n=0时有限和为0、有限积为1，闭事件是整个空坐标样本空间，最终界为`1≤1`；同一有限乘积/Markov推导覆盖它。冻结HEAD没有输出额外ε字段，因此最终tuple只返回原声明要求的八项乘积/概率结论。

`p=3`保留在闭端点，q=3/2仍落在标量引理范围内；B=1时所有正性/实幂身份同样成立。g不需要均值零；这是冻结的能量生产者，不是未授权的物理相对尾消费者。

## 四、实现范围、静态证据与未完成认证

新源码只有冻结的一个public theorem，没有新增public helper、definition或额外假设。所有辅助推导是主证明内的局部have。仅在主PROOF内使用一次`set_option maxHeartbeats 800000 in`；没有修改冻结PREAMBLE中的全局选项。静态禁用词匹配为0，未使用sorry/admit、新axiom、unsafe或native_decide。

目前只能从源文本派生public声明数1，**不能**据此预报全部actual owner数量。后续必须由指定服务器绑定本精确SOURCE的首个成功原对象，枚举所有私有/生成实际owner，审完整TYPE、非定理VALUE及逐owner递归AX，并由独立审阅员完成精确source-to-statement/proof与机器语义接受。本轮没有调用任何这类工具，也没有本地替代检查或隐含kernel通过声明。

本地有一次原始字节组装失败，记录在`FAILED-LOCAL-ASSEMBLY-01.json`：PowerShell路径数组的字符串拼接优先级把四条路径合成一条，读取失败后非终止错误使预览源写成0B，最终静态门报错。该0B预览的SHA256为标准空文件指纹，记录保留。冻结输入和PROOF无变化；修正为逐项路径数组并使本地错误终止后，只替换自己未合格的空预览。当前14730B源是首次完整组装，没有数学源版本回退或被覆盖的成功检查，未触发服务器/数学执行。

原proposal、封存ACK/READY、263补充合格证据和全部接受旧源保持原字节。U1统一物理有限费用桥、U2共同起点相对尾、p54真实条件/三角模型与均值/方差平移、外部SZ、DC、fullOQ56和root均未因此闭合。

请求模型/力度仍为`gpt-6.1-sol/xhigh`；实际model/backend/effort未暴露，保持null。input、cachedInput、output、reasoningSubset分别为null，不推算订阅比例。

完成本报告和manifest后，唯一`LASTFINALWRITE.json`最后写出，释放全部作者写入、执行、发布和child权限，`authorRoleRetained=false`，writers/heavy/inflight/uncertain/pendingExternal/children均0。后续若需修订，必须由lead重新明确激活；本作者不自行启动检查或改动已交付源。
