# Unit190 独立终审：源码阶段

STATUS: CORRECT — SOURCE SEMANTICS AND COMPLETE MATHEMATICAL ARGUMENT ONLY.

本阶段结论是：精确源码所表达的十五项声明忠实于冻结接口，完整数学论证没有发现关键缺口。源码尚未经过本单元的服务器 Lean 内核检查；本报告不声称其战术脚本已成功 elaboration，不声称已经发现全部实际所属常量，也不提供 unit190 公理认证。`qualified=false`，`actualOwned=UNKNOWN`。这三项状态只能由同一独立审查员在收到完整真实机器证据后继续完成。

审查员 `/root/oq56_scalar190_final_review` 是与作者 `/root/oq56_scalar190_stage1` 分离的新上下文。作者先前已经 DONE_RELEASE0。本审查没有改写任何源码或数学前提，没有重新审查或重跑已合格的185–189证明。请求的模型和推理强度为 gpt-6.1-sol/xhigh；实际运行模型、实际强度及各类 token 数未由运行接口公开，均记录 null。

精确审查对象为 `C:/game/shao lean/drafts/oq56/unit190/author-01/stage2/CanonicalDoubleGhostScalarMoments.lean`，SHA256 `29c30b00e12b543a13d47db111872fd9919cc09ea98a34d6adf89fefc3b1101a`，31675字节、578 LF、无BOM和CR。冻结文件为 `drafts/oq56/next-source/oq6-canonical-double-ghost-scalar-moments-190/parent-freeze-v1.json`，SHA256 `cc06105e7b843e5c04c3faf423e51a82544fd32c033506b6b36b1818576e2bbd`。冻结后同作者Stage2授权 SHA256 `2847945fd6ce11bb91ff535cf5ef790b2206ee679bfcf85e16fb9c9f38ec55fc`。作者release、manifest、完整proof-notes、Stage1 derivation、完整父级intake均仅作为可核对的输入和来源记录；本报告的数学裁决来自重新逐项阅读。

独立字节审计见 `source-byte-audit.json`：614项静态检查全部通过，63个不同本地引用的哈希与字节数一致。十五个完整声明头、四个全局原值、三十六个具名局部数据的完整类型与原值、三个局部实例和各声明内局部顺序全部与冻结吻合。此统计直接从本次源码和实际映射导出。另逐项核对了十七种匿名模板、左右绑定顺序、嵌套AE作用域及可捕获对象，见下文。字节检查不是内核通过证书。

## 原文到陈述

完整阅读了只读原文p44、p51、p54，哈希分别为 `3d6a674252a81b7ca051fd54aa0a621511ebce94af2f0bdf9b4eca8715bc5239`、`96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`、`e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`。本单元只支付p44第1节式(5)的真实原统计量矩界，取常数8。没有将有限符号界本身当作原随机统计量的结论。

令M为真实 `sampleLaw n ν=ν^(Fin n)`，P为真实 `pairedLaw n ν=(ν.prod ν)^(Fin n)`，J为实际逐坐标配对 `pairSamples`。原统计量是F(x)=Σ(i<j)r(x_i,x_j)。源码先处理一般不对称r的H(x)=½Σ(i≠j)r(x_i,x_j)，然后在明确的点态核对称前提下证明H=F。鬼标量G(z)=½Σ(i,j)D_ij(z)，其中D是四角差且按索引屏蔽对角的真实ghostMatrix；W_i=w(z_i.1)+w(z_i.2)，S(z)=ΣW_i²。最终结论确为

    F的绝对q次幂在M下可积，且
    (∫|F|^q dM)^(1/q) ≤ 8q (∫S^q dP)^(1/q)。

冻结的量词涵盖任意自然n、任意仅带可测结构的Ω、任意概率ν以及实q≥2。明确技术前提是r产品可测及产品L1、两个边缘AE典范条件、AE w≥0、真实ν×ν下的AE产品包络、真实P下S^q的L1。最终上三角F另有明确点态r对称性。没有拓扑Ω、Measurable w、点态典范性、r(a,a)=0或矩结论作为输入。这里只对这些明确前提下的结论裁决，不声称其前提已经最小化。

p51和p54的实际Studentizer、原子安全上尾极限和条件p矩修正不在本单元证明范围。尤其p54对旧p矩速率句的反例与修正仍有效。本报告不认证p51原单稿已自包含；Shao–Zhou Lemma6.1等已发表输入归属保留；不把DC范围扩展成任意原非线性核加2/5扰动。124机制不是前置。C2/C12/OQ56仍OPEN，OQ3仍由用户暂停。没有新颖性认证。

## 十五项声明及完整证明覆盖

| 精确源码行 | 声明 | 独立审查要点与裁决 |
|---|---|---|
| 21–24 | halfSumCLM | 原值为真实EuclideanSpace上的PiLp坐标投影连续线性映射的有限和，再乘½。有限维连续性来自真实CLM构造，未把函数空间的上确界范数误作Euclidean范数。CORRECT。 |
| 25–27 | originalHalf | 全部有序索引对的和，i=j屏蔽后除2；r的观察值对角保持任意。CORRECT。 |
| 28–30 | ghostHalf | 真实quadratic作用在真实ghostMatrix和常一path，除2。CORRECT。 |
| 31–33 | originalUpper | 真正严格上三角索引和Σ(i<j)r(x_i,x_j)。未替换样本或分母。CORRECT。 |
| 34–37 | halfSumCLM_apply | CLM加法、标量乘法和真实坐标投影求值得½Σv_i。CORRECT。 |
| 38–43 | originalHalf_eq_halfSumCLM | originalRows实际第i坐标是Σ(j≠i)r(x_i,x_j)，因此L(originalRows)=H。CORRECT。 |
| 44–49 | ghostHalf_eq_halfSumCLM | 实际rowAction_apply给Σ_j u_jD_ij，u=1；两层有限和与quadratic一致，无额外系数或对称性。CORRECT。 |
| 50–86 | canonical_scalar_ghost_mean | 用188实际向量L1和AE Bochner均值，真实CLM.integrable_comp依次支付原、鬼和AE截面标量L1，再以integral_comp_comm得到AE标量均值。无未导出的188 proof-local接口。CORRECT。 |
| 87–167 | ghost_scalar_sign_law | 四角映射支付D_ij可测；对角独立常零。逐项使用187实际ghostMatrix_swap保留左右两个符号，由交换样本的真实保测度与map_map得到绝对标量推前律。未错误消费行范数换号律。CORRECT。 |
| 168–214 | abs_integral_rpow_le_integral | q≥2给p=1/q∈(0,1]。t↦t^p在闭Ici0上凹且连续，powerF≥0且可积，rootPower∘powerF=|f|且可积，故实际凹Jensen的全部前提齐备。再用积分范数界和非负实幂复合，得到|∫f|^q≤∫|f|^q。CORRECT。 |
| 215–271 | half_quadratic_envelope | 项绝对值≤W_iW_j，Young平方不等式给W_iW_j≤(W_i²+W_j²)/2。双和恰为nΣW_i²；两层三角不等式后除固定2，得到(n/2)energy。无对角/对称要求、无除n或energy。CORRECT。 |
| 272–429 | ghost_scalar_qmoment_bound | 所有固定符号q次幂先以粗(n/2)^q S^q支配独立支付L1；有限立方平均与真实积分交换并由标量换号律识别其积分；189真实half8q界和186真实HS界给AE cubePower≤(8q)^qS^q，实际积分单调性得真实P下G矩界。CORRECT。 |
| 430–527 | canonical_half_qmoment_bound | 实际J保测度拉回G的q-L1；真实Fubini给AE q截面L1与innerQ可积。与标量AE均值满集相交，已证实数Jensen给|H|^q≤innerQ；L1支配、乘积Fubini和真实推前积分完成外层矩，再取合法非负1/q次幂。CORRECT。 |
| 528–559 | original_half_eq_upper | originalMatrix按索引零对角；r点态对称给矩阵对称，189 quadratic_eq_two_upper的两个前提均实际证明。严格上三角处i<j⇒i≠j，故上三角和还原F；除固定2得H=F。CORRECT。 |
| 560–575 | canonical_scalar_qmoment_bound | 将一般H矩定理逐点替换为原F；最终全部假设和8q常数与冻结一致。CORRECT。 |

1–20行的五项导入、autoImplicit=false、命名空间、noncomputable section及open作用域已完整读；576–578行关闭结构完整。上述分段覆盖完整578行，而非只读公共定理头。

## 承重步骤的独立推导

标量化：L(v)=½Σv_i是实连续线性泛函，H=L(originalRows)、G=L(ghostRows)。188既有合格证据给原行向量及鬼行向量可积，以及M-AE x的可积鬼截面和Bochner均值。实CLM作用保持这三类L1，并与可积向量积分交换，得到∫G(J(x,y))dM(y)=H(x)。没有把默认值0的不可积积分拿来充当均值。

换号：真实187恒等式D(swap_s z)_ij=ε_iD(z)_ijε_j在每个i,j成立。展开Q后，G(swap_s z)=½ΣD_ijε_iε_j。r产品可测与有限坐标投影保证G可测；该等式加交换保测度得到有符号Q_s的绝对值可测和精确推前律。左侧符号没有通过行范数消去；此处是标量二次混沌，使用q费用。

可积性：S是平方和，任意w下逐点非负。由实际hS的AE强可测性和连续R(t)=(max(t,0))^(1/q)，有R(S^q)=S，故S本身AE强可测；概率P下S≤1+S^q给S的L1。这一步没有恢复w的可测性。随后D的AE共同包络给每个固定符号|Q_s|≤(n/2)S；因为q>0、所有基数非负，实际可积函数(n/2)^qS^q支配各q次幂，独立支付有限符号平均前的L1。粗维数因子只用于可积性，最终界中消失。源码hSInt是已证明但后续不需要的事实，不是附加假设。

真正外层：A(z)=2^(-n)Σ_s|Q_s(z)|^q是有限个可积函数的线性组合。逐个换号律给∫A dP=∫|G|^q dP，归一使用card(Fin n→Bool)=2^n和2^n≠0。D_ii=0按定义成立，189给A^(1/q)≤8q sqrt(entryEnergy D)。实际entryEnergy与186 matrixEnergy值按相同j/i次序逐项相同；186 envelope给其平方根≤S。以非负q次幂和合法幂复合得到A≤(8q)^qS^q，再以实际L1积分单调性闭合。没有从有限A界直接跳至原F。

条件转移：J从M×M到P保测度，所以G∘J的q次幂在实际M×M下L1。Fubini给其AE可积截面及可积innerQ。与标量均值满集相交，对每个合格截面应用实数Jensen，得|H(x)|^q≤innerQ(x)。H的已知L1及实幂连续性给|H|^q的AE强可测性；支配给其L1。积分比较、已付款的Fubini和J的真实推前积分依次使用，没有交换未证明可积的积分。最后左右积分均非负，q>0且K=8q≥0，合法取1/q次幂得到K乘右侧q范数。

上三角桥：对每个x和索引i,j构造A_ij=0若i=j，否则r(x_i,x_j)。即便观测值x_i=x_j、法则有原子，i≠j处仍使用原核值；没有删除重复观测。点态r对称使A对称。零对角对称矩阵的实际quadratic_eq_two_upper把½ΣA_ij变成Σ(i<j)A_ij=F。核本身r(a,a)无需为0。

## 冻结、作用域与匿名边界

三十六项具名数据已逐项读完完整类型、原值及捕获计划，并与精确源码静态比对：canonical_scalar_ghost_mean有vectorSection一项；sign_law有四corner、ghostEntry、leftAbs、signedHalf、rightAbs八项；Jensen helper四项；envelope helper两项；ghost moment含instP及十项普通data共十一项；half moment含instM/instMM及七项普通data共九项；upper桥originalMatrix一项。总数1+8+4+2+11+9+1=36，实例数3。每项初始化只看完整头内较早绑定及较早数据；K等同名局部只在各自定理内，未跨兄弟范围。

vectorSection在源码69行AE x,hx引入后才于70行创建，捕获x合理；sectionGhost在472行AE x,hx,hxq引入后才于473行创建。二者的截面L1和均值/q-L1来自同一当前x的已绑定证据。各定理没有隐式ambient变量；header内Measure、measurable-space和probability实例的绑定均先于其使用。

十七类匿名模板均已核对：全局坐标类型族和投影族、常一路径、典范左右边缘、pairedEnergy-q、originalUpper-q、标量均值截面、原/鬼/截面的CLM复合、换号复合、Jensen复合、符号cube族、paired-q、sample常边缘及paired常边缘。模板中额外x或z仅在已绑定处使用，未增加可访问信息。

独立评估`anonymousExpressionBoundary`：247–259行中的两次`norm_sum_le`（254和259行）的匿名实值参数，是已消费quadratic原值的字面单项或部分和；没有引入独立新统计量、选择器或未冻结接口。536–554行的上三角有限求和是已冻结originalUpper/已消费quadratic_eq_two_upper的字面展开。`Finset.sum_le_sum`及`sum_congr`中的匿名参数返回普通Prop证明，branch/have/IH不隐藏非Prop数据。其余函数均属于上述已冻结模板或具名initializer。此边界可接受，不需要补冻结。

## 实际依赖与边界攻击

完整阅读Stage1绑定中的28个实际producer TYPE及全部19个非定理FULLVALUE；逐项与原producer actual-owned-metadata.json条目作完整对象相等检查，且五个qualified-evidence哈希和完整嵌入资格记录一致。分布为185:3 TYPE/3 VALUE，186:6/4，187:8/5，188:7/5，189:4/2。188消费严格绑定repair01 source `0b7f38c8840ffefb15fc9185c8f54c2c6907da96cc49bd5e7ee3c5ed512250fc`、object `039bdc5ca03a7505762d852b8e6464c7f88de90c5b68914e6aaf6e6cb3a50d85`、qualified `31b7d87357171a72ba7854bc32a0ad662ed8f0d2e39180e7c349ac195b25af02`。未使用旧失败source、猜测导出名或188 proof-local事实。旧合格producer证明本身按精确已有证据复用，没有重复全面审查。

完整阅读31个实际primary声明和11份原始ambient作用域记录，包括所有类型类、variables、namespace及section边界。逐项把完整声明和此前缀与原保留primary包中的存储字节匹配；28项来自完整文件并核对文件SHA，3项产品积分声明来自已有完整prefix包，未将prefix误记为完整文件。CLM.integrable_comp、integral_comp_comm、真实PiLp.proj、凹Jensen、Ici幂凹性、所有实幂条件、map/map_map、积分有限和、L1支配、产品Fubini和AE截面接口的条件均在本证明使用处有实际前提。静态byte审计记录具体文件、SHA和行号；没有新取回远程raw日志或对象。

已有producer资格的机器告警原样保留：185资格记录写明kernel30/audit1 warnings、nativeRC0/0errors、strict-wrapper=false/FIRSTEMPTY=false；187为source warnings/errors=0/0、两次真实LeanRC0而strict-wrapper均false/FIRSTEMPTY=false；188为13个native source warnings/0errors、strict-wrapper均false/FIRSTEMPTY=false，audit仅已有Lake134问题；189为11个source warnings/0errors、两次真实LeanRC0而strict-wrapper均false/FIRSTEMPTY=false。186继续复用其精确资格和机器证据，没有在本报告推测缺失的同名字段。这些是旧producer的已有实际记录，不能借来推定190任何机器结果；没有为告警清理重编译。

边界逐项检查结果：n=0时全部统计量空和为0，符号cube有唯一空函数，概率积有实际空乘积定义；n=1时索引对角屏蔽使H、G、F均0。所有n只除固定2、2^n及严格正q，不除n、S或任何能量。S=0和矩阵能量0处幂复合使用非负底数与q>0，未偷偷取严格正能量。原子和重复样本保留；AE包络只通过已合格187对应独立异索引结构，未把ν×ν的AE性质拉回同一坐标对角。一般H证明无需r对称；F桥显式需要点态对称；真正Ω上没有拓扑要求。完整源码搜索未见sorry、admit、axiom、unsafe、native_decide。

## 待付机器阶段与交接

本阶段没有unit190实际服务器证据，机器状态为NOT_EXECUTED/UNKNOWN，实际所属常量、TYPE/VALUE行数和递归公理数全部未知，不用15个源码声明推猜。必须由同一审查员在后续收到真实机器工件后完成：

1. 绑定精确本源码、实际服务器source/O、原始成功kernel receipt、pinned Lean/mathlib及真实审计指纹；任何源变动仅使受影响证据失效。
2. 从真实unit190模块取得module index，遍历ALL env.constants而无namespace过滤，独立核对全部actual-owned映射；包含private/generated及foreign命名空间所属项。
3. 完整阅读每个实际owner的TYPE及每个非定理def/opaque/private/generated/foreign项FULLVALUE；核对每项真实body存在，匹配本源码语义和对应来源，无elision。
4. 从仅规范化JSON在内存重建精确raw stdout，独立验证byte数、SHA、全部FULLFP/source/O/receipt绑定；不写本地raw日志、cache、O或二进制。
5. 检查全部actual owner的递归AX仅含propext、Classical.choice、Quot.sound；保留实际warning、strict-wrapper=false或FIRSTEMPTY=false等原状，不为清warning重编译。
6. 全部覆盖且真实内核/AX证据充分后，才可写最终qualified。当前源码阶段既不替代该门，也不要求重审已合格旧producer证明。

本审查只在final-review-01目录写报告，Lean/server/network/Git/API/upload/cache/children调用均0；所有源码和冻结字节保持原样。最后SOURCE-RELEASE0后本上下文普通回合结束，等待父级以相同reviewer明确继续机器阶段；该等待不是持续运行的证明机制。
