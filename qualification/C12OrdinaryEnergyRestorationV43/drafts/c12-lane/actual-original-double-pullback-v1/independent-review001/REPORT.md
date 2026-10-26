STATUS: CRITICAL_GAPS
MATHEMATICAL_CHAIN: CORRECT_FOR_EXPLICIT_HELPER_SCOPE
FORMAL_QUALIFIED: false
SOURCE_ONLY: true

本报告独立完整审查 unit224 source001 的全部114LF，目标公开名为 Shao.C2.ActualOriginalDoublePullback.source_truncation_original_double_pullback。唯一源码证明阻点在第76行的自邻域侧条件 `(by simp)`。没有发现定理数学内容为假的反例，也没有发现同阈值条件混合与付款链的数学缺口。这里的 CRITICAL_GAPS 针对当前静态证明文本不能完整交付该符号侧条件；本次未运行 Lean，不能把它叙述为已观察的编译失败。

授权与独立性

审查角色为 /root/original_double_pullback_formal_review001；父作者/owner 为01a174b9-5b2e-7611-ba13-02580d678eb3。本角色未参与 source001、冻结前导、冻结公开头或数学推导的写作，只写 independent-review001。激活文件3756B/SHA30770f352ab5c61e69e6d489811fb513dc64c4fb826e26c5abb860488bfa2cca及全部10输入在 ACTUAL-ACK 之前逐项按实际字节、SHA256核对通过。源5710B、114LF、0CR、SHA ddb38a2b493bd00ee3623d259a7c060246bf7802ff9573e8d708e9c9ab2f90cf 未变。预先冻结前导和公开头与源第1–39行精确一致（公开头文件的结尾LF仅作文件终止，源接 ` := by`）。冻结记录时间01:29:05.911174Z，完成源码检查点时间01:29:58.199394Z，记录支持先冻结后实现；未根据文件时间虚构额外写作历史。

配置要求为 gpt-6.1-sol/xhigh、新鲜上下文。本工具界面没有实际运行model/effort或input、cached input、output、reasoning subset计数，均记录null。按父授权，本审查零Lean、零AX、零server/network/upload/Git API、零派生代理、C12heavy0。只读取本地固定版本标识 leanprover/lean4:v4.36.0-rc1；未探测或调用本地工具链。旧Rootproducer完整证明和既有成功检查按精确公开接口复用，本报告没有重审其整体证明或重跑它们。

源文与命题忠实性（源1–39，原稿1529–1550）

直接只读核验 C:/game/shao/current/c12/main.tex 的76636B/SHA beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06，与授权摘录所标原稿一致。完整阅读1529–1550，并核对1151–1176的D_n定义和1178–1190的g:main范围。原稿D_n(x)是上下两个闭命中事件的交；本定理同样使用 doubleCrossing hn x，未改为并、严格命中、单时同命中或独立概率事件。原稿1536–1543的同一x坏事件与精确混合恒等式是本单元对应的数学内容；1545的基准范围在本单元显式由d的两个前提供应。

所有对象保持原始x：h=epsilon/(1+x)、N为每个原始坐标满足|v_j|≤h、P0=nu的有限iid乘积、rho=cond nu {|z|≤h}、P=rho的有限iid乘积、p=P0.real N、R=truncationBudget nu n x。P是真实条件坐标law的乘积，并有cond P0 N=P这个实质输出。没有用邻近原始阈值、改变原始law、把rho另行中心化、把原始Q换成方差，或把中心化Brownian比较作为已知事实。

C在全部law/n/x/epsilon/d之前存在。公开前提完整列明：nu为概率测度；n>0；二阶矩可积；原始均值为0；n乘二阶矩为1；x>0；epsilon>0且≤1/800；额外小预算R≤epsilon^3/8。最后d在0≤d≤2Psi(x)范围任意。本单元不证明该小预算由原始最终参数自动满足，也不证明Brownian d的这一范围；调用方必须另行供应。原稿g:main只在固定I_n与x≥1的交上声称完整比较，本单元并未编码或关闭I_n、保留样本比较、g:double/g:absolute或C2/C12根结论。它在较一般的x>0下证明一个显式受条件约束的外层辅助式；不能据此声称原始全部定理完成。原稿1529–1531对Q_A/Q_C及E的处理属于先前保留比较，本单元没有把那段分析冒作自身已证明的输入。

事件和零能量

只读核对 Basic/FinitePath 的Path=Fin n→Real、真实最终energy=sum v_j^2、upperMax在1..n取最大值、lowerMax=upperMax(-v)，以及 Basic/Events 的非严格≤能量壁。TwoSided第13–14行以交定义doubleCrossing；upperMax_ge_iff的存在量词说明两个方向允许不同时间的见证，不要求同一个k，更不引入概率独立性。TwoSided第39–42行明确Q=0时仍属于doubleCrossing；新证明从未以Q>0限制D或除以sqrt(Q)。MeasurablePath第145–147行提供D的可测性；本单元的条件乘积/分割步骤只显式需要N可测。无密度、无原始law对称性、无非原子假设、无零能量排除。n=1和有零能量原子的情形仍在表达域内；x=0由冻结前提明确排除。

旧公开接口与调用顺序（源41–57、73–77）

OriginalCDFPullback第253–290行的 sourceTruncation_original_max_cdf_pullback 的完整公开头已核对。第48行按nu,n,hn,h2,hmean,hnorm,x,epsilon,hx.le,he,he800,hR顺序调用；其lets与本定理所有N/P0/rho/P/p/R定义逐项相同。第49行正确提取六个基础输出p≥7/8、p≤1、1-p≤R/epsilon^3、rho与P为概率测度、cond P0 N=P，并只丢弃本单元不用的两个CDF输出。第50–55行只作定义相等的change，未增加假设。

OriginalCDFPullback第49–72行的 sourceTruncation_original_two_signs_bad_crossing 完整公开头已核对。其参数先是原始x/epsilon，随后是观察阈值u及u>0、自邻域，最后第一分量中是符号s及s=1或-1。第75–76行保留原始x，取u=x、正号s=1，利用第一分量而非错误地把端点事件当最大事件。one_smul去掉正号作用后，目标就是原始upperCrossing hn x在N补集上的概率。唯一问题是自邻域侧条件的现有证明文本，详见下项。没有为得到预算调用邻近原始law或重新选择预算点。

具体源码阻点 G1（源76）

hBad的第三个u后参数需要 |x-x|≤1/(1+x)。源码给出 `(by simp)`。消去sub_self和abs_zero后，需要0≤1/(1+x)，这依赖冻结前提hx:0<x以建立1+x>0；普通simp不包含从hx推导1+x正性的线性算术或positivity步骤。当前文本没有显式支付这个侧条件，因此不能把source001完整证明文本标为CORRECT或形式合格。此处数学命题成立，所需信息已在原冻结前提内；不要求也不允许改前提。本审查未修改输入，也未运行Lean，故不宣称具体编译器诊断、退出码或对象效果。父应在新的源码版本中显式证明该倒数非负，保持source001冻结；受影响覆盖是第73–77行的marked调用及其后继对hDoubleBad/hSum的引用。其余已经完整审查的数学内容可按相同源接口保留。

有限实测度乘积与分割（源59–72）

N等于有限坐标可测闭带的交；坐标投影可测、绝对值连续、与常数的≤集可测，iInter给出hNm。P0是有限个概率测度的乘积，故是有限概率测度；hRho/hP又为rho/P建立局部概率实例。cond_mul_eq_inter hNm D P0给出条件测度乘P0(N)等于P0(N∩D)，再取ENNReal.toReal；hcond、p定义和toReal_mul得到hProduct：P.real D * p=P0.real(N∩D)。乘数p没有丢失，也没有错误倒置为除以p。随后measureReal_inter_add_sdiff以s=D、可测分割集N使用，D\N定义等于D∩N补；交换D∩N并代入hProduct，得到P.real D*p+B=P0.real D。其有限性由P0概率性供应，不需要额外零质量或D独立性假设。公开参考中相同cond/split调用形状已存在；本次只核对适用接口和新调用的数学关系。

真实坏事件和预算（源78–101）

D∩N补包含的每个v已经属于upperCrossing，因此第78–80行取hv.1.1是正确的双交投影。measureReal_mono在有限P0上给B≤原始upper坏事件预算；hBadNonneg由有限实测度非负性给出。R非负由已存在truncationBudget_nonneg nu n h2 x供应，epsilon^3>0由he供应，故R/epsilon^3非负。没有把一个抽象未付B假设写入结论：实际B的Gaussian加权界是通过真实marked接口和事件包含取得。

对任意显式d范围，第90行用p≤1、d≥0证明bias=(1-p)d≥0。第93行mul_le_mul的四个参数分别是hcomp、hdTail、hd、hBudgetNonneg：上界乘数R/epsilon^3非负和被乘原d非负都正确，完全覆盖乘法方向。由此bias≤(R/epsilon^3)2Psi(x)。将B的Cb倍预算相加并ring整理，得到B+bias≤(Cb+2)/epsilon^3 *R*Psi(x)。C=Cb+2由hCb>0推出正，且不依赖任何数据；源中无遗漏的倍数或括号差异。

混合恒等式和绝对误差（源102–112）

从m=pq+B减d，得到m-d=p(q-d)+B-(1-p)d。新源码hMix严格是B减bias，与原稿1541–1543一致；它没有把CDF接口的bias-bad符号机械搬到闭双命中事件。nlinarith only [hSplit]只需展开并消去相同乘积，等式在实数环上成立。最后差值是B-bias，B与bias均非负，且和≤T，所以-T≤B-bias≤T，abs_le两分量成立。第110–111行只引用这三个已付事实，未偷用保留law比较、Gaussian独立性或d的特定Brownian构造。d=0及d=2Psi端点都保留。除G1的源码侧条件外，这一完整数学论证没有缺失步骤。

证据边界与最终状态

单一公开完整proof静态完整阅读；新private、def、instance均为0，禁止词sorry/admit/axiom/unsafe/native_decide扫描为0。SOURCE-SEAL以完整源SHA为首要绑定，另按清晰约定封印第40–112行含末LF的证明文本3590B/SHA3d0bdb2c27e4ed7df25366aab7a5abed43bb42d75dc1035fb8b4ab553be27bfc。父源码CHECKPOINT的completeProofBodySHA256未说明抽取约定，本报告不依赖或冒认该不透明子串hash；完整源与公开头/前导的准确性已直接确认。

实际编译所得owner/TYPE/VALUE/O/AX及新定理的传递公理集均未知。静态无禁用标记不替代内核或传递AX证据。标准公理白名单保留propext、Classical.choice、Quot.sound；未新增公理。本源尚不可作为formalQualified的验收版本；下一步是新版本显式支付G1，再作受影响独立补充和将来授权的精确源码内核/全部所属实际常量传递AX检查。C2/C12/fullRootOD仍OPEN；原始C1完成状态不受本报告扩大；OQ3仍PAUSED_BY_USER。
