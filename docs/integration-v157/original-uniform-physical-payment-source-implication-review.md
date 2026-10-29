# P180 / PR551：共同矩预算的原物理付款与真实 rho 预算

**裁决：267、269 可按其精确范围接受。267 以共同 p/B 的显式低能量常数和模型前共同 N，支付同一原 P 下当前 z 的 H 补集、安全集补集，以及大二阶误差、投影零、clip/physical 不一致和物理零分母的整个联合事件。e1 的参数1没有被偷换为当前 z；当前裁剪与真实 centeredDelta、真实物理 T 的等同已在 H 内实际闭合。269 在同一原残差/原包络上证明真实 rho≤M，使几何约束有合法的模型前数值充分条件。**

267 本身不选编码见证，也没有顶层声明最终下界−2payment、上界+4payment。它供应这些费用所需的原模型生产者；复用已接受的同一 m0/eta 族、Ssafe 运输及通用闭尾消费者，可得下文第5节的普通数学组合。P180 没有发表这一模型前共同 N 的完整 finite-cost/relative-tail 消费者，不能把新付款生产者或 rho 比较命名为完整统一尾界。已接受263固定模型相对尾与264原物理紧区间 CDF 范围保持。

## 1. 精确权威、输入和复用证据

开工时选读 REGISTRY.currentAuthoritativeState 与 library/SNAPSHOT.json 的相关字段，两者为 v156：main a0520a96fe0ba932c7ea4a8466da5d5aa2577a9a，acceptedHead 8ea3f20e366ab7ca375567b84f5e0d9b0aaf7bf0，tree 468f02dfea2a46cb6ca7e66991f19e54a6a12dab。SNAPSHOT SHA256=4ae7007670b88739a9c319f8fceb796b744ada2c1ef410bcb48a570ce349e642，1893B。已接受原题范围文件 integration-v156/root-source-scope-acceptance.json SHA256=23f874461dafef419cafd34c03b887e4a1ea4bb59c9f3b3a4a0480300f72e3c6，7142B。

P180 的 PUBLICATION-COMPLETE.json 为11186B，SHA256=777e7f548990a0c302eb70d24520ab5dee8840f437629539cde7b1c9fcc5d28b；PR551 head 29e7d724cb203111a1e4034e743502d762650c5e，tree ec4fb04a4d4aeae1dd821ce15b2c51445d26d14e，parent abc5b2bf12577e40f2f7060a906fec8bf86e4630。发布仅265/266/267/269；未读取268/270源码、证明或类型，未用其结果。

下表路径相对 C:/game/shao lean/drafts/oq56/：

| 工件 | SHA256 | 字节 / LF |
| --- | --- | --- |
| unit267/author-01/UniformPMomentGoodsetPhysicalPayment.lean | 6ed38ca7c071e20ea6555a8ac47c34e85d9b2afe67e116c942e9bde9c0cf9dc8 | 9790 / 196 |
| unit267/qualified-evidence.json | 79f19d13775deef891e8897bcc46548b21423f5f12dd96eb3777f816c71162c9 | 11158 |
| unit267/source-review-01/FINAL-REPORT.md | 9c1c3261546d7f8ddeb835339d9e4c9fb36cb0cd916916ee027cbf9e32179d20 | 13724 |
| unit267/source-review-01/FINAL-VERDICT.json | f380bc7ad9965774ff05011a83be968761a41414ef9d31cb0c0f523f76c45933 | 13287 |
| unit267/owner-evidence-01/actual-owned-types.txt | a7aee27838565139f2469a8060c7a5dbcd670332005c30adba58f69062806449 | 41066 / 538 |
| unit269/author-01/OriginalEnvelopeRhoBound.lean | 5fc29e9c832de61f4cb1d7e85a54b0499fe4cf263ae1190922f4196474840fc8 | 2735 / 64 |
| unit269/qualified-evidence.json | e9e44739fb2b93d2017200794490543569acc03cd87ba3e21218f7068ebad610 | 12576 |
| unit269/source-review-01/FINAL-REPORT.md | 9c3ab0a4997a7a092061dd4653136a7505494907c19e9d0498ecc7cae0e275b3 | 14043 |
| unit269/source-review-01/FINAL-VERDICT.json | e9ae7bb9868f3fde7c326e8def2ba15ea848eb913bcee1b94b22a50a13072f0a | 4231 |
| unit269/owner-evidence-01/actual-owned-types.txt | 3bb88dea19f162ac7757c6d197e93a1755f79085132b2599293f2541a92c0509 | 7199 / 108 |

完整读两件新公开声明/普通 let、两份完整实际 TYPE 和两份最终独审；原完整局部 SOURCE/proof/全部实际 TYPE/必要 VALUE/递归 AX 审查及首次对象按资格复用。267 的538 LF 含主定理532 LF和生成的有限乘积概率实例6 LF；269恰一个108 LF定理。两者必要非定理 VALUE 均为空，标准空文件 SHA256=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855。267/269 qualification 的18/23个去重本地引用，大小和SHA均核对相合；269采用其已修正的 final-metadata-repair-01 覆盖记录，数学字节未变。

两件首次对象分别为 e0c5a8cf3cf0d74950990099af5611cd29c980e7c19fd823c62e38bc91e9cf11 /475856B，599aae30ad77c166b0e973eb35dae00192e959e76885e3f29ed1b8a438602a80 /72624B；既有 native 与同首对象 audit 均实际 RC0/0，递归 AX 均仅 propext、Classical.choice、Quot.sound。原 strict-wrapper false、警告和269编译前零Lean配置失败按资格原状保留。本次没有机器重检。

265/266仅为接口承重，复用其合格局部审查，不重复全部证明。精确源分别 d0b4bfe9eb107253da068f10bd6ce5450cf2c2b785acaab9a55aef91f3ea05a3 /14912B，f40b9fc01f7c58e94200bdece91e00457f621cc7b1f3afea14696b8989116cd8 /18533B；资格分别43b9316fad646906cf45f06d7b3bce13b5a0f249eb6ac561a75c0b519c1bcfb5、c64e9bad0042ea1e5a9cfeef1ca17966b96e19dd7c2a6f835aef190431941f33。本次读其完整公开接口，并定向看266输出真实 delta/因式分解及付款的消费连接，不另认证其全部局部证明。

## 2. 267 的完整量词、模型条件和窗口

固定实数 2<p≤3、B≥1，定义

\[
t_B=(1/(4B))^{2/(p-2)},\qquad c_g=t_B/4>0.
\]

然后对每组 C,a,M≥0、t0>0，**存在一个 N≥4，先于全部 n≥N、Ω/mΩ/μ、g/r/w、rho/z**。对每个 n 可换模型；N仍相同。它可依赖 p/B/C/a/t0/M与固定宇宙，不能写成跨全部 p/B 的共同 N或共同正 c_g。267直接复用266选出的同一 N；c_g由265共同矩预算给出，不是旧逐模型选择的低能量常数。

后置模型必须真实满足：μ为原可测空间上的概率；g可测、L²、Eg=0、Eg²=1；|g|^p真实可积且 β=E|g|^p≤B。r在原 μ×μ 上联合可测、L¹，左右积分几乎处处均为0，且逐点对称。w在原 μ 下几乎处处非负，w²真实可积且 Ew²≤M，并满足

\[
w\le C(\log n)^a\quad\mu\text{-a.e.},\qquad
|r(o,y)|\le w(o)w(y)\quad(\mu\times\mu)\text{-a.e.}
\]

这里没有假设w逐点有界、额外w可测或r高阶矩；所用条件按实际TYPE保留。包络条件是真实门槛，267没有为任意L²原核构造这种w。每个n可以使用不同合法w，但C/a/M须已固定，不能把模型后变化的预算伪装成同一共同N。B=1、M=0、C=0、a=0均允许，空的模型/窗口并不由定理保证非空。

令 q_n=t0 n^(1/3)、K=tailScale(M)。精确K为

\[
K=\max\{e(M+1),\ 8e(4M+8),\ 8e^2(4M+8)^2\}.
\]

rho是267的自由非负参数，**其TYPE尚未定义为残差标准差**。当前阈值另需同时满足

\[
1\le z\le c_{\rm env}n^{1/6},\qquad (1+\mathrm{rho})z\le\sqrt n,
\]
\[
c_{\rm env}=\min\!\left(1,\frac1{32(K+1)(t0+1)},
\frac1{\sqrt{32(200(1+K+\sqrt K)+1)(1+\sqrt{t0}+t0)}}\right)>0.
\]

后一几何条件不是前一窗口在每个允许n下的无条件推论。267不要求tilt窗口或scalar source的严格矩预算，因为它还没有调用外部概率引擎；这些条件在第5节的组合处才需补齐。

## 3. 实际 H、当前 z、物理零分支和一次联合付款

所有量在同一原 P=μ^(⊗n) 上。记 W=projectionW、V=projectionV、D=residualStatisticD、d=centeredDelta、s_phys=√centeredSq；其字面定义为 W=Σg_i/√n、V²=Σg_i²/n、D=F/[√n(n−1)]、F=Σ_{i<j}r_ij、centeredSq=jackknifeSq(g_i+g_j+r_ij)/4、d=0在V=0，否则centeredSq/V²−1。物理统计量恰为

\[
T=\begin{cases}(W+D)/s_{\rm phys},&s_{\rm phys}\ne0,\\0,&s_{\rm phys}=0.\end{cases}
\]

真实原核h代入时g(o)=∫h(o,y)dμ、r=h−g−g，样本核逐点等于h。v156已接受的n≥3有限行分子恒等式 W+D=√n U/2，及centeredSq=jackknifeSq/4、非负性和同一零分支，识别此T为264的√n U/√jackknifeSq。267仅在n≥4调用，未扩展旧尾几何的样本范围。这是已接受定义/恒等式的普通代数蕴含，不是另一个coded/clip法则替代原T。

G_z的两个测试是 V²≥1/2 与 |W|≤√z n^(1/4)(4+V)。C2恰含 |F|≤K n q_n、‖originalRows‖²≤K n²q_n，H=G_z∩C2；squareSum(w)只在实际残差集中失败payer中，未加入H的新测试。当前修正 e_z=clippedCenteredDelta(n,g,r,512,rho,z)，当前裁剪统计量为Tclip,z。定义

\[
S=\{V>0,\ z|D|\le V/8,\ z^2|e_z|\le1/8\},
\quad E_2=\{z^2|e_z|>1/4\},\quad Z_0=\{V=0\},
\]
\[
E_{\rm clip}=\{T_{\rm clip,z}\ne T\},\quad Z_{\rm phys}=\{s_{\rm phys}=0\},\quad
\Pi_{n,z}=3e^{-q_n}+e^{-c_g n}+4e^{-z\sqrt n/2}.
\]

267实际输出：H、T、Tclip,z、Eclip可测；H⊆S；每个H样本上有V>0、z|D|≤V/8、z²|e_z|≤1/32、s_phys>0、s_phys=V√(1+d)、e_z=d、Tclip,z=T。并有准确包含

\[
(S^c\cup E_{\rm clip}\cup Z_{\rm phys})\subseteq H^c,
\qquad (E_2\cup Z_0)\subseteq S^c,
\]

以及四个各用同一费用的界

\[
P(H^c),\quad P(S^c),\quad
P(E_2\cup Z_0\cup E_{\rm clip}\cup Z_{\rm phys}),\quad P(E_{\rm clip})
\ \le\Pi_{n,z}.
\]

其中真实联合事件直接包含于H补集，不需把四项各≤Π再相加。由同样包含，{z|D|>V/8}也包含于S补集，和上述四事件合并仍只需一份Π；这是普通集合推论，非另发表顶层声明。E2的严格>1/4、S的≤1/8、H内的≤1/32没有混同。投影零和物理零均付费，没有被断言概率为0；s_phys=0时T=0也不把未除法闭越界事件直接变成同一事件。

三项费用分别来自实际残差product-envelope联合失败、265共同p矩的闭低能量界、以及当前z的投影好集失败。265保证 P(Σg_i²≤n/2)≤e^(−c_g n)，包含低能量等号，且无需Eg=0；266的投影和集中组合另使用Eg=0及其余条件。这里没有从一般L²残差单独推出指数付款。

e1桥没有剩余未付假设。266中的e1=clip(C0,rho,1)仅给|e1|≤|d|等收缩与正性，未声称e1=d。267实际消费266的raw界 z²|d|≤1/32、d>−1/8与真实因式分解；先以当前clip收缩得z²|e_z|≤1/32，再用LiteralClippedComparison的当前z、固定512、r对称、n≥4、G_z、rho≥0及独立几何条件，得e_z=d和Tclip,z=T。无需e1=d、e1=e_z或用户另交预算支配证明；去掉几何条件则不能保留这项字面比较。

## 4. 269 的真实 rho 与模型前预算

唯一声明 original_residual_rho_le_envelope_second_moment 在任意原 μ/Ω 上要求r∈L²(μ×μ)、w≥0 a.e.、w²可积、M≥0、Ew²≤M及同一|r|≤ww产品包络。它**不要求对称、退化、g、p矩、bounded-polylog高度或tilt**。hW虽对该局部证明冗余，仍保留在实际TYPE，未因警告删除。

令 v=∫r²d(μ×μ)、rho=√v，其实际输出0≤v≤M²、0≤rho≤M。完整数学含义为

\[
0\le v\le\int w(o)^2w(y)^2\,d(\mu\times\mu)
=(Ew^2)^2\le M^2,\qquad \sqrt v\le M.
\]

r²与产品上界先有真实可积性，随后才作积分单调性和乘积积分分解；不是将不可积积分的总化值当真矩。M是Ew²的预算，因此最后为rho≤M而非rho≤√M。M=0和等号均合法，只推得r=0 a.e.，没有宣称逐点r=0。

联合应用须把267的自由rho**实例化为同一原r的√∫r²**，使用同一个w/M。269不会把任意自由rho自动识别为它。269的r-L²输入在真实原h的L²分解中已由ActualQuadraticTiltMoments.actual_quadratic_source_moments:186–240提供；无需新增残差四矩。若只给267抽象接口，它未把r-L²作为输出，但其联合可测性及|r|≤ww、w²可积普通数学上也蕴含r²可积，故这不是新的统计假设。

于是模型前条件 (1+M)z≤√n 足够推出267的几何条件。更进一步，c_env≤1；若数值n≥(1+M)^3，则所有z≤c_env n^(1/6)同时满足该条件。增大共同N以满足这一数值门槛仍只依赖固定M及原公共参数，不依赖后来模型。这是已发表269与267的普通代数/量词蕴含，**P180尚未另发表消去几何前提的统一尾定理**。同理当前三次解析费用的(1+rho)可上界为(1+M)，但其余scalar预算、tilt、严格eta预算和相对吸收不会因此自动消失。

## 5. 同一合法编码见证与下2Π / 上4Π的接通边界

267既不引入新m0，也不提供另一个独立存在的eta。对真实原h，保留已接受OriginalLevelDependentUpperPhysicalFrontier/其严格矩前沿的**一个**m0≤mΩ、μ0=trim μ，以及该见证内全部n/z/k的canonical eta_k、同一ν和投影q。原m0在n/z/编码参数前选择；267对所有模型的N不依赖该选择，可以对同一原g/r/P应用。g与原r的矩、可测性、对称/退化条件有既有原模型生产者；β≤共同B和共同包络门槛仍需真实满足。

只用由g/D/e_z组成的S在m0中可测；不用假设原w或H在m0可测。令J=q^(−1)(S)，既有同见证transport给

\[
\nu(J^c)=P_0(S^c)=P(S^c)\le\Pi_{n,z}.
\]

NormalizedUpperErrorGoodsetPayment的实际接口，对同一eta_k及signed修正

\[
Q_k=W-W_k+z\sqrt{1+e_z}(V_k-V),\quad D_{\eta,k}=D+Q_k,
\quad E_k=\{z|D_{\eta,k}|>V_k/4\}
\]

使用J上的正V及1/8严格余量，给∀γ>0最终ν(E_k)≤ν(J补集)+γ、limsup_k ν(E_k)≤ν(J补集)。同时原E2/Z0的对应推送事件各≤Π，P(Eclip)≤Π。因此同一canonical族上合法取得pUpper=p2=pZ=pClip=Π；编码k的“最终”指标可依赖固定n/z及模型，267没有统一它到所有模型的一个k。

既有CurrentLevelTrueDeletedConditionalTail的完整公开合同仍另外要求：同eta的真删除Borel分解/包络、独立中心L²单位总能量和正编码分母、真实full/deleted倾斜可积与正I、L_eta及full-I归一费用到原量的极限、严格预算δη_i<1/2和L_eta<cSZ z²、同一clipped推送律，以及显式 broader-L² tail hSZ。其原模型生产者的tilt窗口为z≤√n/(2e^(1/2))；严格原p矩窗口为

\[
z\le \left(\min(1/2,c_{SZ})/2\right)^{1/p}
\beta^{-1/p}n^{(p-2)/(2p)}\quad(\beta>0).
\]

这些已接受接口在同一见证内联合提供，不能只从267的payer推出。预算与费用极限既有资格不重开；本次也不假定模型前共同B会代替实际beta窗口或构成外部hSZ。

在以上全部条件满足的同一族上，令Ψ(z)=1−Φ(z)、L为原截断矩和、R为**原full-I归一的当前z费用**，通用消费者的既有结论是

\[
\Psi(z)e^{-C_1L}(1-C_2R)-2\Pi_{n,z}
\le P\{z\le T\}
\le\Psi(z)e^{C_3L}(1+C_4R)+4\Pi_{n,z}.
\]

这两个系数是公开通用消费者的下向pZ+pClip、上向pUpper+p2+pZ+pClip分别取同一Π；并非把267四坏事件费用相加后的结果。原四事件联合只付一份Π，编码E_k是经J及极限控制的另一类费用。没有已发表同一联合包含就不能把消费者的2/4任意改成1。

在已列全部条件下，上述2/4费用不等式是可接受的普通数学蕴含；缺少另一个同名wrapper不是新增数学缺口。本判断不冒称267 TYPE已含该尾界，不替未发布268认证其源码/机器证据，也不把旧261/263中模型后cg改名为共同cg。进一步统一完整relative窗口/相对付款并完成实际条件模型的原题应用，仍未由本批公开声明交付；所缺不在e1相等、H在m0可测或新的原分母非零假设。

事件始终是**闭上尾{z≤T}**。signed恒等式使未除法事件在编码k中固定，极限用真费用/指标余量；V=0的差异单独由pZ支付，物理零由原H补集支付。该途径不假设P(T=z)=0，不借尾概率连续性；不能直接把闭尾改严格尾或反射成负阈值结论。267的Eclip付款本身对任意Borel比较可作普通对称差控制，仍不等于外部source提供了全部比较方向。

## 6. 原题增量与仍欠的实际应用

267对应p54 F4–F5的共同矩类版本：真实H内安全余量、actual s>0和current-clip同一性及实际H补集付款已交付；F6所需的同eta安全集消费者已接受，可用第5节明确组合。269供应同一原残差二矩标准差的预算比较，不是把欲证rho界作为前提，也不证明任何条件模型自动具有公共预算。

263仍是固定原μ/h/p和包络/外部输入后选正c与最终N的相对多项式尾率；264仍在另一显式hSZC下给任意原Ω、同一物理T、所有n≥3/x∈[0,1]四关系同K绝对误差。267不改变263的固定模型量词，269不把264的模型常数或原p矩自动统一。264的x=0严格CDF合法buffer与x=1闭尾补集原子处理继续有效，无需新反射包；267不是CDF消费者，也没有证明hSZ⇒hSZC。

继续保留的实际原题义务为：

- **条件模型消费**：对p54真实截断/条件化、均值修正和方差标准化模型，须使用正确投影与残差，实际验证共同p/B、Ew²≤M、高度C(log n)^a、对称退化及原模型/统计量法则衔接。267/269不构造这些模型，也不支付确定性均值/方差导致的阈值移动。已有F1–F3修正只支持条件标准化p矩收敛、最终共同有界，不是任意多项式变化率；不能把本批共同B前提当成这一整段应用已形式化消费。
- **最终统一尾消费**：本批新公开声明止于共同物理payer与rho预算；第5节条件式finite-cost组合是已有接口的数学蕴含，不因缺少新wrapper而变成数学缺口。完整统一relative原题应用仍须取实际tilt/矩/包络/几何窗口交集，并在共同cg下支付相对Ψ的异常项；不能从绝对Π单独声称Gaussian-relative估计。本报告未读未发布268/270，不认证其完整局部消费者或最终统一窗口/吸收。普通数值缩窗路线与已经发表、审查的原题消费者应分开。
- **外部归属**：ScalarShaoZhouFiniteCostTailInput(cSZ,C1–4)的全部正常数、完整L²观察/全删一Borel结构、真实倾斜可积/预算域仍是显式外部条件，输入本身无bounded观察前提。独立的ScalarShaoZhouFiniteCostCDFInput(C)则是C>1、所有z≥0、未倾斜compact成本的闭CDF输入，也无bounded观察前提。两者的存在/证明和准确Shao–Zhou归属未由267/269交付，不能由AX白名单、函数名字或彼此推出。
- **原来源边界**：已接受p35删除pointwise domination后的固定法则负面范围，以及fixed-clip1三次费用反例不变。本批真实乘积包络和当前512/rho/z过程均不可删除；有限秩、退化、L²本身不替代所需集中/包络。DC、更广无界条件化、全OQ56/根组不由本次关闭。

必要原来源已只读整读：C:/game/shao/current/oq56/inputs02/p54.md，SHA256 e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43 /6045B；p35.md，SHA256 f5308d1bcdbe2c54e075626617572bf264e3148dd4393324a22ac9664e4e2da5 /11824B。这里复用既有来源决定，不重新认证p35完整反例，也不倒写旧source-completeness记录。

## 7. 必要旧接口指纹及工作范围

下表相对 C:/game/shao lean/library/；按本文所述完整定义/公开合同及必要连接读取，旧局部证明与机器门按已接受资格复用。

| 文件 | SHA256 |
| --- | --- |
| Shao/OQ5/P51/BoundedStudentizerGeometry.lean | bc64d3e11a64f62ad654305ce579c1779546d4df37b5593090105af910502edc |
| Shao/OQ5/P51/LiteralClippedComparison.lean | 8d601a1496ca1a330fb7f96a2ff5cdab6f0d3b37c125a710735d9123c5be1f14 |
| Shao/OQ5/P51/BoundedPolylogWindow.lean | 1d2ad2ca13be7c987c8e0520c5687dba60669af0db6e0dd01edcbc3105043b7e |
| Shao/OQ5/P51/BoundedRemainderPayments.lean | c0102fa13835fb22b01148e42d66cf8ff5704d682b9a6142eb508d7172d95cc9 |
| Shao/OQ6/BoundedProductEnvelopeTails.lean | 43367b3ce14f174a8c8e3db4152e3db3b553ab0dbc9c4521565a1db8ddac1b14 |
| Shao/OQ6/ActualQuadraticTiltMoments.lean | f4772e78008aad28d89f99a6c52e63ba15329fab40c1b66fb41dc2ed3b249d10 |
| Shao/OQ6/OriginalCountablyGeneratedModel.lean | 8691f69ca9ab84649f92b20385c415a2129250cc8f64375d6296e2d59a381627 |
| Shao/OQ6/OriginalLevelDependentUpperPhysicalFrontier.lean | 1136c7f4cd654dc8fcf0ddc9b8c4575f901175e8b785c42aa9fd3926f562a172 |
| Shao/OQ6/NormalizedUpperErrorGoodsetPayment.lean | c95d036b852a66fb86fdef687cdff2ab4a0e6736b45cb015f8d57d3330f1ddf8 |
| Shao/OQ6/CurrentLevelTrueDeletedConditionalTail.lean | 67e7b06fadb28f4865d6f8e63cde2bdd7994242bde9d9783dffb1fa02518770a |
| Shao/OQ6/NormalizedIntegrableTailAssembly.lean | c868ca007153fdc15ff29077702cbb64e8fac5d66ebd9821171ae38454ae5916 |
| Shao/OQ6/OriginalCurrentLevelPhysicalFiniteCostTail.lean | 519d185d374e19e9eb3836c276215366f451122f100f9a5b5cac4b177f797048 |

本次为独立原题语义/跨模型接口审查，不新增Lean定理或数学假设；唯一写入为本报告。未运行Lean/AX/服务器/网络/Git/API，未新增子上下文、调度或共享状态写入。规定配置gpt-6.1-sol/xhigh；实际model/backend/effort及input/cached input/output/reasoning subset均未暴露，分别为null。封存后本角色结束，Root另行接受/集成。
