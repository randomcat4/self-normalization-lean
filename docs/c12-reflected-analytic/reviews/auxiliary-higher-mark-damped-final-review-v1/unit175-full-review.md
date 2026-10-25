STATUS: CORRECT

本文件是封存前获授权增补的单元175独立完整终审；单元177已完成的数学审查保持原样，没有重审或重跑。175的精确源码 `ca4bbacf8de375c2f4a4e3bafeb5aedeb570f0289e794e713c62fa94fe6487f2` 证明了冻结的真实无标记自然阶Gaussian阻尼矩结论，公开接口使用合法，全部实际所属类型/非定理义务和递归公理证据已覆盖，关键缺口为空。指定模型仍为gpt-6.1-sol/xhigh；实际后端与分项用量未知，分别为null。扩展运行确认在unit175-extension-ACK.json；没有新增代理、生产写入或Lean/审计命令。

1. **原文与冻结结论。** 我完整读取新增113行源码、1303字节完整冻结上下文/声明头、冻结记录、当前证明说明、依赖delta及预检查记录；完整读取13,799字节实际类型。原文直接来源是本上下文已经读取的supplement4431–4462，尤其4431–4439取ℓ=0的ordinary阻尼主估计；5155–5160是它供后续Cauchy使用的位置。本文没有把Cauchy的条件式当成普通矩生产者，也没有声称已经证明稀有事件本身。

精确结论是：令c=(1-exp(-2))/8，对每个p:Nat存在C>0，在概率法ν、n:Nat、b,s:Real之前选取；ν只有z²可积、均值0和二阶矩1的前提。若b>0、s>0、s≤2/b，令P是Fin n上真实ν乘积法，retained=∫z²·1_{z²≤b}dν，gamma在retained≥1/2时为-c，否则为1，则实际函数|prefixSum v n|^p exp(-s energy v)在P上可积，其实际Bochner积分≤C·rpow(s,-p/2)·exp(gamma s n)。这里明确保留真实截断矩及两个分支，未假定gamma<0；也没有加强为每个b下任意s。p域是自然数，n包括0，没有第三阶或更高非阻尼矩前提。实际类型中外层let c、所有量词/概率实例、实数乘法和自然幂、if条件、真实integral/pi空间、自然n与p转实数、rpow的负实指数与括号全部与冻结头相符。

2. **Root公共接口依赖变化已处理。** C12冻结记录保留当时计划Root源码e7e200a23fd0a1c1e90ba51cc5b2511e779f1ef1083a5ca51e7e439d6bcc627c及尚待资格/导出的状态。后来Root最终源码为 `f96f193c561a3d6e486f1cde02f009a2af31793f517b326cc65dc556baf9e5bc`，对象为 `4f72de6085a4c06e3d683846305db91de09ca91f6c742727dcda7dfe7b414f0b`。我核对该失败源的确切e7摘要、最终源f96摘要，以及四个完整数学声明头均逐字相同。context-only-amendment01.json（SHA256 `3f927b916b0caf4070443645c3979ccdd7aa3aa91c24f280b8f1012170193bb7`）解释仅加import Lean，并作证明内旧私名构造的词法修复；此变化已经由Root的完整独立审查和原成功内核/全所属公理证据覆盖。C12自身的导入、上下文和冻结数学声明没有变化，也没有访问私名。

Root资格文件SHA256 `2a2ca77941fa9500843582dc57681d01260abfd2abae7f0d1cab331e6ceb6c26`，状态为ROOTQUALIFIED_EXACT_SOURCE_SCOPE_INTERFACES_COMPLETE_INDEPENDENT_REVIEW_AND_ORIGINAL_SERVER_EVIDENCE且qualifiedForSourceBoundConsumption=true；它绑定完整4接口/4实际所属/0值/递归AX审查，以及Root已经完整读过12,004字节独立报告。该独立报告Markdown/JSON摘要分别为 `c3f4369595131ae2d8a9e0b4ea7ec39759068515105c8985c50aef1e76b9076a`、`1a1e7b59e41e3927ab85a327536318bd70d528f5a51f644969ca0d2b26d901ca`；审查者释放SHA256 `08f6066f8cb86919923b224c6ed73ba257568d225218d1b5438585af8595e435`，其中封存8个文件的字节和摘要均重新验证相符。我复用该合格完整证明审查，没有重新审查Root四个别名证明，也没有运行它们的门。旧SourceSuffixMomentBudgets的相同c045源/feb6对象及Root资格3999793e…继续使用单元177已核对的合格证据；不重审旧49份私有证明。

3. **两份完整消费实际类型。** 已完整读取scaled_polynomial_exponentials的2,277字节实际类型，SHA256 `9c5d17f3a6be6e02517baa3b4f10e5e5cbc0ed01408c5621f02df51725232035`；重新从Root最终全部类型导出SHA256 `bdb4f1d1650ecc041c383b98648c36949381750a215fcf838cb39d759b4fa918`的精确TARGET_DECL块截取，字节相同。其结论对p:Nat、lambda,s,d:Real且lambda>0、s>0，给|d|^p≤(p!/lambda^p)·rpow(s,-p/2)·[exp(lambda sqrt(s)d)+exp(-lambda sqrt(s)d)]。没有概率前提、截断或隐藏实例。

另完整读取raw_gaussian_damped_coordinate_factors的22,456字节实际类型，SHA256 `488d2b486e6162018413dd3fd2f11af4b35fd760e3c2e76a06838fc3cd564e75`；从已合格旧完整类型导出023fafc7…的对应完整块无损再截取，字节相同。其lambda=(1-exp(-2))/16与c=(1-exp(-2))/8正；对与175相同的ν、有限二阶矩/中心/单位方差、b,s合法条件，使用同一真实retained和gamma，得到每个epsilon=±1的真实weight(z)=exp(-s z²+epsilon lambda sqrt(s)z)可积，以及实际∫weight≤exp(gamma s)。它还输出带三阶标记的阻尼结果，但本证明没有把这些输出转成额外输入条件。两个公开源声明头和对应导入/全局上下文均已核对；消费的是已合格公开接口，不是仅凭名称推断隐藏结论。

4. **第27–44行：统一常数及前提。** 固定lambda为旧坐标定理的同一正常数，并直接从旧公开结果的第一个分量取得其正性。取C=2·(p!:Real)/lambda^p；自然阶乘严格正，lambda^p>0，所以C>0。选择C后才引入ν、n、b、s，因此它不依赖法、样本长、截断或阻尼参数。A=(p!/lambda^p)rpow(s,-p/2)≥0；B=exp(gamma s n)。hRaw以h2/hMean/hNorm及hb/hs/hsb完全匹配调用旧公开坐标定理，lambda、c、retained和gamma的let都与旧实际类型定义性相同。没有额外有限三阶矩、分布对称性、无原子性或有界支撑要求。

5. **第45–62行：真实有限乘积与可积性。** 对epsilon=1或-1，先由hRaw的对应分量取得g_epsilon在ν上可积。定义每个坐标的f_i=g_epsilon；逐点乘积∏_{i:Fin n}f_i(v_i)通过Real.exp_sum与真实energy/满长度prefixSum的定义，精确等于J_epsilon(v)=exp(-s·energy(v)+epsilon lambda sqrt(s)prefixSum(v,n))。指数中两项的有限求和分配系数完全匹配，未把energy或sum换成期望。

原生Integrable.fintype_prod要求有限索引、各坐标SigmaFinite和各f_i可积；Fin n的有限性及输入概率ν提供的有限/SigmaFinite实例支付全部前提，因此真实乘积函数可积，再由逐点相等转给J。原生integral_fintype_prod_eq_prod给实际乘积法积分等于各坐标实际积分之积；常函数族及card(Fin n)=n给(∫g_epsilon dν)^n。该原生积分等式可用于总定义积分，但这里已先取得各坐标和乘积可积性，故没有依赖不可积默认积分。原生Pi文件中所用两个完整契约及其零长归纳分支都已读取；该文件摘要仍为钉死807d3836…对应43c50a9d…，复用同上下文已核对的pin字节比较。

6. **第63–77行：路径指数矩界。** hRaw.2 epsilon he的.2.2.1确为无标记weight积分≤exp(gamma s)，而非带三阶标记输出。由于g逐点exp>0，实际积分≥0；以自然n次幂保序合法，得到(∫g)^n≤exp(gamma s)^n。Real.exp_nat_mul及实数交换结合把右侧精确转成B=exp(gamma s (n:Real))。这里没有用gamma<0，也没有不合法地对未知符号数取幂比较。两个epsilon均遵守旧接口的epsilon=1∨epsilon=-1条件。

7. **第78–102行：公开标量支配及真实目标可积性。** 把公共scaled_polynomial_exponentials作用在真实d=prefixSum(v,n)，lambda>0和s>0恰为其全部前提。乘以严格正的exp(-s energy(v))，用exp加法恒等式得到目标非负函数≤A(J_1+J_-1)。这一步对应真实随机函数，两个符号和epsilon的乘法展开均准确。J_±已经分别可积，故其和再常数乘A构成可积支配函数。

目标函数由真实prefixSum与energy的连续性、绝对值自然幂和exp连续性而连续；有限实乘积空间是相应标准可测空间，给出所需几乎处处强可测性。目标逐点非负，把实范数转成自身后，hBoundInt.mono'的范数支配正是上一步hPoint，得到hTarget的真实可积性。不存在把待证可积性作为标量定理的参数或把待证矩界塞回支配函数的循环。

8. **第103–111行：真实积分的最终数值界。** integral_mono使用已证明的hTarget和hBoundInt；integral_add明确给两个hProd的可积性，常数乘积分合法。两个实际J积分各≤B，利用A≥0得上界A(B+B)，再按C、A、B定义作实数环等式，恰为C·rpow(s,-p/2)·exp(gamma s n)。这条链同时支付可积性和数值界；不是只得到条件式、形式化定义的预算或有限维代数恒等式。

9. **边界与原始范围。** n=0时乘积为空、真实路径满和及能量均0，J_±=1；原生有限乘积积分的零长分支明确覆盖，完全不要求0<n。p=0时0^0=1，C=2，所有标量/乘积/支配步骤仍成立；n=0,p>0时目标为0。s>0确保sqrt和负实幂的使用合法，lambda>0排除除0；没有除以样本和、样本能量或坐标，也没有漏掉含原子、零样本或正负混合支撑。输入有限二阶矩加概率性使均值的矩语义正常。定理保留s≤2/b，未声称所有正s同时适用于固定b；gamma=-c分支需要真实retained≥1/2，不能把else=1的增长分支写成负指数衰减。自然p结果不自动等于原文所有非负实a；后续Cauchy的2a矩和完整稀有事件装配仍须由消费方另外合法接入。

10. **全部实际所属类型、值与递归公理。** 本次完整实际类型为13,799字节，SHA256 `0e457e7205b7b936c9695f99dc9db98fa90045a4e9d3e60c85ef0036e2212f80`，完整块在成功owned-audit日志内；其所有binder、let、条件和实例均与前述冻结头一致。由113行源码声明、TARGET_DECL块及真实owner行独立推导：1常量、1定理、1公开、0私有、0生成、0非定理、0定义值。所有J/g/A/B/f等为证明内let或have，不是遗漏的全局定义。actual-definition-values.txt为0字节、空文件摘要e3b0c442…，审计日志无DEFINITION_VALUE。因此完整读取13,799字节类型后不存在剩余私有/生成或值覆盖空洞。

我完整读取本单元OwnedAudit.lean：其真实owner选择和每项collectAxioms递归白名单检查与本上下文已完整理解的审计实现一致，只将target和唯一公开名字改成175。实际唯一owner的公理恰为propext/Classical.choice/Quot.sound；无sorryAx。源码禁用项扫描为空。已逐字读取原保存命令、完整kernel001及完整14,024字节owned-audit日志；KERNEL_EXIT=0、AUDIT_EXIT=0且尾部为AUDITED_TARGET_CONSTANTS 1 PUBLIC 1 THEOREMS 1 DEFINITIONS 0。沿用Lean4.36.0-rc1、Mathlib807d3836…、shared-v34、CPU14–17/c12-heavy.lock、-M8192 -j4，审查者零重放。

11. **源对象、依赖与历史标签。** 新源5914字节、冻结1303字节，均UTF-8无BOM/LF，完整上下文和头重构逐字等于冻结6359cf2a1ae8c3d4189ae805edad803c2c8059d9a03ed554dab0cf9bb0b95e58。输出对象SHA256 `4e3db426fb4340ef68c7fd3a81e50c842f6f8effc576c5a74d0b20ad35818dc6`，与C12导入视图对象相同；收据SHA256 `465a1013712ff4b82723ca4d780ec77b523107b959ae8e2a71d2ae4fe8b1d11d`，作者释放SHA256 `13eb6882ae99a7485c5533c2f4726c1fb12b0cef93e2395913cce7fc5f2dfe2d`。服务器19个收据工件逐一只读重hash相符，17个对应本地作者文件也相同，成功快照等于当前源。没有失败的175内核尝试。

Root最终canonical源/对象与C12导入的公共对象精确匹配f96/4f72；旧canonical源与原始/导入对象也匹配c045/feb6。C12两个公共.lean预期不存在，已由Root授权提供精确只读对象及canonical Root源回退，不构成缺失接口；没有复制或写共享源/缓存。旧freeze-record、source-and-proof-plan-v1以及freeze-comparison的execution字段保留了当时“待资格/导出、不执行”标签；当前dependency-source-delta/preflight、source-and-proof末尾的状态转换、精确收据及原始kernel001/AX才给出已经通过的实际执行证据。这些历史计划文字没有被拿来当通过结果，也没有因其仍留存而重跑成功门；它们不改变数学前提或当前源绑定。

12. **组合交接。** 最后组合只读观察为2026-10-24T23:52:51.311948+00:00；HEAD仍为b3ad31734dd2dda8c5c4ce1463fd908f77276392，tree为012943e9fc082aa2a5c8c59a14e397dad0928216。两单元源、对象、冻结、收据及全部19+20保存工件仍匹配，作者均writer/execution released、inFlight=[]；未观察到175/177目标Lean/审计进程。177原数学审查没有重复，所做的是最终字节绑定检查。

因此175为CORRECT，新增与177组合共2模块、2实际所属公开定理、0私有/生成/非定理和值，完整类型字节由实际文件相加为13,799+10,247=24,046。两个模块没有相互导入；177不使用新公共标量接口，175使用已经Root合格的scaled_polynomial_exponentials和旧raw coordinate公开接口；176不在本组合内。正确性为这两个辅助生产者的精确范围，尚非稀有事件、逆矩、加权记录或完整C2根结论。C2/C12仍OPEN，C1原已接受范围及OQ3用户暂停状态不变。父实例须完整阅读组合full-review.md一次并验证封存后自行资格确认；本报告不代写父实例验收。
