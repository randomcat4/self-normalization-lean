# Unit190 repair01：同一独立审查员的受影响源码续审

STATUS: CORRECT_SOURCE_ONLY.

四段变化证明及其源到陈述/冻结语义未发现数学关键缺口。此结论连同精确复用的原完整源码审查，覆盖修复稿的全部数学内容；它不是Lean脚本已通过的声明。`qualified=false`、`actualOwned=UNKNOWN`。修复稿的真实native02和同一O上的全部actual-owner TYPE/FULLVALUE/递归AX证据仍须由本审查员后续完成。

审查员仍是 `/root/oq56_scalar190_final_review`，与作者 `/root/oq56_scalar190_stage1` 分离。本轮独占写 `drafts/oq56/unit190/final-review-01/repair01-source/`。请求的模型/强度为gpt-6.1-sol/xhigh；运行时未公开实际模型、强度或token细分，记录null。本轮没有Lean、服务器、网络、Git/API、上传、缓存写入或子实例调用，没有修改任何作者源码或共享文件。

## 精确版本及复用边界

修复稿 `author-01/stage2/repair-01/CanonicalDoubleGhostScalarMoments.lean` SHA256 `17790c480efcab2d11cb5d00ccd215a6853e289fb078b5b041ae3bba972ab68c`，32159字节/589LF/CR0/BOM0。原稿SHA256 `29c30b00e12b543a13d47db111872fd9919cc09ea98a34d6adf89fefc3b1101a`保持；原完整源码审查SHA256 `5762dcd772f3535e69d570b9e9dfe1b7f9ec8e2fe31cff65f5594a8a7ab3719d`保持。修复作者release SHA256 `cdec2cacdd25b5a4bf4ea15fd80ea6052aa7fdddbbd0592673b9a418e2a5348c`已绑定。

完整阅读了四段变化声明的全部证明、完整proof-only.patch、changed-proof-notes、strict-proof-only-static-compare、diagnostic-disposition，以及原native01九条错误和四条告警的完整投影。父级intake SHA256 `f631aef17251deaa51f3c56ced60ee9a942e127cda245c63763f380398500f68`仅作为intake记录，不作为独立裁决。

本审查重新从两个实际源码切分声明、头和证明体，独立确认：只有下列四个证明体变化；全部15个完整头逐字节相同，四个全局定义整个块逐字节相同，其他七个定理证明逐字节相同，imports/open/namespace前缀和关闭后缀逐字节相同；36个局部let完整块、3个letI逐字节相同。相关声明头还重新与原freeze比对。原31个完整primary声明、28个producer TYPE/19个非定理FULLVALUE及其冻结作用域的完整审查，以精确不变哈希复用；未重复审查旧合格producer证明。

独立审计 `independent-source-delta-audit.json` 的129项检查全部通过，含patch逐字节重建、实际输入哈希、完整头/体边界、36局部块、实例、错误处分与真实错误投影的逐项对应、无禁用证明词和来源状态。该审计是静态字节证据，不是机器证明证书。

## 四段完整受影响证明

| 新稿行 | 声明 | 结论 |
|---|---|---|
| 34–37 | halfSumCLM_apply | CORRECT_SOURCE_ONLY；固定2的除法表示修复，CLM和统计量不变。 |
| 87–175 | ghost_scalar_sign_law | CORRECT_SOURCE_ONLY；显式eta/Pi函数相等及实数范数可测复合保留原四角可测性和双符号标量推前律。 |
| 223–279 | half_quadratic_envelope | CORRECT_SOURCE_ONLY；除法展开修复保持原Young双和恒等式及粗(n/2)energy界。 |
| 536–570 | original_half_eq_upper | CORRECT_SOURCE_ONLY；普通Prop反向不等式补齐矩阵条件式，显式核对称桥不变。 |

**halfSumCLM_apply。** 全部头和halfSumCLM定义不变。旧native01已经把目标化成 `(Σ_i v_i)*2⁻¹=(Σ_i v_i)/2`，并报告未知的 `div_eq_mul`。修复将该名字改为常规除法恒等式 `div_eq_mul_inv`，即a/b=a*b⁻¹。它只把固定分母2的右侧换成左侧已有的乘逆形式。系数仍½，真实Euclidean CLM及坐标求值不变。没有新前提、函数或数据；也没有除以可能为0的n或统计量。该恒等式的数学使用没有新API语义风险，实际脚本可用性留给native02。

**ghost_scalar_sign_law。** 完整证明前八项冻结局部data及其捕获范围不变。每个角仍是原先的坐标投影对，hr复合支付h11/h21/h12/h22的可测性。对i=j，实际矩阵项仍定义为0。对i≠j，128行把目标显式写成 `z↦ghostMatrix n r z i j`；这只是ghostEntry在同一个i,j下的eta表示。展开ghostMatrix后，hij删除索引条件，130行将已有 `((h11.sub h21).sub h12).add h22` 的可测性转为目标，随后在已绑定z下函数外延和Pi.sub_apply/Pi.add_apply给出逐点同一个四角差。这一步只证明两个已存在的函数表示相同，没有改变四角差或补充可测性假设。

原hG的目标在135行先eta展开，再展开ghostHalf/quadratic和常一路径，所得仍是冻结ghostEntry的有限双和除2。实际有限和的每一项可测性由同一hEntry支付。修复没有新增求和选择器或统计量。hLeft在140–144行以实数norm的连续可测映射复合hG，再由Real.norm_eq_abs改写为冻结的leftAbs。`continuous_norm`在这里的拓扑对象是ℝ，复合的定义域依然只需要给定的可测结构；没有为Ω引入拓扑，也没有要求Measurable w。新增的 `z↦‖ghostHalf n r z‖` 与既已冻结的 `z↦|ghostHalf n r z|` 逐点相同，是对原数据的表示证明，并非新的实质函数接口。

此后整个hSwap、hRight、真实swapSample_measurePreserving、右侧可测性和Measure.map_map推前后缀保持原证明字节。完整阅读该后缀确认：仍由ghostMatrix_swap得到左右两端符号ε_i和ε_j，仍是标量二次式的换号律，未改用行范数律。没有改变任何概率法则或积分接口。

**half_quadratic_envelope。** 所有假设及productEntry/squareEntry不变。修复只把Young平方对的 `(W_i²+W_j²)/2` 以 `div_eq_mul_inv` 写为乘2⁻¹，接着原有限和分配/提取与ring归一化证明双和=n*weightEnergy。其数学恒等式对n=0也成立。完整证明其余步骤仍逐项证明entry绝对值≤W_iW_j，再用平方差≥0、两层求和三角和固定正2除法得到(n/2)energy。这一粗界只支付后续q-L1，最终8q界不变。它不取消n、S或entryEnergy，零能量边界保留。

**original_half_eq_upper。** 原hsymMatrix在非等分支中拿hij:i≠j当等式使用.symm，native01准确报告该问题。547行新增 `hji:j≠i`：假定h:j=i，则h.symm:i=j，与hij矛盾。这是普通Prop的完整证明，不是新增数学前提、非Prop数据、选择器或实例。由hij/hji分别去掉两个originalMatrix条件式，剩下的就是已有点态r对称性。整个实际189 quadratic_eq_two_upper调用仍显式支付零对角和矩阵对称，严格上三角简化和除固定2的后续保持。r(a,a)仍任意，重复观测仍保留，原始F没有被替换。

## 冻结与匿名范围裁决

冻结SHA256仍为 `cc06105e7b843e5c04c3faf423e51a82544fd32c033506b6b36b1818576e2bbd`。完整15头及4值不变，因此假设和结论的全部量词不变。36个局部data的类型、值、顺序、作用域由完整块字节相同和原独立完整审查共同覆盖；没有新let/letI。

原17类匿名模板保持。新出现的ghostEntry/ghostHalf显式函数求值是既有冻结数据的eta表示；四角组合只在固定i,j、已绑定z处证明同值，norm复合通过实数norm=abs回到冻结leftAbs。均不增加新的可观察信息或substantive helper/selector。原norm_sum_le的字面求和参数与上三角求和继续属于原已审定的anonymousExpressionBoundary。hji和funext/convert产生的普通相等式目标都是Prop，无需单独冻结。未发现冻结语义gap，也没有实际新数学API风险需要额外primary intake。

## 原失败证据与待付机器阶段

原native01确为失败：来源为 `author-kernel-01-affected-diagnostics-v2.json` SHA256 `c38ee483c1ac2c9164b0c1f61daf0704c99f1db8e8ddbf5e992b904cab7f0c56`，绑定原服务器receipt SHA256 `4b8173aee22222c3541d696c04e94709be7b7c1ca8f4d7400819efd0eaff4a61`，实际RC1、6.567436004057527秒、无O，strictWrapperSuccess=false，owned group已结束。本次只读取本地结构化诊断及其绑定，未取回或重放该服务器命令。先前五错误投影只是解析计数失败，保留为历史证据；本次按完整九错误块逐项审查，未把它记作另一次Lean运行。

九错误均对应四段受影响证明：halfSumCLM_apply的名字错误和剩余乘逆/除法目标；sign_law的Pi函数表示、hG未饱和化简和abs字段问题；envelope的名字错误和无进展化简；upper桥的hij.symm和反向条件式。四条原告警（3个冻结letI与1个未使用simp参数）所在证明体逐字节保留，没有告警抑制或清理。修复稿未来实际告警数量未知，不从原记录推测。原投影未提供FIRSTEMPTY字段，本轮不推断其值。

原完整CORRECT_SOURCE_ONLY报告从未声称原Lean脚本成功，原native01失败不被抹去。修复稿目前也未提供native02结果。后续同一独立审查员必须核对精确修复source/O、真实kernel/audit receipts与FULLFP绑定，从真实190模块index对ALL env.constants无namespace过滤发现全部actual owner，完整审查所有TYPE及所有非定理/private/generated/foreign FULLVALUE、body存在和递归AX，仅允许propext/Classical.choice/Quot.sound；仅从规范化JSON在内存独立重建原stdout哈希与字节数。实际warning/strict-wrapper/FIRSTEMPTY结果必须如实保留，不能为清告警重复编译。

修复保持原p44式(5)真实原F的8q结论及一般非对称半有序前导量；p54修正、Shao–Zhou外部归属、124非前置及C2/C12/OQ56 OPEN、OQ3用户暂停均不变。源码阶段没有数学剩余缺口；唯一待付是修复后真实内核及全部实际所属元数据/公理证据。最后SOURCE-RELEASE0后所有writer/execution/inflight=0，普通回合结束，等待同一reviewer明确继续机器阶段。
