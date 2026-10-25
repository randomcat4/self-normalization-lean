# unit187 独立完整源码审阅：机器证据前的自然边界

STATUS: CORRECT

此处 CORRECT 仅裁决所绑定精确源的 source-to-statement 与全部证明的数学审阅。最终 qualified=false；actualOwned=UNKNOWN；尚未取得本源的服务器内核、完整 actual TYPE、所有非定理 FULLVALUE、私有/生成所属与递归公理证据，不能据此接受 187。

审阅角色 /root/oq56_ghost187_final_review01，与作者独立。请求配置 gpt-6.1-sol/xhigh；运行提供者没有暴露可核实的实际模型、推理努力或分类用量，相关字段为 null。本上下文没有改源，也没有运行 Lean、服务器、网络、Git、上传、缓存写入或子上下文。

精确源 DoubleGhostSignInvariance.lean，SHA256 5c71150709e1825414dcea9d68a14fa25a1a12dc97a4fdad6be4b92b344add8d，14557 字节，256 LF；作者 manifest ce02f632d2aca583d35dd3976c3d00f6e8cb4e8b82f727f351f4583aaca7f57b；作者 RELEASE0 08c4572bf7ee240a177003edef8be8cb8ba3a9fc637ebe840ca6962d8b8d3918 的 writer/execution/inflight/children/locks 全为零，先验证后作实际 ACK。

## 题意、冻结和数据

完整逐行读取生产源 1–256 与 proof-notes。14 个声明头、6 个定义完整原值按完整冻结头后接确切分隔符作直接字节比较，全部相同；有效 prefix/suffix 一致。冻结基底45bed608…、三个 AE 外层 z 祖先修正6d748120…、仅 ENNReal 作用域增补843f1a16…、事前平方根表达式增补9cabb034…均已核对。作者15个 payload 和23个输入绑定逐个重新散列一致。没有新假设、改签名或数据初始化。

6 个定义确切实现：pairSwap 的 true 保持/false 交换；swapSample 按相同 s_i 逐坐标操作；ghostMatrix 的对角字面0和异坐标四项差；ghostWeight 为两个单点权重之和；signLeft 使用 WithLp.toLp 2 的真实 EuclideanSpace；pairedLaw 为 Fin n 上 ν.prodν 的实际有限乘积。无函数空间上确界范数替换，无别的随机法则，无抽取或新选定数据。

完整覆盖全部34个授权嵌入表达式的类型、完整值、外层局部参数和嵌套绑定；33个与基底冻结逐字一致，第34个平方根连接与事前增补一致。34是授权清单数，不是声称源码实际表达式总数。14组公共 telescope/nested scopes 与基底相同；8组实际 proof scopes 的外层 telescope 与对应头相同。共享 ones 的 n 在每个实际使用处由所属声明绑定；sqrt 表达式的 u 在 hnorm 参数下绑定。元语言8记号均未变成命名 Lean let。源码所有 have 是命题证据，未出现 named data let、local instance、private helper、选择器或新数据函数。普通命题 have/branch 不另设行政冻结；它们的实际完整证明仍已阅读。大幅重复 telescope 元数据经确定性比较复用已读源码和冻结，不虚称反复逐字重读重复原始字节。

## 全部证明逐项审阅

1. **swapSample_involutive（29–32）**：给任意 z 后逐坐标外延。每个固定布尔分支都是恒等两次或交换两次。没有要求 n>0、Ω 有可判等或任何可测结构；n=0 不产生索引。
2. **ghostMatrix_swap（34–39）**：i=j 单独由定义得0。i≠j 时，记原四角为 a,b,c,d，true/true 给 a−b−c+d；false/true 给 b−a−d+c；true/false 给 c−d−a+b；false/false 给 d−c−b+a，分别是原差的 +、−、−、+。右侧符号正好是 signValue(s_i) 与 signValue(s_j)，无需 r 对称或典范性。
3. **signLeft_isometry（41–60）**：EuclideanSpace.real_norm_sq_eq 把两边真欧氏平方范数变为有限坐标平方和；符号平方恒为1。非负范数平方相等推出范数相等，无除法。PiLp.ext 与分配律给 Lx−Ly=L(x−y)，继而所有距离相等，得到完整 Isometry。不是只证明某个输入的范数或范数上界。
4. **rowAction_swap_spec（62–79）**：复用已合格186的实际 rowAction_apply，坐标是 Σ_j u_j D_ij。两侧符号共轭代入全1的行作用，提取 ε_i，剩余 Σ_j ε_j D_ij 正是 signPath 行作用坐标；真实 PiLp 外延给向量等式。随后只消去左侧的等距作用得到范数等式。没有逐行取绝对值或丢弃右符号。
5. **ghostMatrix_envelope（81–102）**：W_i≥0来自hW两项非负。对角绝对值0≤W_i²由 mul_self_nonneg。异索引逐次 abs_sub/abs_sub/abs_add 控制四项，hR给四种对应乘积界，展开等于(w_xi+w_yi)(w_xj+w_yj)。nlinarith仅做这些实数代数推论；不除以权重，不用全域逐点包络，不要求对角四角假设。
6. **swapSample_measurePreserving（104–124）**：每个pairSwap按false的产品交换与true的恒等保ν.prodν。概率ν支付两个因子的 SFinite、产品概率与有限性。整体可测用坐标判据和评价复合。pi_map_pi 的实例前提是映射后的坐标测度 SigmaFinite；源码先用实际 hfactor.map_eq 重写成ν.prodν再 infer_instance，条件确实支付。最终是当前 pairedLaw 的 map 等式，不是把不变律作为假设。
7. **ghostMatrix_ae_envelope（126–195）**：eval的保测与fst/snd保测复合给每个实际边缘ν。iIndepFun_pi 用恒等坐标与产品概率给配对坐标独立；固定i≠j经indepFun和可测投影复合。h11/h21/h12/h22各自用有限概率源的独立联合映射定理与两个已证边缘，分别证明四角的实际推前ν.prodν并包装可测性。不能以数值不同替代索引不同。QMP.ae 对任意谓词允许拉回原hW/hR，未偷加r或w可测。两层有限ae_all_iff结合四角AE；i=j分支只产生空的异索引义务。最后使用确定性包络。外层AE z在两个conjunct和两层∀中保持可见，恰好遵守祖先修正，无兄弟作用域泄漏。
8. **ghost_row_norm_law（197–252）**：仅hr的产品可测r，使四角核复合可测；固定索引的对角分支是常数0。任意固定u的行坐标为有限可测线性组合，平方和可测。经 EuclideanSpace.norm_eq、rowAction_apply 和 sq_abs 连接到事前冻结的sqrt坐标表达式，得到真实范数可测。全1与signPath均固定路径，故两个最终范数函数可测。交换保测先替换源律，map_map在两个实际可测前提下给f1∘T_s，rowAction_swap_spec的逐点范数等式再map_congr，方向正确且不需任何q次矩可积前提。

## 接口完整条件与旧证据复用

完整读取当前16个非平凡接口的全部原声明与所需 ambient/实例前提。14个声明文本在哈希绑定fullFile主源直接精确匹配；pi_map_pi和measurePreserving_eval在f9b523…主源packet的350–414完整窗口匹配，同时读取namespace/section/variable/omit标记，确认Fintype Fin n、映射后SigmaFinite、评价的产品概率条件。其他主源的相关variable/section/omit标记亦独立抽取核对；没有把作者的“已读”布尔值当作检查结果。WithLp构造/投影、PiLp的CoeFun和ext、EuclideanSpace=PiLp2、真范数公式实际主源已读。基础有限和/AE有限交、可测坐标与产品、实数连续运算、环/序与距离等使用明确 expected contracts，不虚称另取了机器TYPE。

直接producer186精确source07520a5e…/object1796459c…、父qualification bf0054b9…与实际metadata7d47e64a…绑定一致；本次完整读取实际 column、rowAction的TYPE和非定理FULLVALUE以及rowAction_apply完整TYPE，符合当前调用。其内部旧证明与15actual-owner证据直接复用，不再复审或重编。185在186的producer-qualified-bindings中消费的实际signValue和signPath完整TYPE/FULLVALUE也已读取，true=+1、false=−1，与当前pairSwap约定一致；185父与独立资格、同一源对象绑定复用。Stage1文档中186待资格属于历史时态，当前以精确186 qualification为准。

## 原文范围与边界攻击

已完整读取原p44、p54与本单元Stage1推导/前提；p51当前相关S18、S6、S7和原文归属段实际阅读。187覆盖p44(2)所用的真实交换、不变律、左符号等距和原AE乘积包络适配。p44原先还假定对称、典范，本单元这些交换代数步骤实际上不需要它们，冻结头明确保留更广量词，并未将后续条件典范期望解释成已证。没有条件均值(1)、Jensen、外层Fubini/全q积分、随机行矩/尾(4)(7)(8)、标量二次混沌(5)、DC或根结论。

n=0全为空索引，行作用零向量；n=1矩阵仅有字面零对角；零权重无除法；Ω非标准Borel、原子/重复观测、非对称r、原始非零核对角均保留。异索引的四角AE不用同索引数值去回避零测问题。对测度ν为概率的前提在所需位置真实使用，没有泛化到任意只SFinite测度。

p54修正p51 S6的过强p矩任意多项式速率为收敛/统一有界，原子安全真实坏事件付款保持。Shao–Zhou Lemma6.1原非线性基核行集中仍为具名外部输入；本源码不调用也不重新认领它。C2/C12/OQ56保持OPEN，OQ3保持PAUSED_BY_USER；124统一机制不是前置。

## 待同一上下文续审的唯一最终门

无当前数学关键缺口；source review完成。下一步仅消费父级同源服务器机器证据：确认实际源与对象、内核成功及保持约束；按环境所属模块索引而非命名空间过滤发现全部actual owners；逐项完整读取所有TYPE和每个非定理FULLVALUE（含私有/生成/命名空间外），与已读源码/冻结作语义比对；逐项recursive collectAxioms须仅propext、Classical.choice、Quot.sound；绑定所有原始收据、对象和字节。机器证据前不填造实际个数，不发布qualified=true。普通finalturn只结束这次自然边界，不构成后台继续运行。
