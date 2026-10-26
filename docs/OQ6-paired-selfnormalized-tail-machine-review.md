# 单元199精确修复源的独立机器证据与最终组合审查

STATUS: CORRECT

QUALIFICATION: QUALIFIED

此裁决仅覆盖 `Shao.OQ6.PairedSelfNormalizedTail` 的精确修复源和该源首个成功原对象。完整源码数学审查由原独立完整审查、独立受影响完整 helper／T03 组合审查及本轮机器绑定审查精确组合；本轮没有重新成证、重审旧 producer 或再次运行 Lean。原 S11、C2/C12/OQ56 仍 OPEN，OQ3 仍 PAUSED_BY_USER，原 C1 immutablev85 完成状态保留。

## 精确对象与独立性

本轮审阅者 `/root/oq56_selfnorm199_machine_review` 为全新独立上下文，未参与199作者或父级声明冻结；任务指定 `gpt-6.1-sol/xhigh`。实际模型、推理档位及输入／缓存输入／输出／推理子集计量没有独立可见接口，均记录为 null。唯一写入范围为本目录；服务器、Lean、AX、上传、Git、API 与子实例调用全部为0。

源码为 `author-01/stage2/repair-01/PairedSelfNormalizedTail.lean`，SHA256 `23d5e22f5bd8669f8e7d41afec78cf1b5bcf8150052ec666fc2bfbac507a7d8b`，7364字节、169LF、0CR、无BOM。完整读取新源用于源／实际类型／定义绑定；禁止词扫描为空。FIRST 原对象为 `da3d2658aabde869760cf289534d016fe65529a3e5ad43293e22a5e11aac92e2`，214424字节，mtime_ns `1792990004512870374`。原生检查、手动 AUTHORSTOP、审计前后、元数据规范化及补充只读当前观测均绑定同一对象；无告警清理或重编。

原完整独立源码报告 SHA256 `73c6701d1acebc4cfd7e7fbd17378cab32d86b489ec797379da9922a6e10f939` 与覆盖 `fbcfbc3d99078fc059f37803187239e84021295134efa6d571dde8aa9803f641` 已完整读取。受影响完整源码报告 `61994abe40f6b419630b0970b1e53fde484856ca9b5248eee25aef8dd3c229f8` 与覆盖 `62106719cf2e7dac8608b6a0a9730e137ed8bf47a71c7034ab2b36194953dbcb` 同样完整读取。重复的28数据行、10命题头及全部匿名分支经区分大小写的结构相等核验后复用；没有把报告中历史 machine-pending 状态回写成机器通过。

四套原 author／review manifest 的全部载荷、DONE、CHECKPOINT、RELEASE0 和父级接收记录已精确核验。实际载荷数分别为13、7、10、8，所有 manifest／control 引用均与文件哈希、字节数一致；旧版 manifest 当时允许列入 CHECKPOINT 的边界原样保留。两位作者及两次源码审阅的 RELEASE0 均为 writer／execution／heavy／inflight／pendingExternal／children 全0。本目录新 manifest 排除自身及全部控制记录，不产生自引用。

## 既有完整数学审查的组合范围

旧源 SHA256 `60425a4454af45f28c22e3e81bb9a23344953c074f3f38108e08509dc55fecc6`，7295字节。独立字节核验确认：前缀5248字节和后缀1847字节，共7095字节不变；只以事前冻结的269字节完整新 `hint` 代替旧200字节 helper，实际改动仅125–126行。新源完整重建等于旧前缀＋冻结新 helper＋旧后缀。

原完整审查覆盖 T01 逐坐标交换／符号差、能量不变与符号和；T02 严格事件可测；T03 固定符号交换保测度、原像事件、实数指标积分、有限符号平均与实际配对概率的精确积分桥；T04 将已合格198点态有限符号尾界积分。受影响审查独立覆盖了完整新 `hint`、`integral_indicator_const` 的精确头与有效前缀专门化，以及全部T03输入和下游消费组合。两份审查的未改部分仅按上述精确字节与接口复用。

六个声明头、两个全局定义右端项、28数据类型／初始化／捕获／绑定器／作用域均保持事前冻结。源码仍有且仅有 D/B/I 三条数据 let、两条局部概率实例、十个完整显式命题头。新 API 的显式实数1是已冻结常函数的值，无新数据选择、假设或实例。T03与T04各自从原 `hμ` 派生 `IsProbabilityMeasure (pairedLaw n μ)`，实际生成类型正好确认这种依赖。

## 全部实际所属常量

审计输入 SHA256 `020f3c74c561155b5bae4217744237e95dc393c9480f91d32ac9fe33be645f9b`，2739字节／62LF，完整读过。它以锚点的 `env.getModuleIdxFor?` 取得实际模块索引，遍历所有 `env.constants`，没有命名空间过滤；对每个实际所属常量调用递归 `Lean.collectAxioms`，完整输出名称组件、宇宙参数、种类、body presence 和 TYPE，并对非定理输出 FULLVALUE。`pp.all=true`、`pp.maxSteps=1000000`，无截断标记。

实际发现10项：8定理、2定义；123行TYPE与15行FULLVALUE均逐项完整读取。10项均有body，均只有宇宙参数 `u_1`；没有 axiomInfo、opaqueInfo、私有名称遗漏或缺失定义值。四个额外生成声明也全部审阅，未只检查四个公开定理。

以下省略公共前缀 `Shao.OQ6.PairedSelfNormalizedTail.`。逐项完整TYPE／非定理完整VALUE、名称组件、宇宙、body及公理清单保存在 `OWNED-TYPE-VALUE-AXIOM-REVIEW.json`。

| 实际名称 | 种类；TYPE／VALUE行 | 源码对应与语义 | 递归公理 |
|---|---:|---|---|
| `paired_tail_cube_integral._proof_1_1` | 定理；7／不适用 | T03 82–83行概率实例；只捕获 n、Ω、mΩ、μ、hμ | 三项白名单 |
| `pairedDifference.eq_1` | 定理；5／不适用 | D01 方程；第一个坐标的g值减第二个坐标g值 | 三项白名单 |
| `measurableSet_pairedTailEvent` | 定理；6／不适用 | T02；仅可测空间、g可测与任意实数t | 三项白名单 |
| `pairedDifference` | 定义；2／4 | D01；完整lambda右端项精确为配对差值 | 三项白名单 |
| `paired_tail_cube_integral._simp_1_2` | 定理；7／不适用 | 任意半群的 `a*(b*c)=(a*b)*c`；与133行反向结合律simp参数相符 | 空 |
| `paired_swap_spec` | 定理；24／不适用 | T01全部三项合取，量词、顺序、等式方向一致 | 三项白名单 |
| `pairedTailEvent` | 定义；2／11 | D02；严格 `t*sqrt(energy)<abs(sum)` 事件；规范实数运算 | 三项白名单 |
| `paired_selfnormalized_tail` | 定理；26／不适用 | T04；概率律、g可测、t≥0，结论精确为 `2*exp(-t²/2)` | 三项白名单 |
| `paired_selfnormalized_tail._proof_1_1` | 定理；7／不适用 | T04 142–143行独立概率实例；不是T03局部实例泄漏 | 三项白名单 |
| `paired_tail_cube_integral` | 定理；37／不适用 | T03；实际事件质量等于同一配对律上的有限符号指标平均积分 | 三项白名单 |

“三项白名单”恰为 `propext`、`Classical.choice`、`Quot.sound`，各出现在9项依赖表中；第5项公理依赖为空。全部公理数从实际10项重算，没有新增公理。生成反结合律helper的 `[Semigroup G]` 只属于它自身的正确恒等式，没有成为公开T03/T04的额外前提；因133行相关simp参数有未使用提示，不主张此helper仍被主证明实际引用。

全部六个实际源声明的TYPE与冻结头逐项配对，两个实际FULLVALUE与源右端项逐项配对：Nat样本数、任意Type宇宙、规范Pi／乘积可测结构及实数实例均一致。T01没有概率或矩前提，T02没有概率前提，T03对t无符号限制，T04仅增加冻结的 `0≤t`。没有隐含 n>0、正能量、t>0、L1/L2、均值零、单位方差、有界性或标准Borel假设。

本地根据所有逐项 JSON／TYPE／VALUE／COUNT 块独立重建原输出，得14347字节、SHA256 `4d0fedfaa04002ba252cb6ffa5122db001adfeb29c9f72d29e97d5355abeb8b4`，与原审计stdout和服务器绑定完全一致。未将原始日志或原对象复制到本目录。

## 实际收据、诊断与资源绑定

native02收据为 `eaf6e5b79ce010f95f6b8263399136779a3e9638be912bfae68c0540c80f348d`，实际Lean退出0、0源码错误、5警告，5.0566秒。其实际命令在CPU52–55执行 `lake env lean -M 8192 -j 4 -o <FIRST原对象> Shao/OQ6/PairedSelfNormalizedTail.lean`。配置前没有原对象，实际 `nativeObjectAfter` 正是上述FIRST原对象。源码和12553条实际受保护记录前后精确一致。

同一原对象全所属审计收据为 `6daeefb4b8b88c16fd39804f1e0f28e2b3e99fff984e2ab3e55afa7e13af2f1b`，实际Lean退出0，5.1963秒。实际命令只检查导入原对象的审计输入，不带 `-o`；原生产源及原对象的哈希／字节／mtime_ns前后完全一致。实际受保护记录12565条精确保留。两个计数均来自本单元实际records，而非其他单元描述。

补充只读收据配置投影 SHA256 `cde28e9bbefdb9ec526c856cdc6769451e8664edb587cf498573169c2e0c9430`，8280字节，完整读取。收据对配置的精确before／after绑定、unit199、实际argv、源／对象、退出码、no-o／import语义、CPU52–55、8192MiB、4任务、mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 均一致；沿用已接受的 Lean `leanprover/lean4:v4.36.0-rc1` 钉死环境与保护记录。两次均自然结束、无超时、无清理事件、ownership_issue为null、进程组已结束。历史执行phase31原样保留；后续phase32或200活动不归到199未结束。

严格外层 `success=false` 与传输返回1原样保留，未改写为严格包装器通过。native02五条完整警告全部审阅：50行 `hsi` 未使用；82与142行对命题更偏好let而非letI；133行 `Fintype.card_fun` 未使用；133行 `←mul_assoc` 未使用，且其移除正向simp规则的附加作用说明保留。这些均不报告证明缺口。审计stdout为预期元数据输出，也不是源码错误。

两次stderr均为完整134字节、SHA256 `11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf`，内容是mathlib仓库有本地改动的路径提示，与已接受198同哈希分类复用；无新Lean错误。没有清理共享包、抑制诊断、修改风格或重编。手动AUTHORSTOP明确保留 FIRSTEMPTY=false、首成功原对象、5警告和严格false；这不影响实际内核0和完整递归AX的审查事实。

## 裁决范围与封存

`STATIC-VERIFICATION.json` 的227项本地检查全部通过，覆盖59个唯一精确绑定文件；补充 `RECEIPT-CONFIG-CHECKS.json` 的19项检查全部通过。这246项均为本地证据核验，本轮Lean调用为0。

最终数学陈述仅为：在实际配对样本律 `pairedLaw n μ` 上，对可测实值g与t≥0，配对差值向量的严格自归一双侧事件概率至多 `2*exp(-t²/2)`，并含交换与积分桥的三个辅助定理。n=0、零能量、t=0、原子法则和阈值等号边界保留。原单样本上尾、幽灵好事件质量、实际样本运输、原W/V规范化及G_y补集付款不由此自动闭合。

完整读取只读p51并核对S10／S11范围；p54修复、外部Shao–Zhou／Jing–Shao–Wang归因及124非前置条件均保留。本轮不作新颖性或根定理完成主张。没有关键数学或机器证据缺口。自身两次PowerShell解析失败与一次大小写JSON读取失败均为只读／执行前工具问题，已保存于 `LOCAL-FAILURES.json`，不涉及源或服务器修改。

完成后释放本角色全部写入、执行与子实例权限，运行计数全0。下一步由父级按既定流程接收本精确资格并选择后续依赖；本报告不创建持续运行机制。
