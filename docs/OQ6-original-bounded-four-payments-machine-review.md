# 207 精确61行源码的独立最终审查

STATUS: CORRECT

本次最终结论为 `qualified=true`、`machineChecked=true`，只绑定 `Shao.OQ6.OriginalBoundedFourPayments` 的精确新61行源码及其首个原始对象。已合格SOURCE审阅按原封印复用；本次独立完整阅读全部233行实际TYPE、完整62行所属审计源码、既有执行器和有关准备、规范化、回执投影逻辑。没有重审旧生产者证明，没有重跑Lean或公理检查。

## 精确证据对象

- 新源码SHA256：`7c2d9c530c44479e6e27017b284a42626c3547a8805af897b031a288e74c6d1a`，3112字节、61LF；服务器mtime_ns为 `1793016880054487894`。
- 首个原始O SHA256：`e075819ac5170bc38fb95dbdcb2eadf625451d46c5d8e4fcac765010fd9862a1`，130760字节；mtime_ns为 `1793016922578370202`。
- 已有独立SOURCE清单SHA256：`d599280b66685428d7e99e0e990a4c377dc99eb82a4d1878f3a3eaeff52ea9fc`，1834字节；其6项载荷全部精确读回验证。原SOURCE报告、逐行覆盖与冻结合同保持原字节。
- 完整实际元数据SHA256：`7b3d79f05280e97583346c2d4c9aef731d5d55ba84c7976e5971a30a10bc06d6`，22071字节；摘要SHA256 `859b0eef03f9f824c1448cbe55dc4a0639cbd7859ca4566999f17597e45d9ea0`，4440字节；服务器绑定SHA256 `a638904acc46360b6ea7f6b45dc514d0955ba21fbf8d39a805214bb8868861e8`，2745字节。

## 完整实际类型、宇宙与捕获核对

唯一实际所属常量为公开定理 `Shao.OQ6.OriginalBoundedFourPayments.eventually_original_boundedPolylog_four_payments`，`constantKind=thmInfo`、证明体存在、宇宙参数仅 `u_1`。实际所属总数1、定理1、非定理0，故所需非定理FULLVALUE义务为0；该计数来自实际模块索引输出，而非命名空间或源码声明数猜测。

全部233个实际TYPE行已完整读取，未使用类型摘要替代原文，亦未省略重复实例展开。1–62行保留任意 `Ω : Type u_1`、同一个可测空间实例、概率测度μ、g可测及二阶可积、零均值、二阶矩等于1，并保留C、a、M非负和t0正。实数的拓扑、范数、积分、乘幂和序结构均为相应规范实例；没有隐藏的额外数据或假设参数。

63–67行先是实数c的存在量词及c>0，然后是在自然数atTop上的最终n，再在该n内全称量化r和w。68–83行保留r联合可测与μ.prod μ下可积；84–107行保留两个方向的几乎处处典范积分条件；108–119行保留w几乎处处非负和原多对数高度；120–149行保留w平方可积与平方矩≤M；150–165行保留完整乘积包络及逐点对称性。166–183行保留任意实数y、y≥1以及精确 `remainderWindowScale (tailScale M) t0 * n^(1/6)` 上界，未增加或删除边界条件。

184–194行左端是同一 `sampleLaw n μ` 的实值测度作用于 `projectionGood n g y` 补集，再加同一样本律、g、r、y的 `remainderPayment`。样本空间为 `Fin n → Ω`，使用同一个mΩ生成的乘积可测结构，没有测度或样本律替换。195–232行右端精确为 `(exp(-c*n)+4*exp(-(y*sqrt n)/2))+9*exp(-boundedPolylogMomentOrder t0 n)`；负号、实数强制转换、分母2、系数4和9均准确。233行关闭原自然数atTop过滤器。没有意外捕获n、r、w、y到c之前，也没有把最终量词移到r/w/y之后。

先前完整SOURCE证明审阅已经核对：205先取c，197与n≥4交会，206精确集合等式改写补集，`.2.2.2.1`取五项右结合合取的第四项9倍付款，最后实数不等式相加。此证明及其假设、窗口、作用域已按精确旧SOURCE清单复用；本轮实际TYPE忠实表达同一冻结声明。

## 全模块所属、公理与原始输出

审计输入SHA256 `317f5febdaee98779d67df46bde89023fd12b9dc933a84c295eaa2f9fb767804`，2767字节、62LF，已全文阅读。它从已导入锚定理的 `env.getModuleIdxFor?` 得实际模块索引，遍历全部 `env.constants.toList`，只按实际模块索引相等选择所属；没有命名空间前缀筛选。对每个实际所属调用递归 `Lean.collectAxioms` 并检查白名单，打印完整TYPE，并对defn/opaque输出所需完整VALUE。实际仅发现一个thmInfo，因此没有漏掉任何已出现的非定理VALUE义务，也没有要求打印庞大定理证明项。

唯一实际所属的递归公理为propext、Classical.choice、Quot.sound，各出现一次，无额外公理。名称组件还原、宇宙参数、证明体存在、COUNT=1以及TYPE行数均已独立派生核对。

使用元数据中的原始JSON行、完整TYPE正文和COUNT行，在内存中逐字重构整个原始审计标准输出：19301字节，SHA256 `9767eb855368ba9da1e36794a0b60741a55cc62d86f83eaef9fb3b9933e963e4`，与元数据、摘要、服务器绑定和审计回执投影完全一致。没有把原始日志写入本地工作区。

## 首原始对象、严格标记与执行保护

原生首检receipt SHA256 `fd8dd1cba3dad40b3c7989c8f66c03af282fc3ac64acbdeed4cdb98ad5ce2988`：实际Lean RC0，4.822979094460607秒，源码标准输出0字节，源码错误0、警告0。原生检查前O不存在；生成的首O和后续元数据/审计准备/手动冻结中的O在路径、完整SHA、字节数和纳秒时间戳上完全相同。

同首O审计receipt SHA256 `ca685ead968cfc6ae4312ee39b3c9b7c34217c501910507c9c7a809a667f22e3`：实际Lean RC0，5.285180404782295秒。命令无 `-o`，只导入同首O读取实际模块元数据；实际配置将该源码和O指定为 `FULL_SHA_BYTES_NS`。规范化步骤还确认原生O等于审计前后保护映射中的同一O。

两次外层严格执行器结果及其传输exit_code均保留原值：外层返回1、`strictWrapperSuccess=false`；原生 `FIRSTEMPTY=false`。两次标准错误均为同一134字节Lake仓库本地变更提示，SHA256 `11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf`；其完整文本已读并重新核对字节哈希，不含本源码诊断。原生准备配置的 `require_empty_stdout=true`，审计配置为false；不能把两者一律写成false。手动AUTHORSTOP明确冻结成功首O并保留严格false与Lake提示，未清理提示、改写首检或重编译。

语义回执投影SHA256 `41ca6bb61c8049026fc41bbc4f0f0edccdd61798637887a61180b51525506b73`，13590字节，与原有成功传输结果中的JSON语义逐项一致。实际RC序列为[0,0]；所有进程组自然结束，无超时、清理信号、所属身份错误、后处理错误或残存进程。这里使用的是已完成回执与实际结束证据，没有用历史DISPATCHED标记代替运行事实。

既有执行器SHA256 `3b0efaddec8746510e5acdb3247578fa2cc9d0cda85188ee57023ba512a755fe`，11802字节，已全文阅读。执行器核对自身和配置哈希、精确源码字节、无禁用项、固定CPU与所属锁；无旧请求自动重放。保护映射前后相等，原生13698条、审计13710条。旧接受记录复用封印SHA并核对当前字节数/纳秒时间戳；新输入及指定源/O使用完整SHA模式。审计的 `allProtectedInputBindingFullSHA=false` 保留，不能误称所有旧记录均重新完整哈希。配置模式计数与实际快照条数相差1，由既有执行器在快照前加入配置自身这一条完整SHA记录解释。

两次均在ROOT_OQ56_38、CPU52–55、原OQ56单重锁下执行，原生限制8192MiB和4作业未变。新鲜准备与实际启动资源记录均符合80GiB项目进程预算、180GiB总量门和200GiB硬上限；两次启动的实际内存加8GiB均低于180GiB。外部CPU0–23及80GiB保护不变，没有新执行包装器或旧生产者/叶子AX重放。

## 最终作用域与释放

本结果仅合格原S15有界乘积、多对数高度背景下全部四项付款总界。完整SOURCE忠实性、全部新实际TYPE、实际所属覆盖、递归AX及首原始对象证据已闭合。它不合格DC加扰动背景、完整S12比较、S14、全根扩展或整个OQ56；总根仍OPEN，OQ3不唤醒。

本次仅写 `final-review-01/final-machine-source61-01/`，未修改已封存SOURCE、作者或机器证据。没有服务器、网络、Lean、AX、上传、Git、API或子代理调用。指定配置仍为gpt-6.1-sol/xhigh；实际配置和input/cachedInput/output/reasoningSubset分项遥测不可得，分别记null。
