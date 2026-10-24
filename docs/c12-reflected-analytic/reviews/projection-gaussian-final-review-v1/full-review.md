# 单元45、46独立最终完整审查

**STATUS: CORRECT**

两份最终冻结的局部标量证明均正确。该结论绑定下表确切源码、定义、对象及作者服务器凭据；不将条件代数引理视为原始 Brownian 完成核身份或完整局部余项结论。实际读完两个最终模块的全部证明、全部23个所属声明完整实际类型和全部5个非定理完整透明值，包含7个生成辅助定理；未用抽样、缩略类型或字典压缩替代阅读。

审查者为新鲜独立 FINAL 上下文 `/root/projection_gaussian_final_review`，按明确配置使用 `gpt-6.1-sol/xhigh`，与作者分离。审查期间仅写本报告目录，未修改生产源码、冻结文件、既有证据、共享文件或 Git；未运行 Lean、安装工具链或重放任何通过的旧门。使用 math-theorem，未启用 math-ultra、目标、计划任务或子代理。Windows 文件处理采用 UTF-8 明确读取和 LF 写入，遵守 windows-gbk-utf8 防护。

## 1. 确切版本及完整覆盖

| 单元 | 45 ProjectionOvershoot | 46 GaussianWallEnvelope |
|---|---|---|
| 最终源码 SHA256 | `153b3fb011ea51f87b2d19ae1f76aa4d562e94346cfc47e3f4f5bf021f29b5cc` | `5f8b3966e314c88f5091a5e7bf7353be0ec0cae4d6cf2842b83bc61a436d06d9` |
| 冻结 SHA256 | `353adfaadf4b485c883283d63ffce89126d69feaa3ffce41b5fa103c1e52e33a` | `1eaed93b0eec51221449579792e39d681f45d04732eb6d7afcb536221a40f005` |
| 对象 SHA256 | `47df27f6230b781136a919ed24a64665a689da34c600319506da8f96cb799f3e` | `54a9bd090e395db8d447e3cb095ef7a6e6ab9ec482a95150e20fe3a77a657e45` |
| 作者凭据 SHA256 | `88415394800873ee0c124ca33ead01ae4c2a9f144c5cfa97e35841481339eab6` | `682b51e94b66001559cb0639567467b6d538fa0844c84e2a1fedf15d3f2505c7` |
| 实际所属集合导出计数 | 16：12定理、4定义；5公开定理 | 7：6定理、1定义；6公开定理 |
| 成功内核尝试 / 公理审计 | attempt003 / 0退出 | attempt002 / 0退出 |
| 源码编码 | UTF-8无BOM、LF、CR=0，6125字节 | UTF-8无BOM、LF、CR=0，4117字节 |

计数由实际 owner map、实际类型导出、完整定义值导出三者逐名一致性重新导出，不沿用描述性计数。合计11公开定理、18实际定理、5定义、23实际所属声明。4+1个定义值完整；全部7个生成项为定理，没有未审生成定义、私有定义或未知 kind。

完整冻结比较包含 imports、noncomputable/namespace/open 上下文、每一个公开定理的完整量词/假设/结论，以及每一个透明定义的完整值。两个最终版本及所有保存的失败尝试均与冻结完全一致；只有证明体不同。完整实际 elaborated 类型逐一与源声明核对。机器可读报告逐声明记录类型块/实际类型哈希、值块/实际值哈希、具体审查、来源及递归公理集合。

## 2. 原文到冻结陈述的语义

只读原文为 `C:/game/shao/current/c12/supplement.tex`，整文件 SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。完整阅读4192–4253定义/小步Taylor上下文，以及4319–4398投影与局部高斯引理及证明。

4192–4206把 f 定义为严格 Brownian bridge 存活概率；墙上或墙外完成延拓为零， reachable 零能量内部完成为一，终端不同端点的零方差约定另列。4208–4220给出监测墙符号、d、D、单壁端点距离及 P、P_b。4234–4242中的真实补偿余项包含完整的 `b-b²d/T` 项，且小步Taylor估计有独立的解析义务。形式文件没有暗中证明这些尚未建立的物理身份。

单元45对应4319–4358的**归一化零未来完成标量部分与条件预算传递**。在源几何下取 η=sign(b)、B=|b|、u=a−ηy、e=η(z−y)、G=ηf_y、F=f；则0<u≤B、e<u、B²≤T/2及T>0。源投影p=ηu，δ=B−u。η²=1使真实线性/时间补偿化为 `(B−B²e/T)G`，`c=1−(B+u)e/T`，`D=1+|e|/sqrt T`，`O=−δcG`。保留负号、墙方向、交叉项和时间补偿。`zeroFutureRemainder` 明确仅为未来完成值零时的表达式 `−F−(b−b²e/T)G`；它不声称实际完成值已经识别为零。F≥0和投影三次Taylor预算 `|R_u|≤K u³` 都作为完整显式前提保留。取 K 为原文非负的常数乘 T^(−3/2)D³ 才得到原文该步的预算；本模块不供应这一解析前提。

单元46对应4360–4393中**逐壁高斯包络比较**。令w为该墙初始距离、e=ηd，e<w即终端距离w−e>0；B=|b|，M=B+e_+，r=(w−M)_+，单壁包络为exp(−r²/T)。原文Π是监测墙上的求和，模块仅定义一项并给出初始轮廓、增量轮廓、正未来时间反射亏损的比较及击中值。它没有声称完整的ℓ余项组装、全壁和、q³支付、零能量实际亏损或原根定理已经闭合。未来比较显式保留 `0<T−b²`，避免将原文 reachable 零时亏损零的独立分支混入正时反射公式。

## 3. 单元45完整证明核对

设 A=1−ue/T、c=1−(B+u)e/T、R_u=−F−uAG。

1. **projection_factors_bounds**：由0<u≤B得到B≥0及u²≤B²。e<u给ue≤u²≤T/2，因此A≥1/2。又(B+u)e≤(B+u)u≤2B²≤T，故c≥0。设s=sqrt T>0，s²=T及B²≤T/2推出B≤s，因而B+u≤2s。由−e≤|e|得到−(B+u)e≤2s|e|，按T=s²>0相除，故c≤1+2|e|/s≤2(1+|e|/s)。完整源码中每次乘法和除法的符号条件均具备；末端纯加法整理无隐藏假设。
2. **projection_factor_identity**：展开后 `(B+u)A−uc=B` 完全消去同分母项。无除以u或A的操作，任意实数参数的冻结量词成立，包括总定义的T=0。
3. **zero_future_remainder_projection_identity**：展开 `R_B=R_u+O` 后，只需 `u²+(B−u)(B+u)=B²`。F及完整时间补偿都保留。这个任意参数代数等式没有偷用物理概率身份。
4. **projected_positive_slope_budget**：G≥0时，`−|R_u|≤R_u=−F−uAG` 与F≥0给uAG≤|R_u|；G<0时max(G,0)=0，目标为0≤|R_u|。无须u、A、T预设符号，强量词真实成立。G=0归入第一分支。
5. **projection_own_negative_budget**：令G_+=max(G,0)≥0。由上一步及投影预算，按u>0取消得到 `A G_+≤K u²`。恒等式给 `uc=(B+u)A−B≤(B+u)A`；乘G_+并用B+u≥0，再按u>0取消得 `cG_+≤Ku(B+u)`。δ,c≥0时对G分正负得到精确等式 `max(−O,0)=δcG_+`。因此

   `|R_u|+max(−O,0) ≤ Ku³+(B−u)Ku(B+u) = KuB² ≤ KB³`。

   最后一步使用K≥0和u≤B；中间消去平方项精确，无损失常数。等号击中u=B使δ=0，K=0、G=0和任意负e均覆盖；不假设G≥0，也不要求投影p属于剩余标签。

完整公开类型及四个透明值均与冻结逐项一致。生成辅助项属于同一因素界证明的实际编译 owner，完整泛型类型分别为非零数字、非零乘积/幂和特征零转换；它们不编码新的源问题假设。逐项明细如下，全部类型已完整读而非只看名称：

| 生成声明后缀 | 完整类型的数学内容 | 审查 |
|---|---|---|
| `_simp_1_1` | Zero α、OfNat 2、NeZero 2 ⇒ 命题2=0等于False | CORRECT |
| `_simp_1_2` | Zero α、OfNat 3、NeZero 3 ⇒ 命题3=0等于False | CORRECT |
| `_simp_1_3` | Zero α、OfNat 4、NeZero 4 ⇒ 命题4=0等于False | CORRECT |
| `_simp_1_4` | 无零因子、a≠0、b≠0 ⇒ 命题ab=0等于False | CORRECT |
| `_simp_1_5` | MonoidWithZero、IsReduced、a≠0、任意Nat n ⇒ 命题a^n=0等于False | CORRECT |
| `_simp_1_6` | GroupWithZero、a≠0、任意Int n ⇒ 命题a^n=0等于False | CORRECT |
| `_simp_1_7` | AddMonoidWithOne、CharZero、任意Nat n ⇒ 命题(n: R)+1=0等于False | CORRECT |

## 4. 单元46完整证明核对

1. **wall_product_lower_bound**：B≤B+e_+且e≤B+e_+给 `r≤max(w−B,0)` 与 `r≤w−e`。r及max(w−B,0)非负，正确方向相乘得到 `r²≤max(w−B,0)(w−e)`。接口中的hw虽然对这一小步冗余仍被完整保留。
2. **increment_profile_le_wallEnvelope**：完整消费35的 `incrementProfile (u v T b)=exp(−max(u−|b|,0)v/T)`。代入u=w、v=w−e后应用上项；取负按T>0相除，再由exp单调性。分母、负号、正部及参数顺序正确；P_b没有反射亏损的额外系数2。
3. **initial_profile_le_wallEnvelope**：`max(w−|b|,0)≤w`，因w−e>0可乘，故r²≤w(w−e)。同样取负、正分母及指数单调性即得初始轮廓界。
4. **future_reflection_deficit_le_wallEnvelope**：设P=(w−b)(w−e)≥0，S=T−b²。b≤|b|+e_+且e≤|b|+e_+，配合w−b≥0、w−e>0，得r≤w−b、r≤w−e，因而r²≤P。0<S≤T保证

   `r²/T ≤ P/T ≤ P/S ≤ 2P/S`。

   最后一项用P/S≥0乘1≤2。取负及exp单调得到 `exp(−2(w−b)(w−e)/S)≤exp(−r²/T)`，系数2和严格正未来时间均完整。闭墙等号w−b=0覆盖；S=0不在定理范围。
5. **crossing_wallEnvelope_eq_one**：w≤|b|≤|b|+e_+使r=0，故exp(−0²/T)=1。b任意符号、等号击中均覆盖。代数上任意T均成立，包括Lean全定义除法的T=0，但没有把它推广为零时实际反射亏损公式。
6. **wallEnvelope_bounds**：exp始终严格正；T>0与平方非负使指数≤0，故包络≤exp0=1。w、B、e任意，不含隐式正距离条件。

六份完整实际定理类型和唯一完整定义值均与冻结一致。46不调用45任何专门标量定理，仅通过它导入35；两个新模块的命名空间及接口没有相互覆盖问题。

## 5. 依赖复用与服务器凭据

35 `HalfLineTaylorSegment` 的既有合格独立完整审查 `0ff0cc92f656a87761ab28d636b7c4d141b13f4d0c89ad874e0273fec9f6fae7` 状态CORRECT、独立新鲜gpt-6.1-sol/xhigh；绑定源码 `45e62ea4cdf287373cf774167dc78e90e27ae682017a650a715e33e6b32098ea`，对象 `a9ae0eb927304b1bea8378c3f92c7fc41cfaf7180de1a3a6528268ff80640071`，作者凭据 `eb8bb14cd2de34aea31c2360596a1202266ac92bd992529f972c771fbc98def7`。此次只完整核对消费的incrementProfile源定义、完整实际类型和完整透明值，并核实服务器当前源/安装对象/合格输出对象 exact 相同；复用其余已合格证明，不重审或重编旧模块。45虽导入35，不消费35专用声明。

只读服务器观察时间为 `2026-10-24T10:04:31.275996+00:00`，凭据补充绑定为 `2026-10-24T10:05:26.643273+00:00`。工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71` 当时已推进到分支 `author/c12-projection-overshoot-v71`、HEAD `73ac2a64924be782f630ef07391ace1f06ffbeaf`；记录中的原base `467e398d5468d0614ba0ae97406cd3a5df6c4a69` 经只读Git检查仍为祖先。分支推进不影响本审查绑定的45/46源码、快照和对象。

实际观察确认：

- 两个当前生产源码、各成功attempt源码快照，均与本地最终源码哈希相同。
- 两个输出对象和当前安装对象都与各自凭据对象哈希相同。
- 两个远程receipt文件本身与本地凭据逐字节相同，kernelExit=0且auditExit=0；全部列明的源快照、失败/成功日志、OwnedAudit源、owned-audit.json、完整类型/值导出和审计日志均匹配凭据哈希与字节数。
- 完整实际类型及完整值逐块原文出现在绑定的OwnedAudit日志中；日志声明头集合恰与实际owner map一致，数量分别16与7，无导出替换或缺项。
- `OwnedAudit.lean` 使用 `env.constants.toList` 遍历全部环境常量，以 `env.getModuleIdxFor?` 的真实模块归属选择目标，而非命名空间前缀或手选公开表。对所有所属声明逐个 `Lean.collectAxioms`，递归审计定理及定义，只允许 `propext`、`Classical.choice`、`Quot.sound`；全部23所属项均在白名单内。公开表仅另作存在性计数，不限制实际审计集合。
- 源码没有sorry、admit、新axiom、unsafe或native_decide。固定 `leanprover/lean4:v4.36.0-rc1`；实际mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`；包链接为既有只读 `cache-overlays/shared-v34/packages`。日志的既有mathlib本地变更提示来自接受的缓存视图，不构成静默版本升级；本次未写缓存。
- 原作者检查按CPU14–17、c12-heavy.lock、-M8192、-j4执行。审查者仅发出两次只读观察请求，无Lean命令、无锁租用、无重放。

## 6. 失败历史与前提稳定性

45 attempt001/002的完整日志及与最终源码的完整差分已读。修正仅涉及：把zeroFutureRemainder同样展开到目标的绝对值中；用正确的 `le_of_mul_le_mul_left` API取消正u；以明确加法单调性、加非负1及ring处理分式/左右关联。没有变动F≥0、K≥0、0<u≤B、T>0、B²≤T/2、e<u或投影预算，未弱化结论。最终attempt003只有无效后继tactic的lint提示，没有错误。

46 attempt001的失败仅在 `P/S≤2P/S` 上，自动归一化未解出；最终attempt002改用明确的非负乘法单调性并整理等式。所有六个完整头、上下文、导入及唯一透明值与冻结完全相同。最终日志只有未使用前提/顺序tactic的lint提示，没有错误。没有删去严格正未来时间或加入额外前提。全部失败快照和日志原地保留。

## 7. 可接受范围与剩余义务

**可接受**：45的4个定义、5个公开定理及7个生成辅助项；46的1个定义及6个公开定理，均为该exact source版本的合格独立完整审查CORRECT，并可复用所绑定的服务器内核/全所属递归公理成功凭据。

**继续OPEN**：实际Brownian killed-kernel/反射概率身份；区间完成核的Taylor正则性与解析预算供应；条件zeroFutureRemainder到实际完成余项的适配；全壁Π与ℓ的完整局部余项拼装、大小步及可达零时间分支。这里没有新颖性、正超调分离项、C1/C2或其他原始根群闭合声明。OQ3按用户暂停保持暂停。

本审查无关键缺口，不请求改变冻结前提或源范围。作者与审查者的字节绑定及作用域限制必须一起保留。用量接口未暴露input、cachedInput、output、reasoningSubset计数，全部记录null；不把原始token或信用估计解释为订阅百分比。

完整逐声明结构证据见同目录 `full-review.json`；只读请求/响应和精确服务器对象图保存在本审查目录。审查者最终无生产写入/执行租约、无在途任务；显式释放记录见 `writer-release.json`。
