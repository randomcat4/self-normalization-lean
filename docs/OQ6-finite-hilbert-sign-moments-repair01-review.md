# 单元185修复01独立续审

状态：`REPAIR01_AFFECTED_REVIEW_COMPLETE_NATIVE02_FAILED`，`qualified=false`。本次仅续审精确修复稿的全部受影响范围，并复用原上下文已经完整读过的未变范围。精确新source为SHA256 `996ed0366cff7d89d37365d6e358d5b40027a863d811efaba58bb0f292fce7e6`，40456字节、811 LF；修复作者已由SHA256 `56beb2a70d42c03d67ecd552bf0009df43ea096153c43adec022e5c2b4b6950a` 的RELEASE0释放。实际第二门已RC1、3errors、无对象；形式源码仍不完整，不能认证。完整失败分析见native02-disposition.md。

旧source `f5a30c5f…33fd6` 的首门确实RC1、17errors、无对象、无超时、所属进程组全部结束。诊断绑定文件SHA256 `6c3876d39e3a13a51b63ddabaf2f25dd706dd31897fb020da2d2ca067a482a76`，原native receipt为 `cfa45c5693f433586b990769db2203fe4f62a7e2a820f17dda84dc2296a0ac1c`。5080条保护记录相等是父级实际执行证据，不是本审阅者运行的检查。

## 对旧报告错误的明确更正

原source-review.md第34–46行覆盖说明中，我把旧pairCount的两个indicator都解释为同一Σr的求和体。这一源码作用域判断错误；实际旧文本没有把加法整体括入求和体，第二indicator中的r未绑定，首native明确报告第36行Unknown identifier r。因此旧报告不能证明原source在这个定义上语义正确，更不能证明它能展开或通过内核。旧文件按字节保留，本补充明确取代该处旧scope判断及其受影响消费者的源语义结论。

修订05在修复使用前冻结的实际新值是：

```lean
∑ r : Fin k, ((if (t r).1 = j then 1 else 0) + (if (t r).2 = j then 1 else 0))
```

显式外括号使 `r : Fin k` 真正作用于两个indicator；n,k,t,j是完整外层telescope，第二端点没有自由r。它实现原推导D4–D5的总端点重数，而非覆盖一个先前已经内核接受的定义。t(r)=(j,j)时该位置贡献2；只出现一个端点时贡献1；k=0时计数0。

旧pair_sign_mean的头在证明体classical执行前也无法合成Decidable；新private头把同一个Prop指示的决策写成 `@ite ℝ (evenPairs n k t) (Classical.propDecidable (evenPairs n k t)) 1 0`。这不是添加一个Decidable前提，也不限制n/k/t。旧报告的源码级正确判断仍须受该真实RC1限制，不能用数学意图正确掩盖这些实际失败。

## 已完整续审的范围和交互

已完整读repair-reasons、source-to-statement、8903字节完整diff、freeze-comparison实质字段、affected-scopes的8个完整old/new声明与18处变更/类型/chronological scope，以及全部17条原错误和对应disposition。有效freeze05的SHA256为 `b3003fbe90532dd2ce6fddd35b4ec88f74f051ff119d53ab5cd42016286557b3`；freeze06为 `8c0d0ad1eb3309db1d906bf0e856c835b8187c1915f3524b4931a02d7ba8f20a`；完整不可变系数proposal为 `ced5b675c0bf693a81da94d2679063ebc5745e33041e09aed8d971ad9a101b58`。它们的完整正文均已读。

| 新source行 | 完整续审对象 | 独立判断 |
| --- | --- | --- |
| 36 | pairCount完整新值及r作用域 | 上述显式求和体正确计算两个端点重数。未变evenPairs仍逐坐标要求该完整重数为偶。 |
| 97–117 | pair_sign_mean完整头/体 | e仍逐坐标等于修复后的pairCount。hreg需要把每个位置的两个indicator指数先作加法，再用pow_add分解并交换有限积；native02显示源码最后的simp尚未证明剩余单位置聚合恒等式，特别须保留重合端点的两次出现。随后全偶/非全偶分支的0/1化简含义正确，不依赖两个Decidable实现归约相同；整条实际证明仍待修复。 |
| 119–219 | hilbert_even_domination完整证明 | hsq初始化中的s、i、j及两个membership仅在该子证明；实际展开产生的inner(vj,vi)先用real_inner_comm对齐，再作交换环代数。其余完整配对展开、两次符号平均、全偶支配与绝对值Cauchy比较均保持。两处hps实际消费修复后的pair_sign_mean，仍得到相同0/1系数。 |
| 512–535 | rpow_tangent完整证明/三分支 | 仅在1处的导数、两个割线接口及其正分母条件正确。新增rpow_eq_pow使literal函数与库Pow实例明确相同；不新增在0处求导或x>0的假设。两个hnum只在其分支内，由同一等式转回原literal陈述后线性算术。 |
| 537–609 | cubeMean_rpow_le完整证明/两分支 | B=0仍由正权与非负性推出所有f(s)=0，hr给r≠0；规范化后才使用zero_rpow。B>0之后才定义g=f/B，hscale逐项的mul_rpow由hBpos.le和hg s支付，允许g(s)=0。数据值未变。 |
| 611–649 | cubeMean_Lp_mono完整证明 | r=q/p、g=f^p未变；两次复合前明确转换到实际Pow记号。点态底数f(s)非负、平均底数非负；p,q正保证指数除法合法。零底数保持允许。 |
| 654–729 | finite_hilbert_sign_moment_bound完整证明 | k/p/A/f原值和全量量词不变。hpow先转Pow，再用自然指数桥；native02显示该目标已被rw关闭，但随后rfl无goal而报错。hpowered两步规范化，使用hbase≥0和平方根平方；hroot只在其初始化中规范化已完成的hpowered，使用hU≥0、hbase≥0和hp>0反射实幂不等式。不存在能量正性前提；该多余指令仍需源码修复。 |
| 731–762 | radMeasure_atomic完整证明 | hLaw完整约化Bool真/假后才展开原边缘law；native02显示1/2与2⁻¹及乘法顺序仍留有未证目标，原ring指令没有闭合它。新的显参正是当前E上的原indicator系数，前后有限和/积所用函数一致；Fin/Bool有限、Fin可判等、ENNReal交换半环条件成立。E/hE仍为pi_eq给出的任意可测矩形，不假定成员事件为真/假；hLaw仍需源码修复。 |

未变消费者的交互已核：hilbert_even_bound以相同头消费新的整向量偶矩支配；有限主界经修复的Lp桥及偶矩界取得相同结论；rad_integrable_and_integral以相同测度等式消费修复的原子测度桥，pathSum_signPath与最终rademacher主界恢复相同moment。没有因private定义修复改变任何公开数学前提。

## 实幂实际实例核对

直接读取已钉死Mathlib原包 `rpow-factorial-choose-composition-primary-source-packet.json` 中 `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`（文件SHA256 `f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd`）的真实定义、实例和定理：

```lean
namespace Real
variable {x y z : ℝ}
noncomputable def rpow (x y : ℝ) := ((x : ℂ) ^ (y : ℂ)).re
noncomputable instance : Pow ℝ ℝ := ⟨rpow⟩
@[simp] theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl
```

该桥对任意实底数/实指数无额外前提，证明就是实际Powℝℝ实例的反身性。修复中的指数r,p,q、1/p、1/q、实数2均取这个实例；自然数k次幂另由 `Real.rpow_natCast` 连接。这里明确是从完整主源核对的类型/实例，仍不冒充尚未收到的实际owner TYPE。旧失败体现了受限rw/simp不会自动把所有literal rpow重写成库定理的Pow模式；新源码在对应实际失败位置显式使用此等式。

inner symmetry的主源 `real_inner_comm (x y : F) : inner ℝ y x = inner ℝ x y` 在真实实内积空间上成立，包括d=0。两条ConcaveOn割线接口的完整原声明/环境和第1版独立scope补充继续有效，新行号分别520/530，其导数与分母义务未变。

## 不变证据复用与边界

复用 `parent-repair01-source-intake.json`（SHA256 `d1e5a412fd31c5bf1a833304c6667adddce57f229de59b37a31bba8201dd2db4`）的16工件、34有效冻结头、15有效值、8完整old/new声明、18变更span及无损前缀、12未变证明体的精确绑定检查。它只作为静态输入证据。33个其他头、14个其他值、5公开定理头、8公开定义值、prefix03/suffix、4转换函数、2uncurry函数和23个原局部let按冻结比较保留；没有重审12个不变proof，也没有重跑其旧检查。

n=0时Bool函数空间仍唯一空路径，平均质量1；k=0时新pairCount全0且空积1；d=0实内积/范数均0。公开q≥2保证主界正指数；能量只要求非负，A=0仍在rpow复合/平方根/保序的合法域内。全实q、固定常数2与维数无关界均保留。

范围继续仅为p44§1(3)的固定向量符号矩及同一真实radMeasure积分版本。p51 S18的Shao–Zhou Lemma6.1外部归属、p54条件p矩收敛/统一有界修正和严格好事件余量不变；无183/184依赖，无根闭合/新颖性主张。C2/C12/OQ56 OPEN，OQ3 PAUSED_BY_USER。

本次受影响范围的数学意图与接口条件未发现新的前提缺口，但第二次真实native已证实三个实际源码缺口，故形式完整性结论为 `INCOMPLETE_NATIVE02_RC1`。接下来只需独立续审pair_sign_mean、finite_hilbert_sign_moment_bound、radMeasure_atomic的实际新proof-only delta及其受影响scope，复用其余已读范围；不把第二次失败伪称部分或全部内核通过。实际全部owner及每owner TYPE/非定理FULLVALUE/递归AX仍未取得；owner数UNKNOWN，不用34源码声明或490静态map条目代替。

唯一写范围为本新增目录；未改作者source、旧报告或共享文件；执行/server/network/Git/upload/cache/children/locks均0。
