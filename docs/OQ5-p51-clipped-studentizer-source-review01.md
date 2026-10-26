# 单元208完整独立源码与证明审查

STATUS: CORRECT

结论：本次读取的完整新源码在冻结的条件有限S12范围内，陈述忠实，证明推导完整，未发现关键数学缺口或具体的精化错误。`sourceAcceptedForNative=true`。本审查没有编译或服务器调用，`machineChecked=false`、`qualified=false`；新模块的实际生成所有者、内核接受的完整类型与非定理值、递归公理依赖均尚未知晓。这里的 CORRECT 是完整源码审查裁决，不是机器验收结果。

审查员为 `/root/oq56_clip208_final_review`，不是证明作者；本上下文是按 gpt-6.1-sol / xhigh 指定配置启动的新上下文。模型与努力级别的额外运行遥测不可取得，输入、缓存输入、输出及推理子集用量分别记为 null。写权限仅限本 `final-review-01` 目录。服务器、网络、Lean、公理检查、上传、Git、API发布及子委派调用均为0，其他作者和源文件改动为0。

## 精确审查对象与上游封签

完整对象为 [ClippedStudentizer.lean](<C:/game/shao lean/drafts/oq56/unit208/author-01/stage2/ClippedStudentizer.lean>)：SHA256 `a8bffbabb649cdc788b58517a89185691f72de92776a882f3b9ffdcddc0b748b`，11786字节，264个LF，CR=0，无BOM，恰有一个末尾LF。已读第1—264行，包括全部上下文、4个定义、8个定理的完整证明及结尾。

先于实现的 `parent-freeze-v1.json`（SHA256 `32f3009afe66736624c0601121187f7184900267496b4edf6f1933dfb8bb0591`，8900字节）及 `parent-frozen-data-contract-v1.json`（SHA256 `d1d5b55128fd930a6be5f6149996d828e6fc5ba44333ad774ada714823812f7b`，9779字节）均精确匹配。12项全局头／定义右端、唯一导入、前言和结尾逐字相同。实现没有改变前提、量词、零分支、预算或比较目标。

阶段2清单的7项载荷及阶段1清单的9项载荷均按**各自清单所在目录**解析并验证SHA256和字节数；两次作者自然释放中的零状态得到确认。父实例完整源码接收记录精确匹配。全部静态记录及路径解析见 `STATIC-BINDING-VALIDATION.json`，当前导出的69条本地绑定均验证成功。该数字来自本次绑定表，不是完成比例或机器声明数。

既有196／197只复用合格源码、最初成功对象及独立审查封签；本次没有重审其已接受证明，也没有重跑旧检查。196源码为 `bc64d3e1…502edc`，最初对象为 `372a8570…1bf8be3`；197源码为 `c0102fa1…2d95cc9`，最初对象为 `f733c223…970ffaf`。完整指纹见静态验证文件。所选实际TYPE及非定理FULLVALUE与各自既有实际所有者元数据逐项相同。旧元数据的历史 `qualified=false` 没有被改写；合格状态来自精确绑定的最终独立封签及父级合格证据。

Mathlib的四个承重平方根接口已核对固定版本包中的完整原始头及有效命名空间／绑定上下文：`Real.sqrt_nonneg`、`Real.sqrt_sq`、`Real.sqrt_pos`、`Real.sqrt_mul`。尤其 `sqrt_sq` 需要非负参数，`sqrt_mul` 需要首因子非负；新证明均实际提供相应符号事实。固定版本保持 Lean `v4.36.0-rc1` 与 mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。

## 逐项全局声明与完整证明

| 源码行 | 声明 | 完整审查结论 |
| --- | --- | --- |
| 12—13 | `studentizerClip` | 右端恰为 `max (-(min B (1/2))) (min d B)`，与S12标量式一致；定义本身对任意实数B、d全定义。 |
| 15—18 | `studentizerClipBudget` | 恰为S10的 `C0*((1+rho)*y/sqrt(n)+J/((1+rho)*y*sqrt(n)))`，使用实际196的J；未引入替代包络。 |
| 20—25 | `clippedCenteredDelta` | 对实际V=0显式返回0，否则裁剪实际196的受保护d；未加入好事件指示函数。 |
| 27—33 | `clippedCenteredStatistic` | 同一V=0分支返回0；非零分支使用实际W+D与 `V*sqrt(1+裁剪d)`。 |
| 35—82 | `studentizerClip_contract` | 下界、预算绝对界、绝对收缩及条件不动点四项均成立，详见下文。 |
| 84—97 | `studentizerClipBudget_nonneg` | 使用精确J平方和与实数除法非负性；n=0、y=0没有被省略。 |
| 99—107 | `clippedCentered_zero` | 精确复用196的d零分支定理，再展开两个新定义的同一守卫。 |
| 109—147 | `clippedCenteredDelta_bounds` | 按V=0／V≠0穷尽；正分母结论仅在V>0时提出。 |
| 149—182 | `centered_studentizer_factorization` | 从d的实际定义推导平方根分解；没有额外对称性前提或未满足的除法条件。 |
| 184—224 | `clippedCentered_comparison_on_projectionGood` | 保留显式逐点hDom与hLower，证明两分母严格正且相等，随后化简两个守卫商。 |
| 226—238 | `clippedCentered_denominator_bad_subset` | 绝对收缩乘以非负y²，保留严格1/4阈值与实际好事件，得到实际197坏集。 |
| 240—260 | `clippedCentered_comparison_exception_subset` | 在好集内按严格下坏事件分支；其余由全称hDom和前一定理排除不等。 |

标量证明中，令a=min(B,1/2)、c=max(−a,min(d,B))。B≥0给出0≤a≤B且a≤1/2，所以c≥−1/2、−B≤c≤B，得到前两项。若d≥0，则min(d,B)≥0≥−a，c=min(d,B)，故0≤c≤d；若d<0，则min(d,B)=d，d≤c≤0，取绝对值即得第三项。最后由|d|≤B提取−B≤d≤B，再按B≤1/2及其否定证明−a≤d；两次min／max均选中d。B=0、d=0、d=−1/2、d=±B及B=1/2的等号边界均包含在这些非严格比较中。

预算证明把实际 `residualEnergyJ` 展开成 `∑ i, (residualU ... i)^2`。有限和每项非负，1+rho、y、sqrt(n)均非负，两个分式及外乘C0因此非负。所用 `div_nonneg` 不需要分母严格正，没有把零分母消去；Lean实数除法的全定义覆盖n=0或y=0。这只是定义及非负性延拓，没有把原文n≥4、y≥1的概率适用区间扩张到这些边界。

全局界先得B≥0。V=0时，新偏差为0、预算界由B≥0给出、收缩由|d|≥0给出，而V>0与该分支矛盾。V≠0时直接使用标量四项合同。由1+裁剪d≥1/2，根号严格正；再乘明确给定的V>0得到实际分母严格正。证明没有声称V=0时分母正。

分解证明从V>0得到V≠0及V²≠0，只在这个守卫分支展开既有d，得到d=S/V²−1，其中S=centeredSq。`div_eq_iff` 的非零前提明确提供；由该等式和交换代数得S=V²(1+d)。hLower给出1+d≥1/2>0。使用V²≥0分解根号，再用V≥0化简sqrt(V²)=V，得到sqrt(S)=V sqrt(1+d)，其右侧严格正。此处没有调用需要核对称性的中心行恒等式；它证明的是既有受保护定义的代数后果。

好集比较使用196实际 `projectionGood_bounds n g x y hn hy hGood` 的第一分量取得V>0。虽然这个冻结声明没有另外要求C0、rho、y的符号条件，hDom本身已经推出B≥|d|≥0，足够调用标量合同。hLower与hDom使裁剪d=d；分解定理给出原根号分母正以及分母相等。最后用已证明的V≠0、sqrt(S)≠0化简各自守卫，等式成立。目标一直是源码明写的受保护商，未创造或借用一个不存在的全局originalT接口。

大分母坏集包含的证明，只把|裁剪d|≤|d|乘以y²≥0，故保留 `1/4 < y²*|d|` 的严格方向；同一个样本的 `projectionGood` 合取不变。例外集包含先穷尽好集与补集。在好集内，d<−1/2恰是197实际 `lowerStudentizerBad`；否则有包含端点的d≥−1/2，全称hDom在同一样本上提供逐点支配，前一定理给出商相等，与不等假设冲突。没有把坏集换成预算超阈值事件，没有引入概率或无原子假设。

## 局部命题、数据绑定与闭包

从新源码独立数得12个全局声明、40个 `have`、5个 `by_cases`、5个 `intro` 命令、1个 `obtain` 和1个显式证明lambda；这些均与实际源码映射一致。它们是**源码级**计数，实际生成声明数仍未知。`SOURCE-COVERAGE.json`逐项保存全部12项冻结头与完整块指纹、40项局部命题的完整类型／推断展开、每个分支和绑定作用域，不能拿这些记录替代实际生成所有者审计。

标量定理的17个局部事实仅涉及B、d及已证明的序关系；hd的两个分支及不动点的hLower、hDom、hBhalf均在各自词法作用域内。预算定理的hsigma、hJ是命题；唯一lambda `fun i _ => sq_nonneg (residualU n r x i)` 绑定 `i:Fin n` 与其全集成员证明，只捕获n、Ω、r、x。没有构造新样本、选择器、随机变量或数据见证。

全局界的hZero、hScalar、hDelta、hHalf及两个分别作用于各分支的hPos都是已有冻结结论或前面事实的命题实例。分解的hVne、hVsqne、hRatio、hSquare、hRad、hFactor均有源码明确类型，hRatio来自定义，hSquare由它推得，不是新增假设。比较的hSourcePos、hFactor仅是一个已证合取的拆分，未从命题中取出非命题数据。其余hV、hVne、hB、hFixed、hDelta、hDenom、hClipPos也都在冻结输入之内。

两个包含证明中的x均已由冻结集合谓词绑定，hx、hDisagree是冻结左集成员条件，hGood／hBad各分支没有越域捕获。新集合谓词闭包仅捕获n、Ω、g、r、C0、rho、y。四个定义闭包仅捕获它们显示的参数。未使用阶段1允许但可选的非命题局部别名；没有新let、函数数据别名、全局／private辅助项、局部实例、附加导入或隐式section变量。`autoImplicit=false`、宇宙u及经典命题可判定上下文均保持冻结；没有暗加可测性、独立性、矩、对称性或样本存在性条件。全部局部事实满足冻结的普通推导Prop政策。

## 原文忠实性与未覆盖范围

已完整读取只读p51材料第1—211行，SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`。S1明确核对称、n≥4，并给出原W、V、D、J与s；S10写出本单元的字面预算，S12写出同一裁剪式及零约定，S15要求实际分母事件。新源码逐项对应这些有限组件。

196的实际FULLVALUE确实是受保护的 `d = if V=0 then 0 else centeredSq/V²−1`。将sqrt(centeredSq)解释为原文s时，仍必须使用既有 `centeredSq_eq_center_sum` 的实际对称性与n≥4前提；本单元没有对非对称核声称原中心行解释。这个来源条件与分解定理本身不需要hsym并不冲突。

本单元的比较结论是条件命题。原文从几何及Young不等式得到的**无条件字面S10支配**仍由后续209承担，不能由已有S17的不同K、q上界冒充。实际 `projectionGood` 写的是sqrt(sqrt(n))；它到原文幂形式Gy的206桥是独立依赖，本单元没有导入或假定尚未完成的205／206。S11、S15的概率付款和完整OQ56根结论仍开放。所读p51自身是补证候选；其Shao–Zhou外部定理和p54修复归属保持原样，本次不作新颖性认证。

原C1 immutablev85及原C2／C12既定范围v112完成的既有结论保持，OQ3仍由用户暂停，OQ4处于已接受有限范围的空闲状态。本次审查不改变这些状态。

## 静态读取中保留的记录与下一门

首次静态读取器把5处 `· have` 的分支项目符当成局部头的一部分，还把冻结时HOLD05的可变当前指针当成不可变数学输入，因此留下静态失败记录。原始失败完整保存在 `static-history/attempt01-parser-and-current-control.json`；随后只修正审查侧的词法比较与历史控制指针解析，新证明字节未动。冻结时HOLD05的1146字节、SHA256 `f8997502…c011557`与保存的 `CURRENT-RESOURCE-HOLD-05-before-clear.json`精确相同；当前指针已另行记录为清除状态。该资源控制变化不是数学冻结变化，也不授予本审查任何服务器执行权。

下一项实际缺口是：父实例在现行资源规则下执行此精确新源码的第一次native检查，成功后对**同一最初对象**读取全部实际所有者的完整TYPE、非定理FULLVALUE及递归公理依赖。允许公理仅 `propext`、`Classical.choice`、`Quot.sound`。本实例随后可从当前审查追加仅覆盖实际机器产物及其新证据缺口的独立审查；未变化的旧证明无需重审。任何源码修订只使其受影响证据失效，应保留本次精确版本。

本次所有者现已自然完成有界源码审查；释放记录为精确零写入、零执行、零heavy、零inflight、零pending、零子实例。最终回复结束本次普通回合，不构成后台继续运行机制。
