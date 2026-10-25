# 单元185最终独立资格审阅

最终结论为 `QUALIFIED_EXACT_SOURCE_AND_ALL_ACTUAL_OWNERS`、`qualified=true`。此结论只绑定源码 SHA256 `f5e4f873f4e6a2b10dfad014a2e3ac0341fb277bf970a206091342c95121350a`（40511字节、813 LF、无CR/BOM）及其服务器对象 SHA256 `bdb6542999a10e63f19e9c14d0e98e39cd648821edd95e5ec3a3e2f8ca24e39d`（1437296字节）。本独立上下文已完整审过最初源码和随后全部受影响范围，本轮复用精确不变部分，完成全部实际所有者的最终类型、定义值、公理和接口核对。作者源及所有旧报告、旧失败记录按字节保留。

## 实际机器证据与资格边界

服务器 native04 的实际退出码为0、错误数0、用时6.994329754263163秒；receipt SHA256为 `f61f5ddc17364d17d79aec301bb9779773b1765f959f860916a065c92444aa91`。同一对象的全所有者审计实际退出码为0、错误数0、用时5.5009697917848825秒；receipt SHA256为 `894beb7013f26855dffe24ddaf34c97d2a78763f4a1d4a76aa287a22d6269bb8`。两门均无timeout、所属进程组全部结束、ownership_issue/post_error为空，分别5197/5209项保护记录保持相等。对象生产后没有重新编译生产模块。AUTHOR-STOP SHA256为 `51e72192e67d855450a5ab39b39fbfcddcf98bcf9ccb681af8a3a0c769fdd54f`。

机器原件保留在服务器，本审阅使用本地哈希绑定的完整实际元数据和摘要。`actual-owned-metadata.json` SHA256为 `e68afb83def773e41445c7893006c8c869f04591bfc8f78c9af02a5519eef2ff`，177644字节；机器摘要 SHA256为 `2361e09aba79272be07e49eb579652cf3afcc874d719785a58e32545763de6c8`，10896字节。已独立将每个原始JSON、完整TYPE、非定理FULLVALUE和最终COUNT按审计脚本的顺序重构，得到107984字节和 SHA256 `3ea1f59b1a660038168daddbfb2e89ecda25f381450547423f353ad6b025d9e0`，与服务器stdout绑定一致。没有省略标记、重名、缺失类型、缺失定义值或未映射所有者。

内核有30条警告，审计有1条警告，涉及弃用的条件化简名、未使用的化简参数/战术和既有mathlib工作区变更提示。原严格包装器 `success=false` 保留，`FIRSTEMPTY=false` 保留。本结论不声称clean、无警告或FIRSTEMPTY；资格基于实际native退出0、零错误、精确对象绑定、完整独立语义审阅及全部所有者递归公理审计。元数据和机器摘要中的 `qualified=false` 是等待独立最终审阅时的原始状态，也不改写。

此前native01、02、03分别RC1、17/3/1错误且无对象，均为失败。后续修复的成功不能回填为旧源码或旧证明的机械通过。

## 全部实际所有者

独立完整读取了实际module-index列出的67项完整TYPE（885行）、15项非定理完整FULLVALUE（208行）和每项递归AX。已读审计程序通过锚定公开主定理的真实模块索引遍历整个环境，按模块索引相等选取，不使用命名空间过滤；每个name调用 `Lean.collectAxioms`。因此私有名和生成名包含在内。67项由52个 `thmInfo` 与15个 `defnInfo` 构成，所有项均有body expression，没有新增axiom/opaque/unsafe证明路径。实际所有者计数来自这份清单，不来自34个源码声明或旧490条词法映射。

34个直接源码所有者为15个定义和19个定理；另33项全部是已核对的生成定理：9个定义方程、13个化简辅助定理、11个证明辅助定理。逐项来源、源码范围、完整TYPE/VALUE的哈希及读取状态见 `actual-owner-map.json`。生成方程准确展开相应定义。其余辅助项是反身序关系、等式对称、自然数奇偶/整除与界、有限和/积换序和非零化简等局部证明义务；泛型类型类和条件均在生成项自己的类型中，未向五个公开接口引入额外前提。

所有67项递归公理均为白名单子集 `{propext, Classical.choice, Quot.sound}`；逐name记录完整保留，出现项数分别67、50、56。公理清单来自递归依赖收集，不是只检查源码关键字，也不是只审五个公开定理。

## 冻结数据、实际类型与公开接口

再次逐字核对了34个有效冻结头、15个有效定义值和源码声明映射的34个完整字节span。有效冻结为原v1加事前批准的修订01–06；只修订05改变 `pairCount` 的括号和值及private `pair_sign_mean` 的显式判定器头，修订06明确原有有限积和系数。其余33头、14值、全部五个公开定理头和八个公开定义值保持原字节；prefix03、suffix、四个双射、两个uncurry函数、23个局部let及修订06系数保留。当前源码相对repair02的唯一变化是第754行 `rw [mul_add]`，独立验证了该17字节插入及其前后全部字节相同。

完整实际FULLVALUE确认：`signValue` 为Bool真取1、假取−1；`signPath` 逐坐标应用它；`cubeMean` 为实数 `2^(-n)` 乘全部 `Fin n → Bool` 的有限和；`signSum` 和 `pathSum` 是实数标量作用下的整个EuclideanSpace向量和；`energy` 为各向量Hilbert范数平方的和；`moment` 对整个向量和的范数应用 `Real.rpow` 后取cubeMean；`hilbertConstant` 精确等于实数2。私有 `scalarSignSum/pairCount/evenPairs/pairSign/pairInner/allocations/evenFactor` 的完整实际值亦逐项与冻结意义核对，其中内积和范数实例都来自实EuclideanSpace的二范数Hilbert结构，未换成坐标绝对值和。

五个公开实际TYPE的结论及前提完全对应冻结源码：

| 公开声明 | 实际接口意义 |
| --- | --- |
| `hilbertConstant_pos` | `0 < hilbertConstant`，无参数，常数为2。 |
| `finite_hilbert_sign_moment_bound` | 任意自然数n、d、固定向量族 `v : Fin n → EuclideanSpace ℝ (Fin d)` 和实数q，仅假设 `2 ≤ q`，得到 `(cubeMean ‖Σσⱼvⱼ‖^q)^(1/q) ≤ 2√q√(Σ‖vⱼ‖²)`。 |
| `rad_integrable_and_integral` | 任意 `f : Shao.Path n → ℝ`，对既有真实 `radMeasure n` 可积，积分等于符号立方平均；接口没有添加全局可测性假设。 |
| `pathSum_signPath` | 任意n、d、v、s，真实路径和在 `signPath n s` 的值精确等于符号向量和。 |
| `rademacher_hilbert_moment_bound` | 同一任意n、d、固定v和实数 `q ≥ 2`，同时给出真实radMeasure下范数q次幂的可积性及同一常数2的积分矩界。 |

公开实际TYPE没有n>0、d>0、正能量、整数q、坐标独立假设参数、额外实例参数或未冻结前提。独立性由既有真实产品测度承载。所有自然数幂与实数 `Real.rpow` 的实例分开核对；已完整读过 `Real.rpow` 定义、`Pow ℝ ℝ` 实例和 `Real.rpow_eq_pow` 主源，后者只是同一实数实指数运算的定义相等，无额外正性要求；把自然数幂接入实指数时的非负底数等义务由原证明单独支付，未以expected type冒充actual TYPE。

## 完整证明链与修复继承

本轮沿原独立完整审阅和repair01/02/03的精确受影响范围连续覆盖全部19个源码证明。原12个完全不变证明复用首次完整审阅；repair01完整续审七个改变的证明及 `pairCount` 新值与所有消费者；repair02完整续审其中三项；repair03完整续审 `radMeasure_atomic` 整个声明、证明、局部值/类型和按时间顺序的scope。本轮没有重审未变18个证明，新增的是同一成功对象上全部实际TYPE/FULLVALUE/AX及它们与既有源码审阅的结合。逐声明继承矩阵见 `final-coverage.json`。

证明从有限产品平均与奇偶筛选开始，将完整Hilbert范数平方展开为有序端点对的内积和，再对k次幂的全部pair词取平均。保留全偶端点项，对可能为负的内积乘积先用绝对值和Cauchy–Schwarz控制，再与范数系数的标量偶矩比较。这里没有先逐行取绝对值造成额外维数或项数损失。

标量偶矩通过完整multinomial展开、全偶重索引和平方multinomial处理。四个双射的值域界、除2精确性、模数不回绕、正反逆和全部系数均已完整独审，阶乘分母非零的条件有明确证明。由 `(2ℓ)! ≥ 2^ℓ ℓ!` 和配对系数上界得到偶矩控制。再用在1处的凹幂切线、非负函数的有限Jensen与Lp单调性，将任意实数 `q ≥ 2` 接到 `k=⌈q/2⌉` 的偶矩，使用 `q ≤ 2k ≤ 2q` 得常数2。两个割线dot调用的实际接收对象、端点、顺序和完整scope已在原独审补充中核对，所需凹性、导数点1、非负域和指数范围均已支付。

必须保留原错误的准确记载：最早source-only报告曾将旧 `pairCount` 的两个indicator误读为都在Σ的scope内；旧冻结文本实际缺外括号，第二个r未绑定，native01以错误拒绝。修订05事前冻结的括号修复后，当前完整实际FULLVALUE明确是 `Finset.sum ... (fun r => ite(first=j) 1 0 + ite(second=j) 1 0)`。本最终结论使用这份新值，不复述旧误读。repair02对重聚合先拆 `pow_add`、再拆 `prod_mul_distrib`、再分别计算两个端点；端点相同时仍保留两次出现、计数2和平方，未擅自合并成一次。空乘积/空和、n=0、d=0、k=0和energy=0均在原完整证明与续审中保留；主定理的q范围仍为全部实数 `q ≥ 2`。

真实测度桥通过 `Measure.pi_eq` 在任意可测有限矩形上证明与权重 `((2 : ENNReal)^n)⁻¹` 的有限Dirac和相等。边缘是既有对称±1概率law，已有概率实例提供SigmaFinite；矩形及各 `E j` 的可测性支付所有Dirac应用条件。修订06的显式系数为 `(j : Fin n) → Bool → ENNReal`，没有新数据或假设。随后有限Dirac和对任意实值函数可积，有限权重非顶，转成实数平均；积分桥消费的是同一真实测度和同一signPath。

repair03在hLaw初始化中加入的 `rw [mul_add]` 正向展开剩余目标右侧的 `2⁻¹*(I₊+I₋)`，得到与左侧 `2⁻¹*I₊+2⁻¹*I₋` 相同的表达式。插入点只见n、nu、E/hE、先前完成的hrect/hAtom及当前 `j : Fin n`，不能使用尚未完成的hLaw或未来hweight。此ENNReal原有半环分配律不需要除数非零、有限值或额外成员条件；native04现已对这份精确源码完成展开及内核检查。n=0时不添加j或样本大小前提。

## 范围、归属与交付

最终资格只闭合单元185的p44固定有限实Hilbert/Rademacher矩界及真实测度积分桥。它不是p51/p54全部论证、186实现或C2/C12/OQ56根群完成；保留p51外部Shao–Zhou结果归属、p54修正及既有原始scope。没有183/184数学依赖。186实现仍HOLD，C2/C12/OQ56仍OPEN，OQ3仍PAUSED_BY_USER。

所有新增输出仅位于本目录。审阅者没有写作者源，没有运行Lean/server/network/Git/upload/cache，没有子代理和锁。请求配置为gpt-6.1-sol/xhigh；平台实际模型、effort和分项token usage不可见，均以null记载，不推算订阅比例。最终输入哈希、局部静态复核、全部owner映射、资格记录、manifest、DONE和零在途RELEASE0作为独立新增文件交付。
