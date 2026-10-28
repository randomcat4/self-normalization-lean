# Unit250 独立完整源码审稿

STATUS: CORRECT

JUSTIFICATION: 冻结的同一原始模型、level-dependent 预算、原长删除归一化与 full/partial 指数在新源码中均保持。证明先比较正分母系数，再分别消去 full/deleted 预算内共同确定项，得到真实的绝对删除差支配；由实际可测性和非负范数支配转移承重接口的可积性，最后以同一个正积分归一化。逐行数学推理未发现关键缺口。

本结论仅是 SOURCE-to-statement/proof 完整独立审查。`qualified=false`，kernel、首次成功对象的实际全部 TYPE、必需 VALUE 和所有实际所属声明的递归公理材料仍为 PENDING。没有运行 Lean、lake、PP 或 AX，也没有服务器、网络、上传、Git/API、发布或子上下文操作。

## 精确对象与独立性

审稿角色 `/root/oq56_unit250_review` 与匿名证明作者隔离，唯一写入目录是本目录。请求模型 `gpt-6.1-sol`、强度 `xhigh`；实际模型/强度不可见，input/cachedInput/output/reasoningSubset 均为 null。使用 math-theorem；未使用 math-ultra。未改源码、冻结、旧生产者或任何前提。

- 冻结 `freeze-01/frozen-declaration.json`：SHA256 `a26f0a109e8f06fd03c4326ecd868ed882ae40f84a927c172b67e567ac8166de`，4352B。
- 完整源码 `author-01/OriginalLevelDependentWeightedSourceCost.lean`：SHA256 `17ab15bf0299531a33ba9710cbb8e43c61d59de6d306aeb5e900378b2a799c2a`，19166B，363LF，UTF-8、无 BOM、0CR。
- 完整实读源码 1–363 行，包括完整冻结声明14–59、所有 let/have、局部嵌套证明与全部分支。前导、完整头和结尾均与冻结字节相符。
- 原始 p51 全文1–355行、p54全文1–86行均完整阅读；hash分别为 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359` 与 `e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`。
- 实际唯一顶层声明是14行的 `actual_original_level_dependent_weighted_source_cost`；没有新增顶层辅助、结构、实例、选择器或数据。`classical` 是61行局部决策能力。

## 原文到冻结声明

p51的S10（130–137）、S13（159–164）在这里分别是原 `studentizerClipBudget n r C0 rho z` 与相同原n的 deleted 版本。其行能量为 `J=L/(n-2)^2`，deleted版本只擦除incident edges，仍保留原 `(n-2)^2`。p51的 `D=F/(sqrt(n)(n-1))` 与 deleted D 的相同分母没有变化；两者都与承重生产者的 pair sum 完全对应。rowSum排除对角，unorderedPairSum对每个 `j<k` 恰计一次。

结论是S14的有限样本解析费用之一个显式三次上界，采用冻结常数 `64*exp(1/2)^4*(1+4*C0)*(1+rho)`。sourceCost中的full/partial权重、cap `min |z*ξ0_i| 1`、以及绝对值的删除差均字面保留。未把原费用替换为另一个tail/CDF表达式。

p54第一节修复p51 S6的条件p矩过强变化率：只有收敛和统一界，不能声称任意多项式速率。本证明完全不使用该错误速率，也不需要p矩、混合 `g²r²`、高阶矩、标准Borel、额外包络或新模型选择。原外部概率引擎与集中结果继续归属Shao–Zhou；本模块未证明它们。

## 分母比较和真实删除差：123–197行

123–138行从 `n>=4` 得 `N=sqrt(n)>0`、`K=(n-2)^2>0`、`n²>0`；从 `rho=sqrt(v)>=0`、`z>=1` 得 `Q=(1+rho)zN>0`、`A=(1+rho)z/N>=0`、`denA=n²Q>0`。没有除以C0或rho。

139–150行方向正确：`4(n-2)^2-n²=3(n-4)^2+8(n-4)>=0`，故 `n²<=4K`，经乘非负C0和正Q并用正分母交叉相乘，得到 `k=C0/(KQ)<=kA=4C0/(n²Q)`。不是反向比较。

153–172行使用已接受精确能量接口与原deleted定义，分别证明：

`B=C0*A+k*L`，`Bdelete=C0*A+k*Ldelete`；

`BA=4C0*A+kA*L`，`BAdelete=4C0*A+kA*Ldelete`。

173–180行用平方和L非负和 `C0<=4C0` 得B非负与B<=BA。关键的182–197行另证绝对差：先在同一对预算内消去共同确定项，再用 `abs(k*x)=k*abs(x)`（k非负），得到 `|B-Bdelete|=k|L-Ldelete|` 和 `|BA-BAdelete|=kA|L-Ldelete|`，从而差分支配。不假定L-Ldelete的符号，也没有从B和Bdelete各自上界推出差分上界。

退化边界C0=0时两个系数和预算项均为0，上述推理保持；rho=0时Q依旧为正；z=1时仍全部成立。n=4时K=4、n²=4K，代数桥有效；整个冻结声明同时要求z>=1与窗口，此n下窗口不相容，所以没有漏掉一个可行端点。所有可行n的D分母 `sqrt(n)(n-1)` 也严格为正。

## 同一个正归一化积分及生产者对应：198–235行

198–203行从原产品可测hh，通过参数积分可测性得到实际g可测，再得到r及φ可测；概率测度给相关s-finite条件，不需要Ω是标准Borel。204–208行使用已接受weight_bounds给 `exp φ<=exp(1/2)`，并有正值和可测性，故一维指数真实可积。

209–215行向 `finite_observation_product_tilt` 提供同一μ与φ的实际可积性，输出的是本声明中 `I=integral exp(S)`，常数坐标积分乘积确为m^n，并直接得I>0。没有以另一个形式正常数代替I。

216行显式记录 `(z/N)g=z(g/N)`。218–235行只调用一次接受的 `SourceAnalyticCost.actual_quadratic_source_analytic_cost`，保持μ/h、所有原核前提、原n与z及窗口，只把非负系数实例化为4C0，`n>=3`由hn导出。生产者的s正好是1+rho；Λ²与Λdeleted²就是这里的L与Ldelete；D/Ddeleted原长归一化相同；其BA和BAdelete正好是103–106行预算。相位的乘除恒等式由simp中的 `div_mul_eq_mul_div` 与 `mul_div_assoc` 在full、partial、cap、tilted测度的全部相同出现处执行；hscale虽未被该simp显式调用，其等式也没有产生额外假设。

该接口用m^n作分母，新证明在调用前用209–212行的hNorm把I改写为同一个m^n，四个合取输出被完整实例化。最后上界在4C0时逐项等于冻结右端。没有重证或重跑旧生产者；这里只读取接受的完整public头与实际消费定义。

## 可测性、范数支配、积分：236–358行

236–265行由r与坐标投影可测性构造full/erased edge的真实可测性；擦边分支依有限索引判定，逐点为0或同一原r值。finite pair sums完整覆盖j<k和其补分支。266–285行据原定义得到D/Ddeleted绝对值、full/deleted row sums及其平方和可测性。286–312行通过前述精确仿射式得到B/Bdelete可测性，随后ξ、phase、full/partial有限和、cap和完整两个weighted integrands均可测。特别嵌套hAbsD/hAbsB保留了外层hDeleteM的 `i:Fin n`，没有删去坐标量词。

313–321行逐点证明cap非负、full与每个deleted integrand非负。322–331行使用同一个正指数、同一个非负cap与z，将B和真正的删除差支配分别提升为weighted integrand支配。332–342行调用 `Integrable.mono'` 时同时提供了真实aestrong measurability，并通过 `norm=abs=value`（值非负）把上面的点态比较变为该接口要求的范数支配。没有从积分写得出而推定可积。

343–354行用真实可积性和integral_mono分别比较full与每个deleted积分，再有限求和；各原积分非负。355–358行除以相同I>0，得到sourceCost非负以及sourceCost<=sourceCostA，再接唯一生产者的上界，完整闭合冻结的五项合取。

## 实际清单及字节检查

独立从源码提取并核对了118个命名局部/结果绑定，恰为50个let（16个结果telescope、34个证明let）及68个have；118个完整source block与作者清单逐字相同，SHA采用 `UTF8(block+LF)` 约定。还独立比较130个变量绑定站点（包含公共binders、fun、∀、积分/求和、intro、by_cases）之源行/列，无缺失或额外站点。17个公共参数绑定包括Ω、测度空间、概率实例、原核前提与数值窗口，完整阅读；局部所有实质fact具有显式类型。所有匿名有限索引和成员证据都按实际有限集合核对，hSdeleteM是erase i，row sums是erase j。

作者generic `THEOREM_PROOF` 标签须结合其完整区间和缩进理解；本审稿显式补出hAbsD/hAbsB的父作用域是hDeleteM305–312，并核对hAbsB还位于hAbsD之后。未把这些嵌套fact误当作逃逸到外层的假设。清单提供完整源块，足以无损恢复这一关系。

作者包、冻结、原始输入、接受接口及release/manifest的28个独立唯一文件绑定全部匹配。28是本审稿实际检查集合（包含author MANIFEST及lastzeroRELEASE），不复述父阶段较小集合的27。初次本地inventory诊断漏加block结尾LF，导致block hash报告false；已保存原诊断，在确认真实字节约定后仅修复该读取检查为v2，无源码修改或任何数学/机器检查重放。其余输入hash与站点检查前后相同。成功报告为 `BYTE-AND-INVENTORY-CHECK-02.json`。

## 尚待同一独立上下文补足的机器资格

首阶段 `sourceAccepted=true` 只表示本审稿的SOURCE正确性裁决，不能代替lane/root最终接受。`qualified=false`。收到lead材料后需验证确为上述source hash的首次成功O，核对成功native与same-original-O receipt、完整actual owner集合、每个owner的完整unelided TYPE、所有required non-theorem VALUE和逐owner递归公理（白名单仅propext/Classical.choice/Quot.sound），再把实际public statement与本冻结语义逐项对应。未知生成名不能靠命名空间过滤或源码数目推断。

本结果不声称unit249的fixed clipping1三次费用、physical tail、CDF、外部SZ、eventual window、DC或完整OQ56闭合。后续机器核对继续沿用本次完整SOURCE阅读；除非实际变更或覆盖缺口，不重复审旧proof/TYPE/AX。
