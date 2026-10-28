# 261 repair02 加法顺序受影响复核

结论：`CORRECT`，`sourceAccepted=true`；仍为 `qualified=false`、`machinePending=true`。同一独立上下文复用完整 SOURCE 报告 887919dc… 和 repair01 报告 32f35b87…，本次只复核明确的相邻两行增量。

当前源码 SHA256 `519d185d374e19e9eb3836c276215366f451122f100f9a5b5cac4b177f797048`，25471 字节、433 LF；PROOF 为 `5ffad082222fb584d77a13830ff9067bdbb1f9526f65a3e82b27ba6a3b2667d0`，19468 字节、322 LF。已实际读取当前源码 410–433 行、完整 13 行 DIFF、REPORT、STATIC-CHECKS、修复激活及实际 native02 单一诊断，并核对 release 六零与精确绑定。作者静态结论不替代本次独立字节和数学检查。

新 428–429 行把未限定的 add_le_add_right 应用改为 `_root_.add_le_add (mul_le_mul_of_nonneg_left hUpperFactor hUpperPrefactor) (le_refl (4 * payment))`。令 U=standardNormalTail(z)·exp(C3·Loriginal)，a=1+C4·sourceCost0，b=1+C4·cubicCost。此前已审且未变的 hUpperPrefactor 给出 U≥0，hUpperFactor 给出 a≤b，因此第一个输入是 U·a≤U·b；第二个输入是 4payment≤4payment。根命名空间的双输入加法单调性得到的顺序正是 U·a+4payment≤U·b+4payment，与 hExact.2 的右端逐项对齐。由传递性得到冻结的三次费用上界。不需要 payment 的符号、新前提或额外交换律改写。下界及最终六项合取没有变化。

独立比较得到：源码仅 428、429 行改变，证明仅 320、321 行改变，字节增加 11，行数未变。反向替换精确恢复 repair01 源码 986ab611… 和 PROOF 733d1040…；新源码仍严格等于冻结前文＋原 96 行声明＋当前 PROOF＋冻结结尾。所有其他字节完全相同，因此同一见证、原始模型／量词／窗口／真实删点 full-I 费用／原始 P 分布／四类费用／条件式广 L² hSZ，以及 repair01 的两处 Borel 修复、nlinarith only 和唯一 proof-local 800000 设置全部精确复用。没有新选项、资源变更、声明变更或数学前提变更。新的 UTF-8 无 BOM、LF、单末尾换行和禁用构造检查通过；明确源码 theorem 数仍为一，实际拥有者计数仍待服务器。

REPAIR02-CHECK 自行核验 manifest 产物及输入列表的唯一直接绑定；逐项结果和派生计数均保存在该文件，不复制父实例不同集合的描述计数。旧 native01、native02 失败来源及审阅报告保持原字节；native02 的自然 RC1/noO 不是机器通过。后续仅由 lead 对当前精确新源码做新检查，本上下文接续同一首个原始对象的完整实际 TYPE／必要 VALUE／递归 AX 最终审阅。现在不写 FINALWRITE，保留独占审阅职责。ExternalSZ、CDF、relative-tail、DC、fullOQ56、root 均保持 OPEN；实际模型／后端／强度与分项用量未暴露，均为 null。
