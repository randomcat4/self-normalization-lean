# Unit265 U0 proof repair01：积分上界的最小形式修复

状态：`REPAIR_IMPLEMENTED_STATIC_PASS; AFFECTED_INDEPENDENT_REVIEW_PENDING; NOT_KERNEL_CHECKED; NOT_QUALIFIED`。

本轮仅修复指定服务器首次 actualnative01a 的唯一 SOURCE228 错误。冻结的 public theorem、全部前提、量词次序、导入、选项、共同见证与其余证明字节保持不变。没有运行 Lean/AX、工具链探测、服务器、网络、Git/API、发布或子代理。

## 一、精确授权和阅读

激活文件为 `repair01-author-ACTIVATION.json`，SHA256 `347d3ad55b9c19763065c64e700a541cca9c257e587efbb889992edad90bbdc6` /5422B。其13个输入均核验SHA256/字节，完整读取，包括原SOURCE308LF、PROOF261LF、完整实现报告/清单/最后释放、冻结四件、完整 normalized native01a 诊断、原独立SOURCE报告/裁决及parent intake。原作者LAST的全部权限释放、authorRoleRetained=false及六零已实际读取。

本作者先写 `READ_ACK.json`，SHA256 `0b170d62c10ed2ae7aaeb808af60bb7bf5f679a535aca2e46f0807c34e21964a` /4933B，再开始证明修复。工作范围严格为本 `author-repair-01` 新目录，没有编辑其他作者、library、冻结、原失败源或receipt。

初次本地READ_ACK构造因PowerShell hashtable中的裸true被解释为命令而自然失败。该命令只创建本目录；下一命令实际观察其为空，未产生ACK、SOURCE或PROOF，也没有外部/数学执行或不确定操作。`FAILED-LOCAL-ACK-01.json`完整保留这个本地失败及其精确效果，随后仅修正JSON布尔语法。

## 二、唯一问题和修复

原完整源码SHA256 `8d6897dc939cd5e5e07e3d29f8a262b7942536bc41042a47052f1d8a5d7b6d32` /14730B/308LF。其完整SOURCE/PROOF数学与语义原已由独立审阅者接受；本作者不替代该独立角色。服务器actualnative01a自然结束RC1、无对象，诊断只含SOURCE228一个错误及SOURCE239一个建议风格warning。

唯一错误在`hLLinear`积分比较中。原来不带显式类型的`hBound`被显示为`tB ^ q * I ≤ tB ^ q * B`，目标显示为`Real.rpow tB q`。随后`linarith only [hBound]`未能把这两个表面表示对齐。该诊断属于形式证明失败，不构成数学反例，也未产生可复用成功对象或AX。

原SOURCE226–228 / PROOF181–183被以下6行替换，其他字节不变：

```lean
          have hBound :
              Real.rpow tB q * (∫ o : Ω, Real.rpow |g o| p ∂μ) ≤
                Real.rpow tB q * B :=
            mul_le_mul_of_nonneg_left hβBound (Real.rpow_nonneg htBPos.le q)
          simpa only [mul_one] using
            (sub_le_sub_left (sub_le_sub_left hBound tB) (1 : ℝ))
```

这里显式指定乘子的实幂表达式，使hBound的类型与目标采用同一表达式；不再要求线性算术预处理识别该幂记号。局部变量和数学内容没有变化。

## 三、修复处的完整数学推导

记A=Real.rpow tB q、I=∫|g|^p dμ。原上下文已有tB>0，因而A≥0；冻结hβBound给I≤B，非负数A左乘得到AI≤AB。这正是显式hBound，使用的条件全部来自原上下文，没有增加新假设。

第一次`sub_le_sub_left hBound tB`从AI≤AB推出`tB−AB≤tB−AI`。第二次对这个不等式使用`sub_le_sub_left ... 1`，得到

    1−(tB−AI)≤1−(tB−AB).

紧邻的原`rw [hgsecond]`已经将Eg²换成1，所以实际目标左端为`1−(tB*1−AI)`。`simpa only [mul_one]`恰把`tB*1`化为tB，完成上述目标。不再调用该处linarith，也不需要除法、严格p矩界、额外积分存在性、额外符号前提或新尾假设。

其后原代码原样使用`AB=tB/4`，得到`L≤1−3tB/4`。先前的共同数值见证、标量指数比较、真实μ下的可测/可积性、有限乘积积分身份和闭事件Markov证明均未改动。n=0、p=3、B=1和g取0/负值的原证明覆盖不受影响。原haveI建议风格warning的代码保留，源行号因新增3LF从239移至242。

## 四、完整新SOURCE、PROOF及字节差异

交付完整 `UniformPMomentLowEnergy.lean`：SHA256 `d0b4bfe9eb107253da068f10bd6ce5450cf2c2b785acaab9a55aef91f3ea05a3` /14912B/311LF。完整 `PROOF.txt`从`:= by`开始：SHA256 `390bd398911a5a21d7a69111adbaa5c10df82c3d24853c37ae670ae37a8d117e` /12605B/264LF。相对于原源仅一个连续proof区域改变，旧3行变成新6行，净增182B/3LF。

新SOURCE严格等于原冻结PREAMBLE+HEAD+新完整PROOF+原冻结CLOSING的原始字节拼接：

| 区段 | 新源行 | 零起点字节区间 | 字节数 |
| --- | --- | --- | --- |
| 原PREAMBLE | 1–11 | [0,340) | 340 |
| 原HEAD | 12–45 | [340,2266) | 1926 |
| 新完整PROOF | 46–309 | [2266,14871) | 12605 |
| 原CLOSING | 310–311 | [14871,14912) | 41 |

`STATIC-CHECKS.json`记录各段SHA256及实际切片比较。修复区域之外的前缀和后缀均精确复用原始字节；未对冻结段作重新排版、行尾转换或语义清理。

保存的 `DIFF.patch` 为一个标准unified hunk：`@@ -223,9 +223,12 @@`；保存的 `REVERSE-DIFF.patch` 为其反向：`@@ -223,12 +223,9 @@`。本轮实际从磁盘读入两份补丁，以严格本地解析器逐行核对所有context/deletion、核对hunk旧/新行计数并执行增删。正向实际应用于完整原源后生成的UTF8字节精确等于新SOURCE；反向实际应用于完整新源后精确恢复原源码SHA256。检查不是仅比较补丁文字、预报补丁能用或反向字符串替换。

SOURCE、PROOF及已写payload均严格UTF8无BOM、CR0、LF单终LF。源码禁用token sorry/admit/axiom/unsafe/native_decide 匹配0；public源码定理仍1，新增public helper/definition仍0。全部13输入在修复后再次逐项SHA256/字节核对，均未变动。

## 五、认证边界、范围和最后释放

本次静态检查只证明字节、范围、组装、补丁执行和格式结果，不构成Lean elaboration/kernel、actual TYPE/VALUE、递归AX或独立数学接受。新source/proof的改动处仍须由lead安排合格独立审阅；未改动精确部分的既有独立数学证据可以按项目规则复用。原native01a RC1/noO保留，不能标成通过，也不是未知inflight调用的重放依据。

下一依赖为lead对本精确修复版本完成受影响独立证明审阅，再在指定服务器运行新源native；若成功，只绑定该首个成功原对象，枚举全部实际owners、完整TYPE、必要非定理VALUE与逐owner递归AX并完成独立最终绑定。实际owner数量/TYPE/AX在本作者范围内均未知，保持null，不能从源码定理数推算。

冻结范围仍仅U0：先固定p/B选共同tB/cg，随后任意概率模型上的标量Laplace界及全部自然数n的实际有限乘积闭低能量概率界。U1统一物理有限费用桥、U2共同起点相对尾、U3/p54实际条件/三角应用及均值平移、externalSZ、DC、fullOQ56与root均不由本次proof修复闭合。

请求模型/力度为gpt-6.1-sol/xhigh；实际model/backend/effort未暴露，均为null；usage的input、cachedInput、output、reasoningSubset分别为null，不推算订阅比例。

完成清单后唯一 `LASTFINALWRITE.json`最后写出，绑定清单和全部8个payload（包含本地失败记录），释放全部写入、执行、发布和child权限；authorRoleRetained=false，writers/heavy/inflight/uncertain/pendingExternal/children全部0。之后没有写入、启动检查、继续证明或保留隐式作者权限；修订必须由lead重新明确激活。
