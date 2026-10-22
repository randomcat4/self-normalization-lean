# U14b 独立声明与来源审查

STATUS: CORRECT

本报告仅审查冻结声明与来源，未审查实现。独立审查者只拥有本报告及服务器对应报告；不改动实现、冻结 scope、旧报告或共享缓存。本轮未运行 Lean、API 探针或构建。根 A/B/C/D 均保持 OPEN。

## 第一阶段：仅实际冻结 Lean 代码块的盲译

本节在读取 scope 解释、R1 原文或证明路线及库接口之前独立写入。输入为 thirty-third-unit-scope.md 的精确 Lean 代码块，文件 SHA256 0db55bb2ed6bbcd20e41011211b0b5ce6851c8335afb94be2a5633112cf2a053。该块无新定义，含以下三个完整目标。下文 D(p,z) 仅是既有 binaryRelativeEntropy p z 的记号。

1. `binaryRelativeEntropy_ge_first_term (p z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)`：对任意实数 p∈[0,1]、z∈(0,1)，断言 p·log(p/z)−p+z ≤ D(p,z)。p=0、p=1 都包含；不要求 p/z 非零。Real.log 使用库的实自然对数总定义，p=0 时 0·log0 按实数乘法为零。

2. `binaryRelativeEntropy_gt_two_mul (p z : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) (hlog : 3 < Real.log (p / z))`：对任意 p∈(0,1]、z∈(0,1)，若 log(p/z)>3，则 D(p,z)>2p。p=1 仍允许；该结论是严格不等式。

3. `binaryRelativeEntropy_source_gap (q H R : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51) (hR0 : 0 < R) (hR1 : R ≠ 1) (hp0 : 0 ≤ (q * R ^ 2 - 1) / H) (hp1 : (q * R ^ 2 - 1) / H ≤ 1)`：对任意同一组实参数 1<q<103/100、50<H<51、R>0 且 R≠1，令 p=(qR²−1)/H，并显式要求 p∈[0,1]；令 z=(q−1)/H，断言 (7/200)(R−1)² < D(p,z)。z 的合法区间未作为假设重复给出，须由 q、H 范围导出。无关于测度、核、任意分布、KL 数据处理或全局极小化的量词；该目标仅为这组实数构造的二元熵下界。R≠1 与实数域意味着 (R−1)²>0，严格性须真实保留。

本阶段仅记录完整类型的数学含义，不以预期作者证明替代审查。待核：互补项在两个 p 端点的合法性；第三目标全部可行 R 的三段覆盖；各分母正性、严格常数 7/200；真实导入和已缓存库接口。


## 第二阶段：冻结声明、实际定义与 R1 对照

盲译先落盘之后才读取完整 scope、R1 和下列库接口。scope 本地及指定服务器 `runs/oq3/u14b-20261021/scope.md` 实际 SHA256 均为 `0db55bb2ed6bbcd20e41011211b0b5ce6851c8335afb94be2a5633112cf2a053`。R1 实际文件 SHA256 为 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，已直接读取第 161–237 行。

实际承重项目源码仅为已完成独立完整审查的 `BinaryEntropyBounds.lean`；本地和服务器 `Shao/OQ3/BinaryEntropyBounds.lean` 实际 SHA256 均为 `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228`。这里消费其实际定义

`D(p,z) = p log(p/z) + (1−p) log((1−p)/(1−z))`

及已审公开结论 `entropyRemainder_nonneg`（x≥0）和 `binaryRelativeEntropy_refined_lower`（0≤p≤1、0<z<1）：

`(p−z)² / (2 max(p,z)) ≤ D(p,z)`。

该定义是自然对数的标准二元相对熵在合法域的端点连续约定；本 scope 通过实际概率域限制使用它，没有用总化除法或 log 的非正参数伪造概率结论。没有新定义、隐藏的测度参数或未写出的参数族。

R1 第 180–188 行给出 p=(qR²−1)/H、z=(q−1)/H 和待由实际核支持的 KL 数据处理；第 193–225 行给出三段二元熵估计，其中第 221–224 行正是前两个目标的互补项估计及后果。U14b 只抽取这里的纯实数估计，不声称已实现第 180–188 行的核或数据处理。第三目标的 7/200=0.035 并非 R1 逐字陈述的最优常数；它是由这三段估计的实际中间式可推出的统一充分常数。特别地，它大于第 225 行已主动弱化到的 103/3000，却小于该行之前的实际中间系数 2/51；不能将它误称为对最后显示常数 103/3000 的数值弱化。R1 第 229 行的 ell·q<103/3000<7/200 说明该间隙作为后继率比较的充分工具，但本声明没有 ell 或任何 KL 差恒等式。

## 第三阶段：独立数学可行性与边界逐项核对

### 目标一：补项下界，含 p=0 与 p=1

记 b=1−z>0、u=(1−p)/b≥0。已审 `entropyRemainder_nonneg u` 给出 u log u−u+1≥0；乘正数 b 并仅约去 b，得到

`(1−p) log((1−p)/(1−z)) ≥ z−p`。

加上 p log(p/z) 即是目标一。只取消 z 或 1−z 的非零分母；完全不需要取消 p、1−p 或对 log0 使用 log_div。

p=0 时 u=1/(1−z)>0，首项 0·log0=0，目标仍合法。p=1 时 u=0，互补项为 0·log0=0；u logu−u+1=1，仍可使用非负性。故两端点没有隐含严格 p∈(0,1) 前提。z=0、z=1 被正确排除。

### 目标二：严格大于 2p

p>0 与 log(p/z)>3 给出 p log(p/z)>3p。目标一遂给

`D(p,z) ≥ p log(p/z)−p+z > 2p+z > 2p`。

严格乘法依赖 hp0；最后一步依赖 z>0。p=1 被保留且有效。该目标不把非严格 log 门误用成严格门。

### 目标三：全部可行 R 的统一严格 7/200 间隙

统一记 A=qR²−1、p=A/H、z=(q−1)/H、t=(R−1)²。假设给出 H>50>0、q−1>0 且 q−1<3/100。因而

`0 < z < (3/100)/50 = 3/5000 < 1`。

p 的非负性和上界是显式假设，不能从任意 R>0 自动推导。R≠1 给 t>0；R>0 给 R+1>0。精确差值为

`p−z = q(R−1)(R+1)/H`。

以下三段覆盖 R>0、R≠1；R=3/2 可置于中段或大段，均成立。

**第一段 0<R<1。** 此时 p<z，故 max(p,z)=z。U14a 的实际下界可写为

`D(p,z) ≥ t · q²(R+1)² / (2H(q−1))`。

所有分母正，未取消 p；这包括可行边界 p=0。q>1、R>0 给 q²(R+1)²>1；H<51、q−1<3/100 给 2H(q−1)<153/50。系数因此大于 50/153，而

`50/153 − 7/200 = 8929/30600 > 0`。

乘 t>0 后得到目标严格间隙。无需偷加 R>0.98 或源中更强的 1/(1−z) 因子。

**第二段 1<R≤3/2。** 此时 p>z>0，所以 max=p，A>0。令 B=(103/100)R²−1>0。由 q<103/100、H<51 得 HA<51B。故下界系数满足

`q²(R+1)² / (2HA) > (R+1)² / (102B)`。

要使最后一项大于 7/200，只需 P(R)>0，其中

`P(R) = (R+1)² − (357/100)((103/100)R²−1)`。

独立得到如下精确恒等式（不是小数抽样）：

`P(R) = 61861/40000 + (3/2−R)((26771/10000)R + 40313/20000)`。

本段 3/2−R≥0、R>1，所以右侧≥61861/40000>0。该证书的三个系数已在指定服务器用有理数精确展开核对，展开均为 `−(26771/10000)R²+2R+457/100`。这是普通代数核对，没有运行 Lean/API 探针或写入代码。于是每个实际分母及乘 t 的符号均正确，最终仍严格。

**第三段 R≥3/2。** R²≥9/4、q>1 给 A>5/4。因 0<q−1<3/100，且约 H 仅使用 H>0，

`p/z = A/(q−1) > 125/3 > 27`。

下节所核实际指数接口给 exp1≤3，因此 exp3=(exp1)³≤27；p/z>0 后才可用 `Real.lt_log_iff_exp_lt` 得 log(p/z)>3。此段 p>0（A,H 均正），故目标二真实适用，得到 D(p,z)>2p。再由 q>1、H<51、R²−1>0 得

`2p > 2(R²−1)/51`。

最后的严格比较有直接正因子证书：

`2(R²−1)/51 − (7/200)(R−1)² = (R−1)(43R+757)/10200 > 0`。

因此大段成立。这里不需要把源中的 >43 当作既有库事实，也无需新的指数数值模块；较弱但充分的 >125/3>27 已足够。p=1 端点依旧由目标二覆盖。

上述推导没有除以可能为零的 (R−1)²；任何系数比较后乘 t 时均使用 t>0。R=1 被显式排除，也必须排除：该点 p=z、D(p,z)=0，严格结论将为假。可行性 p≤1 在大段调用标准二元熵估计时仍实际需要，未被删去。声明中所有实数定量均一致使用同一组 q,H,R。

## 第四阶段：指定服务器的实际静态 API、导入与缓存

仅通过共享 `tools/server.py` 对指定服务器只读查看源码、散列和文件存在性；实际返回 exit_code=0。没有 Lean 命令、#check/API 探针、构建、Audit 重跑、缓存写入或原始日志下载。源不存在实现，因此没有作者 receipt/build 作为本轮依据。

实际 Mathlib git HEAD 与 manifest rev 都是 `807d3836b165983210ee2ecf3cd28f239436949c`。lean-toolchain 内容为 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。这是静态环境绑定，非本单元编译成功声明。

1. `Mathlib/Analysis/Complex/Exponential.lean` 实际 SHA256 `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`。第 538–541 行实际类型为 `Real.abs_exp_sub_one_sub_id_le {x : ℝ} (hx : |x| ≤ 1) : |exp x−1−x| ≤ x²`。取 x=1 的前提是 |1|≤1；得到 |exp1−2|≤1，故 exp1≤3。第 234–235 行 `Real.exp_nat_mul (x : ℝ) (n : ℕ) : exp(n*x)=exp x^n`，取 x=1,n=3；第 284–287 行 `Real.exp_pos` 给指数非负，立方比较合法。该模块为 scope 明确拟导入项，不依赖误猜的 ExponentialBounds。

2. `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` 实际 SHA256 `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97`。第 167 行实际类型 `Real.lt_log_iff_exp_lt (hy : 0<y) : x<log y ↔ exp x<y`，所需正性 y=p/z 已在大段建立。第 103 行 log_zero=0、第 107–108 行 log_one=0；没有在 p=0 或补质量为零时非法使用 log_div。scope 可见的实际导入链为 `BinaryEntropyBounds → Log.NegMulLog → Log.Deriv → Log.Basic`；后面三条为库源码所列 public import，且 scope 还明确直接导入 Exponential。

3. `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` 实际 SHA256 `00039257907338466419ea23f63e9e403f1f7f4a431d57d0f09bdf9bda6577a1`。第 39–42 行 `Real.self_sub_one_le_mul_log` 的门仅 x≥0，允许 x=0；也可与既有 entropyRemainder_nonneg 互相对应。所消费的 U14a 非负性与 refined_lower 的实际类型、端点和命名均已直接读取现有源码绑定，未重做旧目标。

实际缓存存在：Exponential.olean 210592 字节、NegMulLog.olean 43896 字节、Deriv.MeanValue.olean 76040 字节；U14a 项目 olean 574016 字节。scope 沿用的六个 proof-only tactic 模块也实际存在：FieldSimp 1681840、Ring 1648、Positivity 1832、Linarith 2536、FunProp 2488、NormNum 2496 字节。没有把缺失的总括 Mathlib.Tactic 或 ExponentialBounds 当成可用前提。

静态类型环境中的实数、自然对数、max、幂与数值有理常数均来自上述实际导入，无矩阵范数、默认测度或未知实例问题。namespace Shao.OQ3 与既有二元熵定义吻合。本轮静态审查能够支持批准实现；尚无实现，因此不声称三个目标已经在 Lean 内核中通过。

## 最终裁决与范围

STATUS: CORRECT

JUSTIFICATION: 三个完整冻结目标在其实际量词与端点下均成立；两个基础下界的互补项处理合法，统一 7/200 严格间隙具有完整三段独立代数证明和正分母门。指定服务器的现有公开接口与缓存支持所需标准对数、指数及代数路线，未发现声明级或环境级关键缺口。结论来源准确定位为 R1 三段二元熵估计的标准充分实数工具，未假定作者后续实现会成功。

批准只到声明/source gate。未证明实际 Bernoulli 核、KL 数据处理、精确 likelihood/KL 差、R=1 的 KL 零等价、尾内点混合、任何实际分布族的唯一全局极小性；也不声称最优常数、新颖性、LLT、条件 Lévy、hW 或根闭合。所有根 A/B/C/D 保持 OPEN。
