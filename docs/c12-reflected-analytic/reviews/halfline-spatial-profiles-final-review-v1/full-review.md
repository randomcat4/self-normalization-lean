# 第32单元独立完整终审

STATUS: CORRECT

本轮独立审查最终冻结的 `Shao.C2.HalfLineSpatialProfiles`，覆盖全部源码证明、六个完整冻结声明、全部六个实际所属常量的完整实际类型，以及原文到陈述的对应关系。未发现关键缺口。作者与评审分离；评审仅写本目录，没有修改生产源码、冻结文件、共享文件或 Git，也没有启动 Lean、重复成功审计或重编旧依赖。

## 版本和凭据

- 最终源码：`748ef00e57c2d88ded95208cd4e961916d261b99f91894c2bd15014637e81729`，5992 字节，UTF-8、无 BOM、LF。
- 冻结文件：`705827b18094d40f132b67051d1aeb215f50623a732ffb09099a30246964ab3f`。六个完整定理头以及导入、命名空间上下文逐字节一致。
- 编译对象：`2533120d2cf347520ff211d04e08e6e5028d875e16e4cd34738e3b57faeb1635`，479096 字节。当前生产源码、attempt002 成功快照、输出对象及工作树安装对象均与收据相符。
- 作者收据：`9de139bd129f82d53a7de855b0ffb1497044772b684138a0786280fd6aaee2fc`；作者释放：`06d64a062b1a6e921f26423709ddcedb1f465077663b70c7eafbd902aa344828`。
- 复用 attempt002 内核退出码0和实际全所属递归公理审计退出码0；九项原始远程工件的大小及 SHA256 全部与收据一致。完整实际类型导出17812字节，每个完整块都逐字节包含在该审计日志中；实际定义值导出为0字节，与实际无定义一致。
- Lean `leanprover/lean4:v4.36.0-rc1`；mathlib `807d3836b165983210ee2ecf3cd28f239436949c`；共享只读 packages 视图为 `cache-overlays/shared-v34/packages`。原检查使用 CPU14–17、c12-heavy.lock、-M8192、-j4。本轮只是只读核对既有工件。
- 观察时分支为 `author/c12-uniform-permutation-law-v71`，HEAD `fe32939af989d80cfebfb9c245d456a63b262ce6`；验收绑定源码/对象本身，不将其误记为已提交或已发布。

## 原文范围和忠实性

已完整读取只读 `supplement.tex` 4192–4253。原文的 f 是严格布朗桥存活概率，而本单元中的 `upperReflection`、`lowerReflection` 是已冻结的显式实标量公式 `1-exp(-2uv/T)`。本单元正确实现的是原文4227–4228导数界中的**半直线显式公式、时间阶 l=0、任意正自然空间阶 j**，并给出对所有自然 j 的精确导数公式；没有把标量计算当作已证明真实概率反射恒等式。

固定墙和末端点，只对起点 y 求导。上墙取 u=a-y、v=a-z；下墙取 u=a+y、v=a+z。严格内点及 T>0 恰好给出 u,v,T 正性；D=1+|z-y|/sqrt(T)，两剖面是 exp(-uv/T)。结论中的 `(8*j/sqrt(T)*D)^j` 等价于 `(8j)^j T^(-j/2) D^j`，因而可取 C_(j,0)=(8j)^j，常数仅依赖 j。没有增加端点距离的统一正下界。源码允许标量 a 为任意实数，是对原文 a>0 情形的有效推广。

零阶精确值由两个精确导数定理的 j=0 分支覆盖；对应 exp(-2uv/T)<=exp(-uv/T) 的剖面比较复用单元30的已合格 `reflection_deficit_le_profile`。本模块没有单独新增零阶剖面命名定理，正阶剖面定理的 hj:0<j 没有被省略。

精确导数公式对任意实 T 成立，因为 Lean 中实除法在0处总化，且每个固定 T 的表达式仍是指数仿射函数。T=0 时显式 f 为0，f-1为常数-1：零阶右侧为-1，正阶右侧为0。这只是标量总化行为，**不是**原文零能量存活概率或墙上/墙外扩张的定义或证明。剖面界始终明确要求 T>0 和严格内点。

## 六个完整证明逐项审查

1. `scaled_reflection_slope`（源码7行）：在时间 MT 调用旧的正距离斜率界。由 M>=1、T>0 得 MT>0、sqrt(MT)>=sqrt(T)>0。非负倒平方根及绝对距离项分别比较，再乘 M>0。代数恒等式 M*(2v/(MT))=2v/T 给出所需缩放界。不存在除零或乘负数翻转方向的问题。
2. `positive_reflection_power_profile`（26行）：j>0 通过精确自然数转实数给出 j>=1；M=2j 满足前一引理。底数 `(2v/T)*exp(-uv/(jT))` 非负，故可合法提升至自然数 j 次幂。`Real.exp_nat_mul` 消去指数分母的 j，得到 `(2v/T)^j exp(-uv/T)` 的界。最后乘正数 exp(-uv/T) 并用指数加法，把左边恢复为 exp(-2uv/T)，右边保留 exp(-uv/T)；未错误地丢掉剖面指数。
3. `upperReflection_iteratedDeriv`（55行）：整条实函数 f(u)-1 恰等于 `-exp(b)*exp(c*u)`，b=-2a(a-z)/T、c=2(a-z)/T。使用固定库的全阶指数公式和域上的常数乘法公式，得到 `-c^j exp(b+c*y)`，最后仿射指数的恒等式给出冻结右侧。这不是依靠非可微函数的总化导数为0。
4. `lowerReflection_iteratedDeriv`（79行）：b=-2a(a+z)/T、c=-2(a+z)/T，同样在整条实线上建立函数相等。最终为 `-c^j exp(-2(a+y)(a+z)/T)`。幂内 c 的负号与外层负号都保留，奇偶阶、c=0及j=0正确。
5. `upperReflection_iterated_profile`（103行）：精确导数取绝对值后，系数由 T>0、z<a 保证正，指数因子严格正。将 u=a-y、v=a-z 代入幂剖面引理；u-v=z-y，剖面定义与目标一致。
6. `lowerReflection_iterated_profile`（113行）：绝对值消去外负号及幂底负号；系数 2(a+z)/T 由明确前提为正。u=a+y、v=a+z 均正，u-v=y-z，经绝对差对称得到 |z-y|，剩余指数是目标 lowerProfile。

## 消费接口和独立证据复用

已完整阅读消费的 `positive_reflection_slope_bound` 实际类型、四个标量定义的实际类型及完整透明值，并核对单元30的零阶比较完整类型。单元26和30的当前源码、成功快照、输出/安装对象及类型/值工件均匹配其旧合格版本。复用完整独立终审：单元26 `7f994541cb9e7999a0007570f92314086c9f5db9e999c171716c0d5a4e7a3240`；单元30 `1fcc2466a834a04850bc45b0287058b02dd89443edbaa2dc6209b5a04d13a81f`。本轮没有重编旧生产者，也没有因上下文更换而重新要求旧完整证明审查。

固定 mathlib 的 `iteratedDeriv_exp_const_mul (n:Nat) (c:Real)` 给出整函数导数 `c^n*exp(c*s)`；`iteratedDeriv_const_mul_field` 对范数域到范数除代数的常数乘法没有可微性前提，实数实例满足其类约束。两文件逐字节等于钉死提交的 Git 内容，故日志中的共享包“本地修改”提示没有在这两个消费文件上形成版本漂移。另核对实数 `exp_nat_mul (x:Real) (n:Nat)` 的完整类型及证明、非负底数 `pow_le_pow_left₀` 的完整接口。

## 实际所属及公理覆盖

完整读取 `OwnedAudit.lean`：它遍历 env.constants，并通过 env.getModuleIdxFor? 确定实际所属模块，再对每个目标所属常量运行递归 Lean.collectAxioms；既未以名字前缀筛选，也未只筛选公开定理。实际所属全集恰为上列六个公开定理，零定义、零其他。六个完整实际类型逐项吻合冻结声明，未出现隐式新增假设、替代对象或量词弱化。每个递归公理集合均为 propext、Classical.choice、Quot.sound；源码无 sorry、admit、新 axiom、unsafe、native_decide。

attempt001 的失败源码和日志均保留；与最终源码的唯一字节变化是两处 `Real.iteratedDeriv_exp_const_mul` 改为全局 `iteratedDeriv_exp_const_mul`，位于证明体。该修复没有改变导入、声明、量词或假设。最终 attempt002 无错误；原成功检查没有被重放。

## 判决与边界

冻结局部目标正确，证明完整，机械证据可按精确源码复用，结论 `CORRECT`。不存在本冻结目标内部未覆盖的关键缺口。此处不作新颖性认证，属于原文指定解析依赖的形式化。

真实布朗桥概率的反射恒等、真实区间核正则性/高阶导数、时间和混合阶剖面、墙上一侧估计、补偿 Taylor 余项及原始根定理，均未由本单元证明；其他单元已取得的不同范围结果保持其原范围。所有原始 C12/OQ3/OQ4/OQ56 根组仍为 OPEN，OQ3 的用户暂停不受影响。

评审模型配置为明确指定的 gpt-6.1-sol/xhigh 新上下文；实际分项 token 计数不可得，input、cachedInput、output、reasoningSubset 均记录 null。完成后本评审的写入和执行权释放，零在途任务。
