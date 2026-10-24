# 第 37 单元独立完整终审

STATUS: CORRECT

本次接受范围是 `Shao.C2.HalfLineTaylorRemainder` 的两个冻结精确恒等式。完整源码、两份证明、完整冻结导入与上下文，以及实际模块所属的全部 9 个声明类型均已逐项审阅。没有关键缺口。本单元不证明定量余项界，不识别实际布朗桥概率；C12/OQ3/OQ4/OQ56 原始根组仍全部 OPEN。

审稿人与作者分离，本上下文未参与实现。指定配置为 `gpt-6.1-sol`、`xhigh`；独立运行时模型遥测和分项用量不可见，输入、缓存输入、输出、推理子集均记为 `null`，不推算订阅额度。未创建子审稿人。

## 精确版本与机械证据

| 工件 | SHA256 |
|---|---|
| 完整源码 | `dfe56888ba1b95ec52c89efb5a420a7402271c2527b1eee011ba99d9763ed1d3` |
| 输出及安装对象 | `5532e9f4b568ed18cd24fee36f0c47aed6b1c956524a8e387f29401c561344ba` |
| 冻结完整上下文与两个声明头 | `a7fef4861210395c0fac04eb4d318d68f31e874bdeb861c424caaf3af1a46cdd` |
| 作者回执 | `c00cfa878129cf36ef4b9df6287583bde4c3b9bc50b33c4690e1a4096104fd27` |
| 作者释放文件 | `48ae62a85168dd31f4a46cba0aef84e8c7c6772a2d7967bd7e97a69335d6d7d8` |

去掉两份证明正文后，源码与冻结文件逐字节相同；源码为 UTF-8、无 BOM、LF。服务器当前源码、`attempt001/source.lean` 和本地冻结证明包的源码哈希一致；输出对象与工作树安装对象相同。作者回执的全部 7 个服务器工件均核对了完整字节数与哈希。分支 `author/c12-halfline-taylor-v71`、HEAD `39f0716ef70c0c388f2902a374860451df10ea27` 与回执一致。

复用作者唯一成功 `attempt001` 的内核退出码 0，以及实际模块所属声明递归公理审计退出码 0。审计用 `env.getModuleIdxFor?` 按真实所属模块选择，遍历全部所属常量，并对每项执行递归的 `Lean.collectAxioms`，覆盖私有、生成以及可能落在其他命名空间的名字。当前实际结果为 9 个定理、2 个公开定理、0 个非定理，未省略定义值。每项公理集合都包含于 `propext`、`Classical.choice`、`Quot.sound`。

全部 9 个完整类型块都与服务器原始审计日志绑定，类型名集合与审计所属映射完全相同。空定义导出的大小是 0，SHA256 为 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。源码未含 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。

固定版本为 Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，包视图为 `cache-overlays/shared-v34/packages`。只读核对了本证明所用 mathlib 泰勒、迭代导数、区间唯一微分接口；三个相关源码文件均与固定 HEAD 相同。作者检查资源为 CPU14–17、`c12-heavy.lock`、`-M8192 -j4`。本审稿人的 Lean 调用、审计重放、旧生产模块重编译、缓存写入均为 0。

首次只读证据采集因服务器没有 `rg` 中断，失败回应保存在 `remote-response.json`。随后以服务器已有文本搜索工具完成读取；未执行任何 Lean 命令，未重放成功证明检查。原始编译日志仍只保留在服务器；本地仅保存其哈希和审阅摘要。编译日志只有已有 mathlib 工作区提示及无效/冗余策略提示，没有错误；相关被消费的 mathlib 源码另已验证固定 HEAD。

## 原文与标量路径

完整读取只读 `C:/game/shao/current/c12/supplement.tex` 第 4192–4253 行。整文件哈希为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，保留原始行尾的 2624 字节片段哈希为 `7c114b02812a59089a18904d502318e4ac65a8574c7a80f735aa16dc3a8283f2`。

设 `U(θ)=u−θb`、`E(θ)=T−θb²`，则本模块实际消费的透明定义给出

\[
g(\theta)=1-\exp(-2U(\theta)v/E(\theta)).
\]

时间路径是 `T−θb²`。它在 θ=1 处对应一次揭示后的能量 `T−b²`，其时间速度恒为 `−b²`。源码没有换成 `T−(θb)²`。

上半直线中 `u=a−y`、`v=a−z`，所以 `u−v=z−y=d`，物理空间导数是 `−slopeTime`，冻结补偿项准确为 `(b−b²d/T) f_y`。下半直线须令归一化位移 `β=−b`、归一化差值 `δ=u−v=−d`，从而 `U=u−θβ=u+θb`、`E=T−θβ²=T−θb²`，并有

\[
(\beta-\beta^2\delta/T)(-\mathrm{slopeTime})
=(b-b^2d/T)\mathrm{slopeTime}.
\]

这正是下半直线的物理补偿项。下反射时奇次位移项变号，四次、六次位移项不变。

## 两份完整证明

### 三阶路径分解：源码第 8–24 行

记 `B=2v/E`、`C=2Uv`、`q=−C/E`。已接受的透明定义分别为 `slopeTime=B exp(q)`、`curvatureTime=−B² exp(q)`、`timeCompletion(C,E)=1−exp(−C/E)`。`f_u=slopeTime`、`f_uu=curvatureTime`、`f_uuu=B³ exp(q)`。

沿仿射路径 `U′=−b`、`E′=−b²`，全部三阶链式项为

\[
g'''=-b^3B^3e^q-3b^4\,\mathrm{curvatureTime}_T
      -3b^5\,\mathrm{slopeTime}_{TT}-b^6\,\mathrm{timeCompletion}_{TTT},
\]

所有时间导数均在 `E(θ)` 处求值，`U(θ)`、`v` 在时间求导时固定。系数 1、3、3、1 和四个负号来自 `(-b∂_u−b²∂_T)^3`，没有丢弃混合项。

源码先用第 36 单元实际 `deriv (deriv g)` 的 `HasDerivAt` 证书得到真正的 `g'''`，再用第 34、33 单元中 `curvatureTime_T`、`slopeTime_TT`、`timeCompletion_TTT` 的实际导数证书重写右侧。它们只要求 `E>0`，当前 `hE` 正好满足；没有套用需要正空间端点的定量轮廓定理。

独立代数核对：设 `A=2vb(T−ub)`，则 `q′=A/E²`，已接受三阶路径导数为

\[
-\left(A^3/E^6+6A^2b^2/E^5+6Ab^4/E^4\right)e^q.
\]

将三个时间导数的完整已接受公式代入冻结分解，展开 `A`、`U`、`E`，得到同一式。源码最后的分母消除与环运算只需 `E≠0`，由 `hE` 获得；不需要除以 `u`、`v`、`b` 或 `A`。因此 `b=0`、`v=0`、`A=0` 等退化情形也覆盖。

### 真正的拉格朗日补偿余项：源码第 26–62 行

前提完整保留 `T>0`、`b²≤T/2`；`u`、`v`、`b` 任意实数。第 35 单元区间能量接口给出任意 `t∈[0,1]` 时 `E(t)≥T/2>0`。第 36 单元因此在每个这样的点给出任意有限阶 `ContDiffAt`，源码取三阶并转成整个闭区间的 `ContDiffOn ℝ 3`。

实际调用的固定 mathlib 定理是

```lean
lemma taylor_mean_remainder_lagrange_iteratedDeriv
    {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ (n + 1) f (Set.uIcc x₀ x)) :
    ∃ x' ∈ Set.uIoo x₀ x,
      f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
        iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / (n + 1)!
```

源码取 `n=2`、`x₀=0`、`x=1`，以 `0≠1` 证明闭区间唯一微分性质。对任意 `n`，`iteratedDerivWithin_eq_iteratedDeriv` 的三个完整条件分别是此唯一微分性质、展开点 0 附近的实际 `ContDiffAt ℝ n`、以及 `0∈[0,1]`。源码全部给出；没有仅用端点的区间内光滑性来冒充实际导数。

`taylor_within_apply` 的求和恰含 k=0、1、2；步长为 1，阶乘系数分别为 1、1、1/2，因此多项式准确等于 `g(0)+g′(0)+g″(0)/2`。mathlib 给出的无序开区间通过 `0<1` 化为 `Ioo 0 1`，并给出

\[
g(1)-g(0)-g'(0)-\tfrac12g''(0)=\tfrac16 g'''(\theta),
\quad 0<\theta<1.
\]

最后加入第 36 单元冻结的精确二阶补偿恒等式

\[
g'(0)+\tfrac12g''(0)
 -(b-b^2(u-v)/T)(-\mathrm{slopeTime}(u,v,T))
=b^3\,\mathrm{slopeTime}_T(u,v,T)
 +\tfrac12b^4\,\mathrm{timeCompletion}_{TT}(2uv,T).
\]

两式相加就是当前冻结结论。源码的最终线性组合没有额外前提；两个残余时间项均为正向相加，第一项为三次位移、第二项为四次位移且系数 1/2。`b=0` 时仍有非空区间中的见证 θ；所有项均为零。`b²=T/2` 时整段能量仍至少 T/2，端点等号不会破坏光滑性。当前定理不声称能量为零时的公式。

## 全部实际所属类型覆盖

| 实际声明（共同前缀 `Shao.C2.HalfLineTaylorRemainder.`） | 完整类型审阅结果 |
|---|---|
| `third_path_derivative_decomposition` | 任意实数五参数，仅假设当前能量正；真正三次实际导数及全部四项、求导点、系数和符号一致。 |
| `compensated_lagrange_remainder` | 任意实数四参数，完整保留两个能量前提；存在开区间内 θ，实际三阶导数、源补偿、两个时间余项与冻结声明一致。 |
| `third_path_derivative_decomposition._simp_1_1` | 泛型 `NeZero 2` 下 `(2=0)=False`，类型类前提完整。 |
| `third_path_derivative_decomposition._simp_1_2` | 泛型 `NeZero 3` 下 `(3=0)=False`。 |
| `third_path_derivative_decomposition._simp_1_3` | 泛型 `NeZero 4` 下 `(4=0)=False`。 |
| `third_path_derivative_decomposition._simp_1_4` | 无零因子乘法中，两非零因子之积等于零的命题等于 `False`。 |
| `third_path_derivative_decomposition._simp_1_5` | 约化带零幺半群中，非零元素任意自然数次幂等于零的命题等于 `False`，含 n=0。 |
| `third_path_derivative_decomposition._simp_1_6` | 带零群中，非零元素任意整数次幂等于零的命题等于 `False`，含负指数。 |
| `third_path_derivative_decomposition._simp_1_7` | 特征零加幺半群中，自然数铸型加一等于零的命题等于 `False`。 |

逐项完整类型块的行号、字节数、哈希、递归公理集合与原日志绑定列在 `actual-type-coverage.json` 和 `full-review.json` 中。没有以公开声明数代替实际所属计数；生成项全部覆盖。

## 已合格依赖复用

| 单元 | 模块 | 独立完整复核 JSON 的 SHA256 |
|---|---|---|
| 36 | `HalfLineTaylorPath` | `18e6ccf8ab0d013d9875b864153a48fbe4c587a464149366455312be19e9f2ee` |
| 35 | `HalfLineTaylorSegment` | `0ff0cc92f656a87761ab28d636b7c4d141b13f4d0c89ad874e0273fec9f6fae7` |
| 34 | `HalfLineMixedProfiles` | `08f1a0c45b250d3763b38dec80a1b5e834af6e55a474f0fbfa5f41d5646d90a3` |
| 33 | `HalfLineTimeProfiles` | `92378ff6a2bf4a732a27927ccc9989ea1f8d4fd94e3885c8a7f5af1bff521c14` |

四份报告均为合格完整独立 `CORRECT`，其源/对象、作者回执、作者释放文件均作哈希绑定，释放文件均为无在途。四份当前服务器源码、输出对象及安装对象再次只读核对为相同已接受版本，并与第 37 单元回执的直接依赖哈希一致。完整消费接口及七个透明定义值已经读取；旧证明未重审、未重编译。mathlib 泰勒定理按固定外部依赖明确归属，不作为本项目新定理贡献。

## 仍未覆盖的原始目标

本单元只闭合精确标量路径分解和存在中间点的补偿余项。仍须由后续源绑定单元证明统一定量小余项界，并显式加入空间闭域、端点等必要条件；实际完成核与布朗桥反射概率的识别、区间核的完整条件及其余源目标仍按现有依赖链处理。不能把此有限解析恒等式当作任一原始根定理的闭合。

审稿人仅在自己的报告目录写入工件，未改生产源码、冻结文件、共享协调文件、Git 或缓存。最终无重型命令、无在途操作；确切释放状态见 `writer-release.json`。
