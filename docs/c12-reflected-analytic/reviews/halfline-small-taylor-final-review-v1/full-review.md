# HalfLineSmallTaylor 独立最终审查

STATUS: CORRECT

这版局部单元没有关键缺口。已在独立新上下文完整读取五份证明、完整冻结上下文与五个声明头、二十个实际所属完整类型，并核对完整空定义值导出。接受范围为显式标量半直线的补偿小泰勒界，常数取 8000100。实际布朗桥概率识别、区间小泰勒结果及所有原始根组继续 OPEN。

## 原文到陈述

完整读取只读 `C:/game/shao/current/c12/supplement.tex` 第4192–4253行，重点4234–4242。原文要求严格内部旧点与终点、T>0、b²≤T/2、新点在闭域，并控制补偿余项的 |b|³T^(-3/2)D³P_b。模块的实数参数 u,v,T>0、u-b≥0 与此一致，没有新点距墙正下界。

上半线代入 u=a-y、v=a-z、归一化步长等于实际 b，得到 u-v=z-y=d，空间导数是 -slopeTime。下半线代入 u=a+y、v=a+z、归一化 β=-b，得到 u-v=-d；归一化补偿系数为 -(b-b²d/T)，乘 -slopeTime 正好给出实际正向导数的补偿。两侧 |β|=|b|、|u-v|=|d|，incrementProfile 恰为 exp(-max(u-|b|,0)v/T)。T>0 下 (1/√T)³ 就是 T^(-3/2)。这些是标量公式的语义映射；本模块未另行完成实际概率对象的识别。

b²≤T/2 保证整个路径剩余能量至少 T/2>0。新点可在墙上：u-b=0 时 g(1)=1-exp(0)=0，符合正能量下的零扩展。拉格朗日见证严格在 (0,1)，因旧点 u>0 与新点非负，见证处 U=u-θb>0，所有剖面引理条件成立。b=0 同样被覆盖；终点 v=0、零能量与新点在域外均未被声称覆盖。

## 五份证明的完整审阅

1. 第9–17行 `normalized_power_domination`：将 q^(3+k) 写成 q³q^k，0≤q≤1 给出 q^k≤1；D≥1 与 j≤3 给出 D^j≤D³。乘法的非负条件明确，k 没有被限制到有限枚举。
2. 第19–109行 `third_path_profile_at`：E>0、s=√E>0，b²≤E 给出 |b|≤s，因此 q=|b|/s∈[0,1]，D=1+|U-v|/s≥1。完整使用已合格的四项三阶分解：-b³空间三阶项、-3b⁴ curvature_T、-3b⁵ slope_TT、-b⁶ timeCompletion_TTT。四个绝对值界依次为 13824q³D³P、18432q⁴D²P、2400q⁵DP、108q⁶P；第一系数为24³，随后为3·6144、3·800、108。逐项按归一化幂引理控制到 q³D³P 后相加，13824+18432+2400+108=34764。三次三角不等式包括全部混合项；平方根消去时使用 s²=E 与 s≠0，没有丢失符号或除零。
3. 第111–139行 `third_path_segment_bound`：源小步前提给 E≥T/2≥b²，θ<1 给 U>0。位移 U-v=(u-v)-θb 后调用完整剖面搬移 r=j=3，代价2³3³=216；34764·216=7509024≤8000000。公共剖面非负，常数放大有效，不需终点 θ=1 的严格距离。
4. 第141–192行 `compensation_correction_bound`：完整补偿残差 b³ slope_T+(b⁴/2)timeCompletion_TT，两项分别由混合时间界80与纯时间二阶界12的一半得到80q³DP、6q⁴P。归一化到 D³ 后常数为86；再在θ=0使用剖面搬移将 P换为P_b。q≤1从小步前提推出，所有绝对值因子、三角不等式与分母非零均显式处理。
5. 第194–225行 `compensated_small_taylor_bound`：调用已合格精确拉格朗日恒等式，见证θ∈(0,1)。余项为 g三阶导数(θ)/6 加上述完整补偿残差；重结合只用环恒等式。三角不等式与前两界给出 (8000000/6+86)K，其中K≥0；该系数为4000258/3，确实≤8000100。常数刻意宽松满足原文存在通用常数的要求，没有必要优化。

## 实际归属与定义

原审计按 `env.getModuleIdxFor?` 选择实际所属，逐个调用递归 `Lean.collectAxioms`。二十项均为定理，五项公开，零项非定理。完整37636字节实际类型导出已分块无删节读入，没有字典替代。所有块与服务器原审计日志逐字绑定；`actual-type-coverage.json` 给出每项的类型块哈希、行号、语义与公理。

除五个公开定理外，十四个 `_simp_1_*` 类型完整保留泛型实例条件，分别是非零数值2/3/4、无零因子乘积、约化幺半群自然数幂、带零群整数次幂，以及特征零自然数嵌入加一的非零命题化简。另一项 `Shao.C2.HalfLineTaylorSegment.segmentDistance.eq_1` 虽在依赖命名空间，实际归属本模块，已完整审查并纳入：它只陈述 segmentDistance u b θ=u-θb。没有按命名前缀遗漏它。所有传递公理仅 propext、Classical.choice、Quot.sound。

完整 `actual-definition-values.txt` 为0字节，SHA256为空文件标准摘要；实际所属审计确认二十项全为定理，故空导出确为完整。源文件不存在 sorry、admit、新 axiom、unsafe 或 native_decide。

## 冻结、依赖与服务器证据

本地源码为12519字节，SHA256 `ec71f48b36d548b4fb9f07792a26ec16bddd72f01f1d214f46f379d4aabc3855`；冻结完整上下文及五头摘要 `4acc95461a036d6c9c13cd69c434b85ffa5553ac42f4f18475878980a0f8f6da`。脚本去除全部证明后与冻结文件逐字相等，UTF-8无BOM、LF、CR数0。服务器三次尝试的完整冻结上下文和五头完全一致；失败001/002保留，最终003修复未改数学接口。

服务器只读观察确认当前源码、attempt003/source.lean、本地包一致；输出与安装对象摘要均 `19698aeeed84a98630fabf9d8302cd6020ff59e35a5de55be9e17dae00ecc75c`。原作者回执摘要 `d083517b824b914ac5e55020c9ee3c6816d89a0b8a709574ae0f7096714cda0f`，零在途作者释放摘要 `09f3deb87c4e9c675361f26917c9cbdd0a076bec89a35f08713d7c9626eaecc5`。全部回执工件的服务器字节摘要一致。

复用作者 attempt003 内核退出0、全部实际所属传递公理审计退出0。完整成功日志已读，只有既有mathlib工作树提示与未执行/未使用/风格检查提示，没有 error。分支 `author/c12-halfline-taylor-v71`，HEAD `39f0716ef70c0c388f2902a374860451df10ea27`；Lean `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，只读包视图 shared-v34，均匹配回执。资源回执为CPU14–17、c12-heavy.lock、-M8192、-j4。

复用单元32–37的六份已合格完整独立审查；每份报告摘要、作者回执、零在途释放均核对，当前依赖源/输出对象/安装对象逐项一致。完整读取本证明消费的九个冻结接口和七个透明定义值（g、E、U、incrementProfile、slopeTime、curvatureTime、timeCompletion），记录于 `consumed-project-interfaces.json`。时间剖面使用既有最终 `frozen-v2.lean.txt` 摘要7afb638c…；原 `frozen.lean.txt` 摘要34cbaa9c…按历史保留，先前合格审查已说明v2只增Deriv.Pow导入，接口未变。本轮未重审依赖旧证明，也未重放任何成功编译或审计。

## 独立性、使用与释放

作者与审查上下文分离，按明确委派配置记录 gpt-6.1-sol / xhigh；独立令牌计数不可见，input、cachedInput、output、reasoningSubset各为null，不估算订阅百分比。只写本审查报告目录，生产/冻结/共享/Git/缓存修改0，Lean调用0，审计重跑0，旧生产模块编译0，新增子代理0。

本报告只接受当前冻结局部标量半直线结果。C12、OQ3、OQ4、OQ56原始根组全部OPEN；OQ3仍按用户暂停。报告完成后的 `writer-release.json` 记录writerReleased=true、executionReleased=true、heavyInFlight=false、inFlight=[]。
