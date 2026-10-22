# EnergyPathLaw 作者验证收据

作者实现与所需服务器机械门已通过。父上下文报告独立数学门通过；作者没有阅读其票。独立最终源码／形式门仍单列等待，本收据不自签 CORRECT。

## 冻结工件

- 冻结陈述：drafts/oq4/frozen-energy-path-law-v1.md，SHA256 `dcc050f7c229bbe6410dd5b9562bc4f349d6466b2e82ceeb70956dae7e545899`。
- 匿名证明：proof.md，SHA256 `6262f545ddd10fe868db3386b426d417cb53940fc1e3ab55375f79147dafc601`，保持证明阶段字节不变。
- 正式源：/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/EnergyPathLaw.lean。
- 本地相同源：drafts/oq4/energy-path-law/EnergyPathLaw.lean。
- 源 SHA256 `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536`，15246字节。
- 作者唯一一次生成的 olean SHA256 `6331d6941ff5d6c857191d5a4693035dfeb7ba811f2ba26dcf732c951a367669`。
- 作者专属原始产物目录：server repro_outputs/oq4-energy-path/。
- 源编码为无BOM的UTF-8，仅LF，冻结源末尾无LF；没有为格式重新改源或重发编译产物。

## 实际对象与实现范围

透明定义 energyPathIntegrand 逐字保留实际 closedStrip h 事件及 exp(s*(energy a−n)/h²)，事件外为零；energy 是共享实际坐标平方和。公开非负性、可测性、全空间支配和真可积定理保留 n=0。

可复用 finitePi_withDensity 从实际一维 ν.withDensity d 和实际 Measure.pi 出发，内部按 Fin.cons 首尾拆分归纳非负测试积分。每次用到现有 path_pi_lintegral_cons；截面与参数积分的可测性和概率／σ有限性均已交付。它允许调用者提供实际一维密度可测性及这个实际 withDensity 测度的概率实例，不接收“期望路径律有某密度”的假设，也不定义替代路径律。

energyPathLaw_withDensity 用实际 energyTiltedLaw=ν.withDensity(ofReal(w/Z)) 实例化该通用已证结论。Z>0、实际μ概率由既有真实一维接口内部供应；原ν只保留概率、平方真可积及单位二阶矩，并有 T≥0、h≥1、|s|≤T。没有原中心、第三／第四矩、支持或指数矩等新条件。

共享 closedStrip 逐坐标≤2h 只在实际事件内使用，先得到真实能量上界，再证明全路径空间 Φ≤exp(−sn/h²)*exp(4Tn) 以及真可积性。实际有限乘积密度另由一维真实截断权重的真可积性和有限乘积可积定理支付；事件质量转实只在该真正可积性下进行。截断乘积只在 A 上化成 exp(sQ/h²)，归一化因子严格保留 Z^n。

energyPathLaw_integral 同时返回真正可积性与冻结式(7)的积分等式。energyPathLaw_integral_iid 在任意可测概率空间、逐坐标可测／iIndepFun／IdentDistrib 环境中，直接消费共享 iid_samplePath_map_eq_pi；通过实际 map 的可积等价一起转移真可积性和同一实积分。事件和能量都是原 samplePath 的共享实际对象。

n=0的空乘积密度由真实空π测度处理，主结果不引入 n>0。所有弱闭边界、原子、h=1、T=0、s=0、零路径、Q=0和零生存概率均保留。只对内部已证正的Z／h²作必要归一化，不除以生存概率；s=0的μ仍是可能不同于ν的归一化闭截断律。Centering的导入仅用于冻结名称共存，证明体不调用θ、共同方差或选定参数log结果。

这只完成冻结式(7)有限路径身份叶，不宣称式(8)–(10)、相对渐近、完整E2/E3/E4、K/Kv、随机分母或完整OQ4根已关闭。

## 服务器门与计数

父确认基线：feat/oq4-centering-and-path HEAD1695839731c586cbeb34f157f9aec2246ec00c7a。父先给专属canonical／33模块窗口，另一作者仅scratch。正式写入前目标源与olean均不存在；旧32源摘要在写前、编译后及33共存审计后完全一致，完整33源前后摘要也一致。

全部Lean只在指定服务器按taskset -c 0-3单进程运行，激活后重新进入本工作树。没有重编任何旧target；作者是该新目标的唯一olean生成者。没有修改Git、common、rootimports、manifest、cache、锁或其他作者文件。无安装／下载／额外缓存请求。

工具链：leanprover/lean4:v4.36.0-rc1。mathlib：807d3836b165983210ee2ecf3cd28f239436949c。

| 检查 | 退出码 | 服务器原始记录 |
|---|---:|---|
| 旧32导入＋精确冻结源码体，全部getModuleIdxFor?none常量 | 0 | coexist-exactaudit.log／.exit |
| 正式canonical目标检查，不生成olean | 0 | target.log／.exit |
| 作者唯一一次-o生成目标olean | 0 | olean.log／.exit |
| 实际33模块导入、全新owner签名及全33传递公理 | 0 | audit.log／.exit |

target与olean日志均0字节。冻结源码共存和正式审计均零警告。早期API／实现草稿的类型诊断及一次审计脚手架ppExpr名称错误保留在服务器draft／api／scratch日志；它们没有改冻结数学证明，全部已在正式冻结门前解决。

精确源码无-o审计全取22个getModuleIdxFor?none常量。正式实际模块owner审计也全取22个常量，均收集完整逐项签名和传递公理；显式公开定理9、透明定义1、私有定理4、生成常量8。22个记录中16个为标准三公理，6个仅propext。全部33模块的owner与Shao.OQ4命名空间并集共637个常量，传递公理审计全部在标准三公理内。没有按命名空间漏掉私有或生成常量；导入名energyPathIntegrand.eq_1也包含在内。

summary.json包含全部22个完整签名／公理、9个公开定理名、各类别名称、旧32及完整33源摘要和实际退出码。declarations.md给出易读全签名账。rawlogs、olean及其他二进制仅在服务器。

## 复核入口

CoexistSource.lean为旧32实际导入后附精确源体（仅去除原import）；CoexistExactAudit.lean追加全新常量审计。Audit.lean使用真实33导入并按模块owner全取新目标常量，同时审计全33并集。summarize.py只整理实际记录、核对摘要／退出码／名字／完整签名／公理集合和无禁用词，不运行Lean或重发编译产物。

独立最终审查开始后源和证明均保持冻结，不再写canonical或emit。所有完整根状态仍OPEN。
