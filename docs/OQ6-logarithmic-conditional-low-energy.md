# OQ6：原对数截断下的真实条件严格低能量界

本模块把已合格179的最终统一低能量界接到原对数截断。保留原μ、h、w、α、τ、p输入和真实投影g，令β=∫|g|^p dμ，t0=(1/(8β))^(2/(p−2))、c0=t0/4。对每个实J≥0，精确取A=2(J+1)/(1−2/p)。固定一次179的阈值NL，再取T=τ·NL^α/A、Nlog=ceil(max(3,exp T))。该选择给出Nlog≥3，所有n≥Nlog的原Rn=(A log n/τ)^(1/α)均达到NL。

在Cn={w≤Rn}、真实ν=(μ Cn)⁻¹·μ|Cn下，对所有3≤m≤n且n/2≤m，按实数域取lam=(m−2)/(n−2)。H=g+g′+lam r、κ=∫H d(ν×ν)、G=∫H dν−κ、σ2=∫G²dν、σ=sqrt(σ2)、X=G/σ均使用原定义。在真实Pm=Measure.pi(fun _:Fin m=>ν)下，σ>0、Pm概率、严格事件E={sum X_i²/m<1/2}可测，并且

    Pm.real E ≤ exp(−(c0/2)n)。

证明完整支付ceil/log/rpow反演的正域；严格事件逐点包含于179的闭事件，无需等号边界无原子性；Pm概率使实值测度单调性合法；c0>0、m≥n/2支付负指数比较方向。NL在当前J/n/m/lam之前固定；选择谓词内部原有的R/lam/m全称量词保留。没有另加自由投影、免费Laplace、更高混合矩或g与w独立性。

最终精确生产源SHA256为4ac22d7bcc76014232e19428d67ed5eab29bdffc1fca7412bb8c7e73306e3fd4（13799B、285LF），公开定理actual_logarithmic_conditional_low_energy。2404B公开头cd770486046e829ba2668b0d6d35308ce542f8ab8896cf27edfed469038a841c保持。冻结20公开值、23证明数据、17inline族、8实例族、41实际have、76let/letI、266源块、84完整源码前缀及89字段/44唯一作用域均有完整独立覆盖。历史格式修复仅增加匿名section的end（5B/2LF）；完整11111B证明体未改，旧字节与精确逆变换保留。

指定服务器Lean4.36.0-rc1/mathlib807d3836b165983210ee2ecf3cd28f239436949c下，kernel实际DIRECT0/7.708455618470907秒，生成同一对象1caa64d0c6837d7a0d8cd1131a814012d68d9872da92e967e2ad8498715eea55（671120B），4576项FULLFP/Git保持。import-only/no-o整环境实际模块所有权审计DIRECT0/5.280830848962069秒，4586项FULLFP/Git保持；实际1公开thmInfo、0生成、0非定理完整值，完整TYPE27090B/373LF已独立逐字读取。递归公理propext、Classical.choice、Quot.sound各1。5条源风格警告及现有134B Lake提示保留；没有为清警告改源或重编译。kernelreceipt786856c416f05ba86b80eb09c5c81371ee55dd6ebd0d3fef556e09937c3e1bc3，auditreceipt5c4546e8f44e2e407f65976977f0cd0905872a64807e3e65087a8070ca4c8f7c。

同一全新独立上下文分两阶段完成完整源码审查及实际TYPE/VALUES/AX终审，结论CORRECT，独立资格9d57956c2a967deb03a52ac96e1c907dfe9ec095899332efd330561ef962f69c。父级最终接收核对92处本地引用/42文件、精确源与对象及全部接受门，资格b31ba97deed122e35ea60fc8c106782436665de8c7c432f4752cc0aae1af7fc8。两份原字节审查报告、父级与独立资格随提交提供：最终报告中的历史相对路径表示本地证据目录，源码阶段报告的仓库副本为[源码审阅](OQ6-logarithmic-conditional-low-energy-source-review.md)，完整自含最终报告为[终审](OQ6-logarithmic-conditional-low-energy-review.md)。179仅复用合格接口和已有精确证据，未重放旧证明或检查。

本组件只支付p51 S3/S11条件低能量半项和S6/S28后的统一条件常数消费者。p54对任意多项式标准化p矩变化率的否定保持，只消费eventual≤2β；p44两条基核分支不拼接。Shao–Zhou(92)、行集中和随机区间引擎保持外部归属；ordinary hSZ、W截断、实际大余项、严格source预算、upper/compact相对引擎、均值位移/Mills比、增长窗和OQ56/C2/C12根闭合仍OPEN。无新颖性认证。本PR供Root接收，不执行合并。
