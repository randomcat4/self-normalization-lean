# OQ4 Rademacher 下一有限叶：真实整数状态保持与主余弦的精确有限幂 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

固定源 oq4/c01/spectrum01.md，第11–34行有限整数状态/谱对象及第36–56行模态和奇偶限制；sourcecommit35d4580b61e22e7145f47730045a09874ef93259，文档SHAb65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b。下一叶只实现已认证主一步对向真实有限迭代核传递所缺的支持连接及其主余弦有限幂推论，不宣称完整原有限谱或S1–S4。intake3b43e607f84854d162f4dd0adc772230f44c83046aaff70b7e5f904eef4f466e仅为只读范围侦察，不是数学/Lean认证。

拟新 Shao/OQ4/RademacherIteration.lean。只使用已存在真实 RademacherCosine.law、angle、rho 和 killedKernel、killedIterKernel、killedAction；不得另造抽象Markov链或矩阵自己的闭性以替代实际核结论。Shao/OQ4/RademacherCosine.lean已PR72独立认证，sourcec0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861；KilledIteration source03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5。新作者证明/实施须等本冻结来源语义独审CORRECT；Lean实施还须新鲜匿名数学独审CORRECT。

## 固定对象与全部前提

令 ν_R=RademacherCosine.law=(δ₁+δ₋₁)/2，概率性由已有内部实例给出。固定 m:ℕ、1≤m，h:ℝ满足 (m:ℝ)≤h<(m:ℝ)+1；H=(m:ℝ)+1，a=RademacherCosine.angle m=π/(2H)，ρ=RademacherCosine.rho m=cos a。

I_m={s:ℤ | −(m:ℤ)≤s ∧ s≤(m:ℤ)}，G_m={w:ℝ | ∃s:ℤ,−(m:ℤ)≤s ∧ s≤(m:ℤ) ∧ w=(s:ℝ)}，这是实际有限整数状态集，可透明定义为有限整数闭区间在实际Int.cast下的像。所有起点 r:ℤ 满足 −(m:ℤ)≤r≤(m:ℤ)，全部 n:ℕ 包含0。没有额外生存质量正性、归一化、平滑、其他模态或外部核输入。

## 冻结的有限结论

1. G_m 有限且Borel可测。对真实 killedIterKernel ν_R h n (r:ℝ) 有

∀ᵐ w ∂killedIterKernel ν_R h n (r:ℝ), w∈G_m，

即实际核在有限整数状态内保持；可同时给出真实核对G_m补集的质量为0的等价形式。不能只给 |w|≤h 的实区间支持，因为该条件不能保证整数点上的一步身份可用。ν_R 概率性与前置核的有限性、可测性、递推均沿既有真实接口内部供应。

n=0 时 killedIterKernel_zero 是起点Dirac，起点r∈I_m为必要且保留的条件；不得默称区间外起点在零步已被杀死。正步递推必须使用真实核组合/绑定，不以任意新矩阵递推当作实际迭代核。

2. 主余弦函数 f_m(w)=cos(a*w) 对上述每个实际迭代核真正可积，并有精确身份

∫w:ℝ, cos(a*w) ∂killedIterKernel ν_R h n (r:ℝ)
=ρ^n*cos(a*(r:ℝ))。

等价 killedAction 形式可作为对应辅助定理返回，但不能只给一个新定义函数的n次递推而不绑定现有 killedAction/真实积分。一步身份必须由PR72在整数状态上的真实主对获得，状态支持结论确保后续每层仅在合法整数点调用；不得将该一步身份静默延伸到全部实区间。

n=0 时ρ^0=1并恢复Dirac积分；r=0时恢复ρ^n。n任意，不增加长时间、n/h²或n/h³条件，不以渐近或上下界替代有限等式。

## 弱边界、来源强度与排除范围

h=m 时原子±m仍被保留，吸收点是±(m+1)，不把弱closed事件改成strict退出条件，不把退出行重新归一化。真实 killedIterKernel 为被杀死后的有限次概率核，不能额外要求其总质量为1；即使某个子概率核为零，a.e.支持及积分语言仍按原定义使用。

本叶只对整数起点的r+ℤ=ℤ状态类。其他实起点coset不可套用此G_m和同一频率；若另作一般整数平移版本须单独冻结两端吸收点，当前不做。1≤m保留PR72非退化主对范围；原源0≤h<1的独立零生存分支不在此叶关闭。

这里只迭代正的主模态，原全部模态的有限正弦族、零/负模态、正交与完备、单位函数展开、完整有限S1生存概率式、cot有限和、奇偶负谱项及S2–S4极限/弱strict端点分类均仍OPEN。不得用本主余弦加权积分冒称无权生存概率，不能声称它已给4/π系数或任意起点的完整核谱。n=0虽对主模态只用ρ>0，也不得据此允许将未来完整谱的0^0项删除。一般有限kernel/path-law桥已存在，不另算新的原始承重义务。

本叶可由必要透明def/测度支持/有限幂辅助声明组成；实际公开定理数待完整源码测量，不把定义/private/generated或等价形式当成额外独立原始义务。完整Spectrum/OQ4根保持OPEN。

所有Lean/重计算只在指定server，原始日志/二进制不复制本地。作者唯一新target emit，独立target no-o及完整原source所有getModuleIdxFor?=none无name/namespace筛选，actual imports与全部冻结旧OQ4共存并按owner OR namespace审计所有private/generated/outside-name常量及传递三公理；source/import完整name/kind/universe/fullExprtype/axioms逐项exact比较，父import-only核验。禁sorry/admit/newaxiom/unsafe/native_decide，白名单propext/Classical.choice/Quot.sound。数学/来源门通过后可私有scratch；canonical窗口单独由lead释放，与JointTransport不得同时写新canonical。冻结后不静默改事件、law、起点类、端点或量词。
