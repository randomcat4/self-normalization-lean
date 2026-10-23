# 冻结数学目标：实际布朗存活事件的零边界与端点

FROZEN_MATHEMATICAL_TARGET，未证明/未形式化；math-theorem/no math-ultra。源 C:/game/shao/current/oq4/b01/proof01.md255–259（杀死概率连续集段），整文件SHA7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38。

对象为任意可测样本空间Ω、概率测度P及实际标准实Brownian过程B:NNReal→Ω→ℝ，假设Mathlib ProbabilityTheory.IsBrownianReal B P。必须使用这个实际过程，不选择另一个Brownianlaw来替换原过程；可使用并证明其a.e.连续性、零起点、有限维Gaussian与独立增量等既有接口，不添加连续/可微/有界路径、强Markov或reflection公式为新前提。

对T:NNReal且T>0，u∈[-1,1]，定义真实原始事件

closedSurvival(B,T,u)={ω|∀t:NNReal,t≤T→|u+B_t(ω)|≤1}
strictSurvival(B,T,u)={ω|∀t:NNReal,t≤T→|u+B_t(ω)|<1}。

冻结目标：两事件NullMeasurableSet于P；P(closedSurvival\strictSurvival)=0；并显式推出u=1和u=-1时P(closedSurvival)=0。必须解释在Brownian a.e.连续且compact时域上，这个差事件恰好是实际sup_{0≤t≤T}|u+B_t|=1的事件（a.e.），因此它是源中所需零边界概率，不能只证任一固定正时间B_t无原子。T=0不在零边界结论范围，须说明端点T0会失败；u=±1必须保留，不能静默只证interior。

完整数学proof需给承重Brownian事实的真正推导或精确已形式化库接口：若用reflection principle/strongMarkov/立即crossing，不能把这些缺失结论当新假设/axiom；若使用外部经典事实，明确外部归因与未形式化断点，不能据此宣称Lean可闭合。可选择Gaussian bridge conditioning、独立增量/对称性/germ 0–1、已有Brownian库工具或其它完整路线，但所有量词与可测性必须兑现。数学作者只先交完整证明及public/private exact Lean声明和定义值/API提案；lead冻结exactformal以后才实现。不自动复制过往已接受BrownianSup/有限维旧proof，也不能把本目标等价改名为新的Lemma假设。

这是B0/B1后续弱极限到杀死连续集的独立真实源依赖，不依赖124unified mechanism。先行B2/B3/rowGaussian/FDD/Cpath紧性无论如何都不能替代它。此目标只闭合上述Brownian事件连续集和端点概率；变行弱极限、变化floor时间/starting u_j/strip/terminalobservable回接、B4/B0/B1/K/Kv/所有root仍OPEN/rawleaf0。标准axioms propext/Classical.choice/Quot.sound；no sorry/admit/newaxiom/unsafe/native_decide/partial；任何最终Lean均指定服务器。
