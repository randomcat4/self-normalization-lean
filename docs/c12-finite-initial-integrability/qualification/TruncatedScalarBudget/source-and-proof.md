# 真正截断标量预算与初始iid装配

来源 supplement3914–4025，Pinelis2011(1.10)及(1.7)复述Shao的截断自归一化标量输入；main1038–1076初始完成。所有四完整定理头及两个完整透明定义在实现前冻结，首轮kernel PASS。

scalarGamma2=n∫z²1{|z|>1/2}，scalarGamma3=n∫|z|³1{|z|≤1/2}，严格/闭cutoff及常数10.2=51/5保持。没有使用全局三阶矩；只假设平方可积。复用已接受TruncationIntegrals的完整预算分解t=1与放缩c=2：R(1)=8gamma3+4gamma2≤8R(0)，结合非负性得gamma2+gamma3≤2R(0)，从而10.2gamma2+25gamma3≤50R(0)。旧预算分解本身显式保证截断积分可积，未用默认积分值偷推。

实际iid产品律P=pi ν，n>0、中心性、n∫z²=1完整写入source接口；B/PB真实桥律、energy和normalizedEndpoint均为已接受定义。最后定理有一个明确命名hScalar的外部输入，逐点对同一真实P下W的闭CDF给10.2gamma2+25gamma3界；此输入是原文引用的标量定理，不在本模块证明、不伪装为新公理或已证结果。真实目标初始路径/完成误差不是前提。已证明预算支付将hScalar化为δ≤50R，消费有限路径4δ界，得到两个实际初始边际/closed-joint误差≤200R。阈值a/v保留，全部R取真实Shao.truncationBudget ν n 0，未更换成高矩预算。

hmean/hnorm/hn记录被引用输入的标准化/中心化合法范围；代数传递并不使用这些更强条件，接口未偷偷删掉它们。独立原cn:zero的16R证明仍未认证，零能量支付走已记录CDF原子路线。外部Shao标量定理的证明、完整compact/telescope/terminal/overshoot与C1/C2根仍OPEN。

按v71 baseline map验证TruncationIntegrals与Basic.TruncationBudget源/对象后只增两个readonly叶链接，未重编旧producer、改cache或版本。attempt001内核与全ownerAX PASS：7实际owner=5thm2def，4公开源定理，2完整值。全部新源UTF8无BOM/LF，指定服务器CPU14–17/c12-heavy.lock/-M8192-j4。
