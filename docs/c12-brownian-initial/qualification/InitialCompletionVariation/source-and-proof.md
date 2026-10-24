# 闭端点初始完成函数变差与可积性

来源 main.tex 1038–1076，cn:initial 证明中 TV(g_x 1_{w≤v})≤C+1 的步骤。公开接口在实现前冻结于 frozen.lean.txt，五个完整定理头未改变，证明最终源SHA见 frozen-comparison.json。

一般 cutoff 定理以任意0≤f≤1为输入，逐有序有限划分证明。令q(w)=1_{w≤v}，当x≤y时，截断增量绝对值≤|f(x)-f(y)|+q(x)-q(y)。单次穿越v包含≤号所在一侧，q差非负并望远镜求和≤1，故总变差≤TV(f)+1；不假设f连续、端点无原子或f无跳跃。消费已接受初始区间完成函数TV≤2，得到闭阈值变差≤3。

可测性使用已证明可测的路径范数事件 initialSurvival 在桥坐标上的测度截面，并逐点识别为strictInterval a 0 1 w；不是从不可数坐标可测性跳跃。0≤intervalCompletion≤1在任意概率端点测度下给出可积性；闭Iic遮罩仍可积。所有a,v为实数，未改变正宽原文范围，a≤0自然空事件也合法。

服务器attempt001仅有证明接口方向/展开失败，原源保留attempt001.lean；attempt002内核PASS。沿用Established OwnedAudit，按实际module owner覆盖9项=9定理、0非定理，其中5公开。完整所属types无省略；递归collectAxioms全部只用propext/Classical.choice/Quot.sound。未重编旧producer，未更新缓存/版本。生产源冻结等待fresh独立审查。

尚未证明Kolmogorov到期望误差传递、Q=0移除、离散自归一化端点外部估计或C1/C2根结论。没有将本变差步骤当作整个cn:initjoint。
