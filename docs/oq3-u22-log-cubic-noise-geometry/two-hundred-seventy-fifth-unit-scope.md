# GL275 — 原频率窗口外的实际平滑反演尾积分

三个完整声明、十四个完整声明 let 先冻结后实现。显示 b=1/(2n^6)、R=n³log(n)，尾域为坐标平方和≥R²，实际 gamma/rho/f 与已检查GK274完全相同。第一个实分析声明在明确对数阈值下给 c*x^6*exp(-log²x/4)≤rpow(x,-a)，c>0任意。第二条精确代入GK，取得同一实际全局/尾域真可积和 4*pi*n^6*exp(-log²n/4) 上界。第三条先选只依赖a的N≥1，再对所有n≥N、所有原始概率nu、所有空间点x给实际尾积分≤n^-a；不得把量词换成逐nu/x阈值。

该频窗严格是原 report n³log(n)，并非旧 n³。bR²/2=log²(n)/4 和2*pi/b=4*pi*n^6 必须形式化精确化简。n=1允许R=0而b>0；最终尺度阈值从真实自然数对数趋无穷建立，不以有限数值试验替代。

GK274目前MACHINE_PASS等待唯一最终审查，是预先声明的pending承重；source可写，任何GL Lean/AX前须GK独立完整报告合格并绑定，不能把待审生产者冒充已合格。所有原始失败/首O/冻结字节保留，不重放旧成功门。

原nu允许含原子；结果只处理高斯平滑后的真实独立和，不证明原nu密度或未阻尼CF可积。此处没有完成窗口内典范统一Hermite误差、实际加权去平滑/胞求和、外区/B–D/OQ3正面根。GH/GJ采用较大eps=logn/n³的明确修复及曲边窗口本义均保留，原 h=n^-3/logn 不被暗改。

保持严格0<beta<2/5、p54 v_corr=-hat_t0*sqrt(detDelta)*sqrt(Lambda1)、Song uniform-in-law外部归属与已接受联合非格点反例。指定服务器phase40/CPU36–39,44–47/c12-heavy.lock/-M8192-j4，固定Lean/mathlib/shared-v34；独立审查及同首O全拥有AX必须，无sorry/admit/新axiom/unsafe/native_decide。
