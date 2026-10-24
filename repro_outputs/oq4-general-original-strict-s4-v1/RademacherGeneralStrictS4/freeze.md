# 一般序列严格 S4：负责人冻结

负责人已全文阅读原 spectrum01.md 与 context215 完整数学证明、完整建议类型及实际承重接口。精确冻结为 frozen-interface.lean.txt：3个透明定义 delta/correction/Q，1个实质纯代数 private center_remainder_bound，1个公开 strict_S4_EVENTUAL，合计5源头；所有定义完整值、量词、宇宙和假设已明确。冻结时无实现文件。不得新增 top-level helpers/instances 或暗改数学假设，body-local have/let 允许。

选择已完整推导的 S4(a)+实际布朗平移路线。a=(Nat.ceil h−1:ℕ) cast，只在最终 h≥2 时转实减法。由 h−1≤a<h、a≥h/2，得 a→∞、a/h→1、n/a²→∞、n/a³≤8M。对合法弱左端点 a 调用 S4_EVENTUAL，其正性、时间与小球条件都是输出。实际 Brownian logshift 中 x=h/√n,y=a/√n，中心符号为 λn(1/h²−1/a²)。相乘后与严格中心2λ(n/h³)(ceilh−h)之差，privatelemma给统一60λn/h⁴界；n/h³只有最终上界已足以令其趋零。最后仅在共同正尾部指数化。

private纯代数头对应主证明实际需要的有理函数余项分离，不是管理包装。h≥2与h−1≤a<h保证分母非零；整数墙a=h−1以及n=0均包含。公开定理允许任意有限非法早期项和非单调自然数时间，不新增n≥1、h全正、非格点或结论性概率前提。全部三个新定义为真实概率/显式相位表达，负h早期的delta不声称属于[0,1)。

新两个直接依赖已各自内核/所有owned递归公理成功，冻结时214独立完整终审进行中；待资格完成后才授权实现。原C12/OQ3/OQ4/OQ56根组仍OPEN，本单元不是一般增量律或原空间自归一化传输。真正后继是相同序列条件下原AE iid严格确定事件与真实能量归一化事件的传输。
