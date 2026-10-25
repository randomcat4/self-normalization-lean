# 单元182 repair-01 独立受影响源码补审

STATUS: CORRECT_SOURCE_REVIEW_PENDING_SERVER

QUALIFIED: false

这是原同一独立终审上下文的补审。原完整源码报告 `877418d83318dd8ce722b828e8f2d47bddf28c2990727902f41808062bf7ea6f` 及其394行源码、完整旧producer实际TYPE和原文审查继续复用；原报告及所有作者/共享文件未改。本次只审实际受影响证明、相关完整类型/值/作用域/API和机械偏移，没有重审旧producer证明或执行任何Lean、服务器、网络、Git操作。

新源SHA256为 `c24bb3330f4fb6c384941596f434ef8839af04e9fdb91ce5780081e8dd7168bf`，21227字节、398 LF。修复作者RELEASE0的SHA256为 `1db8ea0788dfa625b9859e4063a3a06b89cf024306b4adf63663008e6c5b64ec`；新source-map为 `8d50ee76335c38d6f7f2f6244110713cf400acc239725830fe4a1991713c049e`；exact-diff为 `30498417f7d829ea9780a355033356222d52dafb1f7a504117fa5aca971b677b`。这些均已按实际字节核对。

独立验证表明唯一替换是旧byte[18211,18289)、原335行，变为新byte[18211,18451)、335–339行，增加162字节和4 LF。原前18211字节、后2776字节逐字相同；逆替换恢复旧源全部21065字节。公开头2872字节、前缀、分隔符、后缀、61冻结条目的类型/值/冻结作用域和22数据绑定均保持。原未受影响源码审查因而足够覆盖全部保留部分。所有后续原行号增加4，其他范围仅作由该替换决定的偏移；139个新映射source span已独立验证。

完整新SCALE块是新328–340行。新增普通局部命题为：

```lean
have hMulRpow : Real.rpow (aenv * w o) α =
    Real.rpow aenv α * Real.rpow (w o) α := by
  simpa only [Real.rpow_eq_pow] using
    (Real.mul_rpow (x := aenv) (y := w o) (z := α) haenvNonneg hwoNonneg)
rw [hMulRpow]
```

其前环境是原SCALE完整外环境，接o:Ω、hwo:1≤w o∧w o≤R、hwoNonneg:0≤w o；仍有已证haenvNonneg:0≤aenv及haenvPowPos:0<Real.rpow aenv α。hMulRpow不在自身或两个库调用的前提内。只有随后rw的环境再包含已完成hMulRpow；它不进入任何后续外层have、数据、阈值或任意λ分支。原第70行classical证明模式及原独立覆盖中的显式overlay保持有效。

已复用并准确对照原完整主库Real.lean第1–484行。第39–40行真实声明 `theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl`，来自第34–37行的rpow及Pow实例。第476–484行mul_rpow的完整实参条件仍为两个非负底数，变量环境是{x y z:ℝ}。新增simpa只把目标三处显式rpow转换成该库定理已有的Pow记号，使用x=aenv、y=w o、z=α及原已付两项非负性，不引入新条件或外部结果。随后rw直接匹配显式Real.rpow(aenv*w o)α。

rw前的目标是τ*Real.rpow(w o)α = τ/Real.rpow aenv α*Real.rpow(aenv*w o)α；rw后右侧变为τ/Real.rpow aenv α*(Real.rpow aenv α*Real.rpow(w o)α)。原下一行 `field_simp [ne_of_gt haenvPowPos] <;> ring` 逐字保留，仍由同一个正分母完成抵消。原AE集合及例外处理、条件积分、统一2Mexp和真实Kstd包络均未改变。

独立补审程序 `repair-source-audit.py` 的467项一致性核对全部通过；完整记录和精确输入绑定见 `repair01-source-audit.json`，其中保留新增Prop、真实mul_rpow调用、记号桥接API和rw的完整作用域文本及实参。检查数量仅代表一致性核对，不是数学或Lean通过数。没有新增data、接口、导入、全局定义、假设、选择器或禁止证明逃逸。

父级报告旧kernel01因PATH缺lake而127、未启动Lean，旧kernel02在原335行rw匹配失败而native1；这些失败不算证明通过。本轮未收到对应原始服务器包，仅记录父级报告，不声称独立检查了其执行日志。新源kernel03及其成功对象/实际全部owner证据尚未送达。本次补审仍qualified=false；后续需要完整读同一对象的实际owner清单、所有TYPE、全部非定理FULLVALUE、每owner递归AX及精确kernel/源对象/保护绑定，才可给最终资格结论。

原范围与OPEN状态保持：本件只为p51 S6到p44指数矩/产品包络适配；后续p44仍需α≤2，不恢复p54已否定的任意多项式p矩变化率，C2/C12/OQ56仍OPEN，OQ3仍PAUSED_BY_USER。请求gpt-6.1-sol/xhigh，实际模型/强度及四类token遥测未知，记录null。
