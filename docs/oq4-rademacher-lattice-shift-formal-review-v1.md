# OQ4 Rademacher Lattice Shift 独立形式终审 v1（统计修订 v2）

STATUS: CORRECT
LEAN_STATUS: LEAN_FULLY_CHECKED
OWN_EMIT: 0
OWN_LIVE_LEAN: 0
FORBIDDEN_EXPOSURE: 0
STATISTICS_REVISION: 2

结论限于冻结的完整有限 DA1、同域合法性、弱胞元左端点和本模块内部辅助引理。规范源码与匿名证明的数学推导、量词和实对象一致，独立无输出工件检查及所有完整结构比较均通过。DA2、真实概率 S3/S4、S2–S5 及 OQ4 根仍 OPEN。

## 父验收发现的统计错误与修订 v2

父实例根据本审查自己的38项 curated roster 指出统计矛盾：v1计算的是预期 _private.Shao.OQ4.RademacherLatticeShift 包装前缀逸出数（0），却将字段与报告写成“实际目标原始 Name 前缀之外0”。该两种前缀不同。这是本审查的统计/表述 bug，未改变任何声明记录或数学结论。

v2只按自身既有 raw 的结构 Name 节点逐层比较前缀，使用与 Lean Name.isPrefixOf 等价的结构关系，未用字符串 contains/startswith。实际目标 raw prefix 内16、外22；全部22项均private wrapper。user target namespace 外0，raw OQ4 prefix 外22，user OQ4 namespace 外0，raw OR user OQ4 范围外0；预期 private wrapper prefix 外仍为0。15项统计负向验证通过，包含私有原始/用户名称区分、数字Name、兄弟名称和显示字符串伪前缀。38项原记录、22个包装声明、源码、sole olean及原始raw均未修改。

交付v1报告8ed90204…/7424B、receipt3c5e2df5…/59491B、manifest3b9b3f59…/12654B已原字节永久归档在独立目录 statistics-v1-archive；对应 compare-final.py、comparison-result.json、comparison-v1.log与command回执同样精确归档。修正比较结果中的统计字段及那1项覆盖注记，其他47项有效检查逐对象保持不变。原比较日志保留为历史v1，不当作修订后统计依据；新统计supplement/命令/log单列。未重跑任何成功Lean、原始基线或有效结构比较，own Lean runs本修订0、emit0、live0。数学审查与原有实际Lean证据继续支持本冻结范围的 CORRECT/LEAN_FULLY_CHECKED，供父实例重新验收修订统计。

## 冻结对象与数学审查

唯一新数学来源为原 spectrum（b65f9e0c…/4306B）；冻结 DA1 为9cf9dba0…/6067B；匿名 proof 为aefff15a…/9818B。规范 Source 为5c5ffa54…/13125B。必要 Scalar 公开类型与透明定义从获准71f4ce77…/91113B声明账定向读取，实际 H=m+1、u=π/(4H)、z=π/(2H)、a=H⁻¹cos(u)/sin(u)、rho=cos(z)、lambda=π²/8，C_a=π/3、C_rho=π⁴/48。未读取 Scalar 定理证明或私有声明语义。

源码19–28行固定 delta=H−h、c=cos(π/8)、C_log=(πC_a/4)/c 和 C=C_rho+3lambda+C_log。它们先于全部 m,h,n 选定。51–88行从 m≥1、m≤h<m+1 得出 h≥1、h>0、H≥2、H>0、H=h+delta、0<delta≤1，证明全部显示分母非零和两个 log 自变量严格为正；69–71行保留 h=m 时 delta=1。

90–153行内部证明 C_log 界：实际 q=πa/4=(u/sin u)cos u≥cos(π/8)>0；SCA1 给 |q−1|≤πC_a/(4H²)，对 log 在正半轴 Ici(c) 的导数界给 |log q|≤C_log/H²。该论证覆盖全部 m≥1，没有自由对数界、替代函数或“大 m”阈值。

155–199行证明精确恒等式
D=1/h²−1/H²−2delta/h³=−delta²(3h+2delta)/(h³H²)。
正分母、delta²≤1 及 h(3h+2delta)≤3H² 给 |D|≤3/h⁴。202–273行精确拆分三个误差项，消费实际 SCA2、内部对数界和该位移界，得到 C(N/h⁴+H⁻²)，未除以 N。276–291行将2lambda换回π²/4，给出先存在 K>0、再全称 m≥1/全部弱胞元 h/全部 n:Nat 的冻结量词。m=1、m=2、h=m、delta=1、n=0 均在同一个证明内；无尺度、奇偶或渐近附加条件。匿名证明各节与这一推导一致，导数、中值定理和所有正性条件均已逐项核对。

## 实际 Lean 与完整声明对照

所有 FINAL Lean 均先 activate 再 cd 指定服务器 worktree，使用 taskset18-21、native -M8192 -j4、整线单重型进程。Lean4.36.0-rc1/c9afcdd、Lake5.0.0-src+c9afcdd、mathlib807d3836b165983210ee2ecf3cd28f239436949c 与实际共享包路径核对一致。

| 独立检查 | records / defs / theorems | actual header / closure | 退出 |
| --- | --- | --- | --- |
| 规范原 Source，actual-R、无-o | 原字节完整内核检查 | 实际规范模块 | 0 |
| A0：仅原4 imports、同词法scope的继承环境 | 128 / 17 / 111 | 7 / 5170 | 0 |
| Asource：完整原 Source，ALL-none | 38 / 4 / 34 | 7 / 5170 | 0 |
| Aall：ALL-none OR imported-project | 166 / 21 / 145 | 7 / 5170 | 0 |
| actual DirectAll：原 imports 对齐加实际目标导入 | 166 / 21 / 145 | 8 / 5171 | 0 |
| B0：复用自己的纯旧44基线 | 1135 / 121 / 1014 | 47 / 5681 | 已有0，不重跑 |
| B1：实际完整45 imports | 1173 / 125 / 1048 | 48 / 5682 | 0 |

本目标38项包含4显式公开定义、9显式公开定理、7显式私有定理、18生成项；共22项 private、0 opaque。ALL-none 依真实 moduleIndex=null 选取，未做名称过滤。所有当前 owner 均为实际目标；实际目标原始 Name 前缀以外为22项，恰为全部22个 private wrapper；用户 Name 均在实际目标 namespace 内，user namespace 以外0。raw OR user OQ4 范围外0。全部38项和22个 wrapper 完整保留。actual DirectTarget 从自己的 DirectAll 按真实 owner 派生，无额外 Lean 或命名空间筛除。

全部结构 Name、宇宙参数顺序、完整 type Expr、全部 def/opaque full value、metadata、unsafe/partial/private/activeInstance、实际 owner 和 oldModuleOwner、公理均逐字段对照。theorem value 从未输出。旧1135项完全保全，目标在 Asource、Aall、DirectAll、B1 的全部38项一致。A0与Source、B0与Source之间的 raw/raw、raw/user、user/raw、user/user 四类交集分别实测均0；不能把这一结果误当作先验不相交假设。Source与旧选择器“owner OR raw/user OQ4范围”的交集为38，亦保留并单独记录。比较器的重名保留旧 owner 逻辑已由自己的 PREP 负向夹具验证。

完整 global/scoped/private/inactive/erased/new/default 注册表、stateStack、activeScopes、所有 flags 与真实 discrTree root/chain/path/node-entry/child 顺序全等。A0/Aall、Aall/DirectAll 和 B0/B1 分别在相同有序闭包、import顺序和完整 Command.Scope（含 options/attrs/variables 等）下比较；仅实际测为空的目标 imported/default export 数组允许去除。未截断字段、树或顺序。48项 FINAL 完整比较全部通过；既有153项独立机制/负向检查复用而未重跑。

所有38项的传递公理并集仅 propext、Classical.choice、Quot.sound；无新 axiom、sorry、admit、unsafe、native_decide 或 partial。完整原 Source 在私有审计路径中保持连续13125B，前方仅必要 import Lean，后方仅审计 suffix；actual-R 精确解析到规范目标名，未插入旧44 imports或目标 self-import。

## 保全、独立性和历史

工作分支 feat/oq4-lattice-shift@3c909bfa5afc3b5d7e6676b0f476aa9b21a54bf3、1eabdc9a… canonical base 未变。初末全部137 source/config与102整个 build集合逐hash一致，旧44/92/101保护和旧136 HEAD blob均通过；5681个旧闭包二进制与自己 PREP qualification 的完整 hash/bytes anchor 一致。规范 Source 与 sole olean（d9c46a2f…/752704B）未变；sole olean 只作 custody标识，独立证明依据是原 Source实际无-o检查、源码审查及完整声明对照。无 canonical写入、-o/私有olean、Git、cache、common或root修改，own emit0、live0。

明确复用白名单通用 instrument.py（240bef57…/11623B）和 compare.py（873a090d…/4772B）；不声称独立工具作者。仅 manifest/old44/target/path 与显式授权的 Aall source-OR-project selection 参数适配，完整字段和顺序保留，比较器原字节未改。自己的 PREP153验证、raw、词法sidecar和旧二进制资格完整保留。原FINAL的Lean检查均一次成功；父验收随后发现的统计bug及v2修订已在前节完整披露。原48项检查中的结构比较结果沿用，其中1项覆盖统计注记已按结构Name前缀重算，其他47项保持不变。Asource在父实例提出可派生子集前已启动，自然完成保留；未为命名或子集重复成功检查。

PREP历史中的线程启动134、夹具语法/API、Python遍历超时和erased夹具不足等全部版本/log保留。FINAL另有一次本地原spectrum错误路径查找，在读内容前失败，已改到授权原路径；JS反引号构造错误均在执行前拒绝。未读作者receipt/notes/raw/交接、其他review推理或Scalar证明；声明账最初短预览仅含provenance/汇总metadata，随后仅定向读取必要公开types/透明values，无私有数学语义或证明暴露。禁止材料暴露0。原 PREP0220591e…/4937B已核对并精确归档，历史v30文字保持原件；当前 root main为v31/PR113实际合并1c760e35，旧20模块206 public按hash接受，Pair111/69 public仍单独待整合。

所有完整 Expr/registry/raw/log/binary清单均只留服务器独立 final目录。本地仅本报告、精选receipt/manifest与输入custody回执，UTF-8无BOM、无CR、恰好一个末尾LF。完整实际命令、退出码、所有输入输出hash/bytes、38项metadata名册和失败史见配套精选回执。审查结束，停止全部检查，等待lead后续处理。
