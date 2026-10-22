# OQ4 立方根精细余项独立最终审查 109 — Phase A

STATUS: CORRECT
PHASE: A_LOCAL_FULL_SEMANTIC_REVIEW_ONLY
MECHANICAL_CERTIFICATION: NOT_RUN_NOT_CLAIMED
RAW_LEAF_INCREMENT: 0
ORIGINAL_ROOT_STATUS: OPEN
REVIEWER: fresh independent final-review context 109

本结论只裁决指定匿名数学证明是否完整、冻结自然语言与形式声明是否忠实，以及完整候选 Source 的证明意图是否闭合。本轮未运行 Lean、native、服务器命令、Git、工具链探测或导入；没有将任何既有编译或他人审查结论当作证据。未读取其他作者或独立审查报告、author receipts/progress、parent intake/gate/acceptance、strict cube Source/proof 或 CP 实现证明。只写本目录的三个指定报告文件。Phase A 不是最终机械认证，原根均保持 OPEN。

## 1. 范围、独立性与来源

审查目标是 spectrum01.md 第96行的 k³−1 根展开及第97–98行固定 α 最近整数子列的根展开，不包括这几行附带的概率倍率结论。原 frozen01.md 第7–9行的一般固定分布、uniform-x 相对概率目标仍 OPEN；spectrum 第101–104行一般 c、第112–116行 strict/相邻格点改变不在本单元结论内。没有概率、Brownian 或一般 c 定量假设进入本单元。

工作目录始终 C:/game/shao lean。遵守 AGENTS.md、SERVER.md 和 TEAM.md 的所有权与只读规则。math-theorem 技能的验证者协议适用；技能的一般 Lean 执行要求在本 Phase A 被任务明确的禁令覆盖，机械工作须另行释放 Phase B。没有新增子代理、没有搜索出处，也没有使用其他审查人的判断。

## 2. 完整读取与哈希账

以下 SHA256 为本轮读取时对原始文件字节计算的值。行号均为各文件本身的1起始行号。

| 输入 | 字节 / 行数 | 本轮阅读范围 | SHA256 |
|---|---:|---|---|
| AGENTS.md | 3577 / 23 | 1–23 全文；随后逐行补读1–23 | 7bdcd9cd2af52ad99fa265b31222b9bb8926f4805b3a62bc74329b0998e6b983 |
| SERVER.md | 5374 / 31 | 1–31 全文；随后逐行补读1–31 | 382428147ddb6a07e35da38b00011a721f7698577284e6fa2e9be1ebe498f246 |
| coordination/TEAM.md | 12940 / 86 | 1–86 全文逐行补读 | 9158122c5b629993e0c8117fab0e76eef24c3e482ed470788a4e1a1ce2e9529d |
| C:/Users/UIO/.codex/skills/math-theorem/SKILL.md | 17974 / 309 | 1–160、161–309 全文逐行补读 | 8ce5ed4f58ca8131bff6a35198e99d13b9a601c2e1c591b5592d09c81b16e1da |
| 技能 references/prompt-library.md | 12632 / 315 | 1–160、161–315 全文 | 0882f2965fad339846af7e92ef89543921b80f5be60ca108090b74943c058117 |
| 技能 references/openai-workflow.md | 5570 / 66 | 1–66 全文 | cc0fa5b42793a1b0e4389fe7004ed33cea39e57f3b4ed21f599f368f81bead84 |
| 技能 references/lean-verification.md | 4476 / 105 | 1–105 全文 | 58ef00c297dd6be325b115e0a7f74404d1b91f9c72623576e3e1b2bccde676f3 |
| C:/game/shao/current/oq4/c01/spectrum01.md | 4306 / 119 | 1–119 全文 | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b |
| C:/game/shao/current/oq4/frozen01.md | 1491 / 20 | 1–20 全文 | ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a |
| drafts/oq4/frozen-rademacher-cube-root-rates-v1.md | 3696 / 53 | 1–53 全文 | a0c30fa54604b8608fd8111c3215898abaa3ac642507e17120c1dd6ef8084725 |
| drafts/oq4/rademacher-cube-root-rates/proof.md | 7852 / 151 | 1–151 全文匿名数学证明 | 8e9c87cc521db97d28d80973bc921c9bf4db35579d144fc9a859853875b6c44e |
| drafts/oq4/frozen-rademacher-cube-root-rates-formal-statements-v1.lean.txt | 3723 / 85 | 1–85 全文；定义28–38、四heads41–48/53–55/60–74/79–81 | a13382ca97759a9768cb16292e0dc3f100b0166054251c2dc0399a2f2185081d |
| drafts/oq4/rademacher-cube-root-rates-implementation-v1/Source.lean.txt | 9422 / 246 | 1–130、131–246 全文，含全部证明 | 6f51957e561b4b693bcff304f797e284d905fc7a5ea3b5457819c3fe5e851247 |
| drafts/oq4/frozen-rademacher-critical-phase-formal-statements-v2.lean.txt | 10959 / 214 | 1–214；透明defs22–51、其余公共heads55–212，无实现证明 | d2656efb76cbbdba2ad08bc9352b05270461e466aec8a94d09b9dca0ed60a4bc |
| drafts/oq4/mathlib-public-api-intake-v1.json | 9434 / 317 | 仅 public_header_rows[0..8] 的 path/sha256/declaration_name/header_lines/header/masking 元数据；头位于JSON24/54/76/98/136/174/208/242/276行；未读实现proof | 5187d36e1a4dfef78e3162030e81bf72144551cd3c9cea8ee5e2346c1771ced7 |

初次合并输出出现一次工具输出截断（工具提示 original token count 10146；显示内容在 TEAM 历史 v37 附近有省略）。已完整补读 TEAM 1–86，并分块完整补读技能1–309；AGENTS/SERVER也逐行补读。后续所有数学输入与 Source 分块输出均无截断，未留未读尾部。指定四个冻结/证明/Source 哈希全部匹配。CP 指定路径实际存在，无需定位或读取 library 实现。

API 仅头投影的原始源码范围：Floor/Defs.lean:307；Floor/Extended.lean:92、118；Floor/Ring.lean:127、161；Floor/Semiring.lean:47、63、66；GroupWithZero/Defs.lean:225。其头显示 Nat.floor 的非负输入下界、严格上界和自然数cast规则，以及 mul_le_mul_of_nonneg_left；未读取这些库定理的证明。与本轮直接代数用法相关的最后一头参数方向正确。

## 3. 冻结对象与量词忠实性

CP 冻结接口22–23、40、43、45行给出 root(n)=Real.rpow(n:ℝ)(1/3)、height(c,n)=c*root(n)、target(c,α,k)=((K+α)/c)³、nearestIndex=Nat.floor(target+1/2)、belowCubeIndex=k³−1（自然数减法）。匿名证明13–25行与 Source 的 CP import/open（8、17–19行）采用这些对象；Source 没有重定义 root/height/索引或改变有限前缀。两个私有引理中实变量 K/r/t 只是代数抽象，其前提在公开定理中由同一个实际 CP 根导出，没有新增公开自由根假设。

Source 22–26、29–32行两个透明 Prop 定义分别与冻结形式28–32、35–38行逐字一致。均含正输出常数与 ∀ k:ℕ, k₀≤k → 实际误差界，不是有限样例、不是只写趋零，也不是未展开的同名占位符。R2 的 α 在公开定理上先固定，保留0<α<1。

四个 BEGIN/END_PUBLIC_HEAD 块与冻结形式头在仅归一化换行后逐字相等；比较结果四项均 True，两个def比较也均 True。Source 的公开heads为137–144、159–161、171–185、232–234行。没有新增假设、削弱结论或改动指数/分母。R1 是每个自然 k≥2，R2 是每个固定0<α<1以及每个自然 k≥2。

## 4. 匿名数学证明完整性

### R1

proof.md 39–48行先在自然数中证明 n+1=k³、n≥7，才取得(n:ℝ)=K³−1，没有把截断自然减法直接当成实数减法。50–52行将 CP.root_spec 的非负及立方身份应用到同一 n，并从透明定义输出 height(1,n)=r。

54–85行对全部K≥2作代数推导。a=K−1/(3K²)，K>0，且 a≥2K/3>0。展开得到 B=a³−r³=(9K³−1)/(27K⁶)，所以0<B≤1/(3K³)。D=a²+ar+r²≥a²≥4K²/9≥K²/3>0。立方差 B=(a−r)D 给出a>r及 |r−a|=B/D≤[1/(3K³)]/[K²/3]=1/K⁵。每次除法及分母比较均有严格正性。没有未给定Taylor余项或隐含局部近似。

proof.md 141–143行输出 C=1>0、k₀=2 并重用全尾界，准确证明原96行 O(k⁻⁵) 的冻结含义。

### R2

proof.md 93–112行固定任意0<α<1与k≥2，t=K+α>2，n=Nat.floor(t³+1/2)。因t³+1/2>0，可使用自然数floor的定义刻画，得到−1/2<n−t³≤1/2及绝对舍入误差≤1/2；从相同下界还得n>0，故n≥1。半整数t³=l+1/2时，输入floor恰为l+1，输出l+1，覆盖平局向上，左右舍入端点的严格/非严格方向正确。

proof.md 114–133行仍取同一 CP.root(n)，以其非负及r³=n身份设D=r²+rt+t²。因r≥0且t≥K>0，有D≥t²≥K²>0；立方差与取绝对值给 |r−t|D=|n−t³|≤1/2，因此 |r−t|≤1/(2K²)。没有额外假设r与t谁大，也没有漏掉向上/向下取整两种情形。

proof.md 145–149行输出每个α都可使用C=1/2>0、k₀=2的全尾界。常数虽在α域上相同，但结论仍是确定性根误差，未据此推出概率一致极限。

## 5. 完整 Source 逐段证明审查

Source 的语法声明清单恰为2个透明def、2个显式private theorem、4个public theorem；完整1–246行均已审查。静态全文禁止词扫描对 sorry/admit/axiom/unsafe/partial/native_decide 无命中。这不是实际环境的公理/安全性审计。

| Source行 | 语义检查与结论 |
|---|---|
| 1–19 | 唯一项目import是既有CP；另有五个Mathlib tactic imports。namespace与open对应冻结对象。 |
| 22–32 | 两个def的完整值与冻结逐字相同，所有cast显式、全尾∀量词保留。 |
| 35–42 | below_cube_error 的hK≥2蕴含K>0、K≠0。hp=(K−2)(K+1)²≥0，即K³−3K−2≥0，联合K≥2得K³≥8。 |
| 43–61 | 正分母3K²支持hshift；a≥2K/3与乘积(a−2K/3)(a+2K/3)≥0给a²≥4K²/9。D≥K²/3>0用r≥0控制交叉项；没有丢失ha2（nlinarith可用局部上下文）。 |
| 62–80 | 两个field_simp/ring目标的代数等式真实；K≠0覆盖所有幂分母。B=(9K³−1)/(27K⁶)≥0、B≤1/(3K³)；cube差因式完全正确。只需非负B即可得r≤a，不依赖未证明严格立方单调性API。 |
| 81–103 | 反证r>a时(a−r)D<0与B≥0冲突；乘a−r≥0保持D下界方向；hratio化简到1/K⁵，le_div_iff₀的除数K²/3>0。最后abs_of_nonpos恰适用r−a≤0。 |
| 105–120 | nearest_cube_error 有K≥2、t≥K，故K>0、t≥0；(t−K)(t+K)≥0给t²≥K²，D≥K²>0。没有要求r>0、α远离端点或r≥t。 |
| 121–134 | cube差、abs_mul、abs_of_pos(D)给绝对值因式；|r−t|≥0允许乘因子下界。除正K²得到(1/2)/K²=1/(2K²)。 |
| 137–156 | 公共R1头与冻结一致。exact_below_cube hk的.1是n≥1，.2.2.1是实际natcast身份（CP头98–109行）；root_spec的.1/.2.1是非负/cube身份（CP55–57行）。height透明化后用私有引理导出误差，所有内容为输出。 |
| 159–168 | 直接构造C=1、k₀=2和正性，展开BelowCubeBigO后对任意尾部k调用below_cube_finite，没有有限样例替代∀。 |
| 171–212 | 公共R2头与冻结一致；由hk和hα0得到t>0、t≥K、t³≥8。nearest_rounding (c=1)的α、c、k条件全部满足；.1/.2.1/.2.2.1/.2.2.2依次投影有符号下界/上界/绝对界/并列向上（CP142–146行）。target在c=1透明化，未改选择器。 |
| 213–229 | 半单位下界与t³≥8推出实际(n:ℝ)>0，n≠0后Nat正性给n≥1；root_spec给同一实际根的非负/cube身份；simp展示真实floor等式与height等式。只有在得到实际cube差界后才调用nearest_cube_error。 |
| 232–246 | 构造C=1/2、k₀=2，正性明确；NearestCubeBigO中∀k尾部调用完整R2有限定理，div_div仅作同一分母表达规范化。关闭namespace和noncomputable section，无后缀隐藏声明。 |

Source 相比匿名证明消费了允许的 CP exact_below_cube 与 nearest_rounding 公共定理头，而匿名证明自己重推自然减法/floor刻画。冻结自然语言21行明确允许取整与索引公开声明；这不增加假设，也不把本单元目标根率作为输入。这些CP heads不含待证O(k⁻⁵)/O(k⁻²)界，故不存在借用目标误差的循环。

## 6. 边界与未编译风险

k=2 已包含在每个≥不等式中。R1 此时n=7、K=2，a=23/12>0，K²/3=4/3>0、1/K⁵=1/32，不存在自然减法截断或分母退化。R2 此时t>2、n≥1，因子下界至少4，根误差上界1/8。论证不需要把k再取大。

α→0⁺及α→1⁻时，同一t≥K≥2的因子下界仍成立；没有使用α的正距离、最终相位稳定或隐藏的α相关阈值。精确α=0、1不是本冻结域，本报告不扩展端点结论。半整数并列已作为输出全称l:ℕ覆盖；有符号误差的−1/2严格、+1/2非严格与floor(z+1/2)规则一致。未发现数学边界异常。

尚未验证的风险属于编译/实际环境层：tactic imports是否在实际环境可用、exact_mod_cast/nlinarith/field_simp/ring/simp是否成功、div_le_iff₀与le_div_iff₀等名称和实际类型是否匹配、私有名称及generated常量实际展开、实际import绑定及对象来源。当前头投影与源码提供了正确的数学调用方向，没有观察到可定位的API错误；不把尚未运行的编译可能性误称为数学漏洞，也不声称它已通过。

## 7. Phase B 必须另行释放的认证工作

本阶段不执行以下工作。Phase B 应在实际owner环境中取得并逐个审查：

1. 模块全部owned常量，含generated、private与namespace外常量；完整actual types，及每个definition的实际value，逐项与冻结语义核对。
2. 公理依赖、unsafe/partial标志与axiom kind；标准白名单只允许propext、Classical.choice、Quot.sound，不能只做源码关键词检查。
3. 从全部owned常量的type及value递归展开的依赖闭包，包含opaque theorem的证明依赖；列出项目依赖常量、owner与module清单。
4. 实际Source及其哈希、实际唯一soleolean、import bindings及其来源；确认检查环境消费的就是此冻结Source与既有CP。
5. 实际编译、完整coverage与公理检查收据；native成功本身仍不能代替上述语义审查。

Phase A 结论为 CORRECT；关键缺口列表为空。raw-leaf新增0；本报告中所有原根仍OPEN，未宣称Spectrum、一般OQ4、strict或一般c闭合。完成本报告后STOP，等待父实例明确释放Phase B。
