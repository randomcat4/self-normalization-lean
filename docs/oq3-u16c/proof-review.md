# U16c 完整独立证明、来源与实际类型审查

STATUS: CORRECT

唯一审查 lease 1，只拥有本报告与服务器 proof-review.md，不改实现、scope、旧票、共享文件或缓存，不 spawn、Lean/API probe/构建/复编，不下载原始完整日志。并非独占代码库，保留他人编辑。承认已审 v1/v2 声明上下文存在；本次仍先仅读取 actual 公开定义完整体与完整定理类型，独立盲译并落盘，尚未读取本次实际证明、私有辅助或机械证据。

## 第一阶段：actual 公开完整体和完整类型盲译

实际输入 drafts/oq3/LocalRateMargin.lean，SHA256 `5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77`，8592字节/182行。本阶段只读一个公开定义完整体和一个公开定理完整类型。

`gaussianRateProfile` 对任意实数 S,T,b,y,z 定义实值 y²/(2S)+(z−by)²/(2T)。定义自身没有正性/非零门；定理依赖 S,T>0 才将这两个实除法项解释为真正二次代价。b 是任意有符号标量，实际定义没有将其绑定为协方差，也未把 I 定义成概率率函数。

`exists_cubic_rate_weight_margin`：给固定实参数 q,ell,S,T,b,D,radius，要求 q>0、ell≥0、S>0、T>0、D≥0、radius>0，严格 ell<q/(32T)。再给任意实二元函数 I 和局部下界 hI：所有满足 |y|+|z|≤radius 的实点上，profile(S,T,b,y,z)−D(|y|+|z|)³≤I(y,z)。在这些输入之后，存在三个严格正实数 delta/gamma/c，同时对全部自然 n≥1、全部实 k≥0 和任意实 r 有效：若 k/(n:ℝ)≤delta、|r|/(n:ℝ)≤delta、(n:ℝ)qk/16≤r²，则 gamma*k+c*r²/(n:ℝ)≤(n:ℝ)I(−k/(n:ℝ),r/(n:ℝ))−ell*k。

见证在全部 n/k/r 之前；k 可为任意非负实层深度，r 可负，D0/ell0允许。必须先真实建立评价点的 l1 邻域门，不能将两个比值分别小误当成原半径条件。全部除n仅在n≥1后合法；b的交叉项必须保留符号控制，不能省略。k=r=0及r=0约束边界不得除零。该完整类型是明确hI假设下的确定性余量，不输出实际Legendre/Taylor/Hessian生产者、概率Chernoff、负层概率或根闭合。

本段独立盲译先保存。随后才按 v2scope/R1→全部实际proof/private/generated/locals与固定库→全部19actual TYPE→receipt/机械证据顺序继续。根A/B/C/D、实际率Taylor/Hessian、真实负层概率、完整LLT与hW均OPEN。

## 第二阶段：冻结声明、真实来源与范围绑定

盲译落盘后才读取完整v2scope、真实R1及全部actual实现。scope-v2 SHA256 `8623fcad91638c2ba30b59612a2d57e0c785948e75d815c653a7a1b8d16e129e`，v2声明票 SHA256 `86bd5b68484d529954543615c7f63e9f1f2001699669726efa0b40b1971c41d9`。本次重新独立提取actual公开定义完整体与唯一完整类型，去空白后分别与冻结v2 Lean fence相同；公开门和量词无增加、削弱或替换。实际第一导入是规范 Mathlib.Basic.Real.Basic，没有改回v1弃用入口。

真实只读来源路径是 `C:/game/shao/current/oq3/proofs/r1/report.md`，SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，本次直接核243–250、348–387行。370–371行的逆协方差二次项及三次O余项、378–383行的负层曲边约束和加权局部代价余量，正是当前确定性步骤来源；362–366行概率Chernoff、373行全局唯一性以及384–387行真实概率(17)不是当前输出。

若后续真实绑定 S=Var(Y)>0、C=Cov(Y,X)、T=Var(X)−C²/S=实际tau²>0、b=C/S，则detCov(Y,X)=S*T，(1/2)(y,z)Σ⁻¹(y,z)^T正好等于公开profile，源kappa²/2=q/(32tau²)>ell正好给hgap。T是方差tau²而非tau；源曲边阈值nqk/16和严格系数32均在冻结类型保留。当前actual代码没有构造真实I/Legendre/Hessian/Taylor或真实协方差，不应因通用profile或hI参数而将这些节点记为完成。没有Shao导入，本单元只消费标准实数代数。

## 第三阶段：全部182行actual证明、两个私有引理与所有locals

本阶段独立数学判断先于任何Audit TYPE、收据或作者机械绿灯，并先落盘。第1–9行规范实数模块和五个tactic导入、namespace/noncomputable与v2冻结一致；第11–12行公开定义完整体无变化。

### 私有 gaussianRateProfile_lower（14–25行）

完整目标为S,T>0下 `(1/(2T))*z²−(|b|/T)*|y*z|≤profile`。16–17行先由真实 le_abs_self 和 abs_mul 得 b(yz)≤|b||yz|，没有把b设非负。18–19行保留交叉项，配合(b*y)²≥0推出 z²−2|b||yz|≤(z−by)²；这是正确的有符号下界。20行利用S>0给y²/(2S)≥0。22–24行用T非零重排共同分母，并以2T≥0保持除法不等式方向；25行才舍去非负y²/(2S)。没有直接丢掉负交叉项或用不可逆的二次式等价。

### 私有 cubic_small_ratio_bound（27–47行）

实际输入u,v,delta,d非负，delta≤1，u,v≤delta，u≤d*v²，输出(u+v)³≤4delta(d+1)v²。32行先得u≤1；34行u(1−u)≥0给u²≤u，结合u≤d*v²得33行hu2。这里采用较粗的u²≤d*v²，足够且不错误重复乘delta。36–37行由(u−v)²≥0得(u+v)²≤2(u²+v²)。39–43行先乘非负u+v，再以u+v≤2delta、平方和非负替换；44–47行乘非负4delta并用hu2，得到完整系数4。_hd虽为显式d≥0门但在这一粗证明中不必单独消费，属于合法冗余，未放松任何公开前提；delta=0、v=0等私有边界也满足上述链。

### 主定理常数与严格gap（61–89行）

实际 let A=1/(2T)、d0=16/q、B=|b|/T、g=A−ell*d0、E=B*d0+4D(d0+1)。66–68行由q,T正与D≥0得d0>0、B,E≥0。69–75行先以正32T合法清hgap分母，得到q−32T*ell>0；实际hgform `g=(q−32T*ell)/(2Tq)`经q,T非零代数成立，正分子正分母给g>0，精确使用源16/32系数。

76–82行在所有n/k/r之前一次性取delta=min1(min(radius/2)(g/(2(E+1))))、gamma=g/(4d0)、c=g/4并分别证严格正。E+1>0而非除E，D0/b0时合法。83–88行delta≤1、delta≤radius/2明确给出；delta≤g/(2(E+1))在正分母门之后清分母，配合delta≥0得deltaE≤g/2。89行先返回全部见证，90行才intro任意n≥1、k≥0、有符号r及小比值/事件门。因此三见证统一位于全部n/k/r之前，未逐点选半径。

### 真实缩放、事件与hI邻域（91–136行）

91–100行N=(n:ℝ)>0由n≥1获得，u=k/N、v=|r|/N、w=r²/N均非负，小比值直接给u,v≤delta。101–105行仅在N≠0后建立k=N*u和w=N*v²，使用sq_abs保留r的符号。106–113行先以16>0清事件分母，再以Nq>0清比例，正确得k≤d0*w。114–122行再以N>0的乘法严格单调反证消去N，得u≤d0*v²；没有把N≥0当成可消去的严格门。

123–127行hyabs/hzabs/hzsq/habsmul分别给|−k/N|=u、|r/N|=v、(r/N)²=v²及|(-k/N)(r/N)|=u*v。每一步使用k≥0、N>0及真实abs规则，未假定r≥0。128–130行先由u,v≤delta、delta≤radius/2得到真正的l1邻域≤radius；131–134行之后才分别消费私有二次下界与实际hI。135–136行给 `A*v²−B*u*v−D(u+v)³≤I(−k/N,r/N)`，没有在未知合法点调用hI，也没有把未量化O记号当作已证明hI。

### 交叉/三次误差与最终权重（137–179行）

137–146行由u≤d0v²、v≥0，再用v≤delta乘d0v²≥0，先得uv≤d0delta v²，后乘N≥0并用w=Nv²得Nuv≤d0delta w。147–152行在所有真实非负、小比值和二次约束门下调用私有cubic，再乘N≥0并用w恒等式得N(u+v)³≤4delta(d0+1)w。

153–157行分别以B,D≥0乘两种误差并相加，环展开准确得误差和≤deltaEw。158–166行先乘N≥0消费实际hIlower，然后真实展开 `N*(A*v²−B*u*v−D*(u+v)³)=A*w−[B*Nuv+D*N(u+v)³]`；减误差的方向正确，推出(A−deltaE)w≤N*I。167–171行用ell≥0和k≤d0w给ell*k≤ell*d0w，故减ell*d0w是合法下界，得到(g−deltaE)w≤N*I−ell*k。没有用错误的负数乘法方向。

172–178行gamma>0允许以d0w替换k，gamma*d0+c=g/2的代数仅在d0≠0后清分母；deltaE≤g/2再乘w≥0得(g/2)w≤(g−deltaE)w，接上hcost。179行仅展开w,N及标准实除法、结合乘法还原公开目标，没有改变I评价点、引入概率或调用隐含渐近接口。

所有field_simp非零门逐项可见：23行T≠0；74行q,T≠0；101、105行N≠0；112行N,q≠0；176行d0≠0。没有除k、r、D、E或ell，故k/r零、D0/ell0均不失效。n0显式被排除，n1正常；r0时事件正Nq强制k0，hI原点提供I(0,0)≥0；b任意符号由|b|处理。全部182行和所有let/have/calc/反证/类型转换已检查，实际数学阶段结论CORRECT。编译生成项留待真实TYPE枚举，不按tactic名称预猜。

## 第四阶段：实际固定库语义

指定服务器只读核对下列实际源码声明，无Lean/probe/编译：

- Mathlib.Basic.Real.Basic SHA256 `f15de163c14198d9b60aeb8ac845b4540c198bbb2e80d6153d0dbc8a6c08936f`，359、471、481行真实IsStrictOrderedRing/LinearOrder/Field ℝ，支撑有序实域而非替代数系。
- Algebra.Order.GroupWithZero.Basic SHA256 `28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c`874–878行div_pos/div_nonneg，1128–1141行le_div_iff₀/div_le_iff₀/lt_div_iff₀等均要求正分母；1193–1195行div_le_div_of_nonneg_right要求a≤b和0≤c。actual调用均给出了对应正性或非负门。
- Algebra.Order.Field.Basic SHA256 `fabd3062223bbdcd4efae38a4a586f88241f67da533e79ee06c56ba507c27b2d`673–674行abs_div，Algebra.Order.Ring.Abs SHA256 `afad3c8ac856f0019cb16aeb194e452613aee2bfe400e82c2e2a7becd89a5abe`49行abs_mul、81行sq_abs；actual hyabs/hzabs/hzsq/habsmul的符号和平方均吻合真实接口。

其余平方非负、le_abs_self、min上下界、正数乘法、sub_le_sub、自然cast序和ring/field_simp/linarith有限算术不涉及数学分析总化。代码没有概率、积分、真实率函数构造或Shao承重依赖；所有核心代价语义已在实际公开定义与hI显式给出。以上数学和库判断先落盘后，才读取actual TYPE；receipt和机械绿灯留最后。

## 第五阶段：全部19个actual owned TYPE

前述数学与库阶段先落盘后，从真实服务器现有Audit.log仅过滤DECL/TYPE及全部长续行，不先读取AXIOMS/PASS/receipt。下列为实际输出顺序的逐项检查；P表示完整 `_private.Shao.OQ3.LocalRateMargin.0.Shao.OQ3.gaussianRateProfile_lower` 前缀，M表示完整 `Shao.OQ3.exists_cubic_rate_weight_margin` 前缀。简称仅便于表内排版，实际已读取每个完整声明名称及类型。

| 序号/实际Audit行 | 实际声明 | 完整类型的独立核对 |
| --- | --- | --- |
| 1 / 1–2 | P | ∀S,T,b,y,z:ℝ，S>0→T>0→(1/(2T))*z²−(|b|/T)*|y*z|≤实际profile；与14–25行私有下界一致，b无符号门。 |
| 2 / 4–5 | Shao.OQ3.gaussianRateProfile | ℝ→ℝ→ℝ→ℝ→ℝ→ℝ，五参数S/T/b/y/z，无隐藏正性假设；实际完整定义体已先审。 |
| 3 / 7–30 | M | 第8–30行所有续行完整读取：q/ell/S/T/b/D/radius及全部正性、严格gap后，∀I及真正局部hI；∃delta/gamma/c>0先于∀n≥1和∀实k/r，k≥0、两个小比值和16因子事件后给公开目标。没有隐藏Taylor生产者、n>0提前省略或量词交换。 |
| 4 / 32–34 | M._simp_1_4 | 任意Mul/Zero/NoZeroDivisors M₀，a≠0→b≠0→(a*b=0)=False；完整前提保留，标准非零乘积规则。 |
| 5 / 36–37 | Shao.OQ3.gaussianRateProfile._proof_1 | 实际TYPE为(1+1).AtLeastTwo，不凭名字猜成definition eq。实际固定Mathlib/Data/Nat/Init.lean425–426行该Prop类唯一字段是2≤n，故此项仅证明2≤1+1；无率函数或二次型数学义务。 |
| 6 / 39–40 | M._simp_1_3 | 任意Zero/OfNat4及NeZero4的α，(4=0)=False；常数非零门未删。 |
| 7 / 42–46 | _private.Shao.OQ3.LocalRateMargin.0.Shao.OQ3.cubic_small_ratio_bound | 全部u/v/delta/d:ℝ，u,v,delta,d≥0、delta≤1、u,v≤delta、u≤d*v²后得(u+v)³≤4delta(d+1)v²；第43–46行全部续行已读，与私有证明一致。 |
| 8 / 48–50 | P._simp_1_4 | 任意Mul/Zero/NoZeroDivisors，a,b非零后(a*b=0)=False；同4的泛代数规则，完整读48–50行。 |
| 9 / 52–53 | P._simp_1_7 | 任意AddMonoidWithOne R及CharZero R，∀n:ℕ，((n:R)+1=0)=False；自然后继非零，非任意有符号实数非零。 |
| 10 / 55–56 | P._simp_1_1 | 任意Zero/OfNat2及NeZero2，(2=0)=False。 |
| 11 / 58–59 | P._simp_1_6 | 任意GroupWithZero G₀，a:G₀、n:ℤ，a≠0→(a^n=0)=False；是有非零门的整数幂规则。 |
| 12 / 61–62 | M._simp_1_2 | 任意Zero/OfNat3及NeZero3，(3=0)=False。 |
| 13 / 64–65 | P._simp_1_3 | 任意Zero/OfNat4及NeZero4，(4=0)=False。 |
| 14 / 67–68 | M._simp_1_5 | 任意MonoidWithZero及IsReduced、a、n:ℕ，a≠0→(a^n=0)=False；保留IsReduced和a非零门，不给任意有幂零元环错误消去。 |
| 15 / 70–71 | M._simp_1_7 | 任意AddMonoidWithOne及CharZero，∀n:ℕ，((n:R)+1=0)=False。 |
| 16 / 73–74 | M._simp_1_1 | 任意Zero/OfNat2及NeZero2，(2=0)=False。 |
| 17 / 76–77 | P._simp_1_5 | 任意MonoidWithZero及IsReduced、a、n:ℕ，a≠0→(a^n=0)=False；同14泛规则，实际分别读取。 |
| 18 / 79–80 | M._simp_1_6 | 任意GroupWithZero，a、n:ℤ，a≠0→(a^n=0)=False；同11整数幂规则。 |
| 19 / 82–83 | P._simp_1_2 | 任意Zero/OfNat3及NeZero3，(3=0)=False。 |

实际15个generated分别是公开定义的1个AtLeastTwo证明、主定理的7个_simp和私有二次下界的7个_simp；没有按作者预计名称省略任何项。AtLeastTwo的真实定义源SHA256 `806975436869c67d4bd0dddfa042b8eaac3d7309d90a4d6b03d33d7ab5a7edfa`，已在指定服务器只读核查其精确Prop语义。其余生成项的全部型别约束/非零前提如表所示，都是标准带前提代数命题，没有新增主目标假设、hI生产者或概率结论。

实际inventory为1公开def、1公开theorem、2 authored private theorem、15 generated theorem，共19；所有长续行和每项完整类型已核。类型阶段独立结论CORRECT。之后才读取作者收据、真实Audit覆盖/公理和构建机械证据。

## 第六阶段：最后读取的真实机械证据及历史保留

全部182行数学与全部19个actual TYPE先审完并保存，之后才读取本地U16c-receipt.json和真实远端receipt、Audit源及公理/计数、现有build/olean/pins。作者机械门不代替本票的独立数学判断；本次没有执行Lean、API probe、目标/Audit构建或复编，也未下载原始完整日志。

- 本地actual稿、远端worktree `Shao/OQ3/LocalRateMargin.lean` 和run冻结快照一致：8592字节/182行，SHA256 `5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77`。实际源无CR、尾空白、sorry/admit/axiom/unsafe/implemented_by/extern。公开定义完整体和唯一完整类型已由本审查独立去空白比对v2scope，完全匹配，而非只采信收据中的PASS。
- 本地和远端receipt均3201字节，SHA256 `0636d6864520a2412561e1c7cafe29762b4501dcd6ebae8b807c4792999918e8`。pending与No U16c commit/PR记录的是author-check当时的历史，不误作本次最终裁决。
- 实际build-03.log为0字节，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`；作者回执保留命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/LocalRateMargin.olean Shao/OQ3/LocalRateMargin.lean` 的exit0。空日志自身不独立证明退出码。本次只读核已有目标olean真实存在，982024字节，SHA256 `5cf0e0af4d6ef502537b61174929b6fb6f82b8554d28093b5d57eae0312f18ec`，未重跑成功目标。
- 实际Audit.lean为1620字节/36行，SHA256 `76a0f695685a78e09eb4bc77ab54cad9b794c73129558187c8dd933c4bb42494`。全文核读：核目标是theorem、profile是defnInfo，遍历公开目标和定义的完整stem加完整 `_private.Shao.OQ3.LocalRateMargin` 前缀；拒绝每项isAxiom，并对每项Lean.collectAxioms检查全部传递依赖。不是仅检查一条公开目标或只数源码中的theorem关键词。
- 实际Audit.log为4823字节/88行，SHA256 `883cbf0ade486d0ff77df8eaf664fd3240f995c0c6a092b331c457e3e7f41077`，真实输出1 frozen target、18 theorem、19 owned，`U16C_AXIOM_GATE PASS`。六项的实际传递AXIOMS为[propext,Classical.choice,Quot.sound]：公开profile/主定理、两个authored private以及P/M两个整数幂_simp_1_6；其余13个generated均只[propext]。全部19项都在白名单内，没有额外项目公理或遗漏生成项；所有actual TYPE已在此前阶段完整连续读取并逐项解释。
- 实际递归Shao import闭包为空，receipt imported_project_sources_sha256亦为{}，因此本单元没有项目承重模块。规范Basic.Real.Basic与FieldSimp/Ring/Positivity/Linarith/NormNum六个既有olean均实际存在，不需新增缓存。没有暗中消费实际率函数或概率模块。
- 实际branch `feat/oq3-local-rate-margin`，HEAD `5fbb497bd0d0f827d5da6c76badc29fcd728010a`，git status仅 `?? Shao/OQ3/LocalRateMargin.lean`。实际toolchain `leanprover/lean4:v4.36.0-rc1`，lean-toolchain SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`；manifest pin和真实mathlib HEAD均为 `807d3836b165983210ee2ecf3cd28f239436949c`。

本地与远端历史文件逐项仍保持原hash：v1scope `9f660ea048c1b2a89ea4ce7f983ef60d8f631561fd52e7c3612bb538979f4133`，旧v1声明票 `e75a5553346aea1a2e272a2cad0af8f94b05e14d0ef52b84f79b85233f97672a`；本次权威冻结v2scope `8623fcad91638c2ba30b59612a2d57e0c785948e75d815c653a7a1b8d16e129e`、v2声明票 `86bd5b68484d529954543615c7f63e9f1f2001699669726efa0b40b1971c41d9`。未覆盖或追改任何旧scope/票，v2与本次actual的canonical导入语义一致。

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: actual完整公开定义体/目标与冻结v2和真实R1局部数值余量步骤相符。全部182行实现、两个private、全部locals与15个generated的真实TYPE已独立核查；源严格因子32与曲边16给正确正gap，所有delta/gamma/c先于n/k/r固定。hI评价点的真实邻域先建立，带符号交叉项和三次误差被合法吸收；正分母、非零清分母门及ell0/D0/b任意符号/k0/r0/n1边界均有效。全部19个owned常量、18个theorem的完整类型和传递公理白名单，实际规范导入、零Shao闭包及source/receipt/Audit/build/pins绑定一致，没有发现需要修改的声明、数学、来源、类型或机械缺口。

本票仅接受从明确假定的generic I局部三次下界到确定性局部权重余量的蕴含。不证明实际Legendre率、其三次Taylor下界、真实Hessian/协方差生产者、紧倾斜族统一Fourier/Chernoff、真实负层概率(16)/(17)、全局唯一最小化或远区率间隙，不完成完整负层支配/LLT/hW/WC/KL/根闭合，不声称最优性或新颖性。实际率Taylor、Hessian、真实负层概率、完整LLT、hW及根A/B/C/D均保持OPEN。整个审查只写本新报告与授权远端副本，不改任何实现、scope、旧票、共同文件或缓存，未spawn或复编。
