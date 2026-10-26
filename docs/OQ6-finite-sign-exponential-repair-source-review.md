# Unit198 repair01 — same-role independent SOURCE delta review

STATUS: CORRECT
QUALIFIED: false
ACTUAL_OWNED: UNKNOWN

本报告只完成本次受影响源码增量的独立审查，复用原完整 SOURCE 审查 `de21eb9be1ba0670ef38e7541a8dafd5d71f14341dbc1db157fc2ad6d3a417f1`。不把修复推作 kernel pass。旧12个已封存审查文件、旧作者/Stage1证据、失败收据均逐项核验未改。审查员与作者分离，仅写本目录；没有 Lean、AX、服务器、网络、Git/API、上传、子代理或源文件写入。请求 gpt-6.1-sol/xhigh，实际模型/努力不可自省为 UNKNOWN，四项 usage 均 null。

## 精确修复与原报告的适用边界

父事先冻结 `parent-repair-freeze01-sum-body-scope.json` SHA256 `d8d160ca969b5d844b1867b88c8c9707016defb555c8d4ac63cccefbd3e52208`（4816B）。旧源 `501c39f8edddc811560f6cec2f72b44ebb4849d572203127e0bcae024f0ba029`（9990B）至新源 `4e3cfd9fcd4e8b943b45e90b75ed54ca34cc1805de99c90ed66c2cd5c917ce88`（9992B）恰在L193加入两个 ASCII 括号，236LF/CR0/BOM0保持。完整正向替换及删除这两个括号后的逆向结果，均与整份新/旧源逐字节相同；其余235行和补丁外全部字节相同。补丁的旧字符区间[7697,7755)、旧字节区间[8016,8078)，新结束位置分别7757、8080。已完整读 full patch、affected-helper-proof.json、父freeze和实际新旧helper。

原审查未识别L193求和记号的绑定优先级问题。原报告对有限平均线性的数学论证仍可复用，但该段不能解释为旧源字节已经可 elaboration。native02 的真实 `Unknown identifier s` 推翻了旧 `change` 语法可直接工作的判断；本报告明确补齐此缺口，旧报告和失败字节保留。本次修复保持公开陈述和所有数据定义不变，纠正的是辅助证明表达式中的实际 binder scope，不是把原来含未绑定 s 的语法当作已经正确。

## 完整受影响辅助证明及类型

完整类型仍为下列 Prop，没有新增量词或前提：

`cubeMean n dominator = weight * cubeMean n Eplus + weight * cubeMean n Eminus`。

完整新proof（L190–197）为：

```lean
    have hDominatorAverage : cubeMean n dominator =
        weight * cubeMean n Eplus + weight * cubeMean n Eminus := by
      change ((2 : ℝ) ^ n)⁻¹ *
          (∑ s : Fin n → Bool, (weight * Eplus s + weight * Eminus s)) =
        weight * (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, Eplus s) +
          weight * (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, Eminus s)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
```

先行完整环境与实际词法范围按原 SOURCE、精确不变前缀及此次相关片段重新核对：T03 telescope 为 n:Nat、a:Fin n→Real、t:Real、ht:0<=t；本helper只在Q≠0分支L127–232。Q=scalarEnergy n a，r=sqrt Q且hrPositive:r>0；u=t*r，lambda=t/r，minusLambda=-lambda，weight=exp(-(lambda*u)):Real；Eplus/Eminus均为 `(Fin n→Bool)→Real`，其值分别 exp(lambda*scalarSignSum n a s) 与 exp((-lambda)*scalarSignSum n a s)。dominator是同一固定weight乘这两个函数的和，完整初始化L141–143未改。先前 hBad、hPos/hNeg 与其 s 都局限于已结束的 hPoint proof；新helper不捕获这些分支的局部变量。其L190开始的完整前缀 SHA256 `b070e5364fdac63bcbbedaeb15b299cd9834360330a1d0de816117eb8317c87c` 在旧新源中完全相同。

新L193的求和binder `s : Fin n→Bool` 明确同时覆盖 `weight*Eplus s` 和 `weight*Eminus s`；整个括号内为Real求和体。它没有新增ambient s、选择一个符号向量或增加独立性假设。右侧L194/L195的单项求和各自仍局限在自己的外层括号内，右侧两项的加号在求和之外，符合平均线性。

记 c=(2^n)^(-1)、A=sum_s Eplus(s)、B=sum_s Eminus(s)，这些只是审查中的数学缩写，不是新增Lean数据。展开已有cubeMean与dominator后，新 `change` 的左侧正是 c*sum_s(weight*Eplus(s)+weight*Eminus(s))，右侧是 weight*(c*A)+weight*(c*B)。sum_add_distrib把和拆开，两次逆向mul_sum给 c*(weight*A+weight*B)，ring用分配律及Real乘法结合/交换得目标。这里weight不依赖s；不需要额外非负条件、n正性、积分交换或概率假设。空有限域的同一代数也成立。由此完整helper在数学层和当前显式语法范围层CORRECT，是否实际被固定版本内核接受仍等待native03。

## 全部新旧source maps与前缀组合

独立递归比较六份完整新旧map，而非只比较计数：source-blocks、actual-scopes、typed-prop-helpers、numeric-source-map、branch-types、source-freeze-compare。允许的数学变更仅为T03完整块/完整proof中这一精确补丁；其余只更换源路径/hash/bytes及准确偏移。所有5个冻结头、2个global RHS、12个具名data的完整类型/初始化/捕获和8项inline族、全部32个具类型Prop头、3个分支说明、78个数字的值/类型/分类均相同。没有新data、instance、universe、choice、selector或前提。

旧补丁之前的字符/字节位置不变；在旧结束位置之后的源位置加2；跨过补丁的整块起点不变、终点加2。LF未增删，行号及补丁之后其他行的列号不变。独立核对全部127个新span（5global、12data、32Prop、78numeric）的原始字符切片、UTF8字节切片及行号，均精确。数字仍是76个数学标型数字（24Nat、52Real）及2个Nat tactic配置；主声明10项仍3Nat/7Real。具名data全部在补丁前，作用域依原完整审查保持。

32条prefix overlay与旧、新helper表逐条相同，且两端都从实际完整源前缀独立重算hash。26个补丁前的prefix hash不变；仅hPlus、hMinus、hRSq、hLambdaU、hLambdaSquare、hExponent这6个补丁后的prefix hash改变；hDominatorAverage自己的头和开始前缀不变。由原完整SOURCE + 当前完整helper审查 + 可逆整源补丁 + 完整map变换/32prefix桥接，未变证明覆盖精确组合到新4e3c版本，不重审或重跑未变旧proof。

旧55输入文件本身未改，当前54项原输入仍字节相同；唯一差别是用户明确替换的AGENTS版本，作为新行政输入单独绑定，不能把旧AGENTS哈希说成仍是当前版本。新80项输入、作者manifest20项、保留旧证据50项及旧独立seal12项全部精确核验。原Stage1有效seal29和Stage2 manifest19通过作者保留表和新绑定继承，未改数学源或已有接受范围。

独立STATIC-COMPOSITION-V3最终为427PASS/0FAIL，计数由实际核对项导出。V1的一项递归比较失败及V2的错误时间排序假设均保留：source-freeze-compare的utc从 `2026-10-26T01:50:28.5443031+00:00` 序列化成 `2026-10-26T09:50:28.5443031+08:00`，是同一历史瞬间，分数秒也完全相同，不是修复时新生成的时间。V1未考虑等价时区字符串；V2误将其假定为修复生成时间，排序检验失败；V3只修正该行政字段解释。此前所有数学字段、源切片及输入绑定比较成功，没有因此修改作者文件或掩盖数学错误。作者自己的Python入口、旧AGENTS替换及span尾LF比较失败也均完整读取并保留。

## 机器状态和后续门

native01为KNOWN_END RC1，原缺少Series.olean，无对象/无AX；其失败保持。native02有界诊断SHA256 `8d454927124b94d9e26d4ea5f0becf8bf3154e3fb9e9a9c44ee9b2591e95e7e7`（5038B）已完整读，包含703B完整stdout：RC1、5.322236681秒，唯一错误L193C66 Unknown identifier s；三条既有deprecated-name警告保留，不作额外清理。object=null、ownLean为空、无AX、保护12286项before/after exact。诊断中的大raw receipt只作为父提供的hash绑定，本角色没有读取或虚构其全量机器认证。

本次SOURCE delta结论为CORRECT；qualified=false、actualOwned UNKNOWN。此SOURCE增量阶段不对native03对象作资格裁决，不能把括号修复或静态PASS推为kernel/all-owned/AX PASS。父随后已提供native03成功对象证据，将在另目录完整读取和裁决。后续仍由同一独立角色读取父提供的FIRST successful originalO，按全moduleidx而非命名前缀枚举全部实际所属声明，完整读TYPE、每非定理FULLVALUE、生成/外来归属、body/namecomponents/levels、递归AX以及native/audit收据。只有那时才可判断最终qualified。

原C1immutablev85 complete；C2/C12/OQ56 OPEN；OQ3用户暂停；p54修正、Shao–Zhou/Jing–Shao–Wang外部归因及124非前提保持。后续199的实际iid鬼样本/配对交换、self-normalized W/V/Gy仍是独立未闭合依赖。封存后本SOURCE增量目录的writer/execution/heavy/inflight/pendingExternal/children全部释放为0；同一角色按父的新机器任务在另目录继续，目录封存本身不表示持续运行。
