# 实际微小时钟局部导数：作者完成，待 fresh 独立完整审查

作者结论：服务器完整源 kernel PASS；一次全部 actual-owner 类型/传递公理审计 PASS。
尚未获得独立 reviewer 的 CORRECT，不是原 growing-y 反射比较或 C12 原根闭合。
作者完成本单元后释放生产源和此 draft 目录写权，交 root 安排 fresh reviewer。

## 冻结提交与字节

* 工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/common-short-kernel-v51`。
* 分支：`feat/common-localized-microtime-derivatives`。
* 父提交：`81427457ef601ccf1bfc9ef25ae6fe80e3e99617`。
* 新提交：`d2878214808ef611dcf0b3380339f53c8c0fc0b5`。
* tree：`d35dc116a7c35b6da8d75f278fac5ef7b12e2ce0`。
* 唯一提交源：`Shao/Probability/SourceLocalizedMicrotimeDerivatives.lean`；工作树 clean。
* 新源 SHA256：`bdf57fc81650cf1dbb43d42d70b8d9078ac3fdb00e7637913f1e67f0b7bc1633`。
* 对象 SHA256：`66feb3555bc4481e36a3698bfcae00e3d7a1a8615f8cb43f19e98315c93a9152`。
* 源 42759 字节、794 LF、0 CR、无 BOM。public 头与 root 冻结文本逐字匹配。
* 冻结文件：`coordination/public-localized-microtime-derivatives-declaration-freeze.md`，
  SHA256 `e9657dcd55df751d087f0ce261586dd459ed54bef2a1f0ff3c899ca565cfd279`。
* root 明确允许新增 private helper THEOREMS，零新定义规则不变。实际 15 private +
  2 public = 17 源定理；环境实际 owner 也是 17 theorem constants，0 definitions，0
  额外 generated constants。所有类型都进入此次完整审查范围。

## Reviewer 需完整读取的材料

1. 原始只读 `C:/game/shao/current/c12/supplement.tex:895–927`，本源负责 895–907、922。
   同时核对原始固定 x 条件律、真实 cutoff/平滑噪声定义；不能把仅尾概率生产者当作导数证明。
2. 本目录 `SourceLocalizedMicrotimeDerivatives.lean` **完整全部 794 行**，包括 15 private
   helper 和两条 public 头/证明。`actual-owned-types.json` 给出全部 17 actual types，
   每条有 owner/kind/axioms；类型无任何省略符。零新定义，所以新增 definition values 集为空。
3. `proof-candidate.md` 是冻结前完整数学推导；`candidate-declarations.md` 和 root freeze
   是语义/全部量词/数值边界。候选旧文档保持原样，没有为了接受改写旧证据。
4. `check003-exit.json`、`audit-exit.json`、`localized-microtime-owned-audit.json`、
   `actual-owned-types-scan.json`、`static-checks.json`、`commit-receipt.json`。
5. 已接受 source-tail 输入只复用其合格旧证据，不需要重新完整审查：
   `SourceGrowingMicrotimeTail.lean` SHA256
   `591d52e2a6dbcf3cf133a6b45d4ee3d8c4d482aafbf9ca8fcc4968b4c0d3afde`，父 commit 同上；
   `coordination/common-growing-microtime-tail-full-review.md/json` 及
   `coordination/common-growing-microtime-tail-root-qualification.json`。

Reviewer 必须使用 fresh gpt-6.1-sol/xhigh、作者/审查者分离，进行完整源→statement→proof
审查和全部 actual private/public/generated 类型覆盖。可以重用精确成功对象/receipt；
不自动重复运行 compiler 或重复审查无变化的旧 tail 模块。任何实际改 proof 的 delta
需重新检查受影响证据。

## 证明路线与重点风险

* `lm_scalar_interval` 先对真正独立标量密度作积分变量边界转换，严格开事件因标量律有
  密度而等于 interval integral；它不假设未来和 Sm 无原子。
* `lm_scalar_hasDeriv`、`lm_scalar_first_hasDeriv` 给出两次真实 FTC 端点导数；
  `lm_scalar_average` 明确输出导数积分公式、处处 C² 和统一界，保留全部可测/可积/主导条件。
* `lm_kernel_scalar_eq` 完整展开同一 `quadraticFullNoiseLaw` 的两族八条弦及独立 γV0，
  而不是更换成纯标量噪声或未经证实的 desired-premise 接口。
* 实际弦支撑给 |B|≤32h、|D|≤64h²，完整水平支撑≤34h，局部位移后≤35h。
  `lm_geometry` 用原 192 常数得到 64h²<1、36h≤y/32，无需修改旧 tail 接口。
* 在真正好事件 |Sm|<y/8 上，最终 cutoff 参数 R=q+Qm+D 若活跃，则 y√R>y/4。
  `lm_good_endpoints` 严格推出两个端点的绝对值>1，真实密度及其导数为零。
  原指示函数在中心通常为一；取消是密度导数整支撑积分的 FTC 形式。
* 点态导数主导函数为常数乘路径坏事件 indicator，产品律积分正好等于真实 πm.real(E)。
  E 用 ≥ 保留原子边界，Sm 没有被替换成 Sm−mμ，条件 μ 可以非零。
* q>5：真实 Qm≥0 加纵噪声≥−64h² 得最终 cutoff 参数>4，故整个 w 实轴的函数和
  两导数恒零；不是只在一个 w 点强行使用 deriv 的全定义取零。
* m=0：半径 2h 内核真为常数，半径 h 上两导数真为零；函数本身不要求为零。
  实现还通过真实空积尾概率为零得到全部 q 的两个导数零。
* 第二 public 头在 law 之前量化 L2/epsilon0，保留原始 ν0 只有二阶矩、均值0、n raw2=1
  和实际预算。所有 bounded 条件律平滑输入由既有 accepted bridge 推出。
  只在最后调用已验真实 tail 来得到 exp(-4y²)，并以 C0(2exp17+1) 同时覆盖两类界。
* `SourceBoundedYReflection` 没有被 import 或作为已证明依赖；它此前只作为相同
  FTC/Fubini 的书写参考。所有所需私有证明在此新源自足存在。

## 实际检查与保存的失败

远端证据目录：
`/root/rivermind-data/shao-lean-20261021/outputs/common-localized-microtime-derivatives/`。

* check001：RC1，source/log/hash/direct rc 保留。修复了 abs 加法顺序、−−1、family
  probability 实例、无进展 simp、积分绝对值 API 及有理分式正规化；没有改变声明。
* check002：RC1，唯一实际错误是新 Lean 下 nhds 成员未先标注为 Eventually 导致
  `error(lean.invalidField)`；原始匹配 `error:` 的简报没有捕获此类别，因此读取完整
  8KB 远端日志定位修复。原日志/source/rc 保留；不把 errors 数组为空写成通过。
* check003：完整生产源首次 RC0，17.6606 秒；同一命令带 `-o`，之后没有重编/清理警告。
  log SHA256 `0fb21274dedc9fbea753cbc19f4c01692f4a70e548b5698429ee4f559c2bb552`。
* 一次 owned audit：RC0，21.1599 秒（含锁等待）；17/17 actual-owner 全覆盖、全部
  collectAxioms 传递检查仅 `propext`、`Classical.choice`、`Quot.sound`，0 definitions。
  log SHA256 `c2915792579b94858ca42eb0c49f9dffd5be9477b6160f0cc2dd23796ce3db79`。
* 完整 actual types JSON SHA256
  `d7a99e49dc6d223fa2a05b9b610b3925363b0f423c0cba7fd443d3136f67c813`；
  Unicode U+22EF/U+2026 及 ASCII 三点省略各0。源及对象在 audit 后均未变化。
* 所有实际 Lean/audit 均在服务器同一 root-heavy.lock、CPU10–13、-M8192 -j4 下完成。
  本地 Lean 命令0、旧模块重编0；无 PR、无合并、无缓存写入。
* source-only commit 首次请求因本地模板字符串顺序造成预期 branch 名尾部多 `-tail`，
  在第一个 branch assert 即失败，未发生 Git mutation。修正该请求字面值后 source-only
  commit 正常成功，见 commit receipt；没有重放不确定操作。

## 下一源依赖与释放

作者已完成两条冻结 public 头及全部17所属定理。根现在可安排上述 fresh 独立完整审查。
本单元仍不覆盖原文 923–927 的真实 Taylor 缺陷期望/求和；审查接受后下一承重依赖是
把此次局部指数导数和既有 late regulator moments、short-time Taylor 接到真实
micro-clock growing-y 误差和，再继续完整 growing-y 比较及最终概率链。

作者实际状态：本单元 completed、源和 draft 写权 released、无 in-flight 操作、无子代理。
这份完成记录不构成后台持续执行机制；原 C12/C1/C2 root 组仍 OPEN。
