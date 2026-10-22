# RademacherIteration 独立最终形式审查 v1

STATUS: CORRECT
FORMAL_STATUS: LEAN_FULLY_CHECKED
SOURCE_SEMANTICS_STATUS: CORRECT
ANONYMOUS_PROOF_STATUS: CORRECT
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

冻结 v1 的有限整数状态支持、真正可积性及主余弦精确有限幂结论全部通过。canonical 目标直接无输出检查、完整原始源码的独立镜像审查和实际39模块导入审查均退出0。未发现关键缺口。

本票只关闭该冻结有限叶；完整谱、生存概率展开、S1–S4 与 OQ4 根仍开放。

## 独立性与精确输入

审查先在隔离状态准备：只读冻结声明、原文与已接受依赖接口；AUTHOR_CANONICAL_READY 后才读取 canonical 目标及获准匿名证明。没有读取作者 checkpoint、作者审查推理、其他匿名证明或父审查工具。审查者未执行任何 Git 操作；base commit 与 branch 身份来自已钉定的负责人收据，源码及产物的实际字节均另行独立核对。

| 输入 | 实际 SHA256 | 字节 |
|---|---|---:|
| canonical `Shao/OQ4/RademacherIteration.lean` | `dd8986ebe885d4f5cbe9ea021ee6b193ab927e066b9a15f2e5e22e0d030ad360` | 8111 |
| 唯一 canonical `RademacherIteration.olean` | `850e18f066cb70dec7eb4c9e68f11db5083955bff1d95706de690c1a5215dfe8` | 192304 |
| 获准匿名 `drafts/oq4/rademacher-iteration/proof.md` | `ebb39a86387a22445126bac9248d4215648a52f3aea7ad82a6e507822da98d83` | 14073 |
| 冻结声明 | `15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80` | — |
| 原文 `spectrum01.md` | `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b` | — |

原文实际只读路径为 [spectrum01.md](<C:/game/shao/current/oq4/c01/spectrum01.md>)。冻结声明为 [frozen-rademacher-iteration-v1.md](<C:/game/shao lean/drafts/oq4/frozen-rademacher-iteration-v1.md>)，匿名证明为 [proof.md](<C:/game/shao lean/drafts/oq4/rademacher-iteration/proof.md>)。三份本地输入在最终写票前再次匹配原 SHA，未修改。

old38 immutable base 收据钉定 `78f9bfd7f028c3b6971ca5e393764ccb241047e6`、`feat/oq4-rademacher-iteration`；收据 SHA 为 `1a6badb4484640a67a9ce8558ea6e76606b9aa9e9210969c23e19bc0e6c4c8dd`。old38 源文件实际枚举恰38，逐项 SHA 匹配收据；另92个非 OQ4、共同定义、根与版本文件也逐项匹配负责人钉定 map，map SHA 为 `cf3b164c60adf590af9749d6cdf894f11031c76ed316820111f433bd2858b76f`。

## 实际执行与覆盖

所有 Lean 执行均在指定服务器，先激活 `/root/rivermind-data/shao-lean-20261021/activate.sh`，再进入 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。实际 Lean 为 `4.36.0-rc1`，commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；Lake 为 `5.0.0-src+c9afcdd`；mathlib 钉定 `807d3836b165983210ee2ecf3cd28f239436949c`。没有本地 Lean、版本更换、缓存获取或旧目标源码重编译。

最终三个命令逐一运行，始终仅一个审查 Lean 进程、4核亲和。它们不含 `-o` 或 `-i`：

```text
taskset -c 4-7 timeout 45s lake env lean Shao/OQ4/RademacherIteration.lean

taskset -c 4-7 timeout 45s lake env lean -R /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-iteration-independent-v1/mirror /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-iteration-independent-v1/mirror/Shao/OQ4/RademacherIteration.lean

taskset -c 4-7 timeout 45s lake env lean -R /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-iteration-independent-v1/mirror /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-iteration-independent-v1/mirror/IndependentAll39Audit.lean
```

| 检查 | 退出码 | 秒 |
|---|---:|---:|
| canonical target no-o | 0 | 3.921 |
| 完整原始 source、all-none 镜像 | 0 | 4.851 |
| actual all39 imported owner OR namespace 并集 | 0 | 6.260 |

准备阶段已先通过真实 `-R mirror` 模块身份 smoke：`mainModule=Shao.OQ4.IndependentIdentitySmoke`，其源环境 none-owner 常量数为0，审查尾部未污染原模块常量集合。最终目标镜像再次实际确认 `mainModule=Shao.OQ4.RademacherIteration`，没有假定 `--stdin` 的文件名语义。

镜像仅在原始8111字节 body 前补入12字节 `import Lean`，完整 body 保持逐字节一致，随后追加审查尾部。源环境枚举条件只有 `getModuleIdxFor?=none`，没有任何名称或命名空间筛选。实际导入环境首先读取真实模块表，确认 OQ4 模块集合恰为 old38 加新目标，再以实际 owner 属于 OQ4 模块或名称属于 `Shao.OQ4` 命名空间的并集审查；全部私有、生成项及命名空间外常量均在覆盖内。

## 实测声明与精确比较

实际完整源环境得到9个常量，与源码中的9个明确声明逐项对应：7个公开 theorem、1个公开 definition、1个私有 theorem，未匹配的生成常量为0。以下为实际原名；所有 universe 参数表均为 `[]`，注册实例标志均为 false。

| 实际原名 | 种类 | universes | 实例 |
|---|---|---|---|
| `Shao.OQ4.RademacherIteration.grid` | public definition | `[]` | 否 |
| `Shao.OQ4.RademacherIteration.grid_finite` | public theorem | `[]` | 否 |
| `Shao.OQ4.RademacherIteration.killedAction_principal_power` | public theorem | `[]` | 否 |
| `Shao.OQ4.RademacherIteration.killedIterKernel_ae_grid` | public theorem | `[]` | 否 |
| `Shao.OQ4.RademacherIteration.killedIterKernel_grid_compl` | public theorem | `[]` | 否 |
| `Shao.OQ4.RademacherIteration.killedIterKernel_integral_principal_power` | public theorem | `[]` | 否 |
| `Shao.OQ4.RademacherIteration.measurableSet_grid` | public theorem | `[]` | 否 |
| `Shao.OQ4.RademacherIteration.principal_integrable` | public theorem | `[]` | 否 |
| `_private.Shao.OQ4.RademacherIteration.0.Shao.OQ4.RademacherIteration.killedKernel_grid_compl` | private theorem | `[]` | 否 |

新9个常量的完整原始 name、kind、universe 参数、完整 Expr 类型、公理依赖和实例标志在 source/import 两环境中逐项精确一致。唯一 definition `grid` 的完整原始 Expr value 也精确一致。私有名原样保留，包括 `_private` 模块路径及数字分量；没有重写私有名或通过名称规范化制造相等。

actual all39 并集实测768个常量，包含680 theorem、88 definition，其中25个 private。旧759个常量的原始名称集合完全相同，owner、kind、universe、完整 Expr 类型、全部 definition value、公理及实例标志也逐项一致。旧注册扩展条目同样精确一致。

实际注册扩展测量为：新模块0个条目，all39 总计4个条目；活动旧实例仍为4，新9个常量全部不是实例。以上数量来自真实环境枚举，未以预期名单筛选。

目标源码的 `sorry`、`admit`、`axiom`、`unsafe`、`native_decide` 词元命中为0；全部768个受审常量无 axiom、unsafe 或 partial 常量，传递公理仅在 `propext`、`Classical.choice`、`Quot.sound` 白名单内。新9的实际公理表均为这三项。

## 冻结声明、原文与源码的逐字段语义审查

| 字段 | 独立判断与实际位置 |
|---|---|
| 固定律与频率 | 目标使用已接受的真实 `RademacherCosine.law`、`angle`、`rho`。依赖定义分别确为半 Dirac 增量律、π/(2(m+1)) 和其余弦；没有替代核或替代频率。 |
| 真正有限整数网格 | 源码11–27的 `grid` 是闭整数区间在真实 Int.cast 下的像，并实际证明有限与可测；没有用实区间支持代替整数性。 |
| 起点与全部时间 | 58–61、89–93、104–109、152–158保留 `m:ℕ`、`1≤m`、`m≤h<m+1`、`r:ℤ` 与两个整数边界，`n:ℕ` 无正步或大时间限制。 |
| n=0 Dirac | 63–66明确改写 `killedIterKernel_zero`，用起点 `r∈I_m` 消去补集质量；117–118明确用实际 `killedAction_zero` 与 `pow_zero`。没有预先杀死区间外零步起点。 |
| 真实迭代支持 | 29–55直接使用真实整数原子行，保留原子均落在网格；67–86使用真实核复合及非负积分、a.e. 归纳证明补集质量为0。 |
| genuine integrability | 95–101单独证明真实迭代核上的 `Integrable`，以余弦连续可测、全局绝对值≤1及真实有限核接口供给；130–135也核验一步作用与常数倍的积分条件。其更强的任意实起点可积性不会扩大特征函数身份的起点类。 |
| 真实半群与精确幂 | 120–129先由 a.e. 网格支持取得合法整数状态及两个边界，只在这些点调用 PR72 主一步对。136–149使用真实 `killedAction_semigroup n 1`、a.e. 积分替换与标量乘法归纳得到真实 `rho^n`。152–158直接返回实际核积分身份。 |
| 弱端点 h=m | `hmh` 为≤，`hhm` 为<m+1；已有核定义确为 restrict 到 `Icc (-h) h`。±m 保留，向外的±(m+1)被杀死；不存在 strict 事件替换、行重新归一化或总质量为1的假设。 |
| r=0 与退化质量 | 在合法整数范围内将 r=0 代入，cos0=1即得到ρⁿ，包括n=0。证明不除以生存质量或ρ，零测度时的 a.e./积分语言仍成立。 |
| 原文强度与排除范围 | 只迭代原文有限状态主模态，未把加权余弦积分当作无权生存概率；没有任意实 coset 外推、完整模态族、正交完备、cot 展开、奇偶负谱项、4/π、S1–S4 或根闭合声明。 |

匿名证明第1–8节另行逐段审阅。真实核定义、组合公式、有限性、可积性和外部接口条件都与实际签名一致。证明(12)、(19)、(20)依次把真实核组合、网格上的主一步对和真正可积的积分递推连起来，没有将所需支持隐藏成循环引理，也没有用有限计算替代一般自然数归纳。CORRECT 不依赖作者或其他审查者的票。

## 保护、停止状态与证据

审查前后，旧38源码及总计130个来源、共同定义、根与版本文件，以及95个已有产物的文件集合和 SHA256 完全守恒。作者唯一新增的源码与 canonical `.olean` 同样保持原 SHA；最终锁定保护集合为131个来源/版本文件和96个产物。唯一目标产物路径为 `.lake/build/lib/lean/Shao/OQ4/RademacherIteration.olean`，没有额外目标产物。

全部审查进程已等待完成并回收，审查专属 live 进程为0。审查专属目录没有 `.olean`、`.ilean`、`.ir`、`.o`、`.so` 等二进制产物；审查者 emit 数为0。未改目标、证明、冻结声明、共同文件或任何版本锁。

完整日志、原始 Expr、清单、脚本及失败史只留在服务器专属目录：

`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-iteration-independent-v1`

| 服务器证据 | SHA256 |
|---|---|
| `source-all-none.json` | `313afb8614a08f9941bd4cc0e2c21bf980c6af2975b482cdcee24fd154acac0f` |
| `imported-all39-union.json` | `3a8bf8ce57ffae47f603d7fe52c5831eea5f96640289bd0b3db5e3e713c8dc4a` |
| `old38-imported-union.json` | `c14db9f422a4c8357e2e174b8a857bba9fc21e5b794068d238f2f9823882901d` |
| `comparison-summary.json` | `ddaf61f0ce5d3bf907469a18bbd2625bf7fd572db71047e6b808957c0c2c93d1` |
| `source-semantics-review.json` | `8161354aaa7ad22bdf599d34b53442b09b7740a03d147befeaf42dea72a1dfed` |
| `locked-baseline.json` | `bb9088cb25a59511a06ecded8406556a665f6b7b40c5ffba9653492319b897fd` |
| `old38-locked-prep.json` | `418834e0eb3c796186762c60c374a7ab1816c781c4be6d9279e843aea7354afc` |
| `tool-error-history.json` | `3dba42bb2f0c38f8daf04b1d50b87df307b3f3ec0a6f22a819a977e26f24bc43` |
| `final-receipt.json` | `efc8a6e5c9c970b3f5a0149da4dd12b78cafa6d2ca8f6f1840164034007b44e3` |

准备期首轮审查模板因 `AttributeKind` 没有 `Repr` 实例而退出1；仅在审查者模板中改成 global/local/scoped 三构造子的穷尽编码，v2通过，失败日志保留。只读定位阶段另遇到本地相对原文/工具链路径缺失、服务器 `/root/.elan` 路径缺失和 `rg` 不可用，分别改读获准绝对原文、服务器实际 pins/激活路径及有界 Python 搜索。最终收到的 worktree 匿名 proof 镜像路径不存在，实际读取并核验获准的本地匿名证明。一次长 host 调用的初始回传未显示完成输出，未重放命令；随后只核查已有成功收据与 live0。所有这些工具史均记录在服务器，没有改数学输入或通过换版本消错。

本地仅交付本精炼报告与 [形式审查收据](<C:/game/shao lean/drafts/oq4/review/rademacher-iteration-formal-receipt-v1.json>)；不含完整日志、Expr、缓存或二进制。两份交付均为 UTF-8、无 BOM、无 CR、恰一个末尾 LF。
