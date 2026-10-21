# U6a 最终独立源语义、声明与证明审查

STATUS: CORRECT

独立 reviewer：OQ3 reviewer，gpt-6.1-sol xhigh。只拥有本报告，不修改任何实现、scope 或其他文件，不再委派；不读取作者 notes/frontier/API planning。

裁决绑定固定哈希的 97 行实现，覆盖四个公开目标、全部局部辅助及两项生成证明。声明与冻结接口相同，源语义与完整证明无关键缺口，真实服务器已有构建/传递公理证据相符。只认证原子算术；实际律的特征函数相位等号桥、严格联合非格点和根 A/B/C/D 仍 OPEN。

## 第一阶段：实际签名的独立翻译

本节在本轮读取实际证明、冻结 scope 内容、真实 R1 锚点及作者 receipt/Audit 前落盘。实际 `AtomProjection.lean` 为 97 行，SHA256 为 `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22`，与委派值相同。无新定义，四个实际目标签名如下。

| 实际目标及行号 | 独立自然语言语义与完整量词 |
| --- | --- |
| `dyadicMesh_tendsto_zero`，19–20 | 沿自然数 atTop，实序列 `dyadicMesh j=(2^j)⁻¹` 趋于 0。域包含 j=0，结论是极限而非逐项等于零。 |
| `addedAtom_tendsto`，26–27 | 整个自然数新增点族趋于固定旧点 `β=4+√10`；新增点定义中的 j+1 保留源第一项格距 1/2。 |
| `eventually_zero_of_lattice_tendsto_zero`，36–39 | 对每个一次固定 c>0 和每个实序列 f，若 f→0 且每项属于 cℤ（整数见证可随指标改变），则 f 最终恒等于 0。没有让 c 随指标改变，也不声称有限早期项为零。 |
| `fixedAtom_no_projection_lattice`，53–57 | 任意固定 c>0、实 xi,eta，若全索引 `Fin 4⊕ℕ` 的原子差分二次投影 `xi(a_i−β)+eta(a_i²−β²)` 都属于同一 cℤ，则 xi=eta=0。量词覆盖四旧点和全部新增点，不是只有限阶段或仅几个测试点。 |

这只陈述固定原子族的极限、离散格点与精确投影排除，不涉及实际概率质量、复积分、特征函数等号、真正联合非格点或根 A/B/C/D。已审查的 U1/U3a 共同定义存在，但本轮不预先从作者证明说明形成放行判断。

## 第二阶段：冻结及真实源语义核对

盲译先落盘，再比较 scope 与实际目标；空白归一化后四签名完全相同，无类型、前提或量词改变。实际 scope SHA256 为 `0d269910fcdbe5edbff649ef20053a9362b22c811eb5603da0973445086bc919`，此前独立声明报告 SHA256 为 `81f123f2abfbb0c9a54958c2174120b208755cccbdf39a5642ea09a515e039e4`，均与委派值相符。

本轮实际读取真实只读 R1 113–119、259–277 行，实际源 SHA256 为 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。

| R1 锚点 | 实际代码的语义覆盖 |
| --- | --- |
| 113–119 | dyadic 格距趋零，新增原子向 β 累积。实际 `addedAtom` 内部 j+1 不变，Lean j=0 对源 j=1；没有错成首格距 1 或有限截断。 |
| 261–266 | 源从正原子与复三角等号得到全支撑常相位。实际 hmem 直接假定对应全原子格点关系，未把这一步概率桥藏入证明或声称完成。 |
| 267–271 | 同一正格距 c（后续可取 2π）的投影序列趋零，再由固定离散间隔得到最终精确零；实际整数证人允许逐项变化。 |
| 272–276 | 使用新增点与 β 不同，消去差分因子，再使用两个实际不同尾部原子推出 eta=xi=0。实际输出顺序为 xi=0∧eta=0，数学相同。 |
| 277 | 当前四目标未输出概率联合律真正非格点，因为尚未连接 261–266 的特征函数等号与全正原子条件。 |

## 第三阶段：完整证明与局部辅助审查

完整阅读同一固定哈希实现 1–97 行，在读取作者 receipt/Audit 或真实 build 日志之前形成独立数学判断：CORRECT，无关键缺口。没有读取作者 notes/frontier/API planning。实现只导入已冻结 U3a，不依赖尚未机械检查的 U4 原律构造。

| 实现行 | 全步骤、条件及边界核查 |
| --- | --- |
| 21–24 | 将 dyadicMesh 展开成实逆幂。几何极限定理的基数为 1/2，明确证明 `0≤1/2<1`；`one_div`/`inv_pow` 精确对应 `(2^j)⁻¹`。包括 j=0，有限初项不影响 atTop 极限。 |
| 28–34 | `tendsto_add_atTop_nat 1` 保持定义中 j+1 的源索引平移；常数 10 减该趋零序列得根号参数趋 10，再由实平方根连续性和加 4 得 β 极限。无额外参数或偷偷换原子定义。 |
| 40–43 | 对 f→0 应用绝对值连续性，再用固定 c>0 的零点邻域，得到最终 `|f_j|<c`；没有以逐项整数存在直接断言零。 |
| 44–51 | 在同一个最终集合内逐 j 取整数证人 m。m=0 分支直接给 f_j=0；m≠0 分支用 `Int.one_le_abs` 及精确实数嵌入给 `1≤|m|`，再用 c>0 得 `|c m|≥c`，与严格小量矛盾。c 从不随 j 改变，结论只为最终零。 |
| 58–74 | 固定 β，定义实际新增投影 f。原子趋 β、连续平方趋 β²，两个差分均趋零；乘固定 xi、eta 并相加得 f→0。所有系数是同一冻结实数，无依赖 j 的选择。 |
| 75–77 | 将全索引 hmem 限制到 `Sum.inr j`，实际 fixedAtom 的定义归约为 addedAtom；同一个 c、hc 传入离散零性。`eventually_atTop.mp` 得某 N 后每个 j≥N 均精确为零，不只是某子列。 |
| 78–84 | 对任意 j≥N，展开 f=0 并作精确多项式因式分解 `(z_j−β)(xi+eta(z_j+β))=0`。已审查 U1 的 `addedAtom_lt_limit j` 给 `z_j−β≠0`，通过乘积为零的第一因子排除得到线性关系。没有直接除以可能为零的项。 |
| 85–90 | 选 N 与 N+1，两者均≥N。若实际两原子相等，U1 的 `addedAtom_injective` 给 N=N+1，与自然数算术矛盾。因此两原子确实不同；并非由收敛本身推断不同。 |
| 91–94 | 两个线性关系相减得到 `eta(z_N−z_(N+1))=0`。第二因子已证明非零，故 eta=0；代入同一个 N 的关系得 xi=0。两个不同关系都真实使用，不以单一关系推两个系数零。 |

全部承重局部项（hmesh、hrad、hsmall、整数大小界、hf、hzero、hlinear、hfac、hdiff、heta）已审查。没有额外顶层私有引理。整数比较/cast 均为精确逻辑算术，没有取整、数值近似、浮点探针或新数学前提。

边界上，f 可以有任意有限多个早期非零项，最终阈值允许依赖固定 c 与 f；声明没有错误地要求全部项为零或对所有格距统一阈值。零投影 xi=eta=0 相容；c≤0 不在本引理域。β 虽为新增点极限，但每个有限新增点严格小于 β，非零因子门在每个实际使用点成立。

这只证明全原子精确投影排除。实际 P/π 的特征函数模 1 等号条件、正原子到全相位关系、真正联合非格点，以及近共振、强非格点失败、LLT、对角与根 A/B/C/D 均未在此关闭。

## 第四阶段：服务器已有机械证据及绑定回执

在独立数学判断写成之后才读取 receipt、审计脚本和真实服务器日志。实际 `U6a-receipt.json` SHA256 为 `f979f6e1e2166a255bf57dfd5758ee423337af9f7ad32fb6e0702b8aff9c208a`，与委派值相同。不重复已成功的目标构建；本次所有服务器操作为只读源哈希、日志、Git 状态及环境探测，没有写缓存或实现。

- 实际工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`，分支 `feat/oq3-projection`，HEAD `8d154ffd7f283109241ce81551c45931e9f5ef34`，与 receipt 基线一致。目标在核查时仍为未提交新文件；提交、PR、集成由 lead/root 处理。
- 真实服务器 `AtomProjection.lean` SHA256 为 `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22`，与本地审查源一致。导入的 U1/U2/U3a 源实际 SHA256 依次为 `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0`、`0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d`、`0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b`，均与此前独立 CORRECT 的实现和 receipt 一致。
- 实际只读版本探测：Lean `4.36.0-rc1`，commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；Lake `5.0.0-src+c9afcdd`；项目 pin `leanprover/lean4:v4.36.0-rc1`，manifest mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。
- receipt 记录实际已执行 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/AtomProjection.olean Shao/OQ3/AtomProjection.lean`，退出码 0。真实 `runs/oq3/u6a-20261021/build-04.log` 为空，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`，与 receipt 一致。
- receipt 记录实际已执行 `lake env lean /root/rivermind-data/shao-lean-20261021/runs/oq3/u6a-20261021/Audit.lean`，退出码 0。本地 U6aAudit.lean 已完整读取，SHA256 `f46225d2e13fa2c0520944a31e64291021f8030dfbfaf69adec1fe0b98748e31`，与真实服务器 Audit.lean 一致。真实 Audit.log SHA256 `f1cdc198d6a697f38fc4fb98190abb9d5e9fc0cd9a46e41cb375794d757f9d6d`，完整读取且与 receipt 一致。
- 脚本检查四目标存在且为 theorem，遍历四个源名字前缀与 `_private.Shao.OQ3.AtomProjection`，拒绝项目新增公理，对每项调用 `Lean.collectAxioms`。真实日志输出 `U6A_FROZEN_THEOREMS 4`、`U6A_ALL_THEOREMS 6`、`U6A_ALL_DECLARATIONS 6`、`U6A_AXIOM_GATE PASS`。
- 两项生成证明为 `fixedAtom_no_projection_lattice._proof_1_1`（自然数 N≤N+1）与 `._proof_1_2`（排除 N=N+1），均实际列入审计。全部目标、局部辅助与导入依赖的传递公理只含白名单 `propext`、`Classical.choice`、`Quot.sound`。
- 实际源码扫描未见 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。receipt 的 source、scope、R1、此前独立声明报告、三项导入源与机械产物哈希均实际匹配；其“等待独立审查”是作者检查时的历史状态，本报告完成该审查，不回写原 receipt。

机械覆盖只认证固定哈希的四个 U6a 目标及其传递依赖；本次另独立完成自然语言—Lean—真实源忠实性与完整证明审查。没有执行根集成构建，也不把本局部认证升级成 U4 原律、实际特征函数非格点或整个 OQ3 的闭合。

JUSTIFICATION: 四签名与冻结接口精确一致，原子极限与源索引平移、固定 c>0 的最终整数零性、严格非零因子消去、N/N+1 的实际单射性及系数消去均有完整证明。真实成功构建与传递公理审计绑定同一审查源哈希，无关键缺口。实际概率相位等号桥、联合非格点、LLT、对角与根 A/B/C/D 仍 OPEN。
