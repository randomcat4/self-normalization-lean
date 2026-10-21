# OQ4 有限承重引理独立盲审 v1

审查时间：2026-10-21，服务器检查结束于 2026-10-21T08:11:26Z。

本审查仅认证冻结文件中的 F-D 和 F-R。审查者只读取冻结声明、匿名 F-R 证明、两个目标 Lean 文件及源文稿 §6/§8；未读取作者会话、作者报告或其他审稿票，未修改命题、证明、源文稿或服务器模块。所有 Lean 命令均在指定服务器执行；未安装本机 Lean，未更新或下载缓存。

## 审查对象与版本

| 对象 | SHA256 |
|---|---|
| 本机 `drafts/oq4/frozen-finite-v1.md` | `fc0c0922028bfdd1153d9e85e9756085a8dcfd4452ef8526e58507e1e294eff4` |
| 本机 `drafts/oq4/overshoot-proof.md` | `304c548a5e3d7a8b4419db8a12d4028d66cfc31170d50d1cdea35811b1276e38` |
| 本机 `drafts/oq4/OvershootSum.lean` | `a85e74313eba863b5ce6324d0bb5e2d05d5bd6399204247baea3dfd54e0ac5e2` |
| 远程 `Shao/OQ4/OvershootSum.lean` | `a85e74313eba863b5ce6324d0bb5e2d05d5bd6399204247baea3dfd54e0ac5e2` |
| 远程 `Shao/OQ4/DelayedRecurrence.lean` | `2b8655db071125a3ee51f1a28cdc06a60b56d9e79ccb930c59f32abb5f73e50b` |
| 只读源 `C:/game/shao/current/oq4/b01/proof01.md` | `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38` |

远程工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。两份远程目标源在检查前后的 SHA256 一致；本机 OvershootSum 副本与远程实际检查文件逐字节哈希一致。以下 Lean 行号均对应表中版本。

## F-D：有限延迟递推

STATUS: CORRECT

JUSTIFICATION:

1. **全部量词与假设忠实。** 冻结声明第 7–14 行对应 `DelayedRecurrence.lean:21–29`：`f,g : ℕ → ℝ`，`m,N : ℕ`，`1 ≤ m ≤ N`，四个实参数非负；`g` 的非负性只要求于 `k ≤ N`；初界同时有 `k ≤ N` 和 `k ≤ 2*m`；增量范围为 `m ≤ k < N`；延迟不等式覆盖每个满足 `k+m ≤ N` 的自然数 `k`；小系数中的 `N` 明确转为实数。没有加入单调性、`f ≥ 0`、全局 `g` 上界或长时间核结论。

2. **结论完全一致。** 冻结第 16–18 行对应 `DelayedRecurrence.lean:30–35`，其中 `M = 2*(1+A)*C`。第二个结论中的自然数截断减法仅在 `m ≤ k` 条件下出现，故 `((k-m : ℕ) : ℝ)` 正是自然语义的非负实差 `k-m`；没有更改区间、绝对值或常数。

3. **联合强归纳确证了非循环控制。** 第 42–46 行的归纳命题同时证明当前 `g(k)` 上界和当前 `f(k)` 偏差上界，归纳假设仅提供严格小于当前 `k` 的下标。

   - 对 `g(k)`，第 49–50 行在 `k ≤ 2m` 时直接使用初界。否则第 51–57 行设 `j=k-m`，由 `m ≥ 1` 和 `k > 2m` 得到 `j < k`、`m ≤ j`、`j+m=k`；只调用 `j` 的归纳结论。没有调用当前 `g(k)` 或当前 `f(k)` 的待证结论。
   - 第 58–67 行从先前已证的 `|f(j)-f(m)|`、`f(m) ≤ C` 和 `j-m ≤ N` 得到 `f(j) ≤ C+D*N*M`。这里只需要 `f(m)` 的上界，不需要其绝对值界或非负性。
   - 第 68–78 行据延迟不等式得到 `g(k) ≤ A*C+(A*D*N+B)*M ≤ A*C+M/2 ≤ M`。最后一步的差正好为 `C ≥ 0`：`M-(A*C+M/2)=C`。因此吸收步骤是已证的有限归纳推导，没有把所求统一界作为前提。
   - 对 `f(k)`，第 79–94 行先处理 `k=m`，否则令 `p=k-1`。所用归纳下标仅为 `p < k` 和 `p-m < k`；后者提供 `g(p-m) ≤ M`。第 95–102 行用三角不等式和 `k-m=(p-m)+1` 完成一步望远镜增长。该分支同样不需要当前 `g(k)` 上界。

4. **端点和零参数覆盖。** `k=m` 由第 80–82 行归零。对 `k=N`，增量只在 `p=k-1<N` 处调用（第 91–94 行），没有要求第 `N` 个增量。`N=m` 不需要任何增量；`N ≤ 2m` 的所有 `g` 值直接落在初界分支，`f` 偏差仍按上述归纳控制。证明未除以 `A,B,D,C,M`，因此各参数为零和 `M=0` 都包含。`g` 非负性和 `m ≤ N` 虽未被证明体使用，仍完整保留在定理参数中；这说明证明能承受更弱输入，不是签名漏掉冻结假设。

5. **局部源作用域正确。** 源 `b01/proof01.md:284–288` 是 D2/D3；第 290–312 行用 D4、初值和小系数推出有限控制。此 Lean 定理确证其中的有限数值递推，且以联合强归纳替代有限最大值吸收，未把 D5/D8 当假设。它没有证明 D2/D3 的概率来源、归一化正因子、B1 初值极限或小系数在某一渐近尺度下最终成立。该限制也明确写于 `DelayedRecurrence.lean:9–13` 和冻结第 20 行。

未发现关键缺口。

## F-R：有限第三矩支付

STATUS: CORRECT

JUSTIFICATION:

1. **形式陈述忠实。** `OvershootSum.lean:25–26` 将单项定义为 `((j:ℝ)+1)*max (u-(j:ℝ)) 0`；第 32–33 行对任意 `u:ℝ`、`0 ≤ u` 和任意 `L:ℕ` 给出冻结第 26–30 行的和式及常数 `4`。`Finset.range L` 正是自然数 `0 ≤ j < L`，没有附加 `L ≤ u`、非整数 `u` 或正 `L` 等条件。

2. **任意截断确实覆盖。** 匿名证明第 5 行以及 Lean 第 34–51 行令 `J=⌊u⌋₊+1`。由于 `u ≥ 0`，自然数下取整与普通下取整相符，且 `u<J≤u+1`。对于 `j≥J`，`u-j<0`，故该项为零。Lean 的 `hcut` 用有限集包含和零尾项证明原和等于截止 `min L J` 的和；这对任意大的 `L` 同样成立。

3. **有限和估计无漏项。** 匿名证明第 7 行以及 Lean 第 53–72 行对 `j<min L J` 得到 `j≤⌊u⌋₊≤u`，从而 `max(u-j,0)≤u`、`j+1≤u+1`，所以单项不超过 `(u+1)*u`。项数最多为 `J≤u+1`，于是全和不超过 `(u+1)^2*u`。每次乘法比较的因子非负性都已由 `u≥0` 或 `j:ℕ` 提供。

4. **最后多项式比较有效。** 匿名证明第 9 行以及 Lean 第 73–74 行使用的差为

   `4*(u+u^3) - (u+1)^2*u = u*(u-1)^2 + 2*u^3 + 2*u ≥ 0`。

   这仅使用冻结的 `u≥0`；没有额外增长条件。

5. **所有指定端点覆盖。** `L=0` 时和为空；`u=0` 时每项均为零；`0<u<1` 时 `J=1`，只可能保留 `j=0`；整数 `u=n` 时 `J=n+1`，`j=n` 的零项保留在短和中，`j≥n+1` 的尾项另证为零。证明不需要排除上述任一情形。

6. **局部源作用域正确。** 源 `b01/proof01.md:210–214` 的 R6 要求一个数值常数；本结果提供常数 `4` 的逐点有限版本。源第 204–208 行的概率占据输入及第 214 行的取期望仍是独立步骤。Lean 文件第 13–15 行和冻结第 32 行均明确不声称完成这些步骤。不能据此报告 R3、一般 K 或 Kv 已形式闭合。

未发现关键缺口。

## 服务器机械核验与公理

实际工具链：Lean `4.36.0-rc1`，commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；Lake `5.0.0-src+c9afcdd`。`lean-toolchain` 为 `leanprover/lean4:v4.36.0-rc1`；`lake-manifest.json` 钉死 mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，与冻结要求一致。

所有检查先执行：

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
```

实际目标文件检查（均退出 0，无警告输出）：

```text
taskset -c 0-3 lake env lean Shao/OQ4/OvershootSum.lean
taskset -c 0-3 lake env lean Shao/OQ4/DelayedRecurrence.lean
```

传递公理审计通过将目标源与相应 `#print axioms` 命令拼接后送入服务器 `taskset -c 0-3 lake env lean --stdin` 完成，两个输入均退出 0，不依赖先前生成的目标模块二进制。全部显式新增声明的输出如下：

```text
'Shao.OQ4.overshootCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.overshootCell_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.overshoot_sum_le_cubic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.delayed_recurrence_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

两份源的 `sorry|admit|axiom|unsafe|native_decide` 词项扫描结果为空。新增声明的传递公理均在白名单内。结合上面的逐项语义审查，**F-D 与 F-R 两个冻结有限目标可记为 LEAN_FULLY_CHECKED**；这不是 OQ4 根目标的完整机械认证。

## 根状态

**全部根组保持 OPEN：C1/C2、OQ3、OQ4（含 K/Kv）、OQ5/OQ6。**

本票仅认证两个冻结有限引理。概率占据输入、期望及单调收敛、D2/D3 的概率推导、归一化正因子、初值极限、渐近时间尺度及 K 前因子等后续义务，没有因这两个有限模块通过而自动关闭。
