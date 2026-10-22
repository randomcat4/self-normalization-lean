STATUS: CORRECT
FORMAL_STATUS: LEAN_FULLY_CHECKED
SCOPE: FROZEN_FINITE_ENERGY_LINEAR_PATH_LEAF_ONLY
E3_STATUS: OPEN
OQ4_STATUS: OPEN
SOURCE_WINDOW: ENDED_NO_LIVE

# EnergyLinearPathLaw 独立最终形式审查 v1

本票独立核对冻结有限叶子的实际源码、完整公开声明、全部当前模块声明、真实导入对象及传递公理。数学证明仍绑定先前固定的独立 CORRECT 票。本票不关闭相对渐近、共同二维算子、完整 E3、E4 或 OQ4 根。

## 精确对象与锁定版本

| 对象 | SHA256 | 字节 |
|---|---|---:|
| 冻结命题 `drafts/oq4/frozen-energy-linear-path-law-v1.md` | `54678ca7adbdcfaf007f34b1637693f2b70e6e73a15d69a761bf88f52e601091` | 3705 |
| 匿名数学证明 `drafts/oq4/energy-linear-path-law/proof.md` | `6cb27fdbecad8c22a2b051a4285d55fde4f4d215b562d4f0b8270752f4618776` | 12028 |
| 独立数学票 `drafts/oq4/review/energy-linear-path-law-math-review-v1.md` | `670ca1836bb15f927ddad3058b037bdc1343d6bfa5528be9011de88f4b497edf` | 5645 |
| 实际 canonical `Shao/OQ4/EnergyLinearPathLaw.lean`，本地对应 `drafts/oq4/energy-linear-path-law/EnergyLinearPathLaw.lean` | `039ad7326ea9a80e476f50bf3f46dd0078c2c61f6786f15a6d72f3ba0c227afb` | 18042 |

canonical 为 UTF-8 无 BOM、无 CR、恰好一个末尾 LF。本地审阅副本与服务器 canonical 字节哈希相同。实际导入的目标 olean SHA256 为 `64c1e89a0cc3b6357b0b1ccfbc47947a19a85904e44ad18fb5d6a14ef8400ec3`，独立审查前后不变；独立审查没有 emit 或修改 olean。

继承的发布基础为 PR65、branch `feat/oq4-linear-path`、head `4388ae02623c03dbf6b707fb3847d8793924d39a`。这些分支/head 字段来自冻结 `canonical-release-base.json`；本审查没有运行 Git。旧34个实际 OQ4 源逐项对该文件的逐源 SHA 验证一致。

服务器工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。

实际版本命令 exit 0：Lean `4.36.0-rc1`，commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；Lake `5.0.0-src+c9afcdd`。`lean-toolchain` 为 `leanprover/lean4:v4.36.0-rc1`；实际 lake-manifest 的 mathlib rev 和 inputRev 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。

## 独立命令与退出码

所有 Lean 命令均只在指定服务器执行，并使用 `taskset -c 0-3`。每条命令的实际共同前缀为：

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh && cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4 &&
```

| 检查 | 前缀之后的实际命令 | exit |
|---|---|---:|
| 独立目标 no-o | `taskset -c 0-3 lake env lean Shao/OQ4/EnergyLinearPathLaw.lean` | 0 |
| 首次完整源码审计，附加脚本含未知 option，保留失败记录 | `taskset -c 0-3 lake env lean --stdin Shao/OQ4/EnergyLinearPathLaw.lean` | 1 |
| 只修审计脚本后的全新完整源码审计 v2 | `taskset -c 0-3 lake env lean --stdin Shao/OQ4/EnergyLinearPathLaw.lean` | 0 |
| 显式导入全部实际35个 OQ4 模块的独立审计 | `taskset -c 0-3 lake env lean repro_outputs/oq4-energy-linear-path/independent-review-v1/all35-import-audit.lean` | 0 |
| 实际 Lean/Lake 版本 | `taskset -c 0-3 lake env lean --version && taskset -c 0-3 lake --version` | 0 |

目标 no-o 用时约4.37秒；完整源码 v2 约5.47秒；全35实际导入审计约5.92秒。完整源码输入为 `import Lean` 加实际 canonical 全部源码，再附独立审计尾部；通过 `--stdin` 和实际模块路径保留真实模块名。没有引用目标自身的 olean来替代其源码展开。

完整源码审计唯一筛选是 `(env.getModuleIdxFor? name).isNone`；未添加任何 namespace/name 根过滤，因此包含全部公开、私有与生成声明。每项都执行 `Lean.collectAxioms`。全35实际导入审计采用“所属模块前缀 Shao.OQ4 或声明命名空间前缀 Shao.OQ4”的并集，逐项执行同一个传递公理检查。

## 声明、类型与公理的实测结果

| 分母 | 独立实测 |
|---|---:|
| 源码显式公开 theorem | 12 |
| 源码显式公开 definition | 1 |
| 源码显式 private theorem | 2 |
| 源码生成声明 | 8 |
| 完整源码所有 getModuleIdxFor? none | 23 |
| 实际目标模块所属声明 | 23 |
| 全35导入 OQ4 模块所属声明 | 670 |
| 全35导入 OQ4 命名空间声明 | 656 |
| 所属模块或命名空间的并集 | 670 |

目标的23项分为1个 definition、22个 theorem。8个生成声明恰为 `Shao.OQ4.energyLinearPathIntegrand.eq_1` 与 `Shao.OQ4.energyLinearPathLaw_integral._simp_1_1` 至 `._simp_1_7`。2个显式私有声明的真实完整名字为：

```text
_private.Shao.OQ4.EnergyLinearPathLaw.0.Shao.OQ4.energyLinearPath_density_mul
_private.Shao.OQ4.EnergyLinearPathLaw.0.Shao.OQ4.energyLinearPath_iid_real_apply
```

对源码所有 none 项与实际导入目标的所属项，独立提取了真实完整名称、ConstantInfo 种类、宇宙参数、`reprStr info.type` 的完整类型表达式及传递公理列表。23项名称集合与每个字段完全一致；公理列表只按顺序排序后比较，没有重命名私有常量、改写类型或删除字段。此方法直接比较真实名称与表达式，不依赖 `#print` 头部显示别名或 dagger 标记。

结构指纹规范文件 `declaration-fingerprints-canonical.json` 共487018字节，SHA256 `3867e6795544fb095d3bdb7eb44a785824c91a03a131137b239bcc43f269198e`，保留全部23项完整类型及公理，服务器留存。所有目标项和全35并集670项的传递公理均包含于 `{propext, Classical.choice, Quot.sound}`；目标并集恰为这三项。目标源码未出现 `sorry`、`admit`、`axiom`、`unsafe`、`native_decide` 关键字。未发现新增目标假设或绕过内核的路径。

## 自然语言到完整声明的忠实性

- `energyLinearPathIntegrand` 正是冻结的同一个 closedStrip 事件内 exp(-t S_n)、事件外0，S_n 使用真实 prefixSum n。公开的可测性、非负性、闭事件内夹界及真可积性辅助定理保留任意 n 和任意实 t；较一般的概率 ρ 辅助引理没有成为实际 law 定理的新前提。
- `energyLinearPathLaw_withDensity` 的两端是实际 μ_t 与 μ 的 Measure.pi，密度明确为 ofReal(exp(t S_n)/L^n)。源码从实际 withDensity 定义和已认证 finitePi_withDensity 推出它；μ、μ_t 的概率性质、L>0 及指数可积性由冻结前提内部供应。原 ν→μ 的能量截断未被删除。
- `energyLinearPathLaw_integral` 同时返回实际 Q 下 F_t 的 Integrable 与冻结反向身份。实际证明还显式建立加权函数的真可积性；唯一相消分母为已证明正的 L^n。其辅助密度乘法是逐点恒等式，没有生存质量的除法。
- `energyLinearPathLaw_sandwich` 的上下端恰为 L^n exp(±|t|h) Q.real A，保持同一个闭事件；没有 n h、累计漂移移墙、中心化参数或生存概率正性前提。
- `energyLinearPathLaw_integral_iid` 返回真实样本路径 F_t 的真可积性、样本积分等于实际 product 积分及反向身份；`probability_iid`、`base_probability_iid` 分别给 μ_t、μ 的真实事件概率拉回；最终 `energyLinearPathLaw_iid` 在两个任意概率空间上合并身份与夹界。逐坐标可测/iIndepFun/实际 law 的 IdentDistrib 与原共享 iid_samplePath_map_eq_pi 完全匹配，没有新密度、条件独立或额外耦合假设。
- 全部目标声明保留 n=0、正负 t、t=0、h=1、T=s=0；closedStrip 本身包括零前缀与弱闭端点，允许原子、全零路径和零生存质量。没有增加原中心、三阶矩、M/K/θ、方差下界、原支持、原指数矩或 n/h 条件。t=0 与 n=0 是全称声明的直接特例，并不依赖额外域外解释。

下列附录逐字保留本次精确源码中的全部12个公开 theorem 的完整签名与唯一公开 definition 的完整定义。所有隐含类型参数和前提均保留；全部23项机械展开的完整类型另见上述结构指纹文件。

## 全部公开定义与完整定理签名

源码第 13 行：

```lean
noncomputable def energyLinearPathIntegrand {n : ℕ} (h t : ℝ) (a : Shao.Path n) : ℝ := by
  classical
  exact if a ∈ Shao.closedStrip h then Real.exp (-t * Shao.prefixSum a n) else 0
```

源码第 17 行：

```lean
theorem energyLinearPathIntegrand_nonneg {n : ℕ} (h t : ℝ) (a : Shao.Path n) :
    0 ≤ energyLinearPathIntegrand h t a
```

源码第 22 行：

```lean
theorem energyLinearPathIntegrand_measurable {n : ℕ} (h t : ℝ) (hh : 0 ≤ h) :
    Measurable (energyLinearPathIntegrand (n := n) h t)
```

源码第 29 行：

```lean
theorem energyLinearPathIntegrand_closed_bounds {n : ℕ} (h t : ℝ) (a : Shao.Path n)
    (ha : a ∈ Shao.closedStrip h) :
    Real.exp (-|t| * h) ≤ energyLinearPathIntegrand h t a ∧
      energyLinearPathIntegrand h t a ≤ Real.exp (|t| * h)
```

源码第 40 行：

```lean
theorem energyLinearPathIntegrand_le {n : ℕ} (h t : ℝ) (a : Shao.Path n) :
    energyLinearPathIntegrand h t a ≤ Real.exp (|t| * h)
```

源码第 47 行：

```lean
theorem energyLinearPathIntegrand_integrable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (n : ℕ) (h t : ℝ) (hh : 0 ≤ h) :
    Integrable (energyLinearPathIntegrand (n := n) h t) (Measure.pi (fun _ : Fin n => ρ))
```

源码第 56 行：

```lean
theorem energyLinearPathLaw_withDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t) =
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).withDensity
        (fun a => ENNReal.ofReal (Real.exp (t * Shao.prefixSum a n) /
          (energyLinearNormalizer ν h s t) ^ n))
```

源码第 98 行：

```lean
theorem energyLinearPathLaw_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Integrable (energyLinearPathIntegrand (n := n) h t)
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)) ∧
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) =
        (energyLinearNormalizer ν h s t) ^ n *
          ∫ a, energyLinearPathIntegrand h t a
            ∂Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)
```

源码第 145 行：

```lean
theorem energyLinearPathLaw_sandwich (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    (energyLinearNormalizer ν h s t) ^ n * Real.exp (-|t| * h) *
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)).real (Shao.closedStrip h) ≤
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) ∧
    (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) ≤
      (energyLinearNormalizer ν h s t) ^ n * Real.exp (|t| * h) *
        (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)).real (Shao.closedStrip h)
```

源码第 206 行：

```lean
theorem energyLinearPathLaw_integral_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p (energyLinearTiltLaw ν h s t)) :
    Integrable (fun ω => energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω)) p ∧
      (∫ ω, energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p) =
        (∫ a, energyLinearPathIntegrand h t a
          ∂Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)) ∧
      (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) =
        (energyLinearNormalizer ν h s t) ^ n *
          ∫ ω, energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p
```

源码第 239 行：

```lean
theorem energyLinearPathLaw_probability_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p (energyLinearTiltLaw ν h s t)) :
    (Measure.pi (fun _ : Fin n => energyLinearTiltLaw ν h s t)).real (Shao.closedStrip h) =
      p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h}
```

源码第 254 行：

```lean
theorem energyLinearPathLaw_base_probability_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p (energyTiltedLaw ν h s)) :
    (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) =
      p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h}
```

源码第 269 行：

```lean
theorem energyLinearPathLaw_iid {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    (p₀ : Measure Ω₀) [IsProbabilityMeasure p₀] (p : Measure Ω) [IsProbabilityMeasure p]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s t : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X₀ : Fin n → Ω₀ → ℝ) (hX₀ : ∀ i, Measurable (X₀ i)) (hIndep₀ : iIndepFun X₀ p₀)
    (hLaw₀ : ∀ i, IdentDistrib (X₀ i) (id : ℝ → ℝ) p₀ (energyTiltedLaw ν h s))
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p (energyLinearTiltLaw ν h s t)) :
    Integrable (fun ω => energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω)) p ∧
      p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} =
        (energyLinearNormalizer ν h s t) ^ n *
          ∫ ω, energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p ∧
      ((energyLinearNormalizer ν h s t) ^ n * Real.exp (-|t| * h) *
          p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h} ≤
        p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} ∧
       p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} ≤
        (energyLinearNormalizer ν h s t) ^ n * Real.exp (|t| * h) *
          p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h})
```

## 旧源、共享源与版本的前后指纹门

在作者 READY 前已独立取得旧34个 OQ4 源、完整32个 Basic/Probability 源的实际文件集合和逐源 SHA，以及版本/根文件四项。READY 后、全部检查结束后均重新取指纹。结果为：旧34逐项符合 canonical-release-base；旧34、共享32的完整文件集合与全部逐源 SHA 在三个采样点相同，四个版本/根文件也相同。目标源码039ad732和目标 olean64c1e89a在独立窗口前后均相同。

| 文件 | 窗口前后相同的 SHA256 |
|---|---|
| `lean-toolchain` | `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4` |
| `lakefile.toml` | `444f3a3a01fd8ff99f219cff08a99b20459c0d177c4e2c884af9eead481daf44` |
| `lake-manifest.json` | `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e` |
| `Shao.lean` | `6dc4c451432716f5d3027adefebf416ea42faef8dd1018be0017cc7fe153676c` |

完整逐源列表均在服务器独立窗口证据目录 `repro_outputs/oq4-energy-linear-path/independent-review-v1/`：

| 证据文件 | SHA256 |
|---|---|
| `pre-snapshot.json`，READY 前 | `e19bc7de235d8689f3df5f24b013a53084936bf066ec6d64fb100c2a42deed97` |
| `ready-snapshot.json`，READY 后检查前 | `b2c85ca8896e8ef01a3b1c256898bf1a02d2b5c6dec05a8e9b83d266b28d3776` |
| `post-snapshot.json`，检查后 | `b19b49f15981ecc7339bac01509763421fcef1feb81a516d0d192d41d79852a8` |
| `target-no-o.receipt.json` | `118215795c266bcfab4b0a0961489c81a273aea26648fda42f373fd750b43033` |
| `fullsource-all-none.receipt.json`，首次附加脚本失败 | `352bfbb2debf410ab1f451d186b74eeeaba17d6f7ed77683f0de1a09cfd45e51` |
| `fullsource-all-none-v2.receipt.json`，修脚本后成功 | `9d535e1d99c27fdca15e11f214255dc6b98843363a966a8ca3f784cc0de64a0a` |
| `all35-import-audit.receipt.json` | `16c0263246c0096c452386e54d02031981c6c32b8f433ef4aa174cb23d690c50` |
| `independent-summary.json` | `1fb8f0589bcf67fa5f4d02410b3b831b3b2f84271510aad6c360b412fd33648a` |
| `declaration-fingerprints-canonical.json` | `3867e6795544fb095d3bdb7eb44a785824c91a03a131137b239bcc43f269198e` |

原始 Lean 日志仅在服务器同目录的 `target-no-o.log`、`fullsource-all-none.log`、`fullsource-all-none-v2.log`、`all35-import-audit.log`，没有复制到本地。

## 审计工具修正与失败历史

1. 准备期曾为防范字面转义箭头进行纯 Python 检查；因文件本来已含有效 Unicode 左箭头、没有字面转义序列，该预防检查断言失败、exit 1，未修改任何文件，也未运行 Lean。后续检查确认两个原始脚本字节哈希均不变。记录为 `tool-preparation-history.json`，SHA256 `e764ad7aed409adddbd039e42df41ad1abed90509ee249f4dcf911a12e902bcb`。
2. 首次完整源码 Lean 审计 exit 1，唯一错误为独立附加脚本的 `set_option pp.width 200`：`Unknown option pp.width`。canonical 已完整展开，日志亦列出全部23个 none 项，但该次不被当作成功。
3. 只删除审计脚本中不支持的 pp.width 行，并加入结构化名称、种类、宇宙、完整 Expr 类型、公理指纹；没有修改 canonical、证明、olean 或导入源。保留首次日志和 receipt 后，进行全新的 fullsource v2，exit 0；全35实际导入审计也 exit 0。
4. 修正前 fullsource-tail SHA 为 `e5d9345b7ba5ea4e1e360ac5de7a1f0b8c28aeda4131504ddee56badc4836ecc`，修正后为 `d25a29464497b4b28aad60072811c5fb6fba6b0f3d0fd95814193295c101fd8d`。导入审计脚本从 `1e4b71fcd84a06914bdfe7d9521faf3fcba9c7111e96c4407e1ae2c28337d9f2` 变为 `dd9a49b845952d30479e807795946aa3a8ee30a9b0e3fbd3692175b703348d22`。修正记录 `audit-tool-correction.json` SHA 为 `aa5f7875db0d18b770102ca18031c107947a2c0eaff5832799ed83d7869e0ee1`。

最终 verdict 为 CORRECT，限于本冻结有限叶子。本独立窗口已结束，所有自身 exec/session 与目标或自身审计 Lean 进程均已结束；服务器进程核对为空。本轮未写 target/proof/olean/common/cache/Git 或他人审查文件。完整 E3 与 OQ4 仍为 OPEN。
