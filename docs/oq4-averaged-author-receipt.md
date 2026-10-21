# AveragedResidual v2 服务器检查收据

范围：冻结v2的完整解析平均支付接口。最终源实际无警告编译，olean生成成功，实际导入后全部8个新常量逐项传递公理审计通过。本收据报告作者机械证据，不替代独立语义/数学审查。

## 最终工件与源

- 远程源：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/AveragedResidual.lean`。
- 本机最终副本：`C:/game/shao lean/drafts/oq4/averaged/AveragedResidual.lean`。
- 最终源SHA256：`ffe155446ff31b1f1e20dc6ff1b8dc14b1c5274b2593a4cc774183b053491aa2`，本机与服务器一致。
- 唯一读取的冻结接口为`frozen-averaged-residual-v2.md`；SHA256：`39a288d06c817ea1e745cf191b239d3b4a083d0367ebe8e16eee78724a755da5`。
- 匿名完整推导为本目录`proof.md`；全部新常量清单为`declarations.md`。
- 源锚`b01/proof01.md` §6 R2/R3/R5/R6，SHA256：`7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`。

实际只读依赖源码哈希也记录于最终审计日志：

| 依赖 | SHA256 |
|---|---|
| `KilledCosine.lean` | `054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8` |
| `OvershootMoment.lean` | `a785a61be3f7c5230f66e053c0a827c9bde7674fc27fa129e6306033c92aee10` |
| `OccupationPayment.lean` | `3ed77e585a0a687b471d46e004872d35c18d7181388a7828c34e83085bd094d9` |

## 实际环境与检查

Lean 4.36.0-rc1，提交`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Linux x86_64 Release；Lake 5.0.0-src+c9afcdd。工具链`leanprover/lean4:v4.36.0-rc1`，mathlib项目锁`807d3836b165983210ee2ecf3cd28f239436949c`。

1. 最终目标命令`taskset -c 0-3 lake env lean Shao/OQ4/AveragedResidual.lean`：exit 0，无输出、无警告。日志`repro_outputs/oq4-averaged/check-04-final.log`及相应`.exit`。
2. 生成`.lake/build/lib/lean/Shao/OQ4/AveragedResidual.olean`：exit 0，无警告。日志`repro_outputs/oq4-averaged/build-05-olean.log`及相应`.exit`。
3. `import Shao.OQ4.AveragedResidual`后动态枚举全部8个新常量并逐项`#print axioms`：exit 0。全部仅使用白名单公理。日志`repro_outputs/oq4-averaged/audit-06-import-all-axioms.log`及相应`.exit`。
4. 最终源禁用项扫描：`sorry`、`admit`、新增`axiom`、`unsafe`、`native_decide`零命中。

参数积分实际使用已缓存的`Mathlib.MeasureTheory.Integral.Prod`及`StronglyMeasurable.integral_prod_right'`。没有缺失缓存请求，也没有共享缓存写入。

前两轮日志保留参数辅助接口与函数表达式规范化错误；第三轮目标已通过，随后进一步把固定w下Kcos/ρ有界核的ν可积性显式用于积分比较，形成最终第四轮。所有修改仅在证明体内，冻结前提、两个精确上界及签名未改变。

## 最小复现

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/AveragedResidual.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/AveragedResidual.olean Shao/OQ4/AveragedResidual.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-averaged/AllAxioms.lean
sha256sum Shao/OQ4/AveragedResidual.lean
```

所有Lean仅服务器、单进程、4核亲和；只由本作者写本模块源/olean。没有Git操作、本机Lean、根文件/公共定义/锁更改或他人源码改动。完整日志留服务器，没有复制到共享本机工作区。

## 语义与关闭范围

显式证明联合核和参数积分可测、固定参数超越核及Kcos/ρ核的ν可积、ψ对κ可积和|r|对κ可积；没有把默认不可积积分0当估计。κ仅AE支持于闭[-h,h]且κ.real(univ)≤1，没有添加密度、F可积前提、第四矩或有界ν支持。

最终两个上界完整保留C，统一类常数为C_{M,C}。层质量仍是独立OPEN O0输入；只关闭解析R3约化，不证明O0概率层质量、完整源R3、R4、Brownian初值/末端块、E1–E6、K、Kv或完整OQ4。
