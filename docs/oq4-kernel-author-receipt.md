# KilledKernel v2 服务器检查收据

范围：冻结v2的一步真实可测核完整接口。最终目标实际无警告编译；本模块olean生成并成功import；全部15个新常量逐项传递公理审计通过。本收据报告作者机械证据，不替代独立语义/数学审查。

## 工件与源

- 远程源：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/KilledKernel.lean`。
- 本机最终副本：`C:/game/shao lean/drafts/oq4/kernel/KilledKernel.lean`。
- 最终源码SHA256：`f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f`；本机与服务器一致。
- 只读取冻结`frozen-killed-kernel-v2.md`，SHA256：`034cbec4c7e447e9fa27a2c71bc87194924bea2528bef0d7fe7da15667ca3ecf`。
- 只读已审`KilledCosine.lean`依赖SHA256：`054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8`。
- 原源`b01/proof01.md` §1及§6 R1，SHA256：`7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`。
- 匿名完整推导为本目录`proof.md`，全部新常量清单为`declarations.md`。

## 实际检查

1. `taskset -c 0-3 lake env lean Shao/OQ4/KilledKernel.lean`：最终exit 0，无输出、无警告。服务器日志`repro_outputs/oq4-kernel/check-02-final.log`及`.exit`。
2. 生成本模块olean：exit 0，无警告。日志`repro_outputs/oq4-kernel/build-03-olean.log`及`.exit`。
3. `import Shao.OQ4.KilledKernel`后动态枚举全部15个新常量并逐项公理审计：exit 0，全部仅在白名单内。日志`repro_outputs/oq4-kernel/audit-04-import-all-axioms.log`及`.exit`。
4. 最终源禁用项扫描：`sorry`、`admit`、新增`axiom`、`unsafe`、`native_decide`零命中。

首轮`check-01.log`只报告一个扩展非负实数类型的记号作用域错误，改为显式`ENNReal`类型后通过；没有数学、前提或签名变更。所需Kernel模块均已有缓存，没有下载或写共享缓存。

实际环境：Lean 4.36.0-rc1，提交`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`，Linux x86_64 Release；Lake 5.0.0-src+c9afcdd。项目工具链`leanprover/lean4:v4.36.0-rc1`，mathlib锁`807d3836b165983210ee2ecf3cd28f239436949c`。

## 最小复现

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KilledKernel.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/KilledKernel.olean Shao/OQ4/KilledKernel.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-kernel/AllAxioms.lean
sha256sum Shao/OQ4/KilledKernel.lean
```

全部Lean仅指定服务器、单进程、4核亲和，本作者唯一写本模块源/olean。没有本机Lean、Git操作、已审源/根文件/共同定义/锁更改或共享缓存写入；完整日志留服务器。

## 语义与关闭范围

ν仅为任意Borel概率law，没有中心、方差、矩、密度或支持限制。h为任意实数。行精确为平移ν后限制闭[-h,h]，不归一化；h=0原子、严格离开killing和整个实轴起点延拓均保留。

有界Borel实测试通过`Measurable f`和存在全局实界M表达，证明两侧真实可积后给出积分恒等式。余弦测试覆盖每个实频率a。

本模块不证明核幂与真实有限iid路径事件表示、长时间Markov估计、O0、R3、K、Kv或完整OQ4；这些仍OPEN。
