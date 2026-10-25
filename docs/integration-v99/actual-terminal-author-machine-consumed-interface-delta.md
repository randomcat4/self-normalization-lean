# 机器修订实际追加消费接口

这两项均来自原已接受 source/object，当前只读取接口/完整值并复用原资格。没有新增 import、全局辅助头、定义或实例。

```lean
namespace Shao
def truncationF (z : ℝ) : ℝ := z ^ 2 * min |z| 1
theorem truncationF_nonneg (z : ℝ) : 0 ≤ truncationF z
end Shao
```

```lean
namespace Shao.Probability.SourceActualLocalProfileBudget
open Shao.C2.BridgeDomination
def wallSigns (J : MonitoredDomain) : Finset ℝ :=
  match J with
  | .upper => {1}
  | .lower => {-1}
  | .interval => {1, -1}
end Shao.Probability.SourceActualLocalProfileBudget
```

前者支付原归一化截断预算非负性。后者让固定后缀证明直接采用实际 terminal corridor 中的同一墙符号集合，避免 proof-local match 编译生成额外参数所致的换型失败。所有数学对象与冻结头/22 statement lets 保持原值。完整源、原对象、独审与原导出凭据见相邻 JSON。
