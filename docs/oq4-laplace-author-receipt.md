# LaplaceTail 实际复现收据

状态：源码冻结；实际目标、唯一 olean 生成、import 全 module-owned 声明传递公理审计均 exit0，目标和 olean 编译日志均为空。此文件不构成独立审查票。

冻结接口：`drafts/oq4/frozen-laplace-tail-v1.md`。数学源仅新增 `Shao/OQ4/LaplaceTail.lean`；未修改任何既审数学源、公共定义、根导入、Git、锁或共享包缓存。

源码 SHA256：`664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2`。

olean SHA256：`bce8f8432b2bf5b9da401112ec5c79f471d30671475986939940714dfd4cde7d`。

实际全部29个新常量（23显式=4定义+19定理，另6生成）各自完整传递公理审计通过：25项 `{propext, Classical.choice, Quot.sound}`，4项 `{propext}`；29条记录与所属模块枚举29项完全匹配，没有额外公理。`summary.json`、`declarations.md` 是精简收据，完整日志仅服务器。

全部 Lean 检查位于指定服务器 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。工具链为 Lean v4.36.0-rc1，mathlib 807d3836b165983210ee2ecf3cd28f239436949c；每次先 activate 再 cd，单进程、4核亲和。完整原始日志仅保留服务器 `repro_outputs/oq4-laplace/`。

最小复现：

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/LaplaceTail.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/LaplaceTail.olean Shao/OQ4/LaplaceTail.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-laplace/Audit.lean
python3 repro_outputs/oq4-laplace/summarize.py
```

接口闭合：

- 任意 Borel 概率 μ 的正部 Laplace 被积函数可积、A∈[0,1]；严格尾积分恒等式与右侧相对 volume.restrict(Ioi0) 的真实可积性。
- 实际标准高斯 Φ(0)=1/2、正半轴质量1/2。
- q≥1、C_BE≥0、1≤β≤L 与全实轴标准化 CDF 输入，推出冻结的 `1/2-(1+C_BE)L/sqrt(q)` 下界。
- 真实有限产品 Pi ν 与公共 prefixSum 推送实例；产品被积函数实际可积，A_q∈[0,1]，同一下界。没有矩、中心、密度、有界支持、非格点或条件生存独立性前提。

实现直接导入已审 `IntervalConcentration` 的 actual standardNormalCDF 和其1-Lipschitz定理；加权严格 layer-cake 来自 `Mathlib.MeasureTheory.Integral.Layercake`；指数矩评估复用已缓存 `Gamma.Basic`。没有下载或修改共享缓存。

传输记录：共享 broker 多次明确返回 operation_may_have_started=false、put completed_files=0/files_may_be_partial=false。只读 native SSH 健康探测成功后，按 SERVER 文档及父实例授权使用有界手动备用通道；一次 server_direct exec 在建立会话前 banner 失败。随后 native SSH 用 base64 编码远程脚本保留确切换行/引号，实际检查日志及 exit 收据写在服务器。所有可能有副作用操作均未在状态不明时自动重放。

早期定向检查的失败属于导数/可测集/重写 API 适配，均保留服务器日志；最终 target08 日志为空且 exit0。冻结后未再改源码。

范围：只关闭 S1 的解析支付桥及真实有限和 law 实例。BE、SP、S2/S3、无条件 S/AC/O0/R3R4、B1、K/Kv、能量界及 OQ4 仍 OPEN；不声称独立形式认证。


格式维护历史：原源 SHA `5ceb63a9c3955f8479b6c0def43e9c2fdeb9ac2f915aa23553cb2243c3f8ffb9` → 当前源 SHA `664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2`。仅将5处 CRLF 改为 LF，并删末尾4个空行，保留单个最终 LF；15121→15112字节，代码token不变。旧源完整副本保存在 server `repro_outputs/oq4-laplace/LaplaceTail.before-format-5ceb.lean`；旧summary另存本机 `summary-before-format.json` 及server同名历史文件。实际重新目标/唯一olean/moduleidx 29项审计均 exit0，前两者日志为空；olean哈希不变。新原始日志分别为 `formatTarget.log`、`formatOlean.log`、`formatAudit.log`。匿名proof原始snapshot与旧独立票未修改。
