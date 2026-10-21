# LaplaceGenerating 实际复现收据

源码已冻结；实际完整目标、作者唯一olean生成、import全部新module-owned常量传递公理审计均exit0，前两者日志为空。本文为作者的机械收据，不构成独立审查票。

冻结接口：drafts/oq4/frozen-laplace-generating-v1.md。新数学源仅 Shao/OQ4/LaplaceGenerating.lean；不修改任何既审数学源、公共定义、根导入、Git、manifest、锁或共享缓存。

源SHA256：eab53afb87248fc0f9b94ddf84e986eedae51f2446e9b7ea176e517c4a861ed8。
olean SHA256：b5d5b308ec183dc097cdb856974ac3a5f0724c274ae17ef06fd80861a942f4ee。

实际全部25新常量：15显式（2定义+13定理）与10生成；按所属moduleidx枚举，不依赖namespace或根名称。25条#print axioms记录逐项同名匹配，所有传递公理均在白名单内：18项为propext/Classical.choice/Quot.sound，6项仅propext，1项propext/Quot.sound。生产源禁用项扫描为空。完整日志仅指定server repro_outputs/oq4-generating/；本机summary.json与declarations.md均是curated摘要。

实现范围：

- 所有k≥1的明确0≤A_k≤1与S1下界、L≥1及C≥0，推出W真正Summable和S2常数1+3C。
- 所有j≥0的0≤a_j≤1使真实G Summable；保留Antitone a及每个0<s<1的精确SP型恒等式作为输入，推出S3。
- 每个m≥1取s=exp(-1/m)，证明0<s<1与1-s≥1/(2m)，从含j=0的有限前缀推出sqrt(2)exp(2+3C)L/sqrt(m)。m=1、L=1、C=0均保留，无额外矩或实际law前提。

完整匿名数学推导见proof.md。最终数学import仅Mathlib.Analysis.SpecialFunctions.Log.Deriv（另有已缓存战术），不依赖LaplaceTail或任何真实law模块。

S2采用J=floor(L²)。有限调和和由1−r⁻¹≤log r望远镜证明；幂尾由1/((x+1)sqrt(x+1))≤2(1/sqrt(x)−1/sqrt(x+1))相加，得到非负部分和有界，从而真正Summable及尾界2/sqrt(J)。初段恰k≤J、尾段严格k>J，2L/sqrt(J)≤3，冻结安全常数不变。

缓存请求历史保留：原积分路线确实缺Mathlib.NumberTheory.Harmonic.Bounds、Mathlib.Analysis.SumIntegralComparisons，并由父实例请求唯一维护者。作者没有下载/写共享缓存；之后内部有限望远镜证明消除这两依赖。原未认证积分草稿仅作历史保存于LaplaceGenerating-integral-draft.lean，不是最终实现或依赖。telescope09叶子先实际exit0，完整target12随后exit0；不把先前未通过草稿当作认证。

工具链Lean v4.36.0-rc1，mathlib 807d3836b165983210ee2ecf3cd28f239436949c。全部Lean只在指定server，先activate再cd worktree，单进程4核亲和。实际复现：

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/LaplaceGenerating.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/LaplaceGenerating.olean Shao/OQ4/LaplaceGenerating.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-generating/Audit.lean
python3 repro_outputs/oq4-generating/summarize.py
```

所有复合执行脚本均set-e；若Lean失败则显式捕获exit、写server日志与exit收据，再返回相同exit。操作未开始的broker false有界手动fallback。一次native连接关闭后先核对旧源、无新日志/exit与无实际Lean进程，确认未开始才重执行。公共main同步期间遵照父实例暂停server检查，恢复后target12才上传最终源；未进行Git操作。早期定向适配失败的完整日志均仅server保存。

源码与curated当前文件为UTF8无BOM、LF、单最终LF；未为格式修改任何既冻数学源。另一次LaplaceTail提交门必需格式维护已单独按父授权完成并有独立收据，本模块不把它作为数学依赖。

范围：仅关闭确定性S1输入→S2→明确SP输入下S3与系数提取。BE、SP、实际随机游走law、无条件S/AC/O0、B1、K/Kv及完整OQ4均保持OPEN。
