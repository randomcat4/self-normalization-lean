# 作者正式检查收据

STATUS: AUTHOR_CANONICAL_GATES_PASSED_AWAITING_INDEPENDENT_REVIEW
ROOT_STATUS: OPEN
SPECTRUM_STATUS: OPEN

源码 `Shao/OQ4/RademacherCosine.lean`：SHA256 `c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861`，8414字节；与冻结 scratch Source.lean 完全相同，UTF-8无BOM、LF、恰一末LF。

数学 proof.md 保持 SHA256 `1d599f635c633e11355f29ef5748e23e1e836486fc8fdc99d404b07afbfd8e6d`，13237字节；数学审查通过由lead报告，本文未改写证明或数学命题。

基线为 frozen canonical-release-base.json 的35个OQ4源文件，head c846961bd3dd7a4bac6178b04baa50393ab23cf2。作者仅获本模块canonical36窗口及一次唯一olean生成授权。

| 检查 | 退出码 | 标准输出字节 | 标准错误字节 | 结果 |
|---|---:|---:|---:|---|
| full-source | 0 | 39042 | 0 | 通过，无警告；审计输出为声明JSON |
| target-no-o | 0 | 0 | 0 | 通过，无警告；审计输出为声明JSON |
| unique-emit | 0 | 0 | 0 | 通过，无警告；审计输出为声明JSON |
| full36 | 0 | 1495040 | 0 | 通过，无警告；审计输出为声明JSON |

full-source预检导入全部旧35模块后拼接逐字节不变的源码正文，并遍历全部 `getModuleIdxFor? = none` 的声明，未作名称过滤，实测34个；与正式模块导入后34个owned声明的user_name/kind/instance集合完全对应。

target-no-o从canonical文件经stdin检查，不生成olean；随后仅执行一次 `taskset -c 0-3 lake env lean Shao/OQ4/RademacherCosine.lean -o .lake/build/lib/lean/Shao/OQ4/RademacherCosine.olean`，退出0，无警告，无标准输出/错误。unique-emit.json记录唯一调用。

full36导入全部冻结旧35模块与新模块，遍历所有模块owned声明与Shao.OQ4命名空间声明的并集。总计704个：旧35模块670个，本模块34个，无36模块之外的namespace-only声明。每项传递公理均在propext、Classical.choice、Quot.sound白名单内；未新增axiom。

本模块实测：9个显式public theorem、4个定义、1个命名实例、6个显式private helper、14个generated helper；全部名称/kind/完整签名/axioms见declarations.md。kind统计为definition=4、theorem=30，实际注册实例=1。

源码精确集合从旧35项变为旧35项加本模块共36项；35项旧源码SHA全部保持。另92项common/root/pins源文件的精确集合与SHA前后完全相同，.lake/packages解析目标未变。未执行Git、cache写入或其他模块emit。

全部作者正式调用均已返回；最终从/proc仅检查lean/lake进程名及cwd，本工作树无live Lean/Lake进程。

原始审计日志及二进制产物只保留服务器repro_outputs/oq4-rademacher-cosine/及指定.lake目标。本地仅整理源码、此收据、完整声明清单、summary与checkpoint；仍须lead安排独立full36审查。

## 正式olean产物

- 路径：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/.lake/build/lib/lean/Shao/OQ4/RademacherCosine.olean`
- SHA256：`bbef5afc3922ee9fbfaaf6b1bc1d579b7ec762862e795e7a78165064bfb5aea3`
- 字节：429360
