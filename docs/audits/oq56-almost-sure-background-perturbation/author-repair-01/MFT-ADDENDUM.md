# unit280 repair01：受影响 T03 忠实性补充

状态：仅T03完整proof修复；完整新源码7679B/170LF，SOURCE/native02/AX均未运行。

| 核对项 | 精确变化/复用 | 数学影响与范围 |
|---|---|---|
| 原失败 | native01 actualRC1，唯一T03L106C20 Measurable.comp pair函数未定元错误；noO/自然全结束/preservation exact | 原失败与源码完整保留，不追认通过，不重放命令 |
| hpair | T03内显式Measurable(fun x:Fin n→Ω =>(x i,x j))，由两eval的prodMk给出 | 固定实际样本域/乘积值域，不新增前提或顶层helper |
| hrx | T03内显式实值残差复合；comp的g=uncurry r、f=实际pair map均显式 | 与原r(xi,xj)定义相同，仅消除elaboration未定元 |
| hwx | T03内显式Measurable(fun x:Fin n→Ω =>w(xi)) | 复用原hw；未升级AE权重为处处，未增加均值/方差要求 |
| E与交集 | 原两主集合交、Fin n有限iInter、i≠j命题证明索引交保持 | 任意可测Ω，原r/w可测条件不变；重复观测、任意对角仍允许 |
| 冻结字节 | 8HEAD/2RHS/PRE/CLOSE逐字相同；2def HEAD各含唯一outer:= | 无签名/定义/条件/顺序/导入/设置变更 |
| 未受影响证明 | T01/T02/T04/T05/T06共5proof/60LF逐字相同 | 原完整SOURCE证据复用，不重复审查/检查；无T05供应变化 |
| 精确差异 | 仅原T03 proof一连续区间；其前缀/后缀逐字相同 | 旧7371B/162LF→新7679B/170LF；+308B/+8LF |
| 新计数 | 8声明/6proof；HEAD39LF，RHS19LF，proof components84LF，ALLPROOF89LF | 源级计数，非新actual-owner/AX结果 |
| 后续认证 | 仅本地文本/哈希/组装guard | 受影响SOURCE与native02待父级；sourceAccepted/kernelChecked/qualified=false |
| 原作用域 | 同一AE E内forallvforallB，半系数/原n−2/中心化系数1均原样 | 不声称选择规则可测；不消费279；条件投影/交互/rareblock/PE/root仍OPEN |
| 权限/历史 | 旧source/SOURCE/failure/freeze/其他owner全只读，唯一新author-repair-01 | 封存后active+dormant全释放；无SSH/Lean/AX/网络/资源修改 |

完整原数学路线与MFT由绑定的原稿/原SOURCE证据承载，本补充只覆盖这24LF的新T03 proof及其明确类型实例化，未重新给其余5proof盖独审结论。
