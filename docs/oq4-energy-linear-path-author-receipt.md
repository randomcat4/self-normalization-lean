# EnergyLinearPathLaw 作者正式检查收据

STATUS: AUTHOR_FORMAL_CHECKS_PASSED_READY_FOR_INDEPENDENT_REVIEW
ROOT_STATUS: OPEN
E3_STATUS: OPEN

正式源码 `Shao/OQ4/EnergyLinearPathLaw.lean` SHA256 `039ad7326ea9a80e476f50bf3f46dd0078c2c61f6786f15a6d72f3ba0c227afb`，18042字节，保持既过scratch全部字节不变。匿名proof与独立数学票分别绑定 `6cb27fdbecad8c22a2b051a4285d55fde4f4d215b562d4f0b8270752f4618776`、`670ca1836bb15f927ddad3058b037bdc1343d6bfa5528be9011de88f4b497edf`。

工作分支 `feat/oq4-linear-path`，HEAD `4388ae02623c03dbf6b707fb3847d8793924d39a`；未操作Git写入。服务器指定Lean工具链 `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。全部Lean检查按单进程、taskset0-3顺序完成。

旧34模块导入加exact body共存预检、canonical no-o目标检查、完整source所有getModuleIdxFor? none无过滤检查、一次唯一目标olean生成、实际35模块导入的target-owner签名/公理及全OQ4 module-owner或namespace检查均exit0。共存、target、emit日志均为空，无错误或警告。完整source检查覆盖23条，正式模块owner检查覆盖23条，名称/种类/签名类型/传递公理逐项相等；导入后两个私有名的显示头部增加†标记，完整私有名及类型正文均相同。

实际12条公开定理、1条公开定义、2条显式私有定理、8条自动生成声明；全35模块owner或namespace并集670条。所有被审计的传递公理均属于propext、Classical.choice、Quot.sound。源码禁止标记扫描无匹配。

前后指纹验证：旧OQ4 34源、Basic/Probability 32源、其他非OQ4 56源及root/version 4文件均完全不变；OQ4源码集合只新增本模块成为35。源码为UTF8无BOM、纯LF、恰好一个末LF。

完整义务包含实际Measure.pi/withDensity指数密度、反向权重真正可积、精确反向身份、有限夹界、真实iid积分拉回及μ/μ_t两侧概率桥。量词保留n=0与任意实t，同一个弱闭事件、原子与零生存概率；不除生存质量，不加中心/三阶矩/原指数矩等前提。

这是作者检查收据，独立正式审核待完成；不自称独立认证，不关闭相对渐近、共同二维算子、E4/K/Kv/随机分母或完整E3/OQ4。详细命令、实际SHA、全部声明和传递公理见summary.json/declarations.md。rawlogs/binaries只在服务器本单元repro_outputs目录；作者未改公共/root/cache或旧源码。
