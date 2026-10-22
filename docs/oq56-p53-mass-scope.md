# P53 稀疏质量与极限的范围

给定同一个稀疏子列 N，SparseMass 定义标签权重 m、完整高层质量 H 和过去层质量 b，证明权重非负且 HasSum m 1。零层保存剩余质量；正层的 b=1−H 与两条完整高层费用估计为后续背景事件提供数值输入。

SparseMassLimits 证明 H→0、b→1，以及同一 SparseSelectionCore 下 N_j H_j→0 和 b_j^[2*(N_j−2)]→1。前两条不增加 α、x 或 N 的条件；后两条使用同一给定 N，自然数减法与指数保持原式。

两个模块共有21条公开定理和3个公开定义，依赖已接受的 SparseScales、SparseSelection。新声明没有按合取分项重复计数。

后续 SparseLabelLaw 将把 b、H 与真实事件概率连接，再把数值极限送到概率侧。实际概率律、全矩与指数预算、真实条件统计量和最终 P53/OQ6/RS2 结论仍需后续工作。P52 已在根 v33 关闭。
