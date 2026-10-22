# EnergyPathLaw 证明发布副本字节对应核验

STATUS: CORRECT
SCOPE: FORMAT_EQUIVALENCE_ONLY
REVIEW_DATE: 2026-10-22

本补记独立确认：指定发布副本逐字节等于冻结原证明后附加且仅附加一个 LF 字节（十进制 10）。没有改动原证明的任何既有字节；数学内容、Lean 源码及原认证均未改变。本补记只证明发布字节对应，不是新的数学或 Lean 复审。

## 原稿与发布副本

| 实际核验文件 | 字节数 | SHA256 |
|---|---:|---|
| `drafts/oq4/energy-path-law/proof.md` | 15016 | `6262f545ddd10fe868db3386b426d417cb53940fc1e3ab55375f79147dafc601` |
| `drafts/oq4/energy-path-law-proof-published.md` | 15017 | `0ad918d0519d025b02a73fce77171c7f04d69324f76c0db66f8837b69ba18c76` |

独立比较结果：

- 发布副本的前 15016 字节与原稿全部字节逐项相同；最后且唯一新增的字节为 LF。因此 `old + b'\n' == new`。
- 从发布副本删除最后一个 LF 后，恢复字节的 SHA256 为 `6262f545ddd10fe868db3386b426d417cb53940fc1e3ab55375f79147dafc601`，与冻结原稿完全相同。
- 两文件均通过严格 UTF-8 解码，均无 BOM、无 CR。原稿有 357 个 LF，末尾 LF 数为 0；发布副本有 358 个 LF，末尾连续 LF 数恰为 1。

读取的对应记录是 `drafts/oq4/energy-path-law-proof-format-receipt.json`，SHA256 为 `c829a0c973675faf407adcb3e126f719ca9c9f33f66a45359b053bf7fabf068c`。记录中的原稿、发布稿字节数、完整 SHA256、追加操作及反向核验描述均与独立结果一致。其 `docs/oq4-energy-path-law-proof.md` 是发布目标映射；本次实际读取和比较的是上表 drafts 发布副本。

## 冻结认证与源码保持原指纹

本轮仅以字节数和完整 SHA256 核对以下文件，没有修改其内容：

| 文件 | 字节数 | SHA256 |
|---|---:|---|
| `drafts/oq4/review/energy-path-law-math-review-v1.md` | 11115 | `5d16459c67934758ffb5c54d2dae3c6998fe68d1cced9b8555087712e9c98894` |
| `drafts/oq4/review/energy-path-law-formal-review-v1.md` | 20378 | `7b72f6ba3838dc9ef3bcbc152b9db6d414c574a9ad69539cbb90207fc953590f` |
| `drafts/oq4/energy-path-law/EnergyPathLaw.lean` | 15246 | `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536` |

原冻结证明依旧绑定 `6262f545ddd10fe868db3386b426d417cb53940fc1e3ab55375f79147dafc601`；发布副本另绑定 `0ad918d0519d025b02a73fce77171c7f04d69324f76c0db66f8837b69ba18c76`。不能把原审稿票写成曾审过不同字节的文件，也不需要重写原票；本补记提供二者之间经过独立核验的唯一末尾 LF 对应。

本轮没有调用服务器、Lean、数学重计算、Git、安装或缓存操作。只新增本补记，原证明、原两票和 Lean 源均保持原样。本报告按 UTF-8 无 BOM、LF 换行、恰一个末尾 LF 写入，其独立指纹另行报告。
