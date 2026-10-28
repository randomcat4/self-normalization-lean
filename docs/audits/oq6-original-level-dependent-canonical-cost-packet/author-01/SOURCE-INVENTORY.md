# 第255单元完整源码局部库存

源码库存不是实际 machine owner / PP 结果。全部完整类型、右端和词法范围按精确当前源列出。

## let g — 第28–28行

UTF8字节[938,992)；片段SHA256 `0b29afa0641c31a76d56ea7620b22e7e753f0de54bf1235c79b167cfc9f10fac`。

完整类型：
```lean
Ω → ℝ
```

完整右端：
```lean
fun o => ∫ y, h o y ∂μ
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let r — 第29–29行

UTF8字节[992,1054)；片段SHA256 `b00240cd6a8bccd8321e184bdc42ef18984f8c7a799e7ae9214f181724e6c6b3`。

完整类型：
```lean
Ω → Ω → ℝ
```

完整右端：
```lean
fun o y => h o y - g o - g y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let v — 第30–31行

UTF8字节[1054,1150)；片段SHA256 `8f1543d4fcfceb0a51be2a06227df5a4b6bac7ca15875ff960abae05b1666ba6`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let rho — 第32–32行

UTF8字节[1150,1183)；片段SHA256 `5c95fef094d0338a5f5278b5385a23d1fce35c2de712e5c818838bc8d3317cde`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
Real.sqrt v
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let μ₀ — 第35–35行

UTF8字节[1303,1355)；片段SHA256 `382ffd6eb5df95b91fe1e09e78d1467734957ec1d393f4b91e188f4d488f2b59`。

完整类型：
```lean
@Measure Ω m₀
```

完整右端：
```lean
μ.trim hm₀
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@36 — 第36–36行

UTF8字节[1355,1395)；片段SHA256 `e6caeaa4d46b95650091781ec0d6b9449555d04de2c9e6aa0bfaee571d026a21`。

完整类型：
```lean
MeasurableSpace Ω
```

完整右端：
```lean
m₀
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@37 — 第37–37行

UTF8字节[1395,1453)；片段SHA256 `15d62b299395cc4740687f5e76b362ae86716ed7c047fd7093f0c1fb59a8c614`。

完整类型：
```lean
MeasurableSpace.CountablyGenerated Ω
```

完整右端：
```lean
hcg
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## let mN — 第44–45行

UTF8字节[1735,1869)；片段SHA256 `1532a3bc286aae308ba27844872b6310d692746210bb169cabd2c3ffa7fd55e5`。

完整类型：
```lean
MeasurableSpace (Fin n → Ω)
```

完整右端：
```lean
@MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let mN₀ — 第46–47行

UTF8字节[1869,2007)；片段SHA256 `cf58a17ac398370e8c2fca3e20a7162679e162c6434aa1dfcbc056d541504c45`。

完整类型：
```lean
MeasurableSpace (Fin n → Ω)
```

完整右端：
```lean
@MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let P — 第48–50行

UTF8字节[2007,2196)；片段SHA256 `123aaace5a6a051ca65b63bd0eb407238c734f467813796e65315caa65fcc30f`。

完整类型：
```lean
@Measure (Fin n → Ω) mN
```

完整右端：
```lean
@Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let P₀ — 第51–53行

UTF8字节[2196,2395)；片段SHA256 `96a0091eb4cd240e26a92b9fd257913d3b4b6b0d12cd0142fe939b6b9152581c`。

完整类型：
```lean
@Measure (Fin n → Ω) mN₀
```

完整右端：
```lean
@Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let N — 第54–54行

UTF8字节[2395,2438)；片段SHA256 `b0dd346585e535f381697477059a9d1dd69a797b6e326f859d60da28400cb8d5`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
Real.sqrt (n : ℝ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let O — 第55–55行

UTF8字节[2438,2506)；片段SHA256 `6e2f89042a775a10443dd30e93e209855cf0c2314d3e45219f2cd0a7604d3d78`。

完整类型：
```lean
Fin n → (Fin n → Ω) → Ω
```

完整右端：
```lean
fun i ξ => ξ i
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let gcoord — 第56–56行

UTF8字节[2506,2570)；片段SHA256 `df7ef07ae8798a838c8cf315777491947c8652afb261238b41fd96b21277bb57`。

完整类型：
```lean
Fin n → Ω → ℝ
```

完整右端：
```lean
fun _ o => g o / N
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Q — 第57–57行

UTF8字节[2570,2642)；片段SHA256 `34d0560698e04d9bf231875721b57485e80107fb08bbf9ae67cb1e52369abd67`。

完整类型：
```lean
(Fin n → Ω) → (Fin n → Ω)
```

完整右端：
```lean
fun ξ i => O i ξ
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let D1 — 第58–58行

UTF8字节[2642,2708)；片段SHA256 `9c7b6592987c974bc1511c709091eafae438acf7f30f9a750c350c4fe538ab83`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
residualStatisticD n r
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let D2 — 第59–59行

UTF8字节[2708,2788)；片段SHA256 `bd2d76f4bd9534628a22c2e37b9fcea25a01626ea101066a860405f7e70775ba`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
clippedCenteredDelta n g r 512 rho y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Tclip — 第60–60行

UTF8字节[2788,2875)；片段SHA256 `cca32d97948da19d9f4605b8c39dff3d557285d4e2047482e1cd0d35633f925c`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
clippedCenteredStatistic n g r 512 rho y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Ddel — 第61–61行

UTF8字节[2875,2960)；片段SHA256 `a8bede803609bdbc764a9a8a1fb1385319c461c39adced7e13de60e8573ca94b`。

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端：
```lean
residualStatisticDDeleted n r
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Jdel — 第62–62行

UTF8字节[2960,3042)；片段SHA256 `518b590ccee383eb179c7a6611ee3e0a8e42031339a0293270e86d9256a27021`。

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端：
```lean
residualEnergyJDeleted n r
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Bdelete — 第63–63行

UTF8字节[3042,3143)；片段SHA256 `a0d47872a6e2c1c0bd6e5613436458a03f64d5c3fb164c74634062867be543df`。

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端：
```lean
studentizerClipBudgetDeleted n r 512 rho y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let κ — 第64–64行

UTF8字节[3143,3197)；片段SHA256 `558fd727fae98a6a22827f77044b2d995cf17ca898d99ae747d919fbbb9adfed`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
fun _ => 0
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let W0 — 第65–65行

UTF8字节[3197,3283)；片段SHA256 `678e6c91872782281cf2303d52f52b0e1c0a649432bdfeefa9fcbc02b9734f55`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let V0 — 第66–67行

UTF8字节[3283,3397)；片段SHA256 `11884c30f2d34d383f2f1e41093b723bd5a76989ace1e0ebf2ad301b1ea1e41c`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let T0 — 第68–70行

UTF8字节[3397,3559)；片段SHA256 `84af2cc8f09d9756ceef25fd6e3c39a2b0e6b60916adbfea5566ba7a76ecf92e`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
fun ξ =>
          if V0 ξ = 0 then κ ξ else
            (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let lambda01 — 第71–71行

UTF8字节[3559,3651)；片段SHA256 `3d231e4a032ab86a8d752417d4815d8a6140076abc2f24a447da664761f17df1`。

完整类型：
```lean
Measure ℝ
```

完整右端：
```lean
(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let mAugLocal — 第72–72行

UTF8字节[3651,3728)；片段SHA256 `25f35add49e8e861a5ea07efc4efa94380acaa28e0e8f2e8cc22adb712e717a3`。

完整类型：
```lean
MeasurableSpace (Ω × ℝ)
```

完整右端：
```lean
m₀.prod (borel ℝ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let mAug — 第73–75行

UTF8字节[3728,3896)；片段SHA256 `484a35d08f6969d5a9af3558338dc1b2de8eae3051239522b8dff7a063b0469a`。

完整类型：
```lean
MeasurableSpace (Fin n → Ω × ℝ)
```

完整右端：
```lean
@MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let νlocal — 第76–77行

UTF8字节[3896,4034)；片段SHA256 `c9bc877c85ade197529a62181e31b5d6d2abea5e84a1b1def0e587e756bad5f8`。

完整类型：
```lean
Fin n → @Measure (Ω × ℝ) mAugLocal
```

完整右端：
```lean
fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ν — 第78–81行

UTF8字节[4034,4244)；片段SHA256 `9eddfa74d662e3cdbb5ccd986564ac290b098c5a3d9f54e1e4bfdf60f1d2e71d`。

完整类型：
```lean
@Measure (Fin n → Ω × ℝ) mAug
```

完整右端：
```lean
@Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mAugLocal) νlocal
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let q — 第82–82行

UTF8字节[4244,4323)；片段SHA256 `9d234e9b45d6e75c75659651922b35eba26057aace025c0a38d1b03fdb684673`。

完整类型：
```lean
(Fin n → Ω × ℝ) → (Fin n → Ω)
```

完整右端：
```lean
fun x i => (x i).1
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let c — 第83–85行

UTF8字节[4323,4510)；片段SHA256 `9f67e68f78e48c02aaaac71f14d6907a3c0f7c8cc5747c656a6c46bffcbf867a`。

完整类型：
```lean
Fin n → (Ω × ℝ) → ℝ
```

完整右端：
```lean
fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ξlocal — 第86–86行

UTF8字节[4510,4589)；片段SHA256 `512ddc7342bc73a0c95b734cb0fded1efbc5da6b235a162ce0bedbfe97d4a2e1`。

完整类型：
```lean
Fin n → (Ω × ℝ) → ℝ
```

完整右端：
```lean
fun i t => gcoord i t.1
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Ylocal — 第87–88行

UTF8字节[4589,4740)；片段SHA256 `3b7d80fefde4a19fca531f1db7d112a2094671921f243e07ab3f68731a9f268c`。

完整类型：
```lean
Fin n → (Ω × ℝ) → ℝ
```

完整右端：
```lean
fun i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ξ — 第89–89行

UTF8字节[4740,4828)；片段SHA256 `b11381ae31fbcbbf3069ec2ed9808975691d877dc61bd27c3b6619d02f2d57cb`。

完整类型：
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun i x => gcoord i (x i).1
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Y — 第90–90行

UTF8字节[4828,4913)；片段SHA256 `f150aa3a04f926f084102738abd1bfb0a49a3c168f3d40b02740e03cd060cc78`。

完整类型：
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun i x => Ylocal i (x i)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let a — 第91–91行

UTF8字节[4913,5007)；片段SHA256 `46759722f24b03abc7ba54ac0d4d20b708d2c9f93201f4a5d07d658aa16d7530`。

完整类型：
```lean
Fin n → ℝ
```

完整右端：
```lean
Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let s — 第92–92行

UTF8字节[5007,5095)；片段SHA256 `475acb50540db8f7fe07fc7787598bd06db120dc988efc36bc1f9ee0644e4db4`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ηlocal — 第93–94行

UTF8字节[5095,5255)；片段SHA256 `0b2391d1738564ef3f9e388492c00388454f9218c8cb1be512c97c06a6d501cd`。

完整类型：
```lean
Fin n → (Ω × ℝ) → ℝ
```

完整右端：
```lean
fun i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let η — 第95–96行

UTF8字节[5255,5388)；片段SHA256 `20b4846e54c733e1ba3288a32a5fa63cdaffedd3f38c455bf64e591e0de99573`。

完整类型：
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let C — 第97–97行

UTF8字节[5388,5467)；片段SHA256 `c3b960cee32d46549999cd53aab9575b211e5c99d81deb9433621877aebd0618`。

完整类型：
```lean
(Fin n → Ω × ℝ) → (Fin n → ℝ)
```

完整右端：
```lean
fun x i => η i x
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let W — 第98–98行

UTF8字节[5467,5547)；片段SHA256 `2ad338a6ce1f89b3df11a3729188a270483e6eb1e1296933be2974efc89ab3ed`。

完整类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun x => ∑ i : Fin n, ξ i x
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let V — 第99–99行

UTF8字节[5547,5645)；片段SHA256 `4e4dbf53a720ae51eeb0e08f59f96929054890c4139571c1c4f4db5931e85c9d`。

完整类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Wη — 第100–100行

UTF8字节[5645,5727)；片段SHA256 `10df7570c5d7d58a40b4d9be72a645adb4f7ceb54ae0f2f10ac3b4e95e598f14`。

完整类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun x => ∑ i : Fin n, η i x
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Vη — 第101–101行

UTF8字节[5727,5827)；片段SHA256 `8652cb426d9863afe552a9594428e06039082b7048acb645ede2f1e63ec8e279`。

完整类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let b — 第102–102行

UTF8字节[5827,5910)；片段SHA256 `a92be81d27643ac8e65b60923b8188a3c769668be0b5c73afbd640b815e8fca9`。

完整类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun x => Real.sqrt (1 + D2 (q x))
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Dη — 第103–104行

UTF8字节[5910,6039)；片段SHA256 `8b15bc1ce889601d9b4a4c84ff505ed681c1c3e25cf3ed1660ff77f49ba08431`。

完整类型：
```lean
ℝ → (Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Tη — 第105–106行

UTF8字节[6039,6153)；片段SHA256 `7241ba08730002cfa96708ef516ec666ea428355389aab10d617255e9dd546c9`。

完整类型：
```lean
ℝ → (Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun z x => (Wη x + Dη z x) / (Vη x * b x)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Z0 — 第107–107行

UTF8字节[6153,6222)；片段SHA256 `3b7b467f5e1c0c0c9006515ff40ade18e52257d366ee32f229a4aaa22b6b4bcf`。

完整类型：
```lean
Set (Fin n → Ω)
```

完整右端：
```lean
{ξ | projectionV n g ξ = 0}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Z — 第108–108行

UTF8字节[6222,6281)；片段SHA256 `89c1ae14326b0524482b3180bbea82ec0e025d19f4b3de699599224fae255e0e`。

完整类型：
```lean
Set (Fin n → Ω × ℝ)
```

完整右端：
```lean
{x | V x = 0}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let p0 — 第109–109行

UTF8字节[6281,6315)；片段SHA256 `b44df8e4c95d6f20a3cd2b996a894400a0ebab066bee9adf2ac1c60952dc96a7`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
P.real Z0
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let comparisons — 第110–113行

UTF8字节[6315,6576)；片段SHA256 `2e09c765bced4ee76b39ecc364c96dab4fc9e400ab57554bcbef4b343a829272`。

完整类型：
```lean
Set (ℝ → ℝ → Prop)
```

完整右端：
```lean
{R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
            R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
            R = (fun a b : ℝ => a = b)}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let F0 — 第114–116行

UTF8字节[6576,6770)；片段SHA256 `79bae7d935044280de67150c9b879de225625d7a0c3c212b4d8c1a942cd14080`。

完整类型：
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω)
```

完整右端：
```lean
fun R z =>
          {ξ | R (projectionW n g ξ + D1 ξ)
            (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let A0 — 第117–118行

UTF8字节[6770,6887)；片段SHA256 `1466b5f547c9e987730392f64e690d58bed1bc5aeddd5fbeab97da6468f6ebe6`。

完整类型：
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω)
```

完整右端：
```lean
fun R z => {ξ | R (Tclip ξ) z}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Eη — 第119–120行

UTF8字节[6887,7010)；片段SHA256 `44357b805401be9a1668e5d7c30a97990c7edcd0719bb6e4c6ebe677f4d09a11`。

完整类型：
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ)
```

完整右端：
```lean
fun R z => {x | R (Tη z x) z}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let J — 第121–121行

UTF8字节[7010,7072)；片段SHA256 `b74432b5ce335159f03eecaedf725a0e58256aec1fbb03666aa9c18122b1c8e1`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
residualEnergyJ n r
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let A — 第122–122行

UTF8字节[7072,7147)；片段SHA256 `504889964f159f157fb58b002d036a276b05aee8200b0a83dc25b707202a2a5b`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
fun ξ : Fin n → Ω => |D1 ξ|
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Adel — 第123–124行

UTF8字节[7147,7263)；片段SHA256 `59aefeb7e4c52f34d2d0120b26121df2d4a54b26407594319d16e3dab41a68a2`。

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端：
```lean
fun (ξ : Fin n → Ω) (i : Fin n) => |Ddel ξ i|
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let B — 第125–125行

UTF8字节[7263,7341)；片段SHA256 `907d38179cb4907c3ba322fe86fb734c9373701dc6e6842c20d10d8098e4d8d6`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
studentizerClipBudget n r 512 rho y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let deletionMass — 第126–128行

UTF8字节[7341,7508)；片段SHA256 `df0e056c02a5082e9131a7e254a6c6279ce79266bf92c926beaeeebfbe71f53a`。

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端：
```lean
fun (ξ : Fin n → Ω) (i : Fin n) =>
            |A ξ - Adel ξ i| + |B ξ - Bdelete ξ i|
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let deletionTotal — 第129–130行

UTF8字节[7508,7630)；片段SHA256 `3f61de70cd3b58c3bbc39ea3a1beee1aaabbd9b611f895e66a06dac69735f4f9`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
fun ξ : Fin n → Ω => ∑ i : Fin n, deletionMass ξ i
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ξ0 — 第131–131行

UTF8字节[7630,7714)；片段SHA256 `29ab51a386b2b791a3fa3752231f2278792bf098aaf30f1b20896a2194b00935`。

完整类型：
```lean
Fin n → (Fin n → Ω) → ℝ
```

完整右端：
```lean
fun i ζ => gcoord i (O i ζ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let S0 — 第132–133行

UTF8字节[7714,7832)；片段SHA256 `4927db54f9bb253628fef65081422d11f9eee9366ab19015f00e693decebf684`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
fun ζ =>
          ∑ j : Fin n, (y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let S0delete — 第134–135行

UTF8字节[7832,7984)；片段SHA256 `0697f1d828bda9a37356075343805fdb3025151cae670dcb757b7075646fe2fb`。

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端：
```lean
fun ζ i =>
          ∑ j ∈ Finset.univ.erase i, (y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Sν — 第136–137行

UTF8字节[7984,8105)；片段SHA256 `1300974446fbd6a1261d0795b4b47119dfbe039b2f744b3232a52cf3c1438a14`。

完整类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun x =>
          ∑ j : Fin n, (y * ξ j x - (y * ξ j x) ^ 2 / 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Sνdelete — 第138–139行

UTF8字节[8105,8260)；片段SHA256 `b8f6404142df5dd8cd5a6b269525b69fb505527ddf5d0a1fcf132acf60b57510`。

完整类型：
```lean
(Fin n → Ω × ℝ) → Fin n → ℝ
```

完整右端：
```lean
fun x i =>
          ∑ j ∈ Finset.univ.erase i, (y * ξ j x - (y * ξ j x) ^ 2 / 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let fullTest0 — 第140–140行

UTF8字节[8260,8344)；片段SHA256 `4629dbb29b8f1a5e15b4e24f821ba16495b79884207eca58cb5e75b9c0d289c2`。

完整类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端：
```lean
fun ζ => y * A ζ + y ^ 2 * B ζ
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let deleteTest0 — 第141–142行

UTF8字节[8344,8500)；片段SHA256 `d22d265067a7a4302d7ca61f80698606cb64cb3baced3ee75cd1eafdf5a97b64`。

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端：
```lean
fun ζ i =>
          min |y * ξ0 i ζ| 1 * (|A ζ - Adel ζ i| + y * |B ζ - Bdelete ζ i|)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let fullTestν — 第143–143行

UTF8字节[8500,8583)；片段SHA256 `b0fa29a9fbe1a25e52a6670825ee5510f5a255668ccb1836968642ac81253ba9`。

完整类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端：
```lean
fun x => fullTest0 (q x)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let deleteTestν — 第144–144行

UTF8字节[8583,8684)；片段SHA256 `2b0a64fcbfe015fa9a87d428dde6a661d18b5706fea25d36e19b26feb9736590`。

完整类型：
```lean
(Fin n → Ω × ℝ) → Fin n → ℝ
```

完整右端：
```lean
fun x i => deleteTest0 (q x) i
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Ioriginal — 第145–145行

UTF8字节[8684,8760)；片段SHA256 `1230ef0bbd2c1a0ec356f432e967ad7b6471c9943613af1746b669827a74ba5f`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
∫ ζ : Fin n → Ω, Real.exp (S0 ζ) ∂P
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Ireduced — 第146–146行

UTF8字节[8760,8838)；片段SHA256 `8cedf9a178e6f54a2cce00fb7dad5e95ccf08af299e446dae9ced222800b8c8a`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
∫ ζ : Fin n → Ω, Real.exp (S0 ζ) ∂P₀
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Icoded — 第147–147行

UTF8字节[8838,8918)；片段SHA256 `498781d10d8d15d88e001430bd4606f984489c19c15d988e49170b575b246867`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
∫ x : Fin n → Ω × ℝ, Real.exp (Sν x) ∂ν
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let costOriginal — 第148–150行

UTF8字节[8918,9109)；片段SHA256 `7be9b04410bcf995e28d0709e7712d13426da6dbc4962e5922ea672c3b6e0108`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P) +
            ∑ i : Fin n, ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P) / Ioriginal
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let costReduced — 第151–153行

UTF8字节[9109,9304)；片段SHA256 `43171b3582e625418fdd128e5513e7c289d88bee17846ceff6a8cafc5db64fdc`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
((∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) +
            ∑ i : Fin n, ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) / Ireduced
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let costCoded — 第154–156行

UTF8字节[9304,9489)；片段SHA256 `020490f9f83010694d58a8d452aaea46e939f54560ef3f4792277f9608f31510`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
((∫ x, fullTestν x * Real.exp (Sν x) ∂ν) +
            ∑ i : Fin n, ∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) / Icoded
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 18, "visibleThroughLine": 293, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## have hcanonical — 第297–299行

UTF8字节[18685,18868)；片段SHA256 `d8204f233ac59fdd69e3ba632f26dd30cc73a42aa9e06f1a907f47b775d6077d`。

完整类型：
```lean
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ :=
      ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ)
        (hcg : @MeasurableSpace.CountablyGenerated Ω m₀),
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      letI : MeasurableSpace.CountablyGenerated Ω := hcg
      IsProbabilityMeasure μ₀ ∧
      ∀ (n : ℕ) (hn : 4 ≤ n)
          (y : ℝ) (hy : 1 ≤ y)
          (hywindow : y ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ)))
          (ε : ℝ) (hε : 0 < ε)
          (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ))),
        let mN : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
        let mN₀ : MeasurableSpace (Fin n → Ω) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
        let P : @Measure (Fin n → Ω) mN :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
        let P₀ : @Measure (Fin n → Ω) mN₀ :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
        let N : ℝ := Real.sqrt (n : ℝ)
        let O : Fin n → (Fin n → Ω) → Ω := fun i ξ => ξ i
        let gcoord : Fin n → Ω → ℝ := fun _ o => g o / N
        let Q : (Fin n → Ω) → (Fin n → Ω) := fun ξ i => O i ξ
        let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
        let D2 : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho y
        let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho y
        let Ddel : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
        let Jdel : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
        let Bdelete : (Fin n → Ω) → Fin n → ℝ := studentizerClipBudgetDeleted n r 512 rho y
        let κ : (Fin n → Ω) → ℝ := fun _ => 0
        let W0 : (Fin n → Ω) → ℝ := fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
        let V0 : (Fin n → Ω) → ℝ :=
          fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
        let T0 : (Fin n → Ω) → ℝ := fun ξ =>
          if V0 ξ = 0 then κ ξ else
            (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
        let lambda01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
        let mAugLocal : MeasurableSpace (Ω × ℝ) := m₀.prod (borel ℝ)
        let mAug : MeasurableSpace (Fin n → Ω × ℝ) :=
          @MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
        let νlocal : Fin n → @Measure (Ω × ℝ) mAugLocal :=
          fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
        let ν : @Measure (Fin n → Ω × ℝ) mAug :=
          @Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mAugLocal) νlocal
        let q : (Fin n → Ω × ℝ) → (Fin n → Ω) := fun x i => (x i).1
        let c : Fin n → (Ω × ℝ) → ℝ := fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
        let ξlocal : Fin n → (Ω × ℝ) → ℝ := fun i t => gcoord i t.1
        let Ylocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
        let ξ : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => gcoord i (x i).1
        let Y : Fin n → (Fin n → Ω × ℝ) → ℝ := fun i x => Ylocal i (x i)
        let a : Fin n → ℝ := Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
        let s : ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
        let ηlocal : Fin n → (Ω × ℝ) → ℝ := fun i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
        let η : Fin n → (Fin n → Ω × ℝ) → ℝ :=
          Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
        let C : (Fin n → Ω × ℝ) → (Fin n → ℝ) := fun x i => η i x
        let W : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, ξ i x
        let V : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
        let Wη : (Fin n → Ω × ℝ) → ℝ := fun x => ∑ i : Fin n, η i x
        let Vη : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
        let b : (Fin n → Ω × ℝ) → ℝ := fun x => Real.sqrt (1 + D2 (q x))
        let Dη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
        let Tη : ℝ → (Fin n → Ω × ℝ) → ℝ :=
          fun z x => (Wη x + Dη z x) / (Vη x * b x)
        let Z0 : Set (Fin n → Ω) := {ξ | projectionV n g ξ = 0}
        let Z : Set (Fin n → Ω × ℝ) := {x | V x = 0}
        let p0 : ℝ := P.real Z0
        let comparisons : Set (ℝ → ℝ → Prop) :=
          {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
            R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
            R = (fun a b : ℝ => a = b)}
        let F0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) := fun R z =>
          {ξ | R (projectionW n g ξ + D1 ξ)
            (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
        let A0 : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω) :=
          fun R z => {ξ | R (Tclip ξ) z}
        let Eη : (ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ) :=
          fun R z => {x | R (Tη z x) z}
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
        (∀ i : Fin n, Measurable (O i) ∧ MeasurePreserving (O i) P₀ μ₀) ∧
        iIndepFun O P₀ ∧
        (∀ i : Fin n, Measurable (gcoord i) ∧
          MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ ∧
          (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 ∧
          (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ)) ∧
        (∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 ∧
        Q = id ∧ W0 = projectionW n g ∧ V0 = projectionV n g ∧ T0 = Tclip ∧
        Measurable D1 ∧ Measurable D2 ∧
        (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ) ∧
        Measurable[mN₀, borel ℝ] Tclip ∧ Measurable[mN, borel ℝ] Tclip ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P ∧
        IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        (1 / 2 : ℝ) < s ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i)) ∧
        iIndepFun η ν ∧
        (∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν) ∧
        (∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν) ∧
        (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
        (∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0) ∧
        ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x) ∧
        Measurable[mAug, borel (Fin n → ℝ)] C ∧
        MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug ∧
        (∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
          ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
            ∀ x : Fin n → Ω × ℝ, H x = F (C x)) ∧
        (∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
          ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
            (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
              d y = F (fun j => ηlocal j.val (y j))) ∧
            Measurable[borel (Fin n → ℝ), borel ℝ]
              (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
            ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x)) ∧
        (∃ G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
          ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
            ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x)) ∧
        (∀ i : Fin n,
          ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
            ∀ x : Fin n → Ω × ℝ,
              (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) =
                Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
        (∀ z : ℝ, Measurable (Dη z) ∧ Measurable (Tη z)) ∧
        MeasurableSet[mN₀] Z0 ∧ MeasurableSet[mN] Z0 ∧ MeasurableSet Z ∧
        ν Z = P₀ Z0 ∧ P₀ Z0 = P Z0 ∧ ν.real Z = p0 ∧
        (∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x) ∧
        (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
          MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN] (A0 R z) ∧
          MeasurableSet[mN₀] (F0 R z) ∧ MeasurableSet[mN] (F0 R z) ∧
          MeasurableSet (Eη R z) ∧
          ν (Eη R z) = P₀ (F0 R z) ∧ P₀ (F0 R z) = P (F0 R z) ∧
          (∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
          P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
          |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0)
```

完整右端：
```lean
Shao.OQ6.OriginalLevelDependentCanonicalCoding.actual_original_level_dependent_canonical_normalized_coding
      μ h hh hh2 hhsymm hcenter hprojectionsecond
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@304 — 第304–304行

UTF8字节[19000,19036)；片段SHA256 `464b3d02d8b2a7fbe3f50fc1d25c9e40caceacda2b19bd28cee0724c717cbb56`。

完整类型：
```lean
MeasurableSpace Ω
```

完整右端：
```lean
m₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@305 — 第305–305行

UTF8字节[19036,19090)；片段SHA256 `d7f0d85fc211d84c49f0e7f15afda86e4d0ccbcb7fd99b5f2468c1d34abf5bce`。

完整类型：
```lean
MeasurableSpace.CountablyGenerated Ω
```

完整右端：
```lean
hcg
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hcan — 第315–315行

UTF8字节[19608,19663)；片段SHA256 `9b7d2cec386580f382479c79d78449d5387270646655dbac1d0b07b2a3e831ac`。

完整类型：
```lean
        @IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
        P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
        (∀ i : Fin n, Measurable (O i) ∧ MeasurePreserving (O i) P₀ μ₀) ∧
        iIndepFun O P₀ ∧
        (∀ i : Fin n, Measurable (gcoord i) ∧
          MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀ ∧
          (∫ ξ, gcoord i (O i ξ) ∂P₀) = 0 ∧
          (∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ)) ∧
        (∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 ∧
        Q = id ∧ W0 = projectionW n g ∧ V0 = projectionV n g ∧ T0 = Tclip ∧
        Measurable D1 ∧ Measurable D2 ∧
        (∀ ξ : Fin n → Ω, (1 / 2 : ℝ) ≤ 1 + D2 ξ) ∧
        Measurable[mN₀, borel ℝ] Tclip ∧ Measurable[mN, borel ℝ] Tclip ∧
        @Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
          @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P ∧
        IsProbabilityMeasure ν ∧ MeasurePreserving q ν P₀ ∧
        (1 / 2 : ℝ) < s ∧
        (∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i)) ∧
        iIndepFun η ν ∧
        (∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν) ∧
        (∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν) ∧
        (∀ i : Fin n, (∫ x, η i x ∂ν) = 0) ∧
        (∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1 ∧
        (∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0) ∧
        ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0 ∧
        (∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x) ∧
        Measurable[mAug, borel (Fin n → ℝ)] C ∧
        MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug ∧
        (∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
          ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
            ∀ x : Fin n → Ω × ℝ, H x = F (C x)) ∧
        (∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
          ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
            (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
              d y = F (fun j => ηlocal j.val (y j))) ∧
            Measurable[borel (Fin n → ℝ), borel ℝ]
              (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
            ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x)) ∧
        (∃ G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
          ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
            ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x)) ∧
        (∀ i : Fin n,
          ∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
            ∀ x : Fin n → Ω × ℝ,
              (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) =
                Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)) ∧
        (∀ z : ℝ, Measurable (Dη z) ∧ Measurable (Tη z)) ∧
        MeasurableSet[mN₀] Z0 ∧ MeasurableSet[mN] Z0 ∧ MeasurableSet Z ∧
        ν Z = P₀ Z0 ∧ P₀ Z0 = P Z0 ∧ ν.real Z = p0 ∧
        (∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x) ∧
        (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
          MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN] (A0 R z) ∧
          MeasurableSet[mN₀] (F0 R z) ∧ MeasurableSet[mN] (F0 R z) ∧
          MeasurableSet (Eη R z) ∧
          ν (Eη R z) = P₀ (F0 R z) ∧ P₀ (F0 R z) = P (F0 R z) ∧
          (∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
          P (A0 R z ∆ F0 R z) ≤ P Z0 ∧
          |P.real (A0 R z) - ν.real (Eη R z)| ≤ p0)
```

完整右端：
```lean
hfor n hn y hy hywindow ε hε hεsmall
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hcost — 第330–333行

UTF8字节[20422,20678)；片段SHA256 `832f20da1550fb09dc3c30dd873725126ed6ac7bc9fc212c2eaa36ba0d585b5f`。

完整类型：
```lean
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let N : ℝ := Real.sqrt (n : ℝ)
    let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
    let D : (Fin n → Ω) → ℝ := residualStatisticD n r
    let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
    let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
    let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
    let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
    let Adelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ => |Ddelete ζ i|
    let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho (y)
    let Bdelete : Fin n → (Fin n → Ω) → ℝ :=
      fun i ζ => studentizerClipBudgetDeleted n r 512 rho (y) ζ i
    let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho (y)
    let V : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (∑ j : Fin n, (ξ0 j ζ) ^ 2)
    let Vdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
      Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ0 j ζ) ^ 2)
    let H : (Fin n → Ω) → ℝ := fun ζ => (1 + V ζ) * (N + (y) * Real.sqrt (1 + B ζ))
    let Hdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
      (1 + Vdelete i ζ) * (N + (y) * Real.sqrt (1 + Bdelete i ζ))
    let M : ℝ → (Fin n → Ω) → ℝ := fun ε ζ => 4 * ε * N * H ζ
    let Mdelete : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
      4 * ε * N * Hdelete i ζ
    let κ : Fin n → ℝ := fun i =>
      4 * N * ((∫ ζ, H ζ ∂P) + (∫ ζ, Hdelete i ζ ∂P))
    let Δ : ℝ → Fin n → (Fin n → Ω) → ℝ := fun ε i ζ =>
      (A ζ + M ε ζ) - (Adelete i ζ + Mdelete ε i ζ) - (A ζ - Adelete i ζ)
    MemLp D 2 P ∧
    (∀ i : Fin n, MemLp (fun ζ => Ddelete ζ i) 2 P) ∧
    Integrable J P ∧ (∀ i : Fin n, Integrable (fun ζ => Jdelete ζ i) P) ∧
    Integrable A P ∧ (∀ i : Fin n, Integrable (Adelete i) P) ∧
    Integrable B P ∧ (∀ i : Fin n, Integrable (Bdelete i) P) ∧ Integrable e P ∧
    (∀ ζ : Fin n → Ω, 0 ≤ A ζ ∧ 0 ≤ B ζ ∧ |e ζ| ≤ B ζ) ∧
    (∀ (i : Fin n) (ζ : Fin n → Ω), 0 ≤ Adelete i ζ ∧ 0 ≤ Bdelete i ζ) ∧
    (∀ i : Fin n, Measurable (ξ0 i) ∧ MemLp (ξ0 i) 2 P ∧ (∫ ζ, ξ0 i ζ ∂P) = 0) ∧
    (∑ i : Fin n, ∫ ζ, (ξ0 i ζ) ^ 2 ∂P) = 1 ∧
    (∀ ζ : Fin n → Ω, V ζ = projectionV n g ζ) ∧
    Measurable H ∧ Integrable H P ∧
    (∀ i : Fin n, Measurable (Hdelete i) ∧ Integrable (Hdelete i) P) ∧
    (∀ ζ : Fin n → Ω, 0 < H ζ) ∧
    (∀ (i : Fin n) (ζ : Fin n → Ω), 0 < Hdelete i ζ) ∧
    (∀ ε : ℝ, Measurable (M ε) ∧ Integrable (M ε) P ∧
      Integrable (fun ζ => |M ε ζ|) P) ∧
    (∀ (ε : ℝ) (i : Fin n), Measurable (Mdelete ε i) ∧ Integrable (Mdelete ε i) P ∧
      Integrable (fun ζ => |Mdelete ε i ζ|) P) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ ζ : Fin n → Ω,
      0 ≤ M ε ζ ∧ ∀ i : Fin n, 0 ≤ Mdelete ε i ζ) ∧
    (∀ i : Fin n, 0 ≤ κ i) ∧
    (∀ (ε : ℝ) (i : Fin n),
      (∫ ζ, M ε ζ ∂P) + (∫ ζ, Mdelete ε i ζ ∂P) = ε * κ i) ∧
    (∀ (ε : ℝ) (i : Fin n),
      (∫ ζ, |M ε ζ| ∂P) + (∫ ζ, |Mdelete ε i ζ| ∂P) = |ε| * κ i) ∧
    (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
      Δ ε i ζ = M ε ζ - Mdelete ε i ζ) ∧
    (∀ (ε : ℝ) (i : Fin n) (ζ : Fin n → Ω),
      |Δ ε i ζ| ≤ |M ε ζ| + |Mdelete ε i ζ|) ∧
    (∀ (ε : ℝ) (i : Fin n), Measurable (Δ ε i) ∧ Integrable (Δ ε i) P ∧
      Integrable (fun ζ => |Δ ε i ζ|) P ∧
      (∫ ζ, |Δ ε i ζ| ∂P) ≤ |ε| * κ i) ∧
    (∀ i : Fin n, Filter.Tendsto (fun ε : ℝ => ∫ ζ, |Δ ε i ζ| ∂P)
      (nhds (0 : ℝ)) (nhds (0 : ℝ)))
```

完整右端：
```lean
@Shao.OQ6.OriginalLevelDependentCorrectionEnvelope.actual_original_level_dependent_correction_envelope
      Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy hywindow
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let τ — 第345–346行

UTF8字节[21288,21408)；片段SHA256 `84b6c819ce79a5aba225e4327fcacc7c2ea554eccf76894a3a4365be03e1a1d3`。

完整类型：
```lean
(Fin n → Ω) → (Fin n → Ω × ℝ)
```

完整右端：
```lean
fun (ζ : Fin n → Ω) (i : Fin n) => (ζ i, (1 / 2 : ℝ))
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let Rdel — 第347–348行

UTF8字节[21408,21580)；片段SHA256 `07c735399df49517b275db68168f43ad021b46731d0a7c97851bcc60f56a3a06`。

完整类型：
```lean
∀ i : Fin n, (Fin n → Ω) → ({j : Fin n // j ≠ i} → ℝ)
```

完整右端：
```lean
fun (i : Fin n) (ζ : Fin n → Ω) (j : {j : Fin n // j ≠ i}) => η j.val (τ ζ)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let K — 第349–349行

UTF8字节[21580,21617)；片段SHA256 `0d141544c27d953cade19a0972a8e116c7dd1b9791ffb7fc9320bdf7a2584e14`。

完整类型：
```lean
ℝ
```

完整右端：
```lean
N * ((n : ℝ) - 1)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let psi — 第350–353行

UTF8字节[21617,21796)；片段SHA256 `16495a51d591046b1d759db573c9cf2dc829c3e1a15708d3b954cf8e6d7f31d0`。

完整类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端：
```lean
fun (ζ : Fin n → Ω) (i : Fin n) =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun (j k : Fin n) => r (ζ j) (ζ k)) i
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hτm — 第354–357行

UTF8字节[21796,21942)；片段SHA256 `7195a21976139ad7a2667e0962be9504065fdf8471ac59e28d3f43d4f17200c0`。

完整类型：
```lean
Measurable[mN₀, mAug] τ
```

完整右端：
```lean
by
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply i).prodMk measurable_const
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hqτ — 第358–360行

UTF8字节[21942,22018)；片段SHA256 `b6d17846cba4b6dfc2fc612860bb5a99f1787cc6da4823fc1216f5bd0d2ef9fd`。

完整类型：
```lean
∀ (ζ : Fin n → Ω),
q (τ ζ) = ζ
```

完整右端：
```lean
by
    funext i
    rfl
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hTripleBorel — 第361–363行

UTF8字节[22018,22164)；片段SHA256 `3f4e2ec8987afb240654e9403f75a6f73407ebb4d33b2c0087b3c039d31a1a9f`。

完整类型：
```lean
(inferInstance : MeasurableSpace (ℝ × ℝ × ℝ)) =
        borel (ℝ × ℝ × ℝ)
```

完整右端：
```lean
BorelSpace.measurable_eq
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hDeletedMeasurable — 第364–391行

UTF8字节[22164,23623)；片段SHA256 `6e51d465121d2d659ea2f5f957d5caec4ac75a964244e029c098a3f7b3557e87`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Ddel ζ i) ∧
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Jdel ζ i) ∧
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Bdelete ζ i)
```

完整右端：
```lean
by
    rcases hdeletedFactor i with ⟨Fdel, hFdel, hFdelpoint⟩
    have hRetainedBorel :
        (inferInstance : MeasurableSpace ({j : Fin n // j ≠ i} → ℝ)) =
          borel ({j : Fin n // j ≠ i} → ℝ) := BorelSpace.measurable_eq
    have hRdel : Measurable[mN₀, borel ({j : Fin n // j ≠ i} → ℝ)] (Rdel i) := by
      rw [← hRetainedBorel]
      apply Measurable.of_eval
      intro j
      exact ((hηL2 j.val).1).comp hτm
    have hTriplePoint :
        (fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i)) =
          (fun ζ : Fin n → Ω => Fdel (Rdel i ζ)) := by
      funext ζ
      simpa only [hqτ, Rdel] using hFdelpoint (τ ζ)
    have hTriple : Measurable[mN₀, borel (ℝ × ℝ × ℝ)]
        (fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i)) := by
      rw [hTriplePoint]
      exact hFdel.comp hRdel
    have hTripleProduct :
        Measurable[mN₀, (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ))]
          (fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i)) := by
      rw [hTripleBorel]
      exact hTriple
    exact ⟨hTripleProduct.fst, hTripleProduct.snd.fst, hTripleProduct.snd.snd⟩
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hRetainedBorel — 第369–371行

UTF8字节[22500,22680)；片段SHA256 `3d417bb73132b1e2408714b8f7c603f4de3084c3155f6a2e83e48804f3fea980`。

完整类型：
```lean
(inferInstance : MeasurableSpace ({j : Fin n // j ≠ i} → ℝ)) =
          borel ({j : Fin n // j ≠ i} → ℝ)
```

完整右端：
```lean
BorelSpace.measurable_eq
```

词法范围：{"enclosing": "proof of hDeletedMeasurable", "contextFromLine": 364, "visibleThroughLine": 391, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hRdel — 第372–376行

UTF8字节[22680,22885)；片段SHA256 `ccc71aa5c883522d5e1ff7705852618f4711486b83fbc4b559f9912e779402b1`。

完整类型：
```lean
Measurable[mN₀, borel ({j : Fin n // j ≠ i} → ℝ)] (Rdel i)
```

完整右端：
```lean
by
      rw [← hRetainedBorel]
      apply Measurable.of_eval
      intro j
      exact ((hηL2 j.val).1).comp hτm
```

词法范围：{"enclosing": "proof of hDeletedMeasurable", "contextFromLine": 364, "visibleThroughLine": 391, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hTriplePoint — 第377–381行

UTF8字节[22885,23114)；片段SHA256 `0a0bd33a6b769a5f717d65c14a4807a852807e79e68a9b014c3bc32ac5ac432f`。

完整类型：
```lean
(fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i)) =
          (fun ζ : Fin n → Ω => Fdel (Rdel i ζ))
```

完整右端：
```lean
by
      funext ζ
      simpa only [hqτ, Rdel] using hFdelpoint (τ ζ)
```

词法范围：{"enclosing": "proof of hDeletedMeasurable", "contextFromLine": 364, "visibleThroughLine": 391, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hTriple — 第382–385行

UTF8字节[23114,23309)；片段SHA256 `7bd51509b0db71d116aec60666234764215053607c1d9464d816efe9cf8fc581`。

完整类型：
```lean
Measurable[mN₀, borel (ℝ × ℝ × ℝ)]
        (fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i))
```

完整右端：
```lean
by
      rw [hTriplePoint]
      exact hFdel.comp hRdel
```

词法范围：{"enclosing": "proof of hDeletedMeasurable", "contextFromLine": 364, "visibleThroughLine": 391, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hTripleProduct — 第386–390行

UTF8字节[23309,23540)；片段SHA256 `5b0664428af77808c461003869826a3c3565d844533474dc54d8952c58c31bb2`。

完整类型：
```lean
Measurable[mN₀, (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ))]
          (fun ζ : Fin n → Ω => (Ddel ζ i, Jdel ζ i, Bdelete ζ i))
```

完整右端：
```lean
by
      rw [hTripleBorel]
      exact hTriple
```

词法范围：{"enclosing": "proof of hDeletedMeasurable", "contextFromLine": 364, "visibleThroughLine": 391, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hrsymm — 第392–395行

UTF8字节[23623,23748)；片段SHA256 `23afb352d06ee6489f3f0f30338ef6581278eec2c362d77d7b89d466e2a7d556`。

完整类型：
```lean
∀ (o y : Ω),
r o y = r y o
```

完整右端：
```lean
by
    change h o y - g o - g y = h y o - g y - g o
    rw [hhsymm o y]
    ring
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hn4R — 第396–396行

UTF8字节[23748,23810)；片段SHA256 `ebf88b7c8930c01ed64a0b71785b92e3ca4972e4543afad2dc64bb9dd6be3668`。

完整类型：
```lean
(4 : ℝ) ≤ (n : ℝ)
```

完整右端：
```lean
by exact_mod_cast hn
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hNpos — 第397–397行

UTF8字节[23810,23876)；片段SHA256 `d9f06883ad134ed24dcee03594d8791e8904ed41ad89bde27f02b637104001b9`。

完整类型：
```lean
0 < N
```

完整右端：
```lean
Real.sqrt_pos.2 (by linarith only [hn4R])
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hKne — 第398–399行

UTF8字节[23876,23965)；片段SHA256 `9353550423ba88d52d66280f3275abedf4b2bcb7ca44351857bf91cb739e1700`。

完整类型：
```lean
K ≠ 0
```

完整右端：
```lean
by
    exact ne_of_gt (mul_pos hNpos (by linarith only [hn4R]))
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hpsiPoint — 第400–416行

UTF8字节[23965,24815)；片段SHA256 `20922596829f41d71a454ef626c13c4660148694ce6b4f840a7d0da41034aaa3`。

完整类型：
```lean
∀ (ζ : Fin n → Ω) (i : Fin n),
psi ζ i = K * (D1 ζ - Ddel ζ i)
```

完整右端：
```lean
by
    have hIncident :=
      Shao.OQ6.ResidualDeletion.unorderedPairSum_sub_eraseIncident
        (fun (j k : Fin n) => r (ζ j) (ζ k))
        (fun (j k : Fin n) => hrsymm (ζ j) (ζ k)) i
    change Shao.OQ5.P35.unorderedPairSum (fun (j k : Fin n) => r (ζ j) (ζ k)) -
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident
          (fun (j k : Fin n) => r (ζ j) (ζ k)) i) = psi ζ i at hIncident
    change psi ζ i = K *
      (Shao.OQ5.P35.unorderedPairSum (fun (j k : Fin n) => r (ζ j) (ζ k)) / K -
        Shao.OQ5.P35.unorderedPairSum
          (Shao.OQ6.ResidualDeletion.eraseIncident
            (fun (j k : Fin n) => r (ζ j) (ζ k)) i) / K)
    rw [← sub_div, hIncident]
    field_simp [hKne] <;> ring
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hIncident — 第402–405行

UTF8字节[24063,24253)；片段SHA256 `c4e72aa84cd69957bdb588bba37c66363ed84fa9603b85d3770966cfc5bcd340`。

完整类型：
```lean
Shao.OQ5.P35.unorderedPairSum (fun (j k : Fin n) => r (ζ j) (ζ k)) -
Shao.OQ5.P35.unorderedPairSum (Shao.OQ6.ResidualDeletion.eraseIncident
  (fun (j k : Fin n) => r (ζ j) (ζ k)) i) =
Shao.OQ6.ResidualDeletion.rowSum (fun (j k : Fin n) => r (ζ j) (ζ k)) i
```

完整右端：
```lean
Shao.OQ6.ResidualDeletion.unorderedPairSum_sub_eraseIncident
        (fun (j k : Fin n) => r (ζ j) (ζ k))
        (fun (j k : Fin n) => hrsymm (ζ j) (ζ k)) i
```

词法范围：{"enclosing": "proof of hpsiPoint", "contextFromLine": 400, "visibleThroughLine": 416, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hpsiMeasurable — 第417–424行

UTF8字节[24815,25169)；片段SHA256 `cd1c51a62db9626ae27f8881bc868a63f1d774064f8fa82e44b40df1570b8877`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => psi ζ i)
```

完整右端：
```lean
by
    have hEq : (fun ζ : Fin n → Ω => psi ζ i) =
        (fun ζ : Fin n → Ω => K * (D1 ζ - Ddel ζ i)) := by
      funext ζ
      exact hpsiPoint ζ i
    rw [hEq]
    exact measurable_const.mul (hD1m.sub (hDeletedMeasurable i).1)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hEq — 第419–422行

UTF8字节[24928,25089)；片段SHA256 `d6e22dfd6cec55c2afd7bd618f884830c53d5e261e310a0e588a9c222d7d7c48`。

完整类型：
```lean
(fun ζ : Fin n → Ω => psi ζ i) =
        (fun ζ : Fin n → Ω => K * (D1 ζ - Ddel ζ i))
```

完整右端：
```lean
by
      funext ζ
      exact hpsiPoint ζ i
```

词法范围：{"enclosing": "proof of hpsiMeasurable", "contextFromLine": 417, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hJm — 第425–433行

UTF8字节[25169,25598)；片段SHA256 `a02dd1fe50d27ac29b5a8f464d73cd241e584443aa6b06d5f0715c38ba987ac5`。

完整类型：
```lean
Measurable[mN₀, borel ℝ] J
```

完整右端：
```lean
by
    have hEq : J = (fun ζ : Fin n → Ω =>
        (∑ i : Fin n, (psi ζ i) ^ 2) / ((n : ℝ) - 2) ^ 2) := by
      funext ζ
      exact residualEnergyJ_eq_rowSqSum n r ζ
    rw [hEq]
    exact (Finset.measurable_sum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
        (hpsiMeasurable i).pow_const 2)).div_const (((n : ℝ) - 2) ^ 2)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hEq — 第426–429行

UTF8字节[25219,25396)；片段SHA256 `aa6324a01da6a43b8f50d1226d36cc50ffb46f64f5c56b988951e631d95dd589`。

完整类型：
```lean
J = (fun ζ : Fin n → Ω =>
        (∑ i : Fin n, (psi ζ i) ^ 2) / ((n : ℝ) - 2) ^ 2)
```

完整右端：
```lean
by
      funext ζ
      exact residualEnergyJ_eq_rowSqSum n r ζ
```

词法范围：{"enclosing": "proof of hJm", "contextFromLine": 425, "visibleThroughLine": 433, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hAm — 第434–435行

UTF8字节[25598,25698)；片段SHA256 `b48c59c1573d3c8db7a52fdff9ad80f1f25297f89ab1b4d572f626205af9cc35`。

完整类型：
```lean
Measurable[mN₀, borel ℝ] A
```

完整右端：
```lean
by
    simpa only [Real.norm_eq_abs] using hD1m.norm
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hAdelm — 第436–438行

UTF8字节[25698,25874)；片段SHA256 `d9868a98b5bf526b931b4442544fb5fcc98cc8a9e99eb243538778f208e58e00`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Adel ζ i)
```

完整右端：
```lean
by
    simpa only [Real.norm_eq_abs] using (hDeletedMeasurable i).1.norm
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hBm — 第439–443行

UTF8字节[25874,26150)；片段SHA256 `a23c660b0c69bf82baa3e945c6c249f6c6e8f148a5818338a49c6cc5c09c12a2`。

完整类型：
```lean
Measurable[mN₀, borel ℝ] B
```

完整右端：
```lean
by
    change Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω =>
      512 * (((1 + rho) * y) / N + J ζ / ((1 + rho) * y * N)))
    exact measurable_const.mul
      (measurable_const.add (hJm.div_const ((1 + rho) * y * N)))
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hBdeletem — 第444–446行

UTF8字节[26150,26290)；片段SHA256 `1f098caab58a61ebe241f30211dbb4d2f3254aafd9fd43fe97ca9ed797093a0f`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => Bdelete ζ i)
```

完整右端：
```lean
(hDeletedMeasurable i).2.2
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hidΩ — 第447–447行

UTF8字节[26290,26369)；片段SHA256 `375872846d10b1305332e8880adcbf40d1d4583bd000764ec6d144b1c5455569`。

完整类型：
```lean
Measurable[mΩ, m₀] (id : Ω → Ω)
```

完整右端：
```lean
measurable_id'' hm₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hidN — 第448–454行

UTF8字节[26369,26729)；片段SHA256 `b63a0d7d8f9d68106b666963a8bae9c6225ffc40e73226b84d47054f9ed0cc3a`。

完整类型：
```lean
Measurable[mN, mN₀] (id : (Fin n → Ω) → (Fin n → Ω))
```

完整右端：
```lean
by
    apply (@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω)
      mN (fun _ : Fin n => m₀) (id : (Fin n → Ω) → (Fin n → Ω))).2
    intro i
    exact hidΩ.comp
      (@measurable_pi_apply (Fin n) (fun _ : Fin n => Ω)
        (fun _ : Fin n => mΩ) i)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hId — 第455–457行

UTF8字节[26729,26913)；片段SHA256 `279fa5c1536d5b5aa6c28c91dd053de108c5e7677436b8d2be76e3e1fc13a831`。

完整类型：
```lean
@MeasurePreserving (Fin n → Ω) (Fin n → Ω) mN mN₀ id P P₀
```

完整右端：
```lean
@MeasurePreserving.mk (Fin n → Ω) (Fin n → Ω) mN mN₀
      id P P₀ hidN hP₀map.symm
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hAI — 第458–460行

UTF8字节[26913,27063)；片段SHA256 `ce56bc58bc496709bd254bec52931ec803b1cf5a9a087101fc6ba52c2d903b59`。

完整类型：
```lean
Integrable A P₀
```

完整右端：
```lean
by
    apply (hId.integrable_comp hAm.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hAIP
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hBI — 第461–463行

UTF8字节[27063,27213)；片段SHA256 `0bda119cf19e4fb142adc0cd447ee957f7ed7eaefef116f93604a49204bdeef8`。

完整类型：
```lean
Integrable B P₀
```

完整右端：
```lean
by
    apply (hId.integrable_comp hBm.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hBIP
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have heI — 第464–466行

UTF8字节[27213,27365)；片段SHA256 `892e15423dd0c51cbca016135cbe5b22d4699241b2fe877795d37da2eecc7434`。

完整类型：
```lean
Integrable D2 P₀
```

完整右端：
```lean
by
    apply (hId.integrable_comp hD2m.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using heIP
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hAdelI — 第467–469行

UTF8字节[27365,27577)；片段SHA256 `a854b94a4b2170ea978a0f21ed4aeb46939812c7c75f1cbe49c347ae12350706`。

完整类型：
```lean
∀ (i : Fin n),
Integrable (fun ζ : Fin n → Ω => Adel ζ i) P₀
```

完整右端：
```lean
by
    apply (hId.integrable_comp (hAdelm i).aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hAdelIP i
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hBdeleteI — 第470–472行

UTF8字节[27577,27801)；片段SHA256 `20b0ad1a2271a9b2065d20ef58baf0b15de49fcea0474ad7073ed496a40a485f`。

完整类型：
```lean
∀ (i : Fin n),
Integrable (fun ζ : Fin n → Ω => Bdelete ζ i) P₀
```

完整右端：
```lean
by
    apply (hId.integrable_comp (hBdeletem i).aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hBdeleteIP i
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hDiff — 第473–488行

UTF8字节[27801,28856)；片段SHA256 `215f24b86fc099898c7a02b53577359252f7495d00b0f395ae1f26e5c20ac2c5`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|) ∧
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|) ∧
      Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => deletionMass ζ i) ∧
      Integrable (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|) P₀ ∧
      Integrable (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|) P₀ ∧
      Integrable (fun ζ : Fin n → Ω => deletionMass ζ i) P₀
```

完整右端：
```lean
by
    have hADm : Measurable[mN₀, borel ℝ]
        (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hAm.sub (hAdelm i)).norm
    have hBDm : Measurable[mN₀, borel ℝ]
        (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hBm.sub (hBdeletem i)).norm
    exact ⟨hADm, hBDm, hADm.add hBDm,
      (hAI.sub (hAdelI i)).abs, (hBI.sub (hBdeleteI i)).abs,
      ((hAI.sub (hAdelI i)).abs).add ((hBI.sub (hBdeleteI i)).abs)⟩
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hADm — 第480–482行

UTF8字节[28305,28492)；片段SHA256 `32764fefd485ff1a1c8e8280342078707c937d7095898900e4e75b8e20c50ef3`。

完整类型：
```lean
Measurable[mN₀, borel ℝ]
        (fun ζ : Fin n → Ω => |A ζ - Adel ζ i|)
```

完整右端：
```lean
by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hAm.sub (hAdelm i)).norm
```

词法范围：{"enclosing": "proof of hDiff", "contextFromLine": 473, "visibleThroughLine": 488, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hBDm — 第483–485行

UTF8字节[28492,28685)；片段SHA256 `654606e9fbdb142240ddb8231177f5c9b1613efa4a7dcc7ff3dac21c9df86075`。

完整类型：
```lean
Measurable[mN₀, borel ℝ]
        (fun ζ : Fin n → Ω => |B ζ - Bdelete ζ i|)
```

完整右端：
```lean
by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hBm.sub (hBdeletem i)).norm
```

词法范围：{"enclosing": "proof of hDiff", "contextFromLine": 473, "visibleThroughLine": 488, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hTotalm — 第489–492行

UTF8字节[28856,29053)；片段SHA256 `4c409f0248d89a4608502d1c048eef25df1de5f7993d544bb57a8a3a710687b7`。

完整类型：
```lean
Measurable[mN₀, borel ℝ] deletionTotal
```

完整右端：
```lean
Finset.measurable_sum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
        (hDiff i).2.2.1)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hTotalI — 第493–496行

UTF8字节[29053,29240)；片段SHA256 `9aadac2c95abab1206712e72cb8a1f1603cda65e329ab0a258c3ddcdcf885190`。

完整类型：
```lean
Integrable deletionTotal P₀
```

完整右端：
```lean
integrable_finsetSum Finset.univ
      (fun (i : Fin n) (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
        (hDiff i).2.2.2.2.2)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hAugDeleted — 第497–517行

UTF8字节[29240,30647)；片段SHA256 `f5fcb6055440f710f6efd40de84a896dc84fd90836e47f7ec1b717379cf334fb`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Adel (q x) i) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => Bdelete (q x) i) ∧
      Integrable (fun x : Fin n → Ω × ℝ => Adel (q x) i) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => Bdelete (q x) i) ν ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => |B (q x) - Bdelete (q x) i|) ∧
      Measurable[mAug, borel ℝ] (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ∧
      Integrable (fun x : Fin n → Ω × ℝ => |A (q x) - Adel (q x) i|) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => |B (q x) - Bdelete (q x) i|) ν ∧
      Integrable (fun x : Fin n → Ω × ℝ => deletionMass (q x) i) ν
```

完整右端：
```lean
by
    rcases hDiff i with ⟨hADm, hBDm, hMassm, hADi, hBDi, hMassi⟩
    exact ⟨(hAdelm i).comp hqpres.measurable,
      (hBdeletem i).comp hqpres.measurable,
      hqpres.integrable_comp_of_integrable (hAdelI i),
      hqpres.integrable_comp_of_integrable (hBdeleteI i),
      hADm.comp hqpres.measurable, hBDm.comp hqpres.measurable,
      hMassm.comp hqpres.measurable,
      hqpres.integrable_comp_of_integrable hADi,
      hqpres.integrable_comp_of_integrable hBDi,
      hqpres.integrable_comp_of_integrable hMassi⟩
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hweighted — 第518–521行

UTF8字节[30647,30926)；片段SHA256 `5ac233bb6dfb4c9930d764ef10f0c9ca4f064ed6159c30db9b52863f90cee4f9`。

完整类型：
```lean
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let N : ℝ := Real.sqrt (n : ℝ)
    let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
    let D1 : (Fin n → Ω) → ℝ := residualStatisticD n r
    let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r ((512 : ℝ)) rho (y)
    let Bdelete : (Fin n → Ω) → Fin n → ℝ :=
      studentizerClipBudgetDeleted n r ((512 : ℝ)) rho (y)
    let S : (Fin n → Ω) → ℝ := fun ζ =>
      ∑ j : Fin n, ((y) * ξ0 j ζ - ((y) * ξ0 j ζ) ^ 2 / 2)
    let Sdelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, ((y) * ξ0 j ζ - ((y) * ξ0 j ζ) ^ 2 / 2)
    let fullTest : (Fin n → Ω) → ℝ := fun ζ =>
      (y) * |D1 ζ| + (y) ^ 2 * B ζ
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
      min |(y) * ξ0 i ζ| 1 *
        (|(|D1 ζ|) - (|residualStatisticDDeleted n r ζ i|)| +
          (y) * |B ζ - Bdelete ζ i|)
    let I : ℝ := ∫ ζ, Real.exp (S ζ) ∂P
    let sourceCost : ℝ :=
      ((∫ ζ, fullTest ζ * Real.exp (S ζ) ∂P) +
        ∑ i : Fin n, ∫ ζ, deletedTest ζ i * Real.exp (Sdelete ζ i) ∂P) / I
    0 < I ∧
    Integrable (fun ζ => fullTest ζ * Real.exp (S ζ)) P ∧
    (∀ i : Fin n,
      Integrable (fun ζ => deletedTest ζ i * Real.exp (Sdelete ζ i)) P) ∧
    0 ≤ sourceCost ∧
    sourceCost ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * ((512 : ℝ))) * (1 + rho) *
        (1 + (y)) ^ 3 / Real.sqrt (n : ℝ)
```

完整右端：
```lean
@Shao.OQ6.OriginalLevelDependentWeightedSourceCost.actual_original_level_dependent_weighted_source_cost
      Ω mΩ μ (inferInstance : @IsProbabilityMeasure Ω mΩ μ)
      h hh hh2 hhsymm hcenter hprojectionsecond n hn y hy hywindow 512 (by norm_num)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hξ0m — 第533–534行

UTF8字节[31531,31630)；片段SHA256 `1abcf25fb3c04feb23967020bdf94a3e033e035e9630bdca1ab23b45a23ac2f8`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ] (ξ0 i)
```

完整右端：
```lean
(hgcoord i).1.comp (hO i).1
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hphase0m — 第535–538行

UTF8字节[31630,31861)；片段SHA256 `3f3b1415704af4efebd986515a32124c700d347f7dcf840ec5d77f3d748ee235`。

完整类型：
```lean
∀ (j : Fin n),
Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => y * ξ0 j ζ - (y * ξ0 j ζ) ^ 2 / 2)
```

完整右端：
```lean
((hξ0m j).const_mul y).sub
      ((((hξ0m j).const_mul y).pow_const (2 : ℕ)).div_const 2)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hS0m — 第539–540行

UTF8字节[31861,31972)；片段SHA256 `0a3fbe5c76b2b5f1d6d0f45f265e0778a687a08ba33dfefe478ad8f40abcb68c`。

完整类型：
```lean
Measurable[mN₀, borel ℝ] S0
```

完整右端：
```lean
Finset.measurable_sum Finset.univ (fun j _ => hphase0m j)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hS0deletem — 第541–543行

UTF8字节[31972,32155)；片段SHA256 `632c0979b798830bd7ea919f177d56ff31735f58c5db8c18e9c48dcac4626014`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ] (fun ζ : Fin n → Ω => S0delete ζ i)
```

完整右端：
```lean
Finset.measurable_sum (Finset.univ.erase i) (fun j _ => hphase0m j)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hcap0m — 第544–547行

UTF8字节[32155,32368)；片段SHA256 `c0cd96e9df247b718f6a9d4b634e6d5d5a6b96b56c7718bb7e69556b2acf8738`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => min |y * ξ0 i ζ| 1)
```

完整右端：
```lean
by
    simpa only [Real.norm_eq_abs] using
      ((hξ0m i).const_mul y).norm.min measurable_const
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hFullWeightedm — 第548–550行

UTF8字节[32368,32554)；片段SHA256 `028b6cf89864875b0ad1c90fca2b5cd67b22a51e2c56b64fe0db1348daa9c7c5`。

完整类型：
```lean
Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => fullTest0 ζ * Real.exp (S0 ζ))
```

完整右端：
```lean
((hAm.const_mul y).add (hBm.const_mul (y ^ 2))).mul hS0m.exp
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hDeleteWeightedm — 第551–554行

UTF8字节[32554,32797)；片段SHA256 `dc2f6af7b77455fe407818254c2e948b7cef8b915de04de7a3d189dc08601dd0`。

完整类型：
```lean
∀ (i : Fin n),
Measurable[mN₀, borel ℝ]
      (fun ζ : Fin n → Ω => deleteTest0 ζ i * Real.exp (S0delete ζ i))
```

完整右端：
```lean
((hcap0m i).mul ((hDiff i).1.add ((hDiff i).2.1.const_mul y))).mul
      (hS0deletem i).exp
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hSνpoint — 第555–556行

UTF8字节[32797,32873)；片段SHA256 `75e43f3d1c3faa61e70a8464645bc239b28fc1b8b5a456b292e2fdc209d703b1`。

完整类型：
```lean
∀ (x : Fin n → Ω × ℝ),
Sν x = S0 (q x)
```

完整右端：
```lean
by
    rfl
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hSνdeletepoint — 第557–559行

UTF8字节[32873,32989)；片段SHA256 `cf41af8e806b912d59167033ce1af73567c9f0d72c1037f8e90da7b8766046f6`。

完整类型：
```lean
∀ (i : Fin n) (x : Fin n → Ω × ℝ),
Sνdelete x i = S0delete (q x) i
```

完整右端：
```lean
by
    rfl
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hFullReducedI — 第560–562行

UTF8字节[32989,33212)；片段SHA256 `f89bba460fa0208069509eeaeeb81f74debf26da9a0c95bb325c8573763bb0ac`。

完整类型：
```lean
Integrable (fun ζ => fullTest0 ζ * Real.exp (S0 ζ)) P₀
```

完整右端：
```lean
by
    apply (hId.integrable_comp hFullWeightedm.aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hFullOriginalI
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hDeleteReducedI — 第563–566行

UTF8字节[33212,33477)；片段SHA256 `1ad305f865f4973559fdf919970b12982454b41709cd5dfcdd3f6c45bb1d479e`。

完整类型：
```lean
∀ (i : Fin n),
Integrable (fun ζ => deleteTest0 ζ i * Real.exp (S0delete ζ i)) P₀
```

完整右端：
```lean
by
    apply (hId.integrable_comp (hDeleteWeightedm i).aestronglyMeasurable).mp
    simpa only [Function.comp_def, id_eq] using hDeleteOriginalI i
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hFullCodedI — 第567–569行

UTF8字节[33477,33682)；片段SHA256 `4fb8e318e7a8d131d6d0d5f1639b28923286e61ee21c6f983fbe03f888fca046`。

完整类型：
```lean
Integrable (fun x => fullTestν x * Real.exp (Sν x)) ν
```

完整右端：
```lean
by
    simpa only [Function.comp_def, fullTestν, hSνpoint] using
      hqpres.integrable_comp_of_integrable hFullReducedI
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hDeleteCodedI — 第570–573行

UTF8字节[33682,33933)；片段SHA256 `8392187f9a7881a2bb652d595326595020696395682b3d6f6bf498681a4a25bc`。

完整类型：
```lean
∀ (i : Fin n),
Integrable (fun x => deleteTestν x i * Real.exp (Sνdelete x i)) ν
```

完整右端：
```lean
by
    simpa only [Function.comp_def, deleteTestν, hSνdeletepoint] using
      hqpres.integrable_comp_of_integrable (hDeleteReducedI i)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hIreducedEq — 第574–577行

UTF8字节[33933,34148)；片段SHA256 `29b2b4813be30c592732b6741e9b714d4bf56e47f7831ada60bbedacf9976c37`。

完整类型：
```lean
Ireduced = Ioriginal
```

完整右端：
```lean
by
    change (∫ ζ, Real.exp (S0 ζ) ∂P₀) = ∫ ζ, Real.exp (S0 ζ) ∂P
    rw [hP₀map]
    exact integral_map hidN.aemeasurable hS0m.exp.aestronglyMeasurable
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hIcodedEq — 第578–584行

UTF8字节[34148,34477)；片段SHA256 `f308752d23c226ef530af799a41dc5923b9dbde8b6b787ecf042e8750a2fbd23`。

完整类型：
```lean
Icoded = Ioriginal
```

完整右端：
```lean
by
    change (∫ x, Real.exp (S0 (q x)) ∂ν) = Ioriginal
    calc
      _ = ∫ ζ, Real.exp (S0 ζ) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable hS0m.exp.aestronglyMeasurable).symm
      _ = Ireduced := by rw [hqpres.map_eq]
      _ = Ioriginal := hIreducedEq
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hIreducedPos — 第585–587行

UTF8字节[34477,34563)；片段SHA256 `677b6e8431706ed0074315af1e5c9ffd0a7e9e4133c29a0e6dc621f128bb4b1c`。

完整类型：
```lean
0 < Ireduced
```

完整右端：
```lean
by
    rw [hIreducedEq]
    exact hIoriginalPos
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hIcodedPos — 第588–590行

UTF8字节[34563,34643)；片段SHA256 `7323348f01959a5a1b24f71651f944f28eea3e420328f0304c8b2b6965ee76ea`。

完整类型：
```lean
0 < Icoded
```

完整右端：
```lean
by
    rw [hIcodedEq]
    exact hIoriginalPos
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hFullReducedEq — 第591–595行

UTF8字节[34643,34879)；片段SHA256 `f46fc96d00a76d66e3bd66272c0726a5099211872f0d6a71ab0e3de17f4942c8`。

完整类型：
```lean
(∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀) =
        ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P
```

完整右端：
```lean
by
    rw [hP₀map]
    exact integral_map hidN.aemeasurable hFullWeightedm.aestronglyMeasurable
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hFullCodedEq — 第596–604行

UTF8字节[34879,35365)；片段SHA256 `c3c194d28e1a7b8ded1660b5e3d23213c89ed01c3336a2d7a2f5b812e565d25d`。

完整类型：
```lean
(∫ x, fullTestν x * Real.exp (Sν x) ∂ν) =
        ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P
```

完整右端：
```lean
by
    change (∫ x, fullTest0 (q x) * Real.exp (S0 (q x)) ∂ν) = _
    calc
      _ = ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable hFullWeightedm.aestronglyMeasurable).symm
      _ = ∫ ζ, fullTest0 ζ * Real.exp (S0 ζ) ∂P₀ := by rw [hqpres.map_eq]
      _ = _ := hFullReducedEq
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hDeleteReducedEq — 第605–609行

UTF8字节[35365,35645)；片段SHA256 `d4dc070f5daa4f995fb5fdfc66e912610f977a325c9bcc8b8c122b6e91c9f07c`。

完整类型：
```lean
∀ (i : Fin n),
(∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀) =
        ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P
```

完整右端：
```lean
by
    rw [hP₀map]
    exact integral_map hidN.aemeasurable (hDeleteWeightedm i).aestronglyMeasurable
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hDeleteCodedEq — 第610–619行

UTF8字节[35645,36225)；片段SHA256 `045d0df6de5bb69cfd8beac67eb6435b221026dd2ec1d76fe5cb2bc498596505`。

完整类型：
```lean
∀ (i : Fin n),
(∫ x, deleteTestν x i * Real.exp (Sνdelete x i) ∂ν) =
        ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P
```

完整右端：
```lean
by
    change (∫ x, deleteTest0 (q x) i * Real.exp (S0delete (q x) i) ∂ν) = _
    calc
      _ = ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂ν.map q :=
        (integral_map hqpres.measurable.aemeasurable
          (hDeleteWeightedm i).aestronglyMeasurable).symm
      _ = ∫ ζ, deleteTest0 ζ i * Real.exp (S0delete ζ i) ∂P₀ := by rw [hqpres.map_eq]
      _ = _ := hDeleteReducedEq i
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hCostReducedEq — 第620–621行

UTF8字节[36225,36371)；片段SHA256 `89a1519085a046071df0754488c4ad8c25781ee6f02cc49d4a3aca718fe736a4`。

完整类型：
```lean
costReduced = costOriginal
```

完整右端：
```lean
by
    simp only [costReduced, costOriginal, hIreducedEq, hFullReducedEq, hDeleteReducedEq]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hCostCodedEq — 第622–623行

UTF8字节[36371,36505)；片段SHA256 `be500eb5a7e74d23cad5ef6f54f58296b634ab8e31f277245dc20f030071fbed`。

完整类型：
```lean
costCoded = costOriginal
```

完整右端：
```lean
by
    simp only [costCoded, costOriginal, hIcodedEq, hFullCodedEq, hDeleteCodedEq]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hCostReducedNonneg — 第624–626行

UTF8字节[36505,36611)；片段SHA256 `82ab0c1b3f66101689632ef99cb1a07a05d4e1aaddb1e48813b52eb085f9c8f6`。

完整类型：
```lean
0 ≤ costReduced
```

完整右端：
```lean
by
    rw [hCostReducedEq]
    exact hCostOriginalNonneg
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hCostCodedNonneg — 第627–629行

UTF8字节[36611,36711)；片段SHA256 `e1361d6d020d19dd0b14112e5a5fac6ae607dd5c771302b943138eb2ea7fdc16`。

完整类型：
```lean
0 ≤ costCoded
```

完整右端：
```lean
by
    rw [hCostCodedEq]
    exact hCostOriginalNonneg
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hCostReducedBound — 第630–634行

UTF8字节[36711,36933)；片段SHA256 `346997421b2485362bae23aa4340f32d419f271c001d48bde4c488c8065d006d`。

完整类型：
```lean
costReduced ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
        (1 + y) ^ 3 / Real.sqrt (n : ℝ)
```

完整右端：
```lean
by
    rw [hCostReducedEq]
    exact hCostOriginalBound
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hCostCodedBound — 第635–639行

UTF8字节[36933,37149)；片段SHA256 `43e39f41a82fc6c2932f9b558b4117fa728c895758dce3b350c7e04d9ab3a0ba`。

完整类型：
```lean
costCoded ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
        (1 + y) ^ 3 / Real.sqrt (n : ℝ)
```

完整右端：
```lean
by
    rw [hCostCodedEq]
    exact hCostOriginalBound
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 295, "visibleThroughLine": 667, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}
