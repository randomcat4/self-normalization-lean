# 第254单元完整源码局部库存

库存仅描述当前源中的局部项；实际编译所属声明数为 null，待服务器。

## let g — 第26–26行

UTF8字节[825,879)；完整声明片段SHA256 `0b29afa0641c31a76d56ea7620b22e7e753f0de54bf1235c79b167cfc9f10fac`。

完整依赖类型：
```lean
Ω → ℝ
```

完整右端／证明体：
```lean
fun o => ∫ y, h o y ∂μ
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let r — 第27–27行

UTF8字节[879,941)；完整声明片段SHA256 `b00240cd6a8bccd8321e184bdc42ef18984f8c7a799e7ae9214f181724e6c6b3`。

完整依赖类型：
```lean
Ω → Ω → ℝ
```

完整右端／证明体：
```lean
fun o y => h o y - g o - g y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let v — 第28–29行

UTF8字节[941,1037)；完整声明片段SHA256 `8f1543d4fcfceb0a51be2a06227df5a4b6bac7ca15875ff960abae05b1666ba6`。

完整依赖类型：
```lean
ℝ
```

完整右端／证明体：
```lean
∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let rho — 第30–30行

UTF8字节[1037,1070)；完整声明片段SHA256 `5c95fef094d0338a5f5278b5385a23d1fce35c2de712e5c818838bc8d3317cde`。

完整依赖类型：
```lean
ℝ
```

完整右端／证明体：
```lean
Real.sqrt v
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let μ₀ — 第33–33行

UTF8字节[1190,1242)；完整声明片段SHA256 `382ffd6eb5df95b91fe1e09e78d1467734957ec1d393f4b91e188f4d488f2b59`。

完整依赖类型：
```lean
@Measure Ω m₀
```

完整右端／证明体：
```lean
μ.trim hm₀
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@34 — 第34–34行

UTF8字节[1242,1282)；完整声明片段SHA256 `e6caeaa4d46b95650091781ec0d6b9449555d04de2c9e6aa0bfaee571d026a21`。

完整依赖类型：
```lean
MeasurableSpace Ω
```

完整右端／证明体：
```lean
m₀
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@35 — 第35–35行

UTF8字节[1282,1340)；完整声明片段SHA256 `15d62b299395cc4740687f5e76b362ae86716ed7c047fd7093f0c1fb59a8c614`。

完整依赖类型：
```lean
MeasurableSpace.CountablyGenerated Ω
```

完整右端／证明体：
```lean
hcg
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## let mN — 第42–43行

UTF8字节[1622,1756)；完整声明片段SHA256 `1532a3bc286aae308ba27844872b6310d692746210bb169cabd2c3ffa7fd55e5`。

完整依赖类型：
```lean
MeasurableSpace (Fin n → Ω)
```

完整右端／证明体：
```lean
@MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => mΩ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let mN₀ — 第44–45行

UTF8字节[1756,1894)；完整声明片段SHA256 `cf58a17ac398370e8c2fca3e20a7162679e162c6434aa1dfcbc056d541504c45`。

完整依赖类型：
```lean
MeasurableSpace (Fin n → Ω)
```

完整右端／证明体：
```lean
@MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω) (fun _ : Fin n => m₀)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let P — 第46–48行

UTF8字节[1894,2083)；完整声明片段SHA256 `123aaace5a6a051ca65b63bd0eb407238c734f467813796e65315caa65fcc30f`。

完整依赖类型：
```lean
@Measure (Fin n → Ω) mN
```

完整右端／证明体：
```lean
@Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mΩ) (fun _ : Fin n => μ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let P₀ — 第49–51行

UTF8字节[2083,2282)；完整声明片段SHA256 `96a0091eb4cd240e26a92b9fd257913d3b4b6b0d12cd0142fe939b6b9152581c`。

完整依赖类型：
```lean
@Measure (Fin n → Ω) mN₀
```

完整右端／证明体：
```lean
@Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => m₀) (fun _ : Fin n => μ₀)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let N — 第52–52行

UTF8字节[2282,2325)；完整声明片段SHA256 `b0dd346585e535f381697477059a9d1dd69a797b6e326f859d60da28400cb8d5`。

完整依赖类型：
```lean
ℝ
```

完整右端／证明体：
```lean
Real.sqrt (n : ℝ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let O — 第53–53行

UTF8字节[2325,2393)；完整声明片段SHA256 `6e2f89042a775a10443dd30e93e209855cf0c2314d3e45219f2cd0a7604d3d78`。

完整依赖类型：
```lean
Fin n → (Fin n → Ω) → Ω
```

完整右端／证明体：
```lean
fun i ξ => ξ i
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let gcoord — 第54–54行

UTF8字节[2393,2457)；完整声明片段SHA256 `df7ef07ae8798a838c8cf315777491947c8652afb261238b41fd96b21277bb57`。

完整依赖类型：
```lean
Fin n → Ω → ℝ
```

完整右端／证明体：
```lean
fun _ o => g o / N
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Q — 第55–55行

UTF8字节[2457,2529)；完整声明片段SHA256 `34d0560698e04d9bf231875721b57485e80107fb08bbf9ae67cb1e52369abd67`。

完整依赖类型：
```lean
(Fin n → Ω) → (Fin n → Ω)
```

完整右端／证明体：
```lean
fun ξ i => O i ξ
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let D1 — 第56–56行

UTF8字节[2529,2595)；完整声明片段SHA256 `9c7b6592987c974bc1511c709091eafae438acf7f30f9a750c350c4fe538ab83`。

完整依赖类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端／证明体：
```lean
residualStatisticD n r
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let D2 — 第57–57行

UTF8字节[2595,2675)；完整声明片段SHA256 `bd2d76f4bd9534628a22c2e37b9fcea25a01626ea101066a860405f7e70775ba`。

完整依赖类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端／证明体：
```lean
clippedCenteredDelta n g r 512 rho y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Tclip — 第58–58行

UTF8字节[2675,2762)；完整声明片段SHA256 `cca32d97948da19d9f4605b8c39dff3d557285d4e2047482e1cd0d35633f925c`。

完整依赖类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端／证明体：
```lean
clippedCenteredStatistic n g r 512 rho y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Ddel — 第59–59行

UTF8字节[2762,2847)；完整声明片段SHA256 `a8bede803609bdbc764a9a8a1fb1385319c461c39adced7e13de60e8573ca94b`。

完整依赖类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端／证明体：
```lean
residualStatisticDDeleted n r
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Jdel — 第60–60行

UTF8字节[2847,2929)；完整声明片段SHA256 `518b590ccee383eb179c7a6611ee3e0a8e42031339a0293270e86d9256a27021`。

完整依赖类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端／证明体：
```lean
residualEnergyJDeleted n r
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Bdelete — 第61–61行

UTF8字节[2929,3030)；完整声明片段SHA256 `a0d47872a6e2c1c0bd6e5613436458a03f64d5c3fb164c74634062867be543df`。

完整依赖类型：
```lean
(Fin n → Ω) → Fin n → ℝ
```

完整右端／证明体：
```lean
studentizerClipBudgetDeleted n r 512 rho y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let κ — 第62–62行

UTF8字节[3030,3084)；完整声明片段SHA256 `558fd727fae98a6a22827f77044b2d995cf17ca898d99ae747d919fbbb9adfed`。

完整依赖类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端／证明体：
```lean
fun _ => 0
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let W0 — 第63–63行

UTF8字节[3084,3170)；完整声明片段SHA256 `678e6c91872782281cf2303d52f52b0e1c0a649432bdfeefa9fcbc02b9734f55`。

完整依赖类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端／证明体：
```lean
fun ξ => ∑ i : Fin n, gcoord i (O i ξ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let V0 — 第64–65行

UTF8字节[3170,3284)；完整声明片段SHA256 `11884c30f2d34d383f2f1e41093b723bd5a76989ace1e0ebf2ad301b1ea1e41c`。

完整依赖类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端／证明体：
```lean
fun ξ => Real.sqrt (∑ i : Fin n, (gcoord i (O i ξ)) ^ 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let T0 — 第66–68行

UTF8字节[3284,3446)；完整声明片段SHA256 `84af2cc8f09d9756ceef25fd6e3c39a2b0e6b60916adbfea5566ba7a76ecf92e`。

完整依赖类型：
```lean
(Fin n → Ω) → ℝ
```

完整右端／证明体：
```lean
fun ξ =>
          if V0 ξ = 0 then κ ξ else
            (W0 ξ + D1 (Q ξ)) / (V0 ξ * Real.sqrt (1 + D2 (Q ξ)))
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let lambda01 — 第69–69行

UTF8字节[3446,3538)；完整声明片段SHA256 `3d231e4a032ab86a8d752417d4815d8a6140076abc2f24a447da664761f17df1`。

完整依赖类型：
```lean
Measure ℝ
```

完整右端／证明体：
```lean
(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let mAugLocal — 第70–70行

UTF8字节[3538,3615)；完整声明片段SHA256 `25f35add49e8e861a5ea07efc4efa94380acaa28e0e8f2e8cc22adb712e717a3`。

完整依赖类型：
```lean
MeasurableSpace (Ω × ℝ)
```

完整右端／证明体：
```lean
m₀.prod (borel ℝ)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let mAug — 第71–73行

UTF8字节[3615,3783)；完整声明片段SHA256 `484a35d08f6969d5a9af3558338dc1b2de8eae3051239522b8dff7a063b0469a`。

完整依赖类型：
```lean
MeasurableSpace (Fin n → Ω × ℝ)
```

完整右端／证明体：
```lean
@MeasurableSpace.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (fun _ : Fin n => mAugLocal)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let νlocal — 第74–75行

UTF8字节[3783,3921)；完整声明片段SHA256 `c9bc877c85ade197529a62181e31b5d6d2abea5e84a1b1def0e587e756bad5f8`。

完整依赖类型：
```lean
Fin n → @Measure (Ω × ℝ) mAugLocal
```

完整右端／证明体：
```lean
fun _ => @Measure.prod Ω ℝ m₀ (borel ℝ) μ₀ lambda01
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ν — 第76–79行

UTF8字节[3921,4131)；完整声明片段SHA256 `9eddfa74d662e3cdbb5ccd986564ac290b098c5a3d9f54e1e4bfdf60f1d2e71d`。

完整依赖类型：
```lean
@Measure (Fin n → Ω × ℝ) mAug
```

完整右端／证明体：
```lean
@Measure.pi (Fin n) (fun _ : Fin n => Ω × ℝ)
            (inferInstance : Fintype (Fin n))
            (fun _ : Fin n => mAugLocal) νlocal
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let q — 第80–80行

UTF8字节[4131,4210)；完整声明片段SHA256 `9d234e9b45d6e75c75659651922b35eba26057aace025c0a38d1b03fdb684673`。

完整依赖类型：
```lean
(Fin n → Ω × ℝ) → (Fin n → Ω)
```

完整右端／证明体：
```lean
fun x i => (x i).1
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let c — 第81–83行

UTF8字节[4210,4397)；完整声明片段SHA256 `9f67e68f78e48c02aaaac71f14d6907a3c0f7c8cc5747c656a6c46bffcbf867a`。

完整依赖类型：
```lean
Fin n → (Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun _ =>
          Shao.OQ6.ScalarObservationCoding.baseFourIndicatorCode
            (MeasurableSpace.natGeneratingSequence (Ω × ℝ))
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ξlocal — 第84–84行

UTF8字节[4397,4476)；完整声明片段SHA256 `512ddc7342bc73a0c95b734cb0fded1efbc5da6b235a162ce0bedbfe97d4a2e1`。

完整依赖类型：
```lean
Fin n → (Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun i t => gcoord i t.1
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Ylocal — 第85–86行

UTF8字节[4476,4627)；完整声明片段SHA256 `3b7d80fefde4a19fca531f1db7d112a2094671921f243e07ab3f68731a9f268c`。

完整依赖类型：
```lean
Fin n → (Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun i =>
          Shao.OQ6.QuantizedObservationCoding.quantizedObservation ε (ξlocal i) (c i)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ξ — 第87–87行

UTF8字节[4627,4715)；完整声明片段SHA256 `b11381ae31fbcbbf3069ec2ed9808975691d877dc61bd27c3b6619d02f2d57cb`。

完整依赖类型：
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun i x => gcoord i (x i).1
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Y — 第88–88行

UTF8字节[4715,4800)；完整声明片段SHA256 `f150aa3a04f926f084102738abd1bfb0a49a3c168f3d40b02740e03cd060cc78`。

完整依赖类型：
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun i x => Ylocal i (x i)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let a — 第89–89行

UTF8字节[4800,4894)；完整声明片段SHA256 `46759722f24b03abc7ba54ac0d4d20b708d2c9f93201f4a5d07d658aa16d7530`。

完整依赖类型：
```lean
Fin n → ℝ
```

完整右端／证明体：
```lean
Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν Y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let s — 第90–90行

UTF8字节[4894,4982)；完整声明片段SHA256 `475acb50540db8f7fe07fc7787598bd06db120dc988efc36bc1f9ee0644e4db4`。

完整依赖类型：
```lean
ℝ
```

完整右端／证明体：
```lean
Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν Y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let ηlocal — 第91–92行

UTF8字节[4982,5142)；完整声明片段SHA256 `0b2391d1738564ef3f9e388492c00388454f9218c8cb1be512c97c06a6d501cd`。

完整依赖类型：
```lean
Fin n → (Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun i =>
          Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation (a i) s (Ylocal i)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let η — 第93–94行

UTF8字节[5142,5275)；完整声明片段SHA256 `20b4846e54c733e1ba3288a32a5fa63cdaffedd3f38c455bf64e591e0de99573`。

完整依赖类型：
```lean
Fin n → (Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let C — 第95–95行

UTF8字节[5275,5354)；完整声明片段SHA256 `c3b960cee32d46549999cd53aab9575b211e5c99d81deb9433621877aebd0618`。

完整依赖类型：
```lean
(Fin n → Ω × ℝ) → (Fin n → ℝ)
```

完整右端／证明体：
```lean
fun x i => η i x
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let W — 第96–96行

UTF8字节[5354,5434)；完整声明片段SHA256 `2ad338a6ce1f89b3df11a3729188a270483e6eb1e1296933be2974efc89ab3ed`。

完整依赖类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun x => ∑ i : Fin n, ξ i x
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let V — 第97–97行

UTF8字节[5434,5532)；完整声明片段SHA256 `4e4dbf53a720ae51eeb0e08f59f96929054890c4139571c1c4f4db5931e85c9d`。

完整依赖类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun x => Real.sqrt (∑ i : Fin n, (ξ i x) ^ 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Wη — 第98–98行

UTF8字节[5532,5614)；完整声明片段SHA256 `10df7570c5d7d58a40b4d9be72a645adb4f7ceb54ae0f2f10ac3b4e95e598f14`。

完整依赖类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun x => ∑ i : Fin n, η i x
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Vη — 第99–99行

UTF8字节[5614,5714)；完整声明片段SHA256 `8652cb426d9863afe552a9594428e06039082b7048acb645ede2f1e63ec8e279`。

完整依赖类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun x => Real.sqrt (∑ i : Fin n, (η i x) ^ 2)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let b — 第100–100行

UTF8字节[5714,5797)；完整声明片段SHA256 `a92be81d27643ac8e65b60923b8188a3c769668be0b5c73afbd640b815e8fca9`。

完整依赖类型：
```lean
(Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun x => Real.sqrt (1 + D2 (q x))
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Dη — 第101–102行

UTF8字节[5797,5926)；完整声明片段SHA256 `8b15bc1ce889601d9b4a4c84ff505ed681c1c3e25cf3ed1660ff77f49ba08431`。

完整依赖类型：
```lean
ℝ → (Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun z x => D1 (q x) + W x - Wη x + z * b x * (Vη x - V x)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Tη — 第103–104行

UTF8字节[5926,6040)；完整声明片段SHA256 `7241ba08730002cfa96708ef516ec666ea428355389aab10d617255e9dd546c9`。

完整依赖类型：
```lean
ℝ → (Fin n → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun z x => (Wη x + Dη z x) / (Vη x * b x)
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Z0 — 第105–105行

UTF8字节[6040,6109)；完整声明片段SHA256 `3b7b467f5e1c0c0c9006515ff40ade18e52257d366ee32f229a4aaa22b6b4bcf`。

完整依赖类型：
```lean
Set (Fin n → Ω)
```

完整右端／证明体：
```lean
{ξ | projectionV n g ξ = 0}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Z — 第106–106行

UTF8字节[6109,6168)；完整声明片段SHA256 `89c1ae14326b0524482b3180bbea82ec0e025d19f4b3de699599224fae255e0e`。

完整依赖类型：
```lean
Set (Fin n → Ω × ℝ)
```

完整右端／证明体：
```lean
{x | V x = 0}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let p0 — 第107–107行

UTF8字节[6168,6202)；完整声明片段SHA256 `b44df8e4c95d6f20a3cd2b996a894400a0ebab066bee9adf2ac1c60952dc96a7`。

完整依赖类型：
```lean
ℝ
```

完整右端／证明体：
```lean
P.real Z0
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let comparisons — 第108–111行

UTF8字节[6202,6463)；完整声明片段SHA256 `2e09c765bced4ee76b39ecc364c96dab4fc9e400ab57554bcbef4b343a829272`。

完整依赖类型：
```lean
Set (ℝ → ℝ → Prop)
```

完整右端／证明体：
```lean
{R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
            R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
            R = (fun a b : ℝ => a = b)}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let F0 — 第112–114行

UTF8字节[6463,6657)；完整声明片段SHA256 `79bae7d935044280de67150c9b879de225625d7a0c3c212b4d8c1a942cd14080`。

完整依赖类型：
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω)
```

完整右端／证明体：
```lean
fun R z =>
          {ξ | R (projectionW n g ξ + D1 ξ)
            (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let A0 — 第115–116行

UTF8字节[6657,6774)；完整声明片段SHA256 `1466b5f547c9e987730392f64e690d58bed1bc5aeddd5fbeab97da6468f6ebe6`。

完整依赖类型：
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω)
```

完整右端／证明体：
```lean
fun R z => {ξ | R (Tclip ξ) z}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## let Eη — 第117–118行

UTF8字节[6774,6897)；完整声明片段SHA256 `44357b805401be9a1668e5d7c30a97990c7edcd0719bb6e4c6ebe677f4d09a11`。

完整依赖类型：
```lean
(ℝ → ℝ → Prop) → ℝ → Set (Fin n → Ω × ℝ)
```

完整右端／证明体：
```lean
fun R z => {x | R (Tη z x) z}
```

词法范围：{"enclosing": "frozen result telescope", "contextFromLine": 16, "visibleThroughLine": 182, "declarationIndent": 8, "coordinateConvention": "1-based inclusive"}

## have hmodel — 第186–188行

UTF8字节[11111,11306)；完整声明片段SHA256 `ae512aecf1e8e65c6b256582d21215bef60546298a22ffd1b0b54dd4d1f0be6c`。

完整依赖类型：
```lean
    let f : ℕ → Ω → ℝ := fun (_k : ℕ) (_o : Ω) => (0 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ :=
      ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω mΩ mΩ μ μ)
    let rho : ℝ := Real.sqrt v
    let rowIntegrable : Ω → Prop := fun o => Integrable (h o) μ
    let gLp : ℝ≥0∞ → Prop := fun p => MemLp g p μ
    let projectionLaw : Measure ℝ :=
      @Measure.map Ω ℝ mΩ (borel ℝ) g μ
    let pairLaw : @Measure (Ω × Ω) (mΩ.prod mΩ) :=
      @Measure.prod Ω Ω mΩ mΩ μ μ
    ∃ (m₀ : MeasurableSpace Ω) (hm₀ : m₀ ≤ mΩ),
      @MeasurableSpace.CountablyGenerated Ω m₀ ∧
      Measurable[m₀.prod m₀, borel ℝ]
        (fun t : Ω × Ω => h t.1 t.2) ∧
      (∀ k : ℕ, Measurable[m₀, borel ℝ] (f k)) ∧
      let μ₀ : @Measure Ω m₀ := μ.trim hm₀
      letI : MeasurableSpace Ω := m₀
      let g₀ : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
      let r₀ : Ω → Ω → ℝ := fun o y => h o y - g₀ o - g₀ y
      let v₀ : ℝ :=
        ∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
      let rho₀ : ℝ := Real.sqrt v₀
      IsProbabilityMeasure μ₀ ∧
      μ₀ = @Measure.map Ω Ω mΩ m₀ id μ ∧
      g₀ = g ∧ r₀ = r ∧ v₀ = v ∧ rho₀ = rho ∧
      (∀ o : Ω, Integrable (h o) μ₀ ↔ rowIntegrable o) ∧
      MemLp (fun t : Ω × Ω => h t.1 t.2) 2
        (@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀) ∧
      (∫ t : Ω × Ω, h t.1 t.2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)) = 0 ∧
      Measurable g₀ ∧ MemLp g₀ 2 μ₀ ∧
      (∫ o, g₀ o ∂μ₀) = 0 ∧ (∫ o, g₀ o ^ 2 ∂μ₀) = 1 ∧
      Measurable (fun t : Ω × Ω => r₀ t.1 t.2) ∧
      MemLp (fun t : Ω × Ω => r₀ t.1 t.2) 2
        (@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀) ∧
      (∀ o y : Ω, r₀ o y = r₀ y o) ∧
      (∀ᵐ o ∂μ₀, (∫ y, r₀ o y ∂μ₀) = 0) ∧
      @Measure.map Ω ℝ m₀ (borel ℝ) g₀ μ₀ = projectionLaw ∧
      (∀ p : ℝ≥0∞, MemLp g₀ p μ₀ ↔ gLp p) ∧
      @Measure.prod Ω Ω m₀ m₀ μ₀ μ₀ =
        @Measure.map (Ω × Ω) (Ω × Ω)
          (mΩ.prod mΩ) (m₀.prod m₀) id pairLaw ∧
      (∀ (J : Type) (instJ : Fintype J),
        let mJ : MeasurableSpace (J → Ω) :=
          @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => mΩ)
        let mJ₀ : MeasurableSpace (J → Ω) :=
          @MeasurableSpace.pi J (fun _ : J => Ω) (fun _ : J => m₀)
        let P : @Measure (J → Ω) mJ :=
          @Measure.pi J (fun _ : J => Ω) instJ
            (fun _ : J => mΩ) (fun _ : J => μ)
        let P₀ : @Measure (J → Ω) mJ₀ :=
          @Measure.pi J (fun _ : J => Ω) instJ
            (fun _ : J => m₀) (fun _ : J => μ₀)
        @IsProbabilityMeasure (J → Ω) mJ₀ P₀ ∧
        Measurable[mJ, mJ₀] (id : (J → Ω) → J → Ω) ∧
        P₀ = @Measure.map (J → Ω) (J → Ω) mJ mJ₀ id P ∧
        ∀ (B : Type) (mB : MeasurableSpace B) (T : (J → Ω) → B),
          Measurable[mJ₀, mB] T →
          @Measure.map (J → Ω) B mJ₀ mB T P₀ =
            @Measure.map (J → Ω) B mJ mB T P) ∧
      (∀ (n : ℕ) (hn : 4 ≤ n)
          (z : ℝ) (hz : 1 ≤ z)
          (hwindow : z ≤ Real.sqrt (n : ℝ) / (2 * Real.exp (1 / 2 : ℝ))),
        (
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
            let rho : ℝ := Real.sqrt v
            let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ₀)
            let N : ℝ := Real.sqrt (n : ℝ)
            let W : (Fin n → Ω) → ℝ := projectionW n g
            let V : (Fin n → Ω) → ℝ := projectionV n g
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
            let Adelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i => |Ddelete ζ i|
            let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
            let Bdelete : (Fin n → Ω) → Fin n → ℝ :=
              studentizerClipBudgetDeleted n r 512 rho z
            let d : (Fin n → Ω) → ℝ := centeredDelta n g r
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
            let Tclip : (Fin n → Ω) → ℝ := clippedCenteredStatistic n g r 512 rho z
            let s : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (centeredSq n g r ζ)
            let Tphysical : (Fin n → Ω) → ℝ := fun ζ =>
              if s ζ = 0 then 0 else (W ζ + D ζ) / s ζ
            let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
            let cap : (Fin n → Ω) → Fin n → ℝ := fun ζ i => min |z * ξ0 i ζ| 1
            let S : (Fin n → Ω) → ℝ := fun ζ =>
              ∑ j : Fin n, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
            let Sdelete : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
              ∑ j ∈ Finset.univ.erase i, (z * ξ0 j ζ - (z * ξ0 j ζ) ^ 2 / 2)
            let fullTest : (Fin n → Ω) → ℝ := fun ζ => z * A ζ + z ^ 2 * B ζ
            let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ζ i =>
              cap ζ i * (|A ζ - Adelete ζ i| + z * |B ζ - Bdelete ζ i|)
            let I : ℝ := ∫ ζ, Real.exp (S ζ) ∂P
            let sourceCost : ℝ :=
              ((∫ ζ, fullTest ζ * Real.exp (S ζ) ∂P) +
                ∑ i : Fin n, ∫ ζ, deletedTest ζ i * Real.exp (Sdelete ζ i) ∂P) / I
            Measurable W ∧ Measurable V ∧ Measurable D ∧ Measurable J ∧
            Measurable A ∧ Measurable B ∧ Measurable d ∧ Measurable e ∧
            Measurable s ∧ Measurable Tclip ∧ Measurable Tphysical ∧
            Measurable fullTest ∧
            MeasurableSet {ζ : Fin n → Ω | V ζ = 0} ∧
            MeasurableSet {ζ : Fin n → Ω | s ζ = 0} ∧
            (∀ ζ : Fin n → Ω,
              (1 / 2 : ℝ) ≤ 1 + e ζ ∧ |e ζ| ≤ B ζ ∧ |e ζ| ≤ |d ζ| ∧
              (0 < V ζ → 0 < V ζ * Real.sqrt (1 + e ζ))) ∧
            (∀ ζ : Fin n → Ω, V ζ = 0 → d ζ = 0 ∧ e ζ = 0 ∧ Tclip ζ = 0) ∧
            (∀ ζ : Fin n → Ω, s ζ = 0 → Tphysical ζ = 0) ∧
            (∀ i : Fin n,
              Measurable (fun ζ : Fin n → Ω => cap ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Ddelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Jdelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Adelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => Bdelete ζ i) ∧
              Measurable (fun ζ : Fin n → Ω => deletedTest ζ i) ∧
              ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
                Measurable E ∧ ∀ ζ : Fin n → Ω,
                  (Ddelete ζ i, Jdelete ζ i, Bdelete ζ i) =
                    E (fun j : {j : Fin n // j ≠ i} => ζ j.val)) ∧
            ((1 + rho) * z ≤ N →
              (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n g z →
                -(1 / 2 : ℝ) ≤ d ζ →
                e ζ = d ζ ∧ 0 < V ζ * Real.sqrt (1 + e ζ) ∧
                0 < s ζ ∧ V ζ * Real.sqrt (1 + e ζ) = s ζ ∧
                Tclip ζ = Tphysical ζ) ∧
              {ζ : Fin n → Ω | Tclip ζ ≠ Tphysical ζ} ⊆
                (projectionGood n g z)ᶜ ∪ lowerStudentizerBad n g r z) ∧
            0 < I ∧
            Integrable (fun ζ => fullTest ζ * Real.exp (S ζ)) P ∧
            (∀ i : Fin n,
              Integrable (fun ζ => deletedTest ζ i * Real.exp (Sdelete ζ i)) P) ∧
            0 ≤ sourceCost ∧
            sourceCost ≤
              64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + rho) *
                (1 + z) ^ 3 / Real.sqrt (n : ℝ)
        ) ∧
        (
            let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ₀
            let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
            let v : ℝ := ∫ t : Ω × Ω, r t.1 t.2 ^ 2 ∂(μ₀.prod μ₀)
            let rho : ℝ := Real.sqrt v
            let P : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ₀)
            let N : ℝ := Real.sqrt (n : ℝ)
            let ξ0 : Fin n → (Fin n → Ω) → ℝ := fun i ζ => g (ζ i) / N
            let D : (Fin n → Ω) → ℝ := residualStatisticD n r
            let J : (Fin n → Ω) → ℝ := residualEnergyJ n r
            let Ddelete : (Fin n → Ω) → Fin n → ℝ := residualStatisticDDeleted n r
            let Jdelete : (Fin n → Ω) → Fin n → ℝ := residualEnergyJDeleted n r
            let A : (Fin n → Ω) → ℝ := fun ζ => |D ζ|
            let Adelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ => |Ddelete ζ i|
            let B : (Fin n → Ω) → ℝ := studentizerClipBudget n r 512 rho z
            let Bdelete : Fin n → (Fin n → Ω) → ℝ :=
              fun i ζ => studentizerClipBudgetDeleted n r 512 rho z ζ i
            let e : (Fin n → Ω) → ℝ := clippedCenteredDelta n g r 512 rho z
            let V : (Fin n → Ω) → ℝ := fun ζ => Real.sqrt (∑ j : Fin n, (ξ0 j ζ) ^ 2)
            let Vdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
              Real.sqrt (∑ j ∈ Finset.univ.erase i, (ξ0 j ζ) ^ 2)
            let H : (Fin n → Ω) → ℝ := fun ζ => (1 + V ζ) * (N + z * Real.sqrt (1 + B ζ))
            let Hdelete : Fin n → (Fin n → Ω) → ℝ := fun i ζ =>
              (1 + Vdelete i ζ) * (N + z * Real.sqrt (1 + Bdelete i ζ))
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
        ))
```

完整右端／证明体：
```lean
Shao.OQ6.OriginalLevelDependentCountablyGeneratedModel.actual_original_level_dependent_countably_generated_model.{u, 0, 0}
      μ h hh hh2 hhsymm hcenter hprojectionsecond
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@193 — 第193–193行

UTF8字节[11444,11480)；完整声明片段SHA256 `464b3d02d8b2a7fbe3f50fc1d25c9e40caceacda2b19bd28cee0724c717cbb56`。

完整依赖类型：
```lean
MeasurableSpace Ω
```

完整右端／证明体：
```lean
m₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@194 — 第194–194行

UTF8字节[11480,11534)；完整声明片段SHA256 `d7f0d85fc211d84c49f0e7f15afda86e4d0ccbcb7fd99b5f2468c1d34abf5bce`。

完整依赖类型：
```lean
MeasurableSpace.CountablyGenerated Ω
```

完整右端／证明体：
```lean
hcg
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let g₀ — 第200–200行

UTF8字节[11814,11872)；完整声明片段SHA256 `c1ad3249cb80d18aa9a5fca50514403fe95b34d314d76c2aca17b98d3ace3338`。

完整依赖类型：
```lean
Ω → ℝ
```

完整右端／证明体：
```lean
fun o => ∫ y, h o y ∂μ₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let r₀ — 第201–201行

UTF8字节[11872,11941)；完整声明片段SHA256 `822687897e055d97437ea4791827a89b632abc825ebece8e242f5a28e2083c4e`。

完整依赖类型：
```lean
Ω → Ω → ℝ
```

完整右端／证明体：
```lean
fun o y => h o y - g₀ o - g₀ y
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let v₀ — 第202–203行

UTF8字节[11941,12047)；完整声明片段SHA256 `026ce0420aa69279161f67f57ef5ef4ee65e43a1965eee45d83095fdb6badebb`。

完整依赖类型：
```lean
ℝ
```

完整右端／证明体：
```lean
∫ t : Ω × Ω, r₀ t.1 t.2 ^ 2 ∂(@Measure.prod Ω Ω m₀ m₀ μ₀ μ₀)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let rho₀ — 第204–204行

UTF8字节[12047,12084)；完整声明片段SHA256 `12a522fe417b5d6c4f706cc18426266a4b597701641fcd595cec9471f02e9079`。

完整依赖类型：
```lean
ℝ
```

完整右端／证明体：
```lean
Real.sqrt v₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hgmeas — 第208–210行

UTF8字节[12177,12253)；完整声明片段SHA256 `7d41c48bea7b8c5204585da02d7bbc95c8b7ce4553ee992c73c47a5a7163320a`。

完整依赖类型：
```lean
Measurable g
```

完整右端／证明体：
```lean
by
    rw [← hgpoint]
    exact hgmeas₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hg₂ — 第211–213行

UTF8字节[12253,12330)；完整声明片段SHA256 `743bd91eba2861a558c071c353debfb71211290c34f97bdbf3be4aa1de510c52`。

完整依赖类型：
```lean
MemLp g 2 μ₀
```

完整右端／证明体：
```lean
by
    rw [← hgpoint]
    exact hg₂₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hgmean — 第214–216行

UTF8字节[12330,12419)；完整声明片段SHA256 `bfc24bdc636d71e0fce27ce4e28ea84ff3f7b37ddbcacd8b71632af68f498102`。

完整依赖类型：
```lean
(∫ o, g o ∂μ₀) = 0
```

完整右端／证明体：
```lean
by
    rw [← hgpoint]
    exact hgmean₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hgsecond — 第217–219行

UTF8字节[12419,12516)；完整声明片段SHA256 `59887d2f16eea3e127688f76e037b93581e8c5b9f695df9190171e6235edc81b`。

完整依赖类型：
```lean
(∫ o, g o ^ 2 ∂μ₀) = 1
```

完整右端／证明体：
```lean
by
    rw [← hgpoint]
    exact hgsecond₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@220 — 第220–220行

UTF8字节[12516,12566)；完整声明片段SHA256 `f935583731d94a002e1ba7cca290356ed8e01191a6d6c468ccc26f875132a158`。

完整依赖类型：
```lean
IsProbabilityMeasure μ₀
```

完整右端／证明体：
```lean
hμ₀prob
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hfiniteN — 第227–227行

UTF8字节[12896,12965)；完整声明片段SHA256 `8dd884ce702fec361de6177dc0b16a3dfbbd32f8ad0fd9115e74c53519fd7c27`。

完整依赖类型：
```lean
@IsProbabilityMeasure (Fin n → Ω) mN₀ P₀ ∧
Measurable[mN, mN₀] (id : (Fin n → Ω) → Fin n → Ω) ∧
P₀ = @Measure.map (Fin n → Ω) (Fin n → Ω) mN mN₀ id P ∧
∀ (B : Type) (mB : MeasurableSpace B) (T : (Fin n → Ω) → B), Measurable[mN₀, mB] T → @Measure.map (Fin n → Ω) B mN₀ mB T P₀ = @Measure.map (Fin n → Ω) B mN mB T P
```

完整右端／证明体：
```lean
hfinite (Fin n) (inferInstance : Fintype (Fin n))
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@232 — 第232–232行

UTF8字节[13271,13319)；完整声明片段SHA256 `b0acfa3a93396ccc5cddc1c994d0d6842c8383732c75daf23617e75fab46a3ab`。

完整依赖类型：
```lean
IsProbabilityMeasure P₀
```

完整右端／证明体：
```lean
hP₀prob
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hstatisticsCurrent — 第233–233行

UTF8字节[13319,13383)；完整声明片段SHA256 `f69ca447fce9c706ad8c51ddb5ff88586a66ae9b1a63926cd8af40d85157bdc7`。

完整依赖类型：
```lean
Measurable (projectionW n (g₀)) ∧
Measurable (projectionV n (g₀)) ∧
Measurable (residualStatisticD n (r₀)) ∧
Measurable (residualEnergyJ n (r₀)) ∧
Measurable (fun ζ => |(residualStatisticD n (r₀)) ζ|) ∧
Measurable (studentizerClipBudget n (r₀) 512 (rho₀) y) ∧
Measurable (centeredDelta n (g₀) (r₀)) ∧
Measurable (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ∧
Measurable (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ∧
Measurable (clippedCenteredStatistic n (g₀) (r₀) 512 (rho₀) y) ∧
Measurable (fun ζ =>
      if (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 then 0 else ((projectionW n (g₀)) ζ + (residualStatisticD n (r₀)) ζ) / (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ) ∧
Measurable (fun ζ => y * (fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ + y ^ 2 * (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ) ∧
MeasurableSet {ζ : Fin n → Ω | (projectionV n (g₀)) ζ = 0} ∧
MeasurableSet {ζ : Fin n → Ω | (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0} ∧
(∀ ζ : Fin n → Ω,
      (1 / 2 : ℝ) ≤ 1 + (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ ∧ |(clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ| ≤ (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ ∧ |(clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ| ≤ |(centeredDelta n (g₀) (r₀)) ζ| ∧
      (0 < (projectionV n (g₀)) ζ → 0 < (projectionV n (g₀)) ζ * Real.sqrt (1 + (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ))) ∧
(∀ ζ : Fin n → Ω, (projectionV n (g₀)) ζ = 0 → (centeredDelta n (g₀) (r₀)) ζ = 0 ∧ (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ = 0 ∧ (clippedCenteredStatistic n (g₀) (r₀) 512 (rho₀) y) ζ = 0) ∧
(∀ ζ : Fin n → Ω, (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 → (fun ζ =>
      if (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 then 0 else ((projectionW n (g₀)) ζ + (residualStatisticD n (r₀)) ζ) / (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ) ζ = 0) ∧
(∀ i : Fin n,
      Measurable (fun ζ : Fin n → Ω => (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (residualStatisticDDeleted n (r₀)) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (residualEnergyJDeleted n (r₀)) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i) ∧
      Measurable (fun ζ : Fin n → Ω => (fun ζ i =>
      (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i * (|(fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ - (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i| + y * |(studentizerClipBudget n (r₀) 512 (rho₀) y) ζ - (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i|)) ζ i) ∧
      ∃ E : ({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ,
        Measurable E ∧ ∀ ζ : Fin n → Ω,
          ((residualStatisticDDeleted n (r₀)) ζ i, (residualEnergyJDeleted n (r₀)) ζ i, (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i) =
            E (fun j : {j : Fin n // j ≠ i} => ζ j.val)) ∧
((1 + (rho₀)) * y ≤ (N) →
      (∀ ζ : Fin n → Ω, ζ ∈ projectionGood n (g₀) y →
        -(1 / 2 : ℝ) ≤ (centeredDelta n (g₀) (r₀)) ζ →
        (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ = (centeredDelta n (g₀) (r₀)) ζ ∧ 0 < (projectionV n (g₀)) ζ * Real.sqrt (1 + (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ) ∧
        0 < (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ ∧ (projectionV n (g₀)) ζ * Real.sqrt (1 + (clippedCenteredDelta n (g₀) (r₀) 512 (rho₀) y) ζ) = (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ ∧
        (clippedCenteredStatistic n (g₀) (r₀) 512 (rho₀) y) ζ = (fun ζ =>
      if (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 then 0 else ((projectionW n (g₀)) ζ + (residualStatisticD n (r₀)) ζ) / (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ) ζ) ∧
      {ζ : Fin n → Ω | (clippedCenteredStatistic n (g₀) (r₀) 512 (rho₀) y) ζ ≠ (fun ζ =>
      if (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ = 0 then 0 else ((projectionW n (g₀)) ζ + (residualStatisticD n (r₀)) ζ) / (fun ζ => Real.sqrt (centeredSq n (g₀) (r₀) ζ)) ζ) ζ} ⊆
        (projectionGood n (g₀) y)ᶜ ∪ lowerStudentizerBad n (g₀) (r₀) y) ∧
0 < (∫ ζ, Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀)) ∧
Integrable (fun ζ => (fun ζ => y * (fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ + y ^ 2 * (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ) ζ * Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ)) (P₀) ∧
(∀ i : Fin n,
      Integrable (fun ζ => (fun ζ i =>
      (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i * (|(fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ - (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i| + y * |(studentizerClipBudget n (r₀) 512 (rho₀) y) ζ - (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i|)) ζ i * Real.exp ((fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ i)) (P₀)) ∧
0 ≤ (((∫ ζ, (fun ζ => y * (fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ + y ^ 2 * (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ) ζ * Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀)) +
        ∑ i : Fin n, ∫ ζ, (fun ζ i =>
      (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i * (|(fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ - (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i| + y * |(studentizerClipBudget n (r₀) 512 (rho₀) y) ζ - (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i|)) ζ i * Real.exp ((fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ i) ∂(P₀)) / (∫ ζ, Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀))) ∧
(((∫ ζ, (fun ζ => y * (fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ + y ^ 2 * (studentizerClipBudget n (r₀) 512 (rho₀) y) ζ) ζ * Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀)) +
        ∑ i : Fin n, ∫ ζ, (fun ζ i =>
      (fun ζ i => min |y * (fun i ζ => (g₀) (ζ i) / (N)) i ζ| 1) ζ i * (|(fun ζ => |(residualStatisticD n (r₀)) ζ|) ζ - (fun ζ i => |(residualStatisticDDeleted n (r₀)) ζ i|) ζ i| + y * |(studentizerClipBudget n (r₀) 512 (rho₀) y) ζ - (studentizerClipBudgetDeleted n (r₀) 512 (rho₀) y) ζ i|)) ζ i * Real.exp ((fun ζ i =>
      ∑ j ∈ Finset.univ.erase i, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ i) ∂(P₀)) / (∫ ζ, Real.exp ((fun ζ =>
      ∑ j : Fin n, (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ - (y * (fun i ζ => (g₀) (ζ i) / (N)) j ζ) ^ 2 / 2)) ζ) ∂(P₀))) ≤
      64 * (Real.exp (1 / 2 : ℝ)) ^ 4 * (1 + 4 * (512 : ℝ)) * (1 + (rho₀)) *
        (1 + y) ^ 3 / Real.sqrt (n : ℝ)
```

完整右端／证明体：
```lean
(hstatistics n hn y hy hywindow).1
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hhalf — 第251–254行

UTF8字节[14199,14440)；完整声明片段SHA256 `58d5cdf95a312cd92ee668cccd561f89b40938046da5268ca3efa9360ae8cd02`。

完整依赖类型：
```lean
∀ (ξ : Fin n → Ω),
(1 / 2 : ℝ) ≤ 1 + D2 ξ
```

完整右端／证明体：
```lean
by
    have hx := (hglobal ξ).1
    change (1 / 2 : ℝ) ≤ 1 + clippedCenteredDelta n g₀ r₀ 512 rho₀ y ξ at hx
    simpa only [hgpoint, hrpoint, hrhopoint] using hx
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hx — 第252–252行

UTF8字节[14268,14298)；完整声明片段SHA256 `c45b3512e38fdec93d56688a13c18a0ddff29d7a2b5c40c9c906e51aa54c19cc`。

完整依赖类型：
```lean
(1 / 2 : ℝ) ≤ 1 + clippedCenteredDelta n g₀ r₀ 512 rho₀ y ξ
```

完整右端／证明体：
```lean
(hglobal ξ).1
```

词法范围：{"enclosing": "proof of hhalf", "contextFromLine": 251, "visibleThroughLine": 254, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hTcliplaw — 第255–258行

UTF8字节[14440,14639)；完整声明片段SHA256 `292181766aca2fe47304ebe35a21f9a0a68ab07965a1dccc279973986d75b27a`。

完整依赖类型：
```lean
@Measure.map (Fin n → Ω) ℝ mN₀ (borel ℝ) Tclip P₀ =
        @Measure.map (Fin n → Ω) ℝ mN (borel ℝ) Tclip P
```

完整右端／证明体：
```lean
hfiniteLaw ℝ (borel ℝ) Tclip hTclipm
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hTclipOriginal — 第259–260行

UTF8字节[14639,14723)；完整声明片段SHA256 `56aa3b6dae16be5c263ac79c1ede808659cb289be8724d64b7f04ae5c9c0f856`。

完整依赖类型：
```lean
Measurable[mN, borel ℝ] Tclip
```

完整右端／证明体：
```lean
hTclipm.comp hidmeas
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hZ0Original — 第261–261行

UTF8字节[14723,14790)；完整声明片段SHA256 `636fea4ef6f1addf4a270d8745bf544284319e5a2799aadcd62c5bed6ce9ad4e`。

完整依赖类型：
```lean
MeasurableSet[mN] Z0
```

完整右端／证明体：
```lean
hZ0m.preimage hidmeas
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hZ0law — 第262–264行

UTF8字节[14790,14886)；完整声明片段SHA256 `64848d65d4087f16b21380e19e6edb8aaa3a535712a15e18faff61bd1e7d2e95`。

完整依赖类型：
```lean
P₀ Z0 = P Z0
```

完整右端／证明体：
```lean
by
    rw [hP₀map]
    exact Measure.map_apply hidmeas hZ0m
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hZ0real — 第265–267行

UTF8字节[14886,15012)；完整声明片段SHA256 `1f391ed57655382f09af3cce8bf199782c4a5bb6e98575e48ab47b4dfad09da2`。

完整依赖类型：
```lean
P₀.real Z0 = p0
```

完整右端／证明体：
```lean
by
    change (P₀ Z0).toReal = (P Z0).toReal
    exact congrArg ENNReal.toReal hZ0law
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hn1 — 第268–268行

UTF8字节[15012,15070)；完整声明片段SHA256 `2601c71e484af3a698287bee8d1a6f8f34af6de28651497a4c9d8f48d1f8b959`。

完整依赖类型：
```lean
1 ≤ n
```

完整右端／证明体：
```lean
le_trans (by decide : 1 ≤ 4) hn
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hnpos — 第269–269行

UTF8字节[15070,15132)；完整声明片段SHA256 `cd5a0a249e10ca4740f63075c8b5a89aa7b01b16ee297c7c2c617e9618665a28`。

完整依赖类型：
```lean
0 < n
```

完整右端／证明体：
```lean
lt_of_lt_of_le (by decide : 0 < 4) hn
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hnRpos — 第270–270行

UTF8字节[15132,15188)；完整声明片段SHA256 `bb09dd602bbf61cf7a8aede213da0f30f80fbc96a46419ca90594b2af74b2410`。

完整依赖类型：
```lean
0 < (n : ℝ)
```

完整右端／证明体：
```lean
Nat.cast_pos.mpr hnpos
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hnRne — 第271–271行

UTF8字节[15188,15238)；完整声明片段SHA256 `af6ba31a5e787e9a9c5b26f71aa84549e78132f2b80cb8640888f43aff93d099`。

完整依赖类型：
```lean
(n : ℝ) ≠ 0
```

完整右端／证明体：
```lean
ne_of_gt hnRpos
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hNsq — 第272–272行

UTF8字节[15238,15306)；完整声明片段SHA256 `251be13cab3420aed9f65cfc4e0d4e0866184cb0d99b62fd63ea373b4548f224`。

完整依赖类型：
```lean
N ^ 2 = (n : ℝ)
```

完整右端／证明体：
```lean
Real.sq_sqrt (Nat.cast_nonneg n)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hO — 第273–273行

UTF8字节[15306,15372)；完整声明片段SHA256 `befc384e0463ed1e8bb6838cfff3fd55cf1007be69b075db6afe888b5574cae6`。

完整依赖类型：
```lean
∀ (i : Fin n),
Measurable (O i)
```

完整右端／证明体：
```lean
measurable_pi_apply i
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hcoord — 第274–275行

UTF8字节[15372,15498)；完整声明片段SHA256 `1ab12df8f81e39f4cff2477412e67ae7c7dcb03088bb943d09e01d21e0ec770a`。

完整依赖类型：
```lean
∀ (i : Fin n),
MeasurePreserving (O i) P₀ μ₀
```

完整右端／证明体：
```lean
measurePreserving_eval (μ := fun _ : Fin n => μ₀) i
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hQid — 第276–278行

UTF8字节[15498,15549)；完整声明片段SHA256 `7323babeb22a98914705e68681e66caf0c937122741afc23fce2a91d2d43a5ec`。

完整依赖类型：
```lean
Q = id
```

完整右端／证明体：
```lean
by
    funext ξ i
    rfl
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let coordinateMarginal — 第279–280行

UTF8字节[15549,15672)；完整声明片段SHA256 `1750f5a20c3b6a24a3220505a2103b360be0f2c925628d24c318c4c5a2f5047e`。

完整依赖类型：
```lean
Fin n → @Measure Ω m₀
```

完整右端／证明体：
```lean
fun i => @Measure.map (Fin n → Ω) Ω mN₀ m₀ (O i) P₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let ambientProductLaw — 第281–283行

UTF8字节[15672,15860)；完整声明片段SHA256 `015d84962527494167cac97d0264074ed599be6380d1d5dd93759555b69ad9a5`。

完整依赖类型：
```lean
@Measure (Fin n → Ω) mN₀
```

完整右端／证明体：
```lean
@Measure.pi (Fin n) (fun _ : Fin n => Ω) (inferInstance : Fintype (Fin n))
      (fun _ : Fin n => m₀) coordinateMarginal
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hcoordMap — 第284–284行

UTF8字节[15860,15935)；完整声明片段SHA256 `02ff654c02fb0ee23821de4e66e2477155b0934fa0f27b74fdb62e153f81c771`。

完整依赖类型：
```lean
∀ (i : Fin n),
P₀.map (O i) = μ₀
```

完整右端／证明体：
```lean
(hcoord i).map_eq
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hproduct — 第285–289行

UTF8字节[15935,16072)；完整声明片段SHA256 `fc0e219ec5c5085f5224dad342bacb100ec1694fc2b6f0f53def2050ef29dcbe`。

完整依赖类型：
```lean
ambientProductLaw = P₀
```

完整右端／证明体：
```lean
by
    dsimp only [ambientProductLaw, P₀]
    congr 1
    funext i
    exact hcoordMap i
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hOindep — 第290–293行

UTF8字节[16072,16279)；完整声明片段SHA256 `b0678b9fecfcf316d6aa0863c4ae026ecccd10b7ca22df48a9a4abdf2c09432a`。

完整依赖类型：
```lean
iIndepFun O P₀
```

完整右端／证明体：
```lean
by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hO i).aemeasurable)).2
    change Measure.map Q P₀ = ambientProductLaw
    rw [hQid, Measure.map_id, hproduct]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have pullbackIntegral — 第294–299行

UTF8字节[16279,16603)；完整声明片段SHA256 `0141b3c511cdffe30c1fcfa46807fb51b33ac8e615c7d6881b7a685b852b10c0`。

完整依赖类型：
```lean
∀ (i : Fin n) (f : Ω → ℝ) (hf : Measurable f),
(∫ ξ : Fin n → Ω, f (ξ i) ∂P₀) = ∫ o, f o ∂μ₀
```

完整右端／证明体：
```lean
by
    calc
      _ = ∫ o, f o ∂P₀.map (O i) :=
        (integral_map (hcoord i).measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [hcoordMap i]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let squareProjection — 第300–300行

UTF8字节[16603,16659)；完整声明片段SHA256 `ce280c89dba2cd77364c9ead26498e69e03dbf6b280eded779be1c65a3dcca92`。

完整依赖类型：
```lean
Ω → ℝ
```

完整右端／证明体：
```lean
fun o => g o ^ 2
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hgcoordm — 第301–301行

UTF8字节[16659,16733)；完整声明片段SHA256 `0f79573c0b58b8251ff359d3d495da29707ef34a41863bee50de229a15ecb24e`。

完整依赖类型：
```lean
∀ (i : Fin n),
Measurable (gcoord i)
```

完整右端／证明体：
```lean
hgmeas.div_const N
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hgcoord₂ — 第302–304行

UTF8字节[16733,16949)；完整声明片段SHA256 `7f6331266a24c1938ee18ca1598fb2fc54ba7761afa0d47b7c215e069a5f251c`。

完整依赖类型：
```lean
∀ (i : Fin n),
MemLp (fun ξ => gcoord i (O i ξ)) 2 P₀
```

完整右端／证明体：
```lean
by
    simpa only [gcoord, O, div_eq_mul_inv, Function.comp_def] using
      ((hg₂.comp_measurePreserving (hcoord i)).mul_const N⁻¹)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hgcoordmean — 第305–307行

UTF8字节[16949,17143)；完整声明片段SHA256 `3be93f78e191b7f10f8f822022e3a1e9809d9365f9905ca8962ad26707a20e63`。

完整依赖类型：
```lean
∀ (i : Fin n),
(∫ ξ, gcoord i (O i ξ) ∂P₀) = 0
```

完整右端／证明体：
```lean
by
    change (∫ ξ, g (ξ i) / N ∂P₀) = 0
    rw [integral_div, pullbackIntegral i g hgmeas, hgmean, zero_div]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hgcoordsecond — 第308–313行

UTF8字节[17143,17436)；完整声明片段SHA256 `face5a4533c918c568995872b8f88b700339ed9dd6acd8973a9b24cf8785b408`。

完整依赖类型：
```lean
∀ (i : Fin n),
(∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1 / (n : ℝ)
```

完整右端／证明体：
```lean
by
    change (∫ ξ, (g (ξ i) / N) ^ 2 ∂P₀) = 1 / (n : ℝ)
    simp_rw [div_pow]
    rw [integral_div, pullbackIntegral i squareProjection (hgmeas.pow_const 2),
      hgsecond, hNsq]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hgcoordenergy — 第314–317行

UTF8字节[17436,17660)；完整声明片段SHA256 `c542d684879bcf28382af9079f13cfa03a6de2ab608d8750b274a925adbf9983`。

完整依赖类型：
```lean
(∑ i : Fin n, ∫ ξ, (gcoord i (O i ξ)) ^ 2 ∂P₀) = 1
```

完整右端／证明体：
```lean
by
    simp_rw [hgcoordsecond]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnRne]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hW0eq — 第318–321行

UTF8字节[17660,17787)；完整声明片段SHA256 `5c62f2cf167313d27e11bf1519deea1805329b49ce8348d17e842646af971922`。

完整依赖类型：
```lean
W0 = projectionW n g
```

完整右端／证明体：
```lean
by
    funext ξ
    dsimp only [W0, gcoord, O, projectionW, N]
    rw [Finset.sum_div]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hV0eq — 第322–328行

UTF8字节[17787,18070)；完整声明片段SHA256 `431111ae149e3668a5f2940c429633b42d636ecd4ab80f1a0fba479a939a2afb`。

完整依赖类型：
```lean
V0 = projectionV n g
```

完整右端／证明体：
```lean
by
    funext ξ
    dsimp only [V0, projectionV, projectionEnergy]
    apply congrArg Real.sqrt
    change (∑ i : Fin n, (g (ξ i) / N) ^ 2) =
      (∑ i : Fin n, g (ξ i) ^ 2) / (n : ℝ)
    simp only [div_pow, ← Finset.sum_div, hNsq]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hT0eq — 第329–332行

UTF8字节[18070,18213)；完整声明片段SHA256 `9b840107b6afcdd4c22a379747e233bc22862708b67178d36e0bc33837b0a404`。

完整依赖类型：
```lean
T0 = Tclip
```

完整右端／证明体：
```lean
by
    funext ξ
    simp only [T0, hW0eq, hV0eq, hQid, id_eq, Tclip, clippedCenteredStatistic,
      κ, D1, D2]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hD2positive — 第333–334行

UTF8字节[18213,18335)；完整声明片段SHA256 `51680b61fa91a4c8d28a1dbcd5a600cc836628ea3355edc7ff91bcf372101796`。

完整依赖类型：
```lean
∀ (ξ : Fin n → Ω),
0 < 1 + D2 ξ
```

完整右端／证明体：
```lean
lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hhalf ξ)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hD2pos — 第335–336行

UTF8字节[18335,18456)；完整声明片段SHA256 `155e77e3517537976c28d3a0f3a2abed2bf8ed32f820ea4102b720fde1e65b43`。

完整依赖类型：
```lean
∀ᵐ ξ ∂P₀, 0 < 1 + D2 (Q ξ)
```

完整右端／证明体：
```lean
by
    simpa only [hQid, id_eq] using ae_of_all P₀ hD2positive
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let ambientA — 第337–337行

UTF8字节[18456,18496)；完整声明片段SHA256 `ce7c24980fe5074e9e253a3342df702b665e566c36969c5d63ec4b99d0213537`。

完整依赖类型：
```lean
Type u
```

完整右端／证明体：
```lean
Fin n → Ω
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let ambientX — 第338–338行

UTF8字节[18496,18553)；完整声明片段SHA256 `dbae00e3ab2332196c6b49f3ce543391d6bbfa7c913a736001dd849daff653c1`。

完整依赖类型：
```lean
Fin n → Type u
```

完整右端／证明体：
```lean
fun _ : Fin n => Ω
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## let ambientMX — 第339–339行

UTF8字节[18553,18640)；完整声明片段SHA256 `f687fe46116ba1ed2709c213e916bbd9391579302a0dbc839ba902764ea36eb7`。

完整依赖类型：
```lean
∀ i : Fin n, MeasurableSpace (ambientX i)
```

完整右端／证明体：
```lean
fun _ : Fin n => m₀
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@340 — 第340–340行

UTF8字节[18640,18706)；完整声明片段SHA256 `16f28678844b675b9703a65a5dd23deb37c502ad1f08207a695e2052b11d3dde`。

完整依赖类型：
```lean
∀ i : Fin n, MeasurableSpace (ambientX i)
```

完整右端／证明体：
```lean
ambientMX
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## letI anonymous-instance@341 — 第341–341行

UTF8字节[18706,18794)；完整声明片段SHA256 `ce2966790372ff73cd5e6c6847feaa658042fa516e95f9460a95aeace7d1d725`。

完整依赖类型：
```lean
∀ i : Fin n, MeasurableSpace.CountablyGenerated (ambientX i)
```

完整右端／证明体：
```lean
fun _ => hcg
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hcanonical — 第342–345行

UTF8字节[18794,19085)；完整声明片段SHA256 `cf6015ea7ffffd4345db3c89ad340787009ffebd699bb3eaf8d98ecfc320c39c`。

完整依赖类型：
```lean
(IsProbabilityMeasure ν) ∧
(MeasurePreserving Q P₀ P₀) ∧
(MeasurePreserving q ν P₀) ∧
((1 / 2 : ℝ) < s) ∧
((∀ (i : Fin n) (x : Fin n → Ω × ℝ), η i x = ηlocal i (x i))) ∧
(iIndepFun η ν) ∧
((∀ i : Fin n, Measurable (η i) ∧ MemLp (η i) 2 ν)) ∧
((∀ i : Fin n, Integrable (η i) ν ∧ Integrable (fun x => (η i x) ^ 2) ν)) ∧
((∀ i : Fin n, (∫ x, η i x ∂ν) = 0)) ∧
((∑ i : Fin n, ∫ x, (η i x) ^ 2 ∂ν) = 1) ∧
((∀ (i : Fin n) (t : ℝ), ν {x : Fin n → Ω × ℝ | η i x = t} = 0)) ∧
(ν {x : Fin n → Ω × ℝ | Vη x = 0} = 0) ∧
(∀ᵐ x ∂ν, 0 < Vη x) ∧
(Measurable[mAug, borel (Fin n → ℝ)] C) ∧
(MeasurableSpace.comap C (borel (Fin n → ℝ)) = mAug) ∧
((∀ (H : (Fin n → Ω × ℝ) → ℝ), Measurable H →
          ∃ F : (Fin n → ℝ) → ℝ, Measurable[borel (Fin n → ℝ), borel ℝ] F ∧
            ∀ x : Fin n → Ω × ℝ, H x = F (C x))) ∧
((∀ (i : Fin n) (d : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ), Measurable d →
          ∃ F : ({j : Fin n // j ≠ i} → ℝ) → ℝ,
            Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel ℝ] F ∧
            (∀ y : {j : Fin n // j ≠ i} → Ω × ℝ,
              d y = F (fun j => ηlocal j.val (y j))) ∧
            Measurable[borel (Fin n → ℝ), borel ℝ]
              (fun t : Fin n → ℝ => F (fun j => t j.val)) ∧
            ∀ x : Fin n → Ω × ℝ, d (fun j => x j.val) = F (fun j => η j.val x))) ∧
((∃ G2 : (Fin n → ℝ) → ℝ,
          Measurable[borel (Fin n → ℝ), borel ℝ] G2 ∧
          (∀ x : Fin n → Ω × ℝ, D2 (q x) = G2 (C x)) ∧
          ∀ z : ℝ, ∃ G1 : (Fin n → ℝ) → ℝ,
            Measurable[borel (Fin n → ℝ), borel ℝ] G1 ∧
            ∀ x : Fin n → Ω × ℝ, Dη z x = G1 (C x))) ∧
(Measurable T0) ∧
(∀ z : ℝ, Measurable (Tη z)) ∧
(MeasurableSet[mN₀] {ξ : Fin n → Ω | V0 ξ = 0}) ∧
(MeasurableSet Z) ∧
(ν Z = P₀ {ξ : Fin n → Ω | V0 ξ = 0}) ∧
(ν.real Z = P₀.real {ξ : Fin n → Ω | V0 ξ = 0}) ∧
((∀ (z : ℝ) (x : Fin n → Ω × ℝ),
          Wη x + Dη z x - z * Vη x * b x = W x + D1 (q x) - z * V x * b x)) ∧
(∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
MeasurableSet[mN₀] {ξ : Fin n → Ω | R (T0 ξ) z} ∧
MeasurableSet[mN₀] {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
MeasurableSet (Eη R z) ∧
ν (Eη R z) = P₀ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
(∀ᵐ ξ ∂P₀, ξ ∈ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) → V0 ξ = 0) ∧
P₀ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) ≤ P₀ {ξ : Fin n → Ω | V0 ξ = 0} ∧
|P₀.real {ξ : Fin n → Ω | R (T0 ξ) z} - ν.real (Eη R z)| ≤ P₀.real {ξ : Fin n → Ω | V0 ξ = 0})
```

完整右端／证明体：
```lean
Shao.OQ6.AmbientCanonicalCodingTransport.ambient_canonical_normalized_observation_consumer
      (X := ambientX) P₀ n hn1 O hO hOindep gcoord hgcoordm hgcoord₂ hgcoordmean
      hgcoordenergy D1 D2 hD1m hD2m κ (by exact measurable_const) hD2pos ε hε hεsmall
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hpositiveDenominator — 第353–356行

UTF8字节[19436,19679)；完整声明片段SHA256 `806d1888d754597c48e91c1b5c07b8e1d16e9bddd5665bcec71a233c816c556c`。

完整依赖类型：
```lean
∀ᵐ x ∂ν, 0 < Vη x ∧ 0 < b x ∧ 0 < Vη x * b x
```

完整右端／证明体：
```lean
by
    filter_upwards [hVηpos] with x hx
    have hbpos : 0 < b x := Real.sqrt_pos.mpr (hD2positive (q x))
    exact ⟨hx, hbpos, mul_pos hx hbpos⟩
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hbpos — 第355–355行

UTF8字节[19569,19635)；完整声明片段SHA256 `d6d91cdeed28e5a8167d4bc3e1663ff413e370d287122280995caef1bdbaeb22`。

完整依赖类型：
```lean
0 < b x
```

完整右端／证明体：
```lean
Real.sqrt_pos.mpr (hD2positive (q x))
```

词法范围：{"enclosing": "proof of hpositiveDenominator", "contextFromLine": 353, "visibleThroughLine": 356, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hZcodedlaw — 第357–359行

UTF8字节[19679,19819)；完整声明片段SHA256 `56f9db10e49cdebecd958b941c66f887e9fc5e7d4a8ae7a43c075df2a8eecce3`。

完整依赖类型：
```lean
ν Z = P₀ Z0
```

完整右端／证明体：
```lean
by
    change ν Z = P₀ {ξ : Fin n → Ω | V0 ξ = 0} at hZlaw
    simpa only [hV0eq] using hZlaw
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hZcodedreal — 第360–362行

UTF8字节[19819,19962)；完整声明片段SHA256 `863abd103c7a43785bbf61a106858b7885d46edffebb60d57e04f3ce89180458`。

完整依赖类型：
```lean
ν.real Z = p0
```

完整右端／证明体：
```lean
by
    change (ν Z).toReal = (P Z0).toReal
    exact congrArg ENNReal.toReal (hZcodedlaw.trans hZ0law)
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hdeletedFactor — 第363–424行

UTF8字节[19962,23516)；完整声明片段SHA256 `f31d381e9e5d723e4ae896bad2392568078f629a319a2ffc70084367432ef824`。

完整依赖类型：
```lean
∀ (i : Fin n),
∃ Fdel : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ,
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ), borel (ℝ × ℝ × ℝ)] Fdel ∧
        ∀ x : Fin n → Ω × ℝ,
          (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) =
            Fdel (fun j : {j : Fin n // j ≠ i} => η j.val x)
```

完整右端／证明体：
```lean
by
    rcases hdeleted i with
      ⟨hcapi, hDdi, hJdi, hAdi, hBdi, htesti, E_i, hEmeas, hEpoint⟩
    have hEpointCurrent (ζ : Fin n → Ω) :
        (Ddel ζ i, Jdel ζ i, Bdelete ζ i) =
          E_i (fun j : {j : Fin n // j ≠ i} => ζ j.val) := by
      have hpoint := hEpoint ζ
      change (residualStatisticDDeleted n r₀ ζ i, residualEnergyJDeleted n r₀ ζ i,
        studentizerClipBudgetDeleted n r₀ 512 rho₀ y ζ i) = _ at hpoint
      simpa only [hrpoint, hrhopoint] using hpoint
    let retainedMeasurableSpace : MeasurableSpace ({j : Fin n // j ≠ i} → Ω) :=
      @MeasurableSpace.pi {j : Fin n // j ≠ i} (fun _ => Ω) (fun _ => m₀)
    let retainedAugmentedMeasurableSpace : MeasurableSpace ({j : Fin n // j ≠ i} → Ω × ℝ) :=
      @MeasurableSpace.pi {j : Fin n // j ≠ i} (fun _ => Ω × ℝ) (fun _ => mAugLocal)
    let retainedFirstProjection : ({j : Fin n // j ≠ i} → Ω × ℝ) →
        ({j : Fin n // j ≠ i} → Ω) := fun y j => (y j).1
    have hFirstMeas : Measurable retainedFirstProjection := by
      apply Measurable.of_eval
      intro j
      exact (measurable_pi_apply j).fst
    let dD : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ :=
      fun y => (E_i (retainedFirstProjection y)).1
    let dJ : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ :=
      fun y => (E_i (retainedFirstProjection y)).2.1
    let dB : ({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ :=
      fun y => (E_i (retainedFirstProjection y)).2.2
    have hTripleBorel :
        (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ)) =
          borel (ℝ × ℝ × ℝ) := BorelSpace.measurable_eq
    have hEproduct :
        Measurable[retainedMeasurableSpace,
          (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ))] E_i := by
      exact hEmeas
    have hdD : Measurable dD := hEproduct.fst.comp hFirstMeas
    have hdJ : Measurable dJ := hEproduct.snd.fst.comp hFirstMeas
    have hdB : Measurable dB := hEproduct.snd.snd.comp hFirstMeas
    rcases hretained i dD hdD with ⟨FD, hFDm, hFDpoint, hFDlift, hFDfull⟩
    rcases hretained i dJ hdJ with ⟨FJ, hFJm, hFJpoint, hFJlift, hFJfull⟩
    rcases hretained i dB hdB with ⟨FB, hFBm, hFBpoint, hFBlift, hFBfull⟩
    let FdelWitness : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ :=
      fun t => (FD t, FJ t, FB t)
    have hFdelBorel :
        Measurable[borel ({j : Fin n // j ≠ i} → ℝ),
          borel (ℝ × ℝ × ℝ)] FdelWitness := by
      rw [← hTripleBorel]
      exact hFDm.prodMk (hFJm.prodMk hFBm)
    refine ⟨FdelWitness, hFdelBorel, ?_⟩
    intro x
    have hDpoint : Ddel (q x) i = dD (fun j => x j.val) :=
      congrArg Prod.fst (hEpointCurrent (q x))
    have hJpoint : Jdel (q x) i = dJ (fun j => x j.val) :=
      congrArg Prod.fst (congrArg Prod.snd (hEpointCurrent (q x)))
    have hBpoint : Bdelete (q x) i = dB (fun j => x j.val) :=
      congrArg Prod.snd (congrArg Prod.snd (hEpointCurrent (q x)))
    change (Ddel (q x) i, Jdel (q x) i, Bdelete (q x) i) =
      (FD (fun j => η j.val x), FJ (fun j => η j.val x), FB (fun j => η j.val x))
    rw [hDpoint, hJpoint, hBpoint, hFDfull x, hFJfull x, hFBfull x]
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hEpointCurrent — 第371–377行

UTF8字节[20430,20837)；完整声明片段SHA256 `dea194f5b897a05e07bb55d0f6f270960f35314b35a4bf5025e7fdb73fa0e9c5`。

完整依赖类型：
```lean
∀ (ζ : Fin n → Ω),
(Ddel ζ i, Jdel ζ i, Bdelete ζ i) =
          E_i (fun j : {j : Fin n // j ≠ i} => ζ j.val)
```

完整右端／证明体：
```lean
by
      have hpoint := hEpoint ζ
      change (residualStatisticDDeleted n r₀ ζ i, residualEnergyJDeleted n r₀ ζ i,
        studentizerClipBudgetDeleted n r₀ 512 rho₀ y ζ i) = _ at hpoint
      simpa only [hrpoint, hrhopoint] using hpoint
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hpoint — 第374–374行

UTF8字节[20588,20620)；完整声明片段SHA256 `ca06c183378f97266a69c44876e2ba2c57e4e5d78678118350118c7f3b10a35e`。

完整依赖类型：
```lean
(residualStatisticDDeleted n r₀ ζ i, residualEnergyJDeleted n r₀ ζ i, studentizerClipBudgetDeleted n r₀ 512 rho₀ y ζ i) = E_i (fun j : {j : Fin n // j ≠ i} => ζ j.val)
```

完整右端／证明体：
```lean
hEpoint ζ
```

词法范围：{"enclosing": "proof of hEpointCurrent", "contextFromLine": 371, "visibleThroughLine": 377, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## let retainedMeasurableSpace — 第378–379行

UTF8字节[20837,21001)；完整声明片段SHA256 `10aa1f8ed49367bb786af38c1cde84a3ddaa81d9d1f704ca7d879fea3e876ef2`。

完整依赖类型：
```lean
MeasurableSpace ({j : Fin n // j ≠ i} → Ω)
```

完整右端／证明体：
```lean
@MeasurableSpace.pi {j : Fin n // j ≠ i} (fun _ => Ω) (fun _ => m₀)
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let retainedAugmentedMeasurableSpace — 第380–381行

UTF8字节[21001,21193)；完整声明片段SHA256 `84722071eac2263d6f7dc09f0a47b065f5a4a45e8784966f26a3037027b5743b`。

完整依赖类型：
```lean
MeasurableSpace ({j : Fin n // j ≠ i} → Ω × ℝ)
```

完整右端／证明体：
```lean
@MeasurableSpace.pi {j : Fin n // j ≠ i} (fun _ => Ω × ℝ) (fun _ => mAugLocal)
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let retainedFirstProjection — 第382–383行

UTF8字节[21193,21332)；完整声明片段SHA256 `d219c3fbf36a15737c9d224f419e0ca7cb39fbce72981ae855e6fefc02a8e7ec`。

完整依赖类型：
```lean
({j : Fin n // j ≠ i} → Ω × ℝ) →
        ({j : Fin n // j ≠ i} → Ω)
```

完整右端／证明体：
```lean
fun y j => (y j).1
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hFirstMeas — 第384–387行

UTF8字节[21332,21480)；完整声明片段SHA256 `4cc9d67e2d6e7e291aef464cd02144e716e6e30e12c03c2ecd9686bb1d1d2fb0`。

完整依赖类型：
```lean
Measurable retainedFirstProjection
```

完整右端／证明体：
```lean
by
      apply Measurable.of_eval
      intro j
      exact (measurable_pi_apply j).fst
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let dD — 第388–389行

UTF8字节[21480,21594)；完整声明片段SHA256 `6e37d0e316bd2aa8017969af9290730d044b0222ff00f501684d1aa8b9a103b0`。

完整依赖类型：
```lean
({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun y => (E_i (retainedFirstProjection y)).1
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let dJ — 第390–391行

UTF8字节[21594,21710)；完整声明片段SHA256 `c52af9d73f7391a12f5752d701440d4a00d8c76a1d22c3fbf9ff5d923b19b61c`。

完整依赖类型：
```lean
({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun y => (E_i (retainedFirstProjection y)).2.1
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let dB — 第392–393行

UTF8字节[21710,21826)；完整声明片段SHA256 `899a5c88bb848c5bff7d04f7f44cb74e6615ecb85dae08d46df6854ce14a534b`。

完整依赖类型：
```lean
({j : Fin n // j ≠ i} → Ω × ℝ) → ℝ
```

完整右端／证明体：
```lean
fun y => (E_i (retainedFirstProjection y)).2.2
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hTripleBorel — 第394–396行

UTF8字节[21826,21978)；完整声明片段SHA256 `71875cac1a7dbfe442edcbef019e4eb10259c54a62062484ed6efc28271334b9`。

完整依赖类型：
```lean
(inferInstance : MeasurableSpace (ℝ × ℝ × ℝ)) =
          borel (ℝ × ℝ × ℝ)
```

完整右端／证明体：
```lean
BorelSpace.measurable_eq
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hEproduct — 第397–400行

UTF8字节[21978,22137)；完整声明片段SHA256 `32c31d9bef4bc69cef8518db85e927be075b42b511021000528cf239ff93e2c3`。

完整依赖类型：
```lean
Measurable[retainedMeasurableSpace,
          (inferInstance : MeasurableSpace (ℝ × ℝ × ℝ))] E_i
```

完整右端／证明体：
```lean
by
      exact hEmeas
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hdD — 第401–401行

UTF8字节[22137,22199)；完整声明片段SHA256 `45c5564c9fe7ae3f512bcb68fa97c546ae1d1964d6ac357ba038be825e736e0a`。

完整依赖类型：
```lean
Measurable dD
```

完整右端／证明体：
```lean
hEproduct.fst.comp hFirstMeas
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hdJ — 第402–402行

UTF8字节[22199,22265)；完整声明片段SHA256 `39262d5e1d116975f793c137ededaaadc34a809319eb0a17f80a2011d86078a9`。

完整依赖类型：
```lean
Measurable dJ
```

完整右端／证明体：
```lean
hEproduct.snd.fst.comp hFirstMeas
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hdB — 第403–403行

UTF8字节[22265,22331)；完整声明片段SHA256 `3364638da23289491f1326e63aab67a3b06df9ba5069b4a940ce3795da921b87`。

完整依赖类型：
```lean
Measurable dB
```

完整右端／证明体：
```lean
hEproduct.snd.snd.comp hFirstMeas
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## let FdelWitness — 第407–408行

UTF8字节[22565,22679)；完整声明片段SHA256 `41a021dce764f180809f4c21ee14a55280f1626f64264b91367a703c9bcaa9cc`。

完整依赖类型：
```lean
({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ
```

完整右端／证明体：
```lean
fun t => (FD t, FJ t, FB t)
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hFdelBorel — 第409–413行

UTF8字节[22679,22886)；完整声明片段SHA256 `89255c57741fbe82546345209ee28defa9351cd65cc13112d0568c1f84717008`。

完整依赖类型：
```lean
Measurable[borel ({j : Fin n // j ≠ i} → ℝ),
          borel (ℝ × ℝ × ℝ)] FdelWitness
```

完整右端／证明体：
```lean
by
      rw [← hTripleBorel]
      exact hFDm.prodMk (hFJm.prodMk hFBm)
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hDpoint — 第416–417行

UTF8字节[22943,23049)；完整声明片段SHA256 `23f02de048eea3e3bc0c1bc55bb48c81c933719a3c2e1c81aa41aa094bd7465a`。

完整依赖类型：
```lean
Ddel (q x) i = dD (fun j => x j.val)
```

完整右端／证明体：
```lean
congrArg Prod.fst (hEpointCurrent (q x))
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hJpoint — 第418–419行

UTF8字节[23049,23175)；完整声明片段SHA256 `5e912219bf967b2c4619b7163c8b89237f737485cbb37cea887b2081bdb98893`。

完整依赖类型：
```lean
Jdel (q x) i = dJ (fun j => x j.val)
```

完整右端／证明体：
```lean
congrArg Prod.fst (congrArg Prod.snd (hEpointCurrent (q x)))
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hBpoint — 第420–421行

UTF8字节[23175,23304)；完整声明片段SHA256 `6ee4b9d81f6427232505bdaf423db1459e8d75adca9de1a61fd01a4f870131bb`。

完整依赖类型：
```lean
Bdelete (q x) i = dB (fun j => x j.val)
```

完整右端／证明体：
```lean
congrArg Prod.snd (congrArg Prod.snd (hEpointCurrent (q x)))
```

词法范围：{"enclosing": "proof of hdeletedFactor", "contextFromLine": 363, "visibleThroughLine": 424, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hcomparison0 — 第425–448行

UTF8字节[23516,24923)；完整声明片段SHA256 `e304eb7ee401fa835fc37d5d6bf3b781bac481d4eddcd0ea4d086f45ec2d6ef3`。

完整依赖类型：
```lean
∀ (z : ℝ) (R : ℝ → ℝ → Prop) (hR : R ∈ comparisons),
MeasurableSet[mN₀] (A0 R z) ∧ MeasurableSet[mN₀] (F0 R z) ∧
      MeasurableSet (Eη R z) ∧ ν (Eη R z) = P₀ (F0 R z) ∧
      (∀ᵐ ξ ∂P₀, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0) ∧
      P₀ (A0 R z ∆ F0 R z) ≤ P₀ Z0 ∧
      |P₀.real (A0 R z) - ν.real (Eη R z)| ≤ P₀.real Z0
```

完整右端／证明体：
```lean
by
    have hc := hcompare z R hR
    change
      MeasurableSet {ξ : Fin n → Ω | R (T0 ξ) z} ∧
      MeasurableSet {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ))
        (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
      MeasurableSet (Eη R z) ∧
      ν (Eη R z) = P₀ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ))
        (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
      (∀ᵐ ξ ∂P₀, ξ ∈ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆
        {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ))
          (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) → V0 ξ = 0) ∧
      P₀ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆
        {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ))
          (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) ≤
        P₀ {ξ : Fin n → Ω | V0 ξ = 0} ∧
      |P₀.real {ξ : Fin n → Ω | R (T0 ξ) z} - ν.real (Eη R z)| ≤
        P₀.real {ξ : Fin n → Ω | V0 ξ = 0} at hc
    simpa only [hT0eq, hW0eq, hV0eq, hQid, id_eq, A0, F0, Z0, Set.mem_setOf_eq] using hc
```

词法范围：{"enclosing": "whole theorem proof", "contextFromLine": 184, "visibleThroughLine": 523, "declarationIndent": 2, "coordinateConvention": "1-based inclusive"}

## have hc — 第431–431行

UTF8字节[23930,23961)；完整声明片段SHA256 `713708639fcfee4b9084fd85b96b4a54f746059ae77133377551dd84b537b47f`。

完整依赖类型：
```lean
MeasurableSet[mN₀] {ξ : Fin n → Ω | R (T0 ξ) z} ∧
MeasurableSet[mN₀] {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
MeasurableSet (Eη R z) ∧
ν (Eη R z) = P₀ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))} ∧
(∀ᵐ ξ ∂P₀, ξ ∈ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) → V0 ξ = 0) ∧
P₀ ({ξ : Fin n → Ω | R (T0 ξ) z} ∆ {ξ : Fin n → Ω | R (W0 ξ + D1 (Q ξ)) (z * V0 ξ * Real.sqrt (1 + D2 (Q ξ)))}) ≤ P₀ {ξ : Fin n → Ω | V0 ξ = 0} ∧
|P₀.real {ξ : Fin n → Ω | R (T0 ξ) z} - ν.real (Eη R z)| ≤ P₀.real {ξ : Fin n → Ω | V0 ξ = 0}
```

完整右端／证明体：
```lean
hcompare z R hR
```

词法范围：{"enclosing": "proof of hcomparison0", "contextFromLine": 425, "visibleThroughLine": 448, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hWηm — 第458–459行

UTF8字节[25507,25607)；完整声明片段SHA256 `f1b4ee9eeb83b68c7ee47b052ac68cb909c8fda26d1071f63e3a049f29fbaff2`。

完整依赖类型：
```lean
Measurable Wη
```

完整右端／证明体：
```lean
Finset.measurable_sum Finset.univ (fun i _ => (hηL2 i).1)
```

词法范围：{"enclosing": "bullet branch at 457", "contextFromLine": 457, "visibleThroughLine": 470, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hVηm — 第460–461行

UTF8字节[25607,25728)；完整声明片段SHA256 `ef645671f7745295def65248ed2cb6eee8a69546e595a6e06a9d25ae9462efb8`。

完整依赖类型：
```lean
Measurable Vη
```

完整右端／证明体：
```lean
(Finset.measurable_sum Finset.univ (fun i _ => ((hηL2 i).1).pow_const 2)).sqrt
```

词法范围：{"enclosing": "bullet branch at 457", "contextFromLine": 457, "visibleThroughLine": 470, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hWaugm — 第462–464行

UTF8字节[25728,25880)；完整声明片段SHA256 `93ab4d50354e6057b46089032597fdfa81a9e473a33d122fb028727a3ccc1345`。

完整依赖类型：
```lean
Measurable W
```

完整右端／证明体：
```lean
by
      exact Finset.measurable_sum Finset.univ
        (fun i _ => (hgcoordm i).comp ((measurable_pi_apply i).fst))
```

词法范围：{"enclosing": "bullet branch at 457", "contextFromLine": 457, "visibleThroughLine": 470, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hVaugm — 第465–467行

UTF8字节[25880,26053)；完整声明片段SHA256 `7dcbe5a597f49cb0fc688e9da44ed79129fcffa4b80f6dbfb83c4799335fd5c2`。

完整依赖类型：
```lean
Measurable V
```

完整右端／证明体：
```lean
by
      exact (Finset.measurable_sum Finset.univ
        (fun i _ => ((hgcoordm i).comp ((measurable_pi_apply i).fst)).pow_const 2)).sqrt
```

词法范围：{"enclosing": "bullet branch at 457", "contextFromLine": 457, "visibleThroughLine": 470, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hA0Original — 第473–473行

UTF8字节[26354,26429)；完整声明片段SHA256 `916f4eae2013b75af0c8bc5a49e6cecd3d515a2ba3bd9b03d3dad589a7067103`。

完整依赖类型：
```lean
MeasurableSet[mN] (A0 R z)
```

完整右端／证明体：
```lean
hA0m.preimage hidmeas
```

词法范围：{"enclosing": "bullet branch at 471", "contextFromLine": 471, "visibleThroughLine": 524, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hF0Original — 第474–474行

UTF8字节[26429,26504)；完整声明片段SHA256 `e2438f73f25d874bab8c4b7d23cdf40240f30dd3890374bd5fe991802061a6a4`。

完整依赖类型：
```lean
MeasurableSet[mN] (F0 R z)
```

完整右端／证明体：
```lean
hF0m.preimage hidmeas
```

词法范围：{"enclosing": "bullet branch at 471", "contextFromLine": 471, "visibleThroughLine": 524, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hF0law — 第475–477行

UTF8字节[26504,26618)；完整声明片段SHA256 `1049f1e949e74e4e6ab87ab24434f62697e097a7a9a9daa5d758d1ea1c2d42c7`。

完整依赖类型：
```lean
P₀ (F0 R z) = P (F0 R z)
```

完整右端／证明体：
```lean
by
      rw [hP₀map]
      exact Measure.map_apply hidmeas hF0m
```

词法范围：{"enclosing": "bullet branch at 471", "contextFromLine": 471, "visibleThroughLine": 524, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hA0law — 第478–480行

UTF8字节[26618,26732)；完整声明片段SHA256 `b3ce79ca7413e947cab06eb2985ecffd1ccc5ae056f7bbf741ec387852b4e827`。

完整依赖类型：
```lean
P₀ (A0 R z) = P (A0 R z)
```

完整右端／证明体：
```lean
by
      rw [hP₀map]
      exact Measure.map_apply hidmeas hA0m
```

词法范围：{"enclosing": "bullet branch at 471", "contextFromLine": 471, "visibleThroughLine": 524, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hA0real — 第481–483行

UTF8字节[26732,26895)；完整声明片段SHA256 `5367fbb686be96ec59118452af3039c674be57ed32d6be1abe152bbee3201c0d`。

完整依赖类型：
```lean
P₀.real (A0 R z) = P.real (A0 R z)
```

完整右端／证明体：
```lean
by
      change (P₀ (A0 R z)).toReal = (P (A0 R z)).toReal
      exact congrArg ENNReal.toReal hA0law
```

词法范围：{"enclosing": "bullet branch at 471", "contextFromLine": 471, "visibleThroughLine": 524, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hpoint — 第484–519行

UTF8字节[26895,28661)；完整声明片段SHA256 `591987d5e446b0ee3a5e7cbb226cee73670af0e71ec1844eac5f332a7afba01c`。

完整依赖类型：
```lean
∀ ξ : Fin n → Ω, ξ ∈ (A0 R z ∆ F0 R z) → ξ ∈ Z0
```

完整右端／证明体：
```lean
by
      intro ξ hdiff
      by_contra hnot
      have hvne : projectionV n g ξ ≠ 0 := hnot
      have hvpos : 0 < projectionV n g ξ :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hvne)
      have hbpos : 0 < Real.sqrt (1 + D2 ξ) := Real.sqrt_pos.mpr (hD2positive ξ)
      have hden : 0 < projectionV n g ξ * Real.sqrt (1 + D2 ξ) := mul_pos hvpos hbpos
      have hTeq : Tclip ξ = (projectionW n g ξ + D1 ξ) /
          (projectionV n g ξ * Real.sqrt (1 + D2 ξ)) := by
        simp only [Tclip, clippedCenteredStatistic, if_neg hvne, D1, D2]
      have hrel : R (Tclip ξ) z ↔ R (projectionW n g ξ + D1 ξ)
          (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ)) := by
        rw [hTeq]
        rw [mul_assoc]
        change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
          R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
          R = (fun a b : ℝ => a = b) at hR
        rcases hR with rfl | rfl | rfl | rfl | rfl
        · exact div_le_iff₀ hden
        · exact div_lt_iff₀ hden
        · exact le_div_iff₀ hden
        · exact lt_div_iff₀ hden
        · constructor
          · intro heq
            apply le_antisymm
            · exact (div_le_iff₀ hden).mp heq.le
            · exact (le_div_iff₀ hden).mp heq.ge
          · intro heq
            apply le_antisymm
            · exact (div_le_iff₀ hden).mpr heq.le
            · exact (le_div_iff₀ hden).mpr heq.ge
      have hevents : ξ ∈ A0 R z ↔ ξ ∈ F0 R z := hrel
      rcases Set.mem_symmDiff.mp hdiff with ⟨ha, hf⟩ | ⟨hf, ha⟩
      · exact hf (hevents.mp ha)
      · exact ha (hevents.mpr hf)
```

词法范围：{"enclosing": "bullet branch at 471", "contextFromLine": 471, "visibleThroughLine": 524, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}

## have hvne — 第487–487行

UTF8字节[27025,27076)；完整声明片段SHA256 `7294f9f8502694772c708102c926cc93b7f7c8940b7fa33bf19dc3977898db88`。

完整依赖类型：
```lean
projectionV n g ξ ≠ 0
```

完整右端／证明体：
```lean
hnot
```

词法范围：{"enclosing": "proof of hpoint", "contextFromLine": 484, "visibleThroughLine": 519, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## have hvpos — 第488–489行

UTF8字节[27076,27180)；完整声明片段SHA256 `8f79fac7f9effa751c9fb6f60f43afed323599a8424fa7f9f28926170d4f4949`。

完整依赖类型：
```lean
0 < projectionV n g ξ
```

完整右端／证明体：
```lean
lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hvne)
```

词法范围：{"enclosing": "proof of hpoint", "contextFromLine": 484, "visibleThroughLine": 519, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## have hbpos — 第490–490行

UTF8字节[27180,27263)；完整声明片段SHA256 `581c83fbc905985b1308fe0ec21e58c6580096583718ebbf8ad5d606df71e917`。

完整依赖类型：
```lean
0 < Real.sqrt (1 + D2 ξ)
```

完整右端／证明体：
```lean
Real.sqrt_pos.mpr (hD2positive ξ)
```

词法范围：{"enclosing": "proof of hpoint", "contextFromLine": 484, "visibleThroughLine": 519, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## have hden — 第491–491行

UTF8字节[27263,27351)；完整声明片段SHA256 `6532a0532996d6e0038865be8ea2169db7ecdb5979a61574fe643031d2698739`。

完整依赖类型：
```lean
0 < projectionV n g ξ * Real.sqrt (1 + D2 ξ)
```

完整右端／证明体：
```lean
mul_pos hvpos hbpos
```

词法范围：{"enclosing": "proof of hpoint", "contextFromLine": 484, "visibleThroughLine": 519, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## have hTeq — 第492–494行

UTF8字节[27351,27545)；完整声明片段SHA256 `013d9047ff35132dd1517515872223ca5d62e64c45b35454e6597b7f268f648a`。

完整依赖类型：
```lean
Tclip ξ = (projectionW n g ξ + D1 ξ) /
          (projectionV n g ξ * Real.sqrt (1 + D2 ξ))
```

完整右端／证明体：
```lean
by
        simp only [Tclip, clippedCenteredStatistic, if_neg hvne, D1, D2]
```

词法范围：{"enclosing": "proof of hpoint", "contextFromLine": 484, "visibleThroughLine": 519, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## have hrel — 第495–515行

UTF8字节[27545,28459)；完整声明片段SHA256 `e2244ef9f139294d74b774bbc94c4c9966289dc716cf41ec0342a0888c304c3c`。

完整依赖类型：
```lean
R (Tclip ξ) z ↔ R (projectionW n g ξ + D1 ξ)
          (z * projectionV n g ξ * Real.sqrt (1 + D2 ξ))
```

完整右端／证明体：
```lean
by
        rw [hTeq]
        rw [mul_assoc]
        change R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨
          R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨
          R = (fun a b : ℝ => a = b) at hR
        rcases hR with rfl | rfl | rfl | rfl | rfl
        · exact div_le_iff₀ hden
        · exact div_lt_iff₀ hden
        · exact le_div_iff₀ hden
        · exact lt_div_iff₀ hden
        · constructor
          · intro heq
            apply le_antisymm
            · exact (div_le_iff₀ hden).mp heq.le
            · exact (le_div_iff₀ hden).mp heq.ge
          · intro heq
            apply le_antisymm
            · exact (div_le_iff₀ hden).mpr heq.le
            · exact (le_div_iff₀ hden).mpr heq.ge
```

词法范围：{"enclosing": "proof of hpoint", "contextFromLine": 484, "visibleThroughLine": 519, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## have hevents — 第516–516行

UTF8字节[28459,28520)；完整声明片段SHA256 `c1d1be0f6de40b49fa7af34f9c2988a383d6ab9f621371c4784d9e59718e9ac8`。

完整依赖类型：
```lean
ξ ∈ A0 R z ↔ ξ ∈ F0 R z
```

完整右端／证明体：
```lean
hrel
```

词法范围：{"enclosing": "proof of hpoint", "contextFromLine": 484, "visibleThroughLine": 519, "declarationIndent": 6, "coordinateConvention": "1-based inclusive"}

## have hreal — 第520–521行

UTF8字节[28661,28780)；完整声明片段SHA256 `65119c2276be024a5168b2dca850219568b7b4a5dc08c5612906f35cf2147051`。

完整依赖类型：
```lean
|P.real (A0 R z) - ν.real (Eη R z)| ≤ p0
```

完整右端／证明体：
```lean
by
      simpa only [hA0real, hZ0real] using hreal₀
```

词法范围：{"enclosing": "bullet branch at 471", "contextFromLine": 471, "visibleThroughLine": 524, "declarationIndent": 4, "coordinateConvention": "1-based inclusive"}
