# Pure fixed-time killed-cosine normalization

`Shao.OQ4.BrownianFixedTimeNormalization.fixed_time_normalization` proves that the actual inverse cosine-coefficient power times the actual killed cosine action at `floor(h^2)`, starting at zero, tends to one as the real height tends to infinity. The public assumptions are an actual real probability law, an integrable third absolute moment, mean zero and second moment one. A Brownian process, a supplied weak limit and the desired normalization are not public assumptions.

`free_cosine_power_tendsto` gives the free factor's limit, and `killed_cosine_tendsto` gives the killed action's matching limit `exp(-pi^2/8)`. `varying_row_fixed_time_limits` proves all three limits for varying laws with a common third-moment bound, paying the later long-time bridge's row uniformity.

The proof derives lower-moment integrability, eventual positivity of the actual cosine coefficient and the logarithmic/floor error estimates. It then uses the actual finite killed-test bridge, the qualified varying-row killed-functional limit and an internally instantiated canonical Brownian process. The qualified Brownian killed-cosine identity supplies the nonzero limiting denominator. The positive-height sequence criterion yields the real-height limit.

All 20 explicit heads, one private row-length value and ten imports were frozen before implementation. The native environment contains 42 owned declarations, its one transparent value and 22 generated theorem types. The first successful whole-source invocation checks the full kernel, audits the unfiltered transitive type/value closure and retains the original reusable object. Independent complete review and exact kernel/object receipts accompany the source; no unchanged producer is recompiled for publication.

This proves source B1 and the explicit common-moment row version. Primitive survival/concentration estimates, long-time K/Kv and the general OQ4 root groups remain open until their separate source-bound dependencies close.
