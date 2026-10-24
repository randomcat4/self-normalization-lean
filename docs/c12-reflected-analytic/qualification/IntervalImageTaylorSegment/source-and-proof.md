# Interval compensated Taylor segment and source profile

Source4302–4315, with original profiles4215–4219. Complete imports/six full theorem heads frozen before implementation; no definitions. UTF-8 no BOM LF before kernel001.

The path (y+θb,T−θb²) stays in the closed interval for θ∈[0,1] and is strictly interior for θ<1 when the initial y is interior and y+b is closed. This follows by applying already-qualified halfline segment-distance positivity to the upper gap with displacement b and lower gap with displacement−b. Time bounds T/2≤S≤T and S>0 are reused unchanged from the same qualified segment interface.

The upper wall transport uses u=a−y,v=a−z,d=z−y,b. The lower uses u=a+y,v=a+z,d=−(z−y),displacement−b. The negative displacement has identical energy and |b|. Exact affine identities and abs_neg give the same displaced distance |z−(y+θb)|. Adding the two already-qualified halfline transport inequalities yields the original intervalIncrementProfile Pb, with constant2^r*3^j and the original time/distance exponents. No new profile definition replaces the actual source Pb.

The identity (4/√S*(1+|d|/√S))^j/S^l=4^j*(1/√S)^(j+2l)*(1+|d|/√S)^j follows from (√S)²=S at S>0 and exact natural-power algebra. Apply the qualified small-time summed mixed-candidate estimate68 at the path point with r=j+2l, then transport its norm bound to the original T,D,Pb. Because S≤T≤a², the needed small-time hypothesis holds at every path point. The explicit resulting constant is4*4^j*mixedTimeConstant(j,l)*2^(j+2l)*3^j. Every spatial j and l≤3 is included, with the exact A0 correction. For θ<1, qualified65 transfers this to the actual time-after-space mixed derivatives of the analytic candidate.

Kernel001/all-owner recursive-axiom PASS,7 actual theorem constants,6 public source theorems,0 definitions; complete value export correctly empty. No failures, all frozen imports/heads exact, successful snapshot/object/source bound by receipt. Independent final complete review pending after71/72.

This is the small-time path estimate with the explicit T≤a² guard. It does not prove high-time estimates, the complete compensated Taylor remainder, actual probability-kernel identification or full original hSmall. Joint Frechet differentiation is the next source seam; its pinned standard dependency is requested from root. All original root groups remain OPEN.
