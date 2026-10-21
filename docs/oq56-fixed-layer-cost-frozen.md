# Frozen fixed-layer cost sources

| Unit | Source | SHA256 | Public definitions | Public theorems |
|---|---|---|---:|---:|
|44|Shao/OQ5/P52/FixedLayerAtomicCost.lean|8114bb4a884325517f13ab95f83cdb9cff84181e5b2e3921f46af3bab5c1d87b|1|6|
|45|Shao/OQ5/P52/FixedLayerCostScales.lean|e045d80bd8bb1e0cb8d0db633db9168bee9b8f9360d87d3186e6625114bb0346|0|8|
|46|Shao/OQ5/P52/FixedLayerCostBudget.lean|d54d689f04340d807ffc35b399842bcf7a0e366201fda96ef9a5bb047c75a70f|0|3|

These exact public surfaces were frozen and independently translated against ORIGINALp50/p52 before implementation. Freezes44 36db0ea5135c5e2161aefe3f33d7f9b29cff1ee83a1fcd4983162ee5595611a8,45 72f791f700fb0b75cae7388ed4a5760a0624008ba059c5a0c87c838fc72c97e8,46 579628f41776e90e2ed0e7d8e4d852ad060464a359779ea10607bbb4a26d0770. Blind reports44 bb26ee7f46d83e5f0c93d191566a495ecfb8909769ff633c50d883fee6d6e080,45 2e6f87e139a730515ec717f0ec1b775212936c57520bf202c077b7b5e7d7ad6a,46 f0fac0dfa25391e12879b0621bbc32d7f33830ac187ed33f0460bbb9c9da5922.

Pinned parser identifier escaping uses «λ» and «hλ» for the same exact Lean.Name values as the older unquoted mathematical catalogs. Only those exact token escapes may be normalized in type comparison; no type, body, premise or ordering change. Lexical note8968e10ab6803b38c6d802c340464a7d523e2fa5929af13d2200738b28178b3a records this elaboration detail. Original freezes are unchanged.

Entire project source closure has12files:44,45,46,43,41,42,40,39,38,37,31 andRowIdentity. Exact predecessors are unchanged from the independently accepted reports/PR54/59:43 34355cc04f477443e6d6a6b22fd0418004db9974d2831fca722b1d52ac63ce6d;41 12cd08915a9f8efd698312c6dc783716b385ec798dfc5f5e63e9fa2b660b003d;42 6e3c036b78417aa0ac45457c5831bd30caccdef1d50ea4c2341035eba728ccc9;40 dcc8bf8e53d35dc9f62d61b6ebf357f4f7fcea503afab7c9d8b27b9267a527b1;39 1c143cef85bf6dcd06736d74611224d1dcfb0e1a897b6221bcaa01b0defd174c;38 a7003ec3186c70fa96ac88fc7cecd86e35bdf851b73765b882f46c3be650e287;37 f548f10879ab5aec82429d719a784f04c353664d6a593d68cde87fd721275c8f;31 f5d25c0acd7d7e5a99b9e1f561f8d2852efe3fec38dbec1a93d19392380acc9a;RowIdentity73bb0809bc6d323b31775327e468677d6320b38f8fe87363936860164f17f975.

Lean4.36.0-rc1 commitc9afcddf514a6772bd4d649f7cfc04eff0b9f15e, Mathlib807d3836b165983210ee2ecf3cd28f239436949c, manifestSHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e. Newownoleans allowed only for authors; no accepted predecessor target rebuilt/rechecked for this milestone.
