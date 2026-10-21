# Frozen scope: p35 finite-row algebra

Source: current/oq56/inputs02/p35.md at source repository commit 35d4580b61e22e7145f47730045a09874ef93259, SHA256 f5308d1bcdbe2c54e075626617572bf264e3148dd4393324a22ac9664e4e2da5. See oq5-counterexample-contract.md for the full root dependency graph.

This milestone implements the finite algebra of D0/D1/D2: the actual unordered-pair U, row means q, adjusted rows b, studentizer square R^2, double counting, centered-row identity and exact target cancellation. A,d,Z are arbitrary real vectors on Fin n. Main identities assume n>=3. For cancellation, J is any finite target set, its Z and d coordinates equal t and delta, and delta=(|J|-1)t^2/(n-2). No extra restrictions on J, t or delta are allowed.

The source formulas and finite conditional calculations motivate this algebra, but no conditional law or fixed infinite iid construction is introduced here. Constant-shift/centering facts beyond the implemented declarations, moments, rarity estimates, positivity almost surely and asymptotic tail failure remain open. Neither the two new files nor their receipt close the p35 root.
