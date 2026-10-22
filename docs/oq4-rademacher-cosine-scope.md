# Genuine Rademacher principal one-step kernel pair

STATUS: LEAN_FULLY_CHECKED_FINITE_PRINCIPAL_ONE_STEP
ROOT_STATUS: OPEN
SPECTRUM_STATUS: OPEN

This leaf realizes the principal one-step cosine pair of source oq4/c01/spectrum01.md on the actual integer state class. The source snapshot is 35d4580b61e22e7145f47730045a09874ef93259; the document SHA256 is b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b.

The increment law is the genuine real Rademacher measure (dirac(1)+dirac(-1))/2, whose probability instance is proved internally. For m>=1, m<=h<m+1 and integer -m<=r<=m, set a=pi/(2(m+1)) and rho=cos(a). The actual closed killed kernel has exactly the surviving half-weight atoms at r+1 and r-1. No exit row is normalized. The cosine is genuinely integrable and its actual row integral, equivalently Kcos, equals rho*cos(a*r). The leaf also proves 0<a<pi/2 and 0<rho<1.

Integer starts and the real closed strip are related by an exact equivalence, including h=m and boundary atoms. The principal identity applies to this integer class only. It does not extend the same frequency to every real start or another lattice coset.

The source module has9 explicit public theorems,4 definitions,1 named probability instance,6 private helpers and14 generated helpers:34 actual owned declarations. The complete-source audit selects every declaration with no module index and the imported audits select module ownership, including private/generated names outside the displayed namespace. Only propext, Classical.choice and Quot.sound are allowed.

This is one finite one-step leaf. Complete finite spectral basis, powers and path survival representation, negative/zero modes, S1-S4 limits, other cosets and endpoint classification remain OPEN, as do the OQ4 root and energy/K chains. Root integration remains pending. No shared source, root imports, manifests, toolchain or cache is modified here.
