# Explicit scalar halfline small-Taylor bound

Readonly supplement.tex4192–4253, especially4234–4242. This is the quantitative halfline scalar estimate with exactly the original absb³*T^(-3/2)*D³*P_b structure. Upper normalized u=a-y,v=a-z,b physical; lower u=a+y,v=a+z,beta=-b and normalized displacement u-v=-d. Universal constant8000100 is deliberately loose; source only requires existence of C. Actual probability reflection identity, interval smallTaylor and all original roots remain OPEN.

Five complete heads and full imports/context frozen before proofs, no new definitions. Final complete proof-stripped source is bytewise frozen.lean.txt, UTF8noBOM LF. Failed001/002 preserved; only explicit nonnegativity, absolute-value alias/factor and association matching fixed, no frozen scope or premises changed.

Normalized power lemma: q in[0,1], D>=1 imply q^(3+k)D^j<=q³D³ for every k>=0,j<=3. At an actual positive segment point put E=T-theta*b², U=u-theta*b, s=sqrt(E), q=absb/s, D=1+abs(U-v)/s, P=exp(-Uv/E). b²<=E gives q<=1. Unit37 actual third-path decomposition has four terms. Unit32 j3 spatial profile, unit34 curvature_T and slope_TT profiles, and unit33 timeCompletion_TTT profile give respective bounds13824*q³D³P,18432*q4D²P,2400*q5DP,108*q6P. Normalize all to q³D³P and sum=34764. No crossed time term is dropped.

Under source smallstep b²<=T/2 and newpointu-b>=0, unit35 gives E>=T/2>=b² and U>0 for theta in[0,1), including every interior Lagrange point. Source profile transport r3,j3 costs2³3³=216, so34764*216=7509024<=8000000 uniformly, with initial P_b and D, no endpoint distance lower bound. Newpointmaylieexactlyonwall.

The exact second-Taylor compensation correction from unit36/37 is b³*slope_T+(b4/2)*f_TT. Initial mixed and puretime bounds give80*q³DP+6*q4P<=86*q³D³P. Source unit35 at theta0 transports P to P_b. Finally actual Lagrange theta in(0,1) gives compensated remainder=g'''theta/6+the correction; triangle inequality yields at most(8000000/6+86)*commonProfile<=8000100*commonProfile. b0 allowed, and wallnewpointg1=0 is continuous explicit scalar reflection value at positive remaining energy. No claim about zero energy or actual Brownian law.

Author kernelattempt003 and actualowner recursiveaxiom auditPASS CPU14–17/c12-heavy.lock/-M8192-j4, pinnedversions. Actual20owners alltheorem,5public,0definitions; complete actualtypes exported and non-theorem export empty. Independent complete final review pending; successful checks and qualified olddependencies reused, no prior producer compilation.
