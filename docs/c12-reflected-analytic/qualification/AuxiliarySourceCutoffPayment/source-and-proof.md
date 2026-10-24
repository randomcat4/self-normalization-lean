# Unit165: original deterministic ceiling cutoff pays both source ranks

Source supplement.tex4984 definesH=Kbeta²(1+x)^6,m=ceil(H). Lines5094–5111,
5122,5133 use t>=m,l=t or t-1,l>=t/2,m>=4, andKchosenonceafterL/rhoStar.
This frozen head makes that exact deterministic payment explicit. It assumes
beta>=1,L>=0,s>=0,x>=1,rhoStar>0, K>=8000000(1+L)^2 and
K>=2(768/rhoStar)^2, the actual naturalceilingcutoff, actualn=t ort-1, and
s*t<=Lx². It returnsm>=4,n>0,n>=t/2,s*n<=Lx² andboth exactrankconditions
needed by158/159/163. No drift/budget/tail conclusion is assumed as an input.

PutM=beta²(1+x)^6>=1. K>=8000000 followsfromL>=0,soH=KM>=K>=4.
NativeNat.le_ceil andNat.ceil_le give4<=m andH<=t respectively. t>=m>=4.
Ifn=t,half-rank/upper-rankare immediate;ifn=t-1,the natural subtractioncast
is valid sincet>=1 andn=t-1>=t/2 sincet>=4. Thusn>0 andn<=t; multiplication
bys>=0 transports the timebound. Multiplying the twoKbounds byM>=0 andusing
H<=t<=2n paysboth required numericalranks. Every floor/cast/subtraction and
positive-length condition is explicitly proved; the n=t-1 case is not hidden
under an asymptotic convention. The rhoStar-positive assumption is retained
for the sourceC1 legalparameter although this purelynumeric transform doesnot
need to dividebyrhoStar outside its alreadydefined squared coefficient.

Completeimports/context/onehead frozenbeforeproof. Attempt001 kernel andall1
actualownerrecursiveAXPASS,onepublictheorem,0private/generated/globalvalues.
Original harmless unusedhRho warning retained; no successful gate replay.
The nativefloorSemiringobject was already in the pinnedread-onlymathlibcache;
no package/cachebuild/update/write. Actualsource/command/log/receipt locators
preserved for independentreview. Currentreview160162164sealed separately;
this unit awaits its own freshqualified review with subsequentconsumers.
OriginalC1COMPLETE,C2/C12OPEN. This algebraicpayment is not rootclosure.
