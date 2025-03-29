debug needsPackage "AR"

debug Core
importFrom_Core "moduleAbbrv"

kk = ZZ/32003
R = kk[x,y,z]/(x^2-y*z)
R = kk[x,y,z,w]/(x*w-y*z)
C = res(coker vars R, LengthLimit => 6)
C.dd
m = matrix"-x,-y;z,x"
m = matrix"x,y;z,w"
M1 = coker m

kk = ZZ/101
R = kk[a,b, Degrees => {6,2}]/(a^2+b^6)
facs = AnFactorizations(5, R)
Ms = AnModules(5, R)

M = prune first Ms
N = prune translate M

Label = new SelfInitializingType of BasicList
net Label := L -> (
    if hasAttribute(L#0, ReverseDictionary) then (
	net getAttribute(L#0, ReverseDictionary) | if L#1 == 0 then "" else net [L#1])
    else L#0)
Label + ZZ := (L, n) -> Label {L#0, L#1+n}
Label - ZZ := (L, n) -> Label {L#0, L#1-n}

quiver = new MutableHashTable

explore0 = (n, M) -> (
    if n == 0 or M == 0 or any(keys quiver, M' -> first isIsomorphic(M, M')) then return;
    quiver#M = true;
    n = n - 1;
    stderr << "." << flush;
    C := rightAlmostSplit M;
    L := prune \ summands C_1;
    apply(L, explore0_n);
    explore0_n C_2;
    if hasAttribute(M, ReverseDictionary)
    then setAttribute(C_2, ReverseDictionary, getAttribute(M, ReverseDictionary) + 1);
    C = leftAlmostSplit M;
    L = prune \ summands C_1;
    apply(L, explore0_n);
    if hasAttribute(M, ReverseDictionary)
    then setAttribute(C_0, ReverseDictionary, getAttribute(M, ReverseDictionary) - 1);
    explore0_n C_0;
    quiver#M = L;
)

-- modules and symbols
explore = (n, Ms, Ss) -> (
    apply(Ms, Ss, (M, S) -> setAttribute(M, ReverseDictionary, Label {S, 0}));
    apply(Ms, Ss, (M, S) -> S <- M);
    apply(Ms, explore0_n);
    quiver)

see = x -> hashTable apply(pairs quiver, (M, L) -> net moduleAbbrv(M, M) => apply(L, N -> net moduleAbbrv(N, N)))

end--
restart
load "./quiver.m2"

--see explore(5, {M}, {symbol M})

Ms = summands directSum Ms
see explore(5, Ms, apply(#Ms, i -> getSymbol("M" | i+1)))
see quiver
