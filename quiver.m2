debug needsPackage "AR"

importFrom_Core { "moduleAbbrv", "ReverseDictionary",
    "getAttribute", "hasAttribute", "setAttribute" }

if instance(see, Symbol) then see = method()

ModuleDictionary = new MutableHashTable

ARQuiver = new Type of MutableHashTable
ARQuiver.GlobalAssignHook = globalAssignFunction
ARQuiver.GlobalReleaseHook = globalReleaseFunction
see ARQuiver := Q -> hashTable apply(pairs Q,
    (M, L) -> net moduleAbbrv(known_ModuleDictionary M, M) => runLengthEncode apply(toList L,
	N -> net moduleAbbrv(known_ModuleDictionary N, N)))

Vertex = new SelfInitializingType of BasicList
net Vertex := M -> net moduleAbbrv(M, M)

Label = new SelfInitializingType of BasicList
net Label := L -> if not hasAttribute(L#0, ReverseDictionary) then L#0 else (
    net getAttribute(L#0, ReverseDictionary) | if L#1 == 0 then "" else net [L#1])
Label + ZZ := (L, n) -> Label {L#0, L#1+n}
Label - ZZ := (L, n) -> Label {L#0, L#1-n}
label = (M, N, n) -> if hasAttribute(M, ReverseDictionary) then (
    if instance(name := getAttribute(M, ReverseDictionary), Label)
    then setAttribute(N, ReverseDictionary, name + n));

known = (Q, M) -> scan(keys Q, N -> if first isIsomorphic(N, M) then break N)

visit = method(Options => { LengthLimit => 5 })
visit(ARQuiver, Complex) := opts -> (Q, C) -> applyValues(C.module, M -> visit(Q, M, opts))
visit(ARQuiver, Module)  := opts -> (Q, M) -> (
    if 1 < #summands M then return apply(summands M, N -> visit(Q, N, opts));
    M = prune M;
    n := opts.LengthLimit - 1;
    if n < 0 or M == 0 or known_Q M =!= null then return {};
    Q#M = new MutableList;
    label(M, prune translate M, 1);
    label(M, prune inverseTranslate M, -1);
    --
    visit(Q, C := rightAlmostSplit M, LengthLimit => n);
    apply(known_Q \ prune \ summands C_1,
	N -> if instance(Q#N, MutableList) then (Q#N)##(Q#N) = M);
    --
    visit(Q, C = leftAlmostSplit M, LengthLimit => n);
    if C != 0 then Q#M = known_Q \ prune \ summands C_1;
)

-- modules and symbols
explore = (Q, n, Ms, Ss) -> (
    apply(Ms, Ss, (M, S) -> ModuleDictionary#M = S);
    apply(Ms, Ss, (M, S) -> setAttribute(M, ReverseDictionary, Label {S, 0}));
    apply(Ms, Ss, (M, S) -> S <- M);
    apply(Ms, M -> visit(Q, M, LengthLimit => n));
    Q)

---

kk = ZZ/32003
R = kk[x,y,z]/(x^2-y*z)
R = kk[x,y,z,w]/(x*w-y*z)
C = res(coker vars R, LengthLimit => 6)
C.dd
m = matrix"-x,-y;z,x"
m = matrix"x,y;z,w"
M = coker m

kk = ZZ/101
R = kk[a,b, Degrees => {6,2}]/(a^2+b^6)
facs = AnFactorizations(5, R)
Ms = AnModules(5, R)
M = prune syzygy(2, coker vars R)

end--
restart
load "./quiver.m2"

A5 = new ARQuiver
see explore(A5, 5, {M}, {symbol M})

A5 = new ARQuiver
Ms = summands directSum Ms
see explore(A5, 5, Ms, apply(#Ms, i -> getSymbol("M" | i+1)))
see A5
