debug needsPackage "AR"

importFrom_Core { "moduleAbbrv", "ReverseDictionary",
    "getAttribute", "hasAttribute", "setAttribute", "nonnull" }

if instance(see, Symbol) then see = method()

ModuleDictionary = new MutableHashTable

ARQuiver = new Type of MutableHashTable
ARQuiver.GlobalAssignHook = globalAssignFunction
ARQuiver.GlobalReleaseHook = globalReleaseFunction

known = (Q, M) -> if M =!= null then scan(keys Q, N -> if first isIsomorphic(N, M) then break N)
index(ARQuiver, Module) := (Q, M) -> try Q#(known(Q, M))

ARQuiver _ ZZ := (Q, i) -> first select(keys Q, M -> i == index_ModuleDictionary M)

net ARQuiver := Q -> hashTable apply(keys Q, M -> { index_ModuleDictionary M, M })
see ARQuiver := Q -> hashTable apply(pairs Q,
    (M, L) -> index_ModuleDictionary M => {
	runLengthEncode apply(L.outgoing, index_ModuleDictionary),
	runLengthEncode apply(L.incoming, index_ModuleDictionary),
    }
    -- (M, L) -> net moduleAbbrv(known_ModuleDictionary M, M) => {
    -- 	runLengthEncode apply(L.outgoing, N -> net moduleAbbrv(known_ModuleDictionary N, N)),
    -- 	runLengthEncode apply(L.incoming, N -> net moduleAbbrv(known_ModuleDictionary N, N)),
    -- }
)

Vertex = new SelfInitializingType of BasicList
net Vertex := M -> net moduleAbbrv(M, M)

Label = new SelfInitializingType of BasicList
net Label := L -> if not hasAttribute(L#0, ReverseDictionary) then L#0 else (
    net getAttribute(L#0, ReverseDictionary) | if L#1 == 0 then "" else net [L#1])
Label + ZZ := (L, n) -> Label {L#0, L#1+n}
Label - ZZ := (L, n) -> Label {L#0, L#1-n}
label = (M, N, n) -> if hasAttribute(M, ReverseDictionary) and not hasAttribute(N, ReverseDictionary) then (
    if instance(name := getAttribute(M, ReverseDictionary), Label)
    then setAttribute(N, ReverseDictionary, name + n));

summands' = M -> (
    L := summands(keys ModuleDictionary, M);
    join(drop(L, -1), summands last L))

visit = method(Options => { LengthLimit => 5 })
visit(ARQuiver, List)    := opts -> (Q, L) -> apply(L, M -> visit(Q, M, opts))
visit(ARQuiver, Complex) := opts -> (Q, C) -> applyValues(C.dd.map, f -> visit(Q, f, opts))
visit(ARQuiver, Matrix)  := opts -> (Q, f) -> (
    if isSurjective f then visit(Q, tars := { target f }, opts) else visit(Q, tars = summands' target f, opts);
    if isInjective  f then visit(Q, srcs := { source f }, opts) else visit(Q, srcs = summands' source f, opts);
    table(tars, srcs, (tar, src) ->
	if (tar = known_Q tar) =!= null and (src = known_Q src) =!= null then (
	    Q#tar.incoming = unique append(Q#tar.incoming, known_Q src);
	    Q#src.outgoing = unique append(Q#src.outgoing, known_Q tar);
	)
    )
)
visit(ARQuiver, Module)  := opts -> (Q, M) -> (
    M = prune M;
    n := opts.LengthLimit - 1;
    if n < 0 or M == 0 or known_Q M =!= null then return {};
    ModuleDictionary#M ??= #ModuleDictionary;
    Q#M = new MutableHashTable from {
	symbol incoming => {},
	symbol outgoing => {},
    };
    
    --
    visit(Q, C0 :=  leftAlmostSplit M, LengthLimit => n);
    visit(Q, C2 := rightAlmostSplit M, LengthLimit => n);
    --
    label(M, Q#M.translate  = known_Q        translate M,  1);
    label(M, Q#M.translate' = known_Q inverseTranslate M, -1);

)

-- modules and symbols
explore = (Q, n, Ms, Ss) -> (
    ModuleDictionary#((ring Ms#0)^1) = 0;
    apply(Ms, Ss, (M, S) -> ModuleDictionary#M ??= #ModuleDictionary);
    apply(Ms, Ss, (M, S) -> setAttribute(M, ReverseDictionary, Label {S, 0}));
    apply(Ms, Ss, (M, S) -> S <- M);
    apply(Ms, M -> visit(Q, M, LengthLimit => n));
    Q)


-- E7
kk = ZZ/101
R = kk[x,y, Degrees => {3, 2}]/(x^3 + x*y^3)
A = coker matrix {{x}}
B = coker matrix {{x^2 + y^3}}
M = prune syzygy(2, coker vars R)

end--
restart
load "./quiver.m2"

-- E7 "by hand" using AR code
see explore(E7 = new ARQuiver, 10, {M}, {symbol M})
see explore(E7 = new ARQuiver, 5, {A, B, M}, {symbol A, symbol B, symbol M})






---

kk = ZZ/32003
R = kk[x,y,z]/(x^2-y*z)
R = kk[x,y,z,w]/(x*w-y*z)
C = res(coker vars R, LengthLimit => 6)
C.dd
m = matrix"-x,-y;z,x"
m = matrix"x,y;z,w"
M = coker m

restart
load "./quiver.m2"
-- A5
kk = ZZ/101
R = kk[a,b, Degrees => {6,2}]/(a^2+b^6)
facs = AnFactorizations(5, R)
Ms = AnModules(5, R)
M = prune syzygy(2, coker vars R)

see explore(A5 = new ARQuiver, 6, {M}, {symbol M})


A5 = new ARQuiver
Ms = summands' directSum Ms
see explore(A5, 5, Ms, apply(#Ms, i -> getSymbol("M" | i+1)))
see A5
