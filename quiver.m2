debug needsPackage "AR"

tallySummands = L -> tally (
    L  = new MutableList from module \ L;
    b := new MutableList from #L : true;
    for i to #L-2 do if b#i then for j from i+1 to #L-1 do if b#j then (
	if first isIsomorphic(L#i, L#j)
	then ( b#j = false; L#j = L#i ));
    new List from L)

importFrom_Core { "moduleAbbrv", "ReverseDictionary",
    "getAttribute", "hasAttribute", "setAttribute", "nonnull" }

-- TODO: reindex for each Q
ModuleDictionary = new MutableHashTable

if instance(see, Symbol) then see = method()

identify = method()
identify(List, Module) := (L, M) -> if M =!= null then scan(L,
    N -> if first isIsomorphic(N, M) then break N)
identify(HashTable, Module) := (H, M) -> identify(keys H, M)

index(HashTable, Nothing) := (Q, M) -> null
index(HashTable, Module)  := (Q, M) -> try ModuleDictionary#(identify_Q M)

alias = M -> (
    if (ind := identify(ModuleDictionary, M)) =!= null
    then ind else ModuleDictionary#M = #ModuleDictionary);

ARQuiver = new Type of MutableHashTable
ARQuiver.GlobalAssignHook = globalAssignFunction
ARQuiver.GlobalReleaseHook = globalReleaseFunction

ARQuiver _ ZZ := memoize((Q, i) -> first select(keys Q, M -> i === index_ModuleDictionary M))

vertexAbbrv = (Q, i) -> (
    -- moduleAbbrv(M, net Qs | "_" | i)
    Qs := getAttribute(Q, ReverseDictionary);
    net Qs | "_" | i)

net ARQuiver := Q -> hashTable apply(keys Q, M -> { index_ModuleDictionary M, M })
see ARQuiver := Q -> (
    H := hashTable apply(pairs Q, (M, L) -> index_ModuleDictionary M => {
	    runLengthEncode sort nonnull toList apply(L.outgoing, index_ModuleDictionary),
	    runLengthEncode sort nonnull toList apply(L.incoming, index_ModuleDictionary),
	    try index_ModuleDictionary L.translate,
	    try index_ModuleDictionary L.translate'
	});
    netList(Boxes => false, apply(pairs H, (i, x) ->
	    {vertexAbbrv(Q, i), ": ",
		x#0, " <- ", i, " <- ", x#1, " | ",
		x#2, " <~ ", i, " <~ ", x#3}))
)

Label = new SelfInitializingType of BasicList
net Label := L -> L#0 | if L#1 == 0 then "" else net [L#1]
Label + ZZ := (L, n) -> Label {L#0, L#1+n}
Label - ZZ := (L, n) -> Label {L#0, L#1-n}
label = (M, N, n) -> if not hasAttribute(N, ReverseDictionary) then (
    if hasAttribute(M, ReverseDictionary)
    and instance(name := getAttribute(M, ReverseDictionary), Label)
    then setAttribute(N, ReverseDictionary, name + n))

summands' = memoize(M -> (
    L := summands(keys ModuleDictionary, M);
    join(drop(L, -1), summands last L)))
newSummands = (Q, M) -> select(
    summands'( identify(Q, M) ?? M ),
    N -> identify(Q, M) === null)

visit = method(Options => { LengthLimit => 10 })
visit(ARQuiver, List)    := opts -> (Q, L) -> apply(
    keys tallySummands L, M -> visit(Q, M, opts))

visit(ARQuiver, Complex) := opts -> (Q, C) -> (
    applyValues(C.dd.map, f -> visit(Q, f, opts)))

visit(ARQuiver, Matrix)  := opts -> (Q, f) -> (
    if isSurjective f then (
	visit(Q, tars := { target f }, opts);
	visit(Q, srcs := newSummands_Q source f, opts);
    );
    if isInjective  f then (
	visit(Q, srcs = { source f }, opts);
	visit(Q, tars = newSummands_Q target f, opts);
    );

    table(tars, srcs, (tar, src) -> (
	    tar = identify_Q tar;
	    src = identify_Q src;
	    if tar =!= null then (
		if isSurjective f then (
		    Q#tar.incoming = identify_Q \ srcs;
		    if src =!= null and instance(Q#src.outgoing, MutableList)
		    then Q#src.outgoing = append(Q#src.outgoing, identify_Q tar));
	    );
	    if src =!= null then (
		if isInjective f then (
		    Q#src.outgoing = identify_Q \ tars;
		    if tar =!= null and instance(Q#tar.incoming, MutableList)
		    then Q#tar.incoming = append(Q#tar.incoming, identify_Q tar));
	    )
	)
    )
)

visit(ARQuiver, Module)  := opts -> (Q, M) -> (
    M = prune M;
    n := opts.LengthLimit - 1;
    if n < 0 or M == 0 or identify_Q M =!= null then return {};
    alias M;
    Q#M = new MutableHashTable from {
	symbol incoming => new MutableList,
	symbol outgoing => new MutableList,
    };
    --
    visit(Q, C0 :=  leftAlmostSplit M, LengthLimit => n);
    visit(Q, C2 := rightAlmostSplit M, LengthLimit => n);
    --
    label(M, Q#M.translate  = identify_Q        translate M,  1);
    label(M, Q#M.translate' = identify_Q inverseTranslate M, -1);
)

-- modules and symbols
explore = (Q, n, Ms, Ss) -> (
    R := ring Ms#0;
    alias module R;
    apply(Ms, alias);
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
M = prune syzygy(2, coker vars R)
see explore(A5 = new ARQuiver, 6, {M}, {symbol M})

facs = AnFactorizations(5, R)
Ms = summands directSum AnModules(5, R)
see explore(A5 = new ARQuiver, 5, Ms, apply(#Ms, i -> getSymbol("M" | i+1)))
see A5

restart
load "./quiver.m2"
-- E7 "by hand" using AR code
see explore(E7 = new ARQuiver, 10, {M}, {symbol M})
see explore(E7 = new ARQuiver, 5, {A, B, M}, {symbol A, symbol B, symbol M})
