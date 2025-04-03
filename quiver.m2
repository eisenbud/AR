debug needsPackage "AR"
needsPackage "Graphs"

tallySummands = L -> tally (
    L  = new MutableList from module \ L;
    b := new MutableList from #L : true;
    for i to #L-2 do if b#i then for j from i+1 to #L-1 do if b#j then (
	if first isIsomorphic(L#i, L#j)
	then ( b#j = false; L#j = L#i ));
    new List from L)

importFrom_Core { "moduleAbbrv", "ReverseDictionary", "sortBy",
    "getAttribute", "hasAttribute", "setAttribute", "nonnull",
    "deepApply" }

-- TODO: reindex for each Q
ModuleDictionary = new MutableHashTable
Triangles = new MutableHashTable

if instance(see, Symbol) then see = method()

identify = method()
identify(List, Module) := (L, M) -> if M =!= null then scan(L,
    N -> if isIso(N, M) then break N)
identify(HashTable, Module) := (H, M) -> if H#?M then M else identify(keys H, M)

index(HashTable, Nothing) := (Q, M) -> null
index(HashTable, Module)  := (Q, M) -> try ModuleDictionary#(identify_Q M)
index(HashTable, Complex) := (Q, C) -> fold(
    apply(reverse values C.module,
	M -> sort(index_Q \ summands' M)),
    (a,b) -> a => b)

alias = method()
alias Module := M -> (
    if M == 0 then return;
    M = identify(ModuleDictionary, M) ?? M;
    ModuleDictionary#M ??= #ModuleDictionary;
    M)
alias Complex := C -> (
    apply(summands C_1, M -> alias prune M);
    C) -- Triangles#(index_ModuleDictionary C) ??= C)

ARQuiver = new Type of MutableHashTable
ARQuiver.GlobalAssignHook = globalAssignFunction
ARQuiver.GlobalReleaseHook = globalReleaseFunction

ARQuiver _ ZZ := memoize((Q, i) -> first select(keys Q, M -> i === index_ModuleDictionary M))

arrows-* ARQuiver*-= Q -> VerticalList flatten apply(keys Q, M -> apply(toList Q#M.incoming, N -> index_Q N => index_Q M))
vertices ARQuiver := Q -> NumberedVerticalList (sortBy index_ModuleDictionary) keys Q
triangles = Q -> VerticalList keys Triangles

-- warning: repeated arrows are collapsed into a single directed edge
digraph  ARQuiver := o -> Q -> digraph (arrows Q, EntryMode => "edges")
show     ARQuiver := Q -> show digraph Q
show     Digraph  := G -> (
    fn := temporaryFileName() | ".svg";
    addEndFunction( () -> if fileExists fn then removeFile fn );
    fn << html G << endl << close;
    show URL urlEncode(rootURI | realpath fn))

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
		x#3, " ~> ", i, " ~> ", x#2}))
)

Label = new SelfInitializingType of BasicList
net Label := L -> net L#0 | if L#1 == 0 then "" else net [L#1]
Label + ZZ := (L, n) -> Label {L#0, L#1+n}
Label - ZZ := (L, n) -> Label {L#0, L#1-n}
label = (M, N, n) -> -* if not hasAttribute(N, ReverseDictionary) then *- (
    if hasAttribute(M, ReverseDictionary)
    and instance(name := getAttribute(M, ReverseDictionary), Label)
    then setAttribute(N, ReverseDictionary, name + n))

summands' = memoize(M -> (
	return summands M;
    L := summands(keys ModuleDictionary, M);
    join(drop(L, -1), summands last L)))
newSummands = (Q, M) -> select(
    summands'( identify(Q, M) ?? M ),
    N -> identify(Q, M) === null)

visit = method(Options => { LengthLimit => 10 })
visit(ARQuiver, List)    := opts -> (Q, L) -> apply(
    keys tallySummands L, M -> visit(Q, M, opts))

flatten Option := List => opts -> deepApply(opts, x -> if instance(x, Option) then toList x else x)

visit(ARQuiver, Complex) := opts -> (Q, C) -> (
    if C == 0 then return C;
    C = alias prune C;
    key := index_ModuleDictionary C;
    if Triangles#?key then return;
    --
    tar = identify_ModuleDictionary C_0;
    mid = identify_ModuleDictionary \ summands C_1;
    src = identify_ModuleDictionary C_2;
    --
    Q#tar.incoming =
    Q#src.outgoing = mid;
    --
    Triangles#key = C;
    visit(Q, mid, opts);
    for M in mid do if Q#?M then (
	if instance(Q#M.outgoing, MutableList) then Q#M.outgoing = append(Q#M.outgoing, tar);
	if instance(Q#M.incoming, MutableList) then Q#M.incoming = append(Q#M.incoming, src));
)

visit(ARQuiver, Module)  := opts -> (Q, M) -> (
    if M == 0 then return M;
    M = alias prune M;
    n := opts.LengthLimit - 1;
    if n == 0 then printerr "warning: hit length limit, quiver may not be complete!";
    if n < 0 or M == 0 or identify_Q M =!= null then return M;
    Q#M = new MutableHashTable from {
	symbol incoming => new MutableList,
	symbol outgoing => new MutableList,
    };
    --
    label(M, Q#M.translate  = visit(Q, translate  M, LengthLimit => n),  1);
    label(M, Q#M.translate' = visit(Q, translate' M, LengthLimit => n), -1);
    --
    visit(Q, C0 :=  leftAlmostSplit M, LengthLimit => n);
    visit(Q, C2 := rightAlmostSplit M, LengthLimit => n);
    --
    M
)

-- modules and symbols
explore = method()
explore(ARQuiver, ZZ, List, List) := (Q, n, Ms, Ss) -> (
    R := ring Ms#0;
    alias module R;
    apply(Ms, alias);
    apply(Ms, Ss, (M, S) -> setAttribute(M, ReverseDictionary, Label {S, 0}));
    apply(Ms, Ss, (M, S) -> S <- M);
    apply(Ms, M -> visit(Q, M, LengthLimit => n));
    Q)

explore(ARQuiver, ZZ) := (Q, n) -> (
    apply(keys ModuleDictionary, M -> visit(Q, M, LengthLimit => n));
    Q)

matrix ARQuiver := o -> Q -> (
    matrix table(#keys Q, #keys Q,
	(i,j) -> number(Q#(Q_i).incoming,
	    M -> j == index_ModuleDictionary M)))

end --

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
