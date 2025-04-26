newPackage(
    "AR",
    Version => "0.1",
    Date => "March 26, 2025",
    Headline => "Auslander Reiten Theory",
    Authors => {
	{ Name => "David Eisenbud", Email => "de@bberkeley.edu", HomePage => "http://eisenbud.github.io"},
        { Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => ""}},
    PackageExports => {
	"Complexes",
	"DirectSummands",
    "Isomorphism"
	},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {
    "isIso",
--    "isomorphism",
    "Isomorphisms",
    "canonicalDual",
    "transposeModule",
    "syzygy",
    "translate",
    "translate'" => "inverseTranslate",
    "inverseTranslate",
    "socle",
    "knorr", -- knoerrer is correct...
    "AnFactorizations",
    "AnModules",
    "theta",
    
    "rightAlmostSplit",
    "leftAlmostSplit",
--    "irreducibles",
    --Symbols:
    "omega",

    "MESQuiver",
    "mesQuiver",
    "compute",
    "makeQuiver",
    "ses",
    "modules"
    }

myRing = GF 8

-* Code section *-

isIso = method()
isIso(Module, Module) := Boolean => (M, N) -> (
    (eq, iso) := isIsomorphic(M, N);
    if eq then (
        M.cache.Isomorphisms ??= new MutableHashTable;
        M.cache.Isomorphisms#N = iso;
        );
    eq
    )

--isomorphism = method()
isomorphism(Module, Module) := Matrix => (M, N) -> (
    result := M.cache.Isomorphisms#N ??= last isIsomorphic(M,N);
    if result === null then error "modules not isomorphic";
    result
    )

-- returns the list of indices of the modules
-- of L isomorphic to M
isIso(Module, List) := List => (M, L) -> (
    for i from 0 to #L-1 list (
        good := isIso(M, L#i);
        if good then i else continue
        )
    )

syzygy = method()
syzygy(ZZ, Module) := Module => (d,M) -> (
    F := freeResolution(M, LengthLimit => d);
    image F.dd_d)

transposeModule = method()
transposeModule Module := Module => M -> (
    coker dual presentation M)

canonicalDual = method()
canonicalDual Module := Module => M -> (
    R := ring M;
        if not (R.cache#?omega) then (
	   R = ring M;
           c := codim R;
           S := ambient R;
 	   omegaR := R**prune(
	             Ext^c(S^1/ideal R, S^{-numgens S}));
	   R.cache.omega = omegaR);
        if not R.cache#? omega then error();
    Hom(M, R.cache.omega)
    )

translate = method()
translate Module := Module => M -> M.cache.translate ??= (
    d := dim M;
    Mt := transposeModule M;
    Md := syzygy(d,Mt);
    N := canonicalDual Md;
    N.cache.translate' ??= M;
    N)

inverseTranslate = method()
inverseTranslate Module := Module => N -> N.cache.translate' ??= (
    d := dim N;
    R := ring N;
    dualN := canonicalDual N;
    M := syzygy(d,transposeModule dualN);
    M.cache.translate ??= N;
    M)

///
restart
loadPackage("AR", Reload => true)

S = ZZ/32003[x_0..x_3]
     mat = matrix{
	 {x_0,x_1,x_2},
	 {x_1,x_2,x_3}}
     I = minors(2, mat)
     R = S/I
     N = coker (R**mat)
inverseTranslate N


T = ZZ/101[a,b,c]
A = T/(ideal"ab,ac,bc")
M = A^1/ideal(b,c)
(N = translate M) == (rightAlmostSplit M)_2
M' = inverseTranslate N
betti M
betti M'
M == M' -- false! -- but they sure look the same
presentation M
presentation M'
--matrices differ by an automorphism of the source!
prune M == prune M'
///

socle = method()
socle Module := Module => M -> (
    mm := ideal vars ring M;
    (0*M) : mm
    )

rightAlmostSplit = method()
rightAlmostSplit Module := Complex => M -> M.cache.rightAlmostSplit ??= (
    --produces 0->N->E->M->0 almost split
    N := translate M;
    if N == 0 then return complex {N};
    E := Ext^1(M, N);
    sE := socle E;
    i := inducedMap(E, sE);
    d := max degrees sE;
    locs := positions(degrees sE, x -> x === d);
    if #locs > 1 then (
        << "warning: E has " << #locs << " socle generators in highest degree" << endl
        );
    prune yonedaExtension (i*sE_{last locs})
    -- psE := prune socle E;
    -- f := psE.cache.pruningMap;
    -- cov := inducedMap (psE, cover psE);
    -- prune yonedaExtension (i*f*cov)
    )
    
leftAlmostSplit = method()
leftAlmostSplit Module := Complex => N -> (
    --produces 0->N->E->M->0 almost split
    M := inverseTranslate N;
    if M == 0 then return complex {M};
    rightAlmostSplit M
    )
///
restart
loadPackage("AR", Reload => true)
     S = ZZ/32003[x_0..x_3]
     mat = matrix{
	 {x_0,x_1,x_2},
	 {x_1,x_2,x_3}}
     I = minors(2, mat)
     R = S/I
     N = coker (R**mat)
    Text
     N represents the line bundle $O_{P^1}(1)$.
    Example
     e = leftAlmostSplit N
     M = prune e_0

restart
loadPackage("AR", Reload => true)
installPackage "AR"

T = ZZ/101[a,b,c]
A = T/(ideal"ab,ac,bc")
M = A^1/ideal(b,c)

N = translate M
prune M == prune inverseTranslate N
L = leftAlmostSplit N
rightAlmostSplit M
M
prune M == prune L_0
///


knorr = method()
knorr(Matrix, Matrix, Symbol) := (phi, psi, u) -> (
    S := ring phi;
    A := S[u, Join => false];
    phiA := sub(phi, A);
    psiA := sub(psi, A);
    m1 := matrix{
        {psiA, -A_0 ** id_(target psiA)},
        {A_0 ** id_(target phiA), phiA}};
    m2 := matrix{
        {phiA, A_0 ** id_(target phiA)},
        {-A_0 ** id_(target psiA), psiA}};
    (m1,m2)
    )
knorr(Matrix, Matrix, Symbol, Symbol) := (phi, psi, u, v) -> (
    S := ring phi;
    A := S[u, v, Join => false];
    phiA := sub(phi, A);
    psiA := sub(psi, A);
    m1 := matrix{
        {phiA, A_0 ** id_(target phiA)},
        {-A_1 ** id_(target psiA), psiA}};
    m2 := matrix{
        {psiA, -A_0 ** id_(target psiA)},
        {A_1 ** id_(target phiA), phiA}};
    (m1,m2)
    )

AnFactorizations = method()
-- R is in 2 variables, n >= 1
AnFactorizations(ZZ, Ring) := List => (n, R) -> (
    -- equation is x^2 + y^(n+1) = 0
    x := R_0; -- degree n+1
    y := R_1; -- degree 2
    if n == 1 then return {matrix{{x}}, matrix{{y}}};
    for i from 1 to n//2 + 1 list (
        m1 := map(R^{(n+1), (2*n+2-2*i)},
                  R^{0, (n+1-2*i)},
                  {{x, -y^i}, {y^(n+1-i), x}});
        m2 := map(
            source m1,
            R^{-(n+1), -2*i},
            {{x, y^i}, {-y^(n+1-i), x}});
        {m1, m2}
        )
    )

AnModules = method()
AnModules(ZZ, Ring) := List => (n, R) -> (
    facs := AnFactorizations(n, R);
    for f in facs list coker first f
    )

---------------------
-- code for handling elements in the
-- free Abelian group generated by the vertices
-- of a quiver.


dot = method()
dot(List, List) := List => (L1,L2) ->
    sum(#L1, i-> L1_i*L2_i)
theta = method()
theta (List,List) := List => (L,ingoingList) ->
     dot(L,ingoingList)
theta(ZZ, List, List, List) := List => (i, L,ingoingList,tauList) -> (
    if i === 0 then return L;
    if i === 1 then return theta (L, ingoingList);
    theta(pos theta(i-1,
	    L,ingoingList,tauList),ingoingList) -
         tau (pos theta(i-2,
	    L, ingoingList, tauList), tauList)
    )
tau = method()
tau (List,List) := List => (L, tauList) ->
     dot(L,tauList)
pos = method()
pos List := List => L -> apply(#L, i->
    if L_i > 0 then L_i else 0)
neg = method()
neg List := List => L -> apply(#L, i->
    if L_i < 0 then - L_i else 0)


-----------------------------
-- Code for constructing a part of the AR quiver
-- 
MESQuiver = new Type of MutableHashTable
compute = method(Options => {Limit => infinity})

-- the following is an internal constructor function.  Do not export.
mesQuiver = method()
mesQuiver List := (Ms) -> (
    R := ring Ms_0;
    if #Ms === 1 then error "expected at least one non-free CM module -- todo: compute one"; 
    result := new MESQuiver;
    result.ring = ring Ms_0;
    result#"Modules" = Ms;
    result#"SES" = {};
    result#"NextLeft" = 1;
    result#"NextRight" = 1;
    result)

isIsoToOne = method()
isIsoToOne(Module, List) := (M, Ms) -> (
    locs := isIso(M, Ms);
    if #locs === 0 then return null;
    if #locs === 1 then return locs#0;
    error("isomorphic to the following: " | locs);
    )

handleRightNode = method()
handleRightNode(List, ZZ) := (Ms, ind) -> (
    ses := rightAlmostSplit Ms_ind;
    first1 := isIsoToOne(ses_2, Ms);
    if first1 === null then (
        first1 = #Ms;
        Ms = append(Ms, ses_2);
        );
    third3 := isIsoToOne(ses_0, Ms); -- this is Ms_ind...
    if third3 === null then error "this module should exist alrady...";
    sums := summands ses_1;
    middle2 := for m in sums list (
        loc := isIsoToOne(m, Ms);
        if loc === null then (
            loc = #Ms;
            Ms = append(Ms, m);
            );
        loc);
    ({third3, sort middle2, first1}, Ms)
    )

handleLeftNode = method()
handleLeftNode(List, ZZ) := (Ms, ind) -> (
    ses := leftAlmostSplit Ms_ind;
    first1 := isIsoToOne(ses_0, Ms);
    if first1 === null then (
        first1 = #Ms;
        Ms = append(Ms, ses_0);
        );
    third3 := isIsoToOne(ses_2, Ms); -- this is Ms_ind...
    if third3 === null then error "this module should exist alrady...";
    sums := summands ses_1;
    middle2 := for m in sums list (
        loc := isIsoToOne(m, Ms);
        if loc === null then (
            loc = #Ms;
            Ms = append(Ms, m);
            );
        loc);
    ({third3, sort middle2, first1}, Ms)
    )

handleLeftNode MESQuiver := Boolean => Q -> (
    if Q#"NextLeft" >= #Q#"Modules" then return false;
    (ses, newMs) := handleLeftNode(Q#"Modules", Q#"NextLeft");
    Q#"NextLeft" = Q#"NextLeft" + 1;
    Q#"Modules" = newMs;
    Q#"SES" = append(Q#"SES", ses);
    true
    )

handleRightNode MESQuiver := Boolean => Q -> (
    if Q#"NextRight" >= #Q#"Modules" then return false;
    (ses, newMs) := handleRightNode(Q#"Modules", Q#"NextRight");
    Q#"NextRight" = Q#"NextRight" + 1;
    Q#"Modules" = newMs;
    Q#"SES" = append(Q#"SES", ses);
    true
    )

makeQuiver = method()
makeQuiver List := Ms -> (
    i := 1;
    thisline := null;
    allLines := while i < #Ms list (
        (thisline, Ms) = handleRightNode(Ms, i);
        i = i+1;
        thisline
        );
    (allLines, Ms)
    )

compute MESQuiver := MESQuiver => opts -> Q -> (
    more1 := true;
    more2 := true;
    i := 0;
    while i < opts.Limit and (more1 or more2) do (
        more1 = handleRightNode Q;
        more2 = handleLeftNode Q;
        i = i+1;
        );
    Q
    )

ses = method()
ses MESQuiver := List => Q -> unique Q#"SES" -- each might be in 2 times

modules = method()
modules MESQuiver := List => Q -> (
    Ms := Q#"Modules";
    for i from 0 to #Ms-1 list i => Ms#i
    )

outgoingMatrix = method()
outgoingMatrix(List, List) := Matrix => (allLines, Ms) -> (
    -- allLines has the graph info, Ms is a list of the modules.
    -- we only use the number of elements of this list.
    -- we assume the first element of the list is R^1, and we ignore that
    -- vertex.
    n := #Ms - 1;
    mat := mutableMatrix(ZZ, n, n);
    for x in allLines do (
        t := tally x#1;
        i := x#2 - 1; -- vertex number, minus one, for zero indexed.
        for pos in keys t do if pos =!= 0 then mat_(i, pos-1) = t#pos;
        );
    matrix mat
    )

incomingMatrix = method()
incomingMatrix(List, List) := Matrix => (allLines, Ms) -> (
    -- allLines has the graph info, Ms is a list of the modules.
    -- we only use the number of elements of this list.
    -- we assume the first element of the list is R^1, and we ignore that
    -- vertex.
    n := #Ms - 1;
    mat := mutableMatrix(ZZ, n, n);
    for x in allLines do (
        t := tally x#1;
        i := x#0 - 1; -- vertex number, minus one, for zero indexed.
        for pos in keys t do if pos =!= 0 then mat_(i, pos-1) = t#pos;
        );
    matrix mat
    )

translates = method()
-- returns a permutation matrix M --> translate M.
translates(List, List) := Matrix => (allLines, Ms) -> (
    n := #Ms - 1;
    mat := mutableMatrix(ZZ, n, n);
    for x in allLines do (
        i := x#0 - 1; -- vertex number, minus one, for zero indexed.
        tau := x#2 - 1;
        if tau < 0 then continue;
        mat_(i, tau) = 1;
        );
    matrix mat
    )


-* Documentation section *-
beginDocumentation()

doc ///
Key
  AR
Headline
 Auslander-Reiten almost split sequences
Description
  Text
   This package implements the basic operation in
   Auslander-Reiten theory. In particular, given a module
   M or its "translate" N we can form the almost split
   sequence with M on the right and N on the left:
  Example
   T = ZZ/101[a,b,c]
   A = T/(ideal"ab,ac,bc")
   M = A^1/ideal(b,c)
   N = translate M
   M == prune inverseTranslate N
   e = rightAlmostSplit M
   prune N == prune e_2
   
   e' = leftAlmostSplit N
   M == prune e'_0
  Text
   One can also create the corresponding Auslander-Reiten quivers.
   See @TO MESQuiver@.
References
 Yuji Yoshino,
 "Cohen-Macaulay Modules over Cohen-Macaulay Rings",
 Cambridge University Press, 1990
Caveat
  Example
   M == prune inverseTranslate N
   M == inverseTranslate N
  Text the second of these
  returns false, because the presentations look different:
SeeAlso
  translate
  inverseTranslate
  rightAlmostSplit
  leftAlmostSplit
  MESQuiver
///

///
  Key
   theta
   (theta, List, List)
   (theta, ZZ, List, List, List)
  Headline
   implements the (iterative) theta operation of Iyama-Wemyss and Nagai
  Usage
   M = theta(L,ingoing)
   M = theta(n, L, ingoingList, taulist)
  Inputs
   L:List
   n: ZZ
    number of iterations to make
   ingoingList: List
    list of lists of sources of the irreducible maps to each vertex
   tauList:List
    List of targets of the translation 
  Outputs
   M:List
    list of multiplicities of each indecomposable
  Description
    Text
     theta is a linear function of the argument L,
     which represents the direct sum of L_i copies of
     the i-th indecomposable module. It is used to compute
     the first syzygy of this module, as follows:

     ingoingList should be the list of lists of sources
     of irreducible maps;

     tauList should be the list of targets of the translation
     functor.

     If
     L is the list {0..0,1,0..0} with a 1 in the i-th place
     then theta(L, ingoingList) is simply the i-th list in
     ingoingList.The function theta(i, L, ingoingList, taulist)
     is defined iteratively: theta(0, L, X,Y) returns X.
     theta(1, L, ingoingList, Y) returns the i-th list
     in ingoingLIst. For i \geq 2,
     theta(i, L, ingoingList, taulist)
     returns
     theta(i-1, L, ingoingList, taulist)_+
     - tau(theta(i-2ingoingList, taulist)_+).

     The syzygy of the module represented by L is represented
     by the negative part of the sum of all the
     theta(i, L, ingoingList, taulist).

     It seems that 
    Tree
    Code
    Pre
    Example
    CannedExample
  ExampleFiles
  Acknowledgement
  Contributors
  References
  Caveat
  SeeAlso
  Subnodes
///

doc ///
Node
  Key
   canonicalDual
  Headline
   computes Hom into the canonical module
  Usage
   M' = canonicalDual M
  Inputs
   M:Module
  Outputs
   M':Module
  Description
    Text
     If R = S/I is a local (or standard graded) ring
     of codimension c in the regular ring S, then
     the canonical module of R is
     omega = Ext^c(R^1, S^{-numgens S}).
     and the canonical dual of a module M is Hom(M,omega).
     This
     is a perfect duality on the category of maximal Cohen-Maculay
     R-modules. The function looks to see whether
     R.cache.omega is defined, and otherwise computes it and
     caches it.

     Consider the twisted cubic:
    Example
     S = ZZ/32003[x_0..x_3]
     mat = matrix{
	 {x_0,x_1,x_2},
	 {x_1,x_2,x_3}}
     I = minors(2, mat)
     R = S/I
     M = coker (R**mat)
     N = canonicalDual M
     isIsomorphic(M, canonicalDual N)
     R.cache.omega
     betti  prune canonicalDual N
    Example
     M == canonicalDual M
    Text 
     returns false, because the presentations look different.
///

doc ///
Node
  Key
   transposeModule
   (transposeModule, Module)
  Headline
   computes the Auslander transpose
  Usage
   N = transposeModule M
  Inputs
   M:Module
  Outputs
   N:Module
  Description
    Text
     the tranpose is the coker of the dual of the presenation
    Example
     S = ZZ/32003[x_0..x_3]
     mat = matrix{
	 {x_0,x_1,x_2},
	 {x_1,x_2,x_3}}
     M = coker mat
     presentation transposeModule M
///
-*
    "socle",
    "rightAlmostSplit",
    "leftAlmostSplit",
*-


doc ///
Node
  Key
   translate
   (translate, Module)
  Headline
   the Auslander-Reiten tau functor
  Usage
   N = translate M
  Inputs
   M:Module
  Outputs
   N:Module
  Description
    Text
     If R is a local Cohen-Macaulay ring and
     M is an indecomposable maximal Cohen-Maculay
     R-module, free on the
     punctured spectrum of R, then the unique
     almost split sequence whose right hand term is M
     has left-hand term transpose M.

      @TO translate@ is a equivalence on the category
     of maximal Cohen-Macaulay modules. It is the
     composite of the three functors
     transpose, d-th syzygy, and
     canonicalInverse * d-th syzygy * transpose
     where d = dim R.

     The inverse of translate is
     @TO inverseTranslate@.
     
    Example
     T = ZZ/101[a,b,c]
     A = T/(ideal"ab,ac,bc")
     M = A^1/ideal(b,c)
     N = translate M
     e = rightAlmostSplit M
     prune N == prune e_2
  SeeAlso
   leftAlmostSplit
   inverseTranslate
///

doc ///
Node
  Key
   inverseTranslate
  Headline
   the inverse functor to the Auslander tau functor
  Usage
   M = inverseTranslate N
  Inputs
   N:Module
  Outputs
   M:Module
  Description
    Text
     If R is a local Cohen-Macaulay ring and
     M is an indecomposable maximal Cohen-Maculay
     R-module, free on the
     punctured spectrum of R, then the unique
     almost split sequence whose right hand term is M
     has left-hand term translate M, and
     M \cong inverseTranslate N.
     Thus @TO inverseTranslate@ is the inverse of @TO translate@.

     @TO inverseTranslate@ is a equivalence on the category
     of maximal Cohen-Macaulay modules. It
     composite of the three functors
     d-th syzygy * transposeModule * canonicalInverse
     where d = dim R.

    Example
     T = ZZ/101[a,b,c]
     A = T/(ideal"ab,ac,bc")
     M = A^1/ideal(b,c)
     N = translate M
     isIsomorphic(M, inverseTranslate N)
     e = rightAlmostSplit M
     e' = leftAlmostSplit N
     prune M == prune e'_0
  SeeAlso
   translate
   leftAlmostSplit
///


doc ///
Node
  Key
   syzygy
   (syzygy, ZZ, Module)
  Headline
   computes the d-th syzygy module
  Usage
   N = syzygy(d,M)
  Inputs
   d:ZZ
   M:Module
  Outputs
   N:Module
  Description
    Text
     The d-th syzygy of M is the image of the d-th map
     in a resolutino of M.
    Example
     S = ZZ/32003[x_0..x_3]
     mat = matrix{
	 {x_0,x_1,x_2},
	 {x_1,x_2,x_3}}
     I = minors(2, mat)
     R = S/I
     M = coker (R**mat)
     F = freeResolution(M, LengthLimit =>5)
     syzygy(5,M) == image F.dd_5
///




doc ///
Key
 socle
 (socle, Module)
Headline
 computes the socle of a module
Usage
 s = socle M
Inputs
 M:Module
Outputs
 s:Module
  submodule of M
Description
  Text
   If mm is the maximal ideal of R then
   socle M = (0*M) : mm.
   It is the sum of all the simple submodules of M
  Example
   S = ZZ/101[a,b]
   R = S/ideal"a5,b6"
   socle (R^1)
///

doc ///
Node
  Key
   rightAlmostSplit
   (rightAlmostSplit, Module)
  Headline
   produces the almost Split sequence with a given right end
  Usage
   C = rightAlmostSplit M
  Inputs
   M:Module
  Outputs
   C:Complex
  Description
    Text
     If R is a local Cohen-Macaulayring and M is an indecomposalble
     maximal Cohen-Macaulay R-module that is locally
     free on the punctured spectrum but not free, then there is a
     unique ``almost split'' short exact
     sequence with right hand
     module M

     e: 0 -> N -> E -> M -> 0.

     The is the output of rightAlmostSplit M
     Here N is the module translate(M), and e (up to scalars)
     the unique socle element of Ext^1(M,N). The module N
     is also an indecomposable maximal Cohen-Macaulay (MCM) module,
     free on the punctured spectrum.

     Similarly given an indecomposable MCM module N,
     that is locally free on the punctured spectrum
     but not isomorphic to the canonical module,
     there is a
     unique almost split sequence as above, with
     M = inverseTranslate N

     The irreducible maps from indecomposable MCM
     modules to M are precisely the maps induced
     on summands of E.

     If R is the localization at the vertex of the
     homogeneous coordinate ring of the
     rational normal curve C  of degree $d$ then any
     MCM R-module is locally free on the punctured
     spectrum, so the 
     the isomorphism classes of indecomposable
     Cohen-Macaulay R-modules are precisely
     $\omega = O_{C}(-2), O_{C}(-1), O_{C} \cong R,
     O_{C}(-1), ..O_{C}(d-3)$, 
    Example
     d = 5
     S = ZZ/32003[x_0..x_d]
     mat = matrix{
	 {x_0..x_(d-1)},
	 {x_1..x_d}}
     I = minors(2, mat)
     R = S/I
     RS = map(R,S)

     M1 = coker (R**mat)
     M = apply(d, i -> symmetricPower(i, M1))
     M/(X -> pdim pushForward(RS, X))
    Text
     M_i represents the line bundle $O_(P^1)(i points)$.
    Example
     rightAlmostSplit M_1
     netList (e = apply(d, i-> try (prune rightAlmostSplit M_i) else false))
     netList (E = apply(e, ee -> if ee=!=false then summands ee_1))
    Text
     Here M_i represents the line bundle
     O_(P^1)(i points).
  SeeAlso
   leftAlmostSplit
///

doc ///
Node
  Key
   leftAlmostSplit
   (leftAlmostSplit, Module)
  Headline
   produces the almost Split sequence with a given left end   
  Usage
   C = leftAlmostSplit N
  Inputs
   N:Module
  Outputs
   C:Complex
  Description
    Text
     See the description for @TO rightAlmostSplit@.
    Example
     S = ZZ/32003[x_0..x_3]
     mat = matrix{
	 {x_0,x_1,x_2},
	 {x_1,x_2,x_3}}
     I = minors(2, mat)
     R = S/I
     N = symmetricPower(2,coker (R**mat))
    Text
     N represents the line bundle $O_{P^1}(2)$.
    Example
     e = leftAlmostSplit N
     M = prune e_0
     
--     isIsomorphic(N, symmetricPower(2,M))
    Text
     This shows that N represents the line bundle
///

doc ///
  Key
    "Using MESQuivers"
    MESQuiver
  Headline
    a simple structure to aid in computing an Auslander-Reiten Quiver
  Description
    Text
      In order to compute an Auslander-Reiten quiver, one can create an object $Q$ of this type as
      below, and then do {\tt compute Q}.  This finds either all of a number of indecomposable
      CM modules over the base ring $R$.  Getting information out after the computation is
      described below as well.

      An {\tt MESQuiver} is initialized using @TO "mesQuiver"@, and computation
      is initiated with @TO (compute, MESQuiver)@, which optionally takes a {\tt Limit => n} to
      limit the number of computations that will be performed before stopping.
    Text
      As an example, lets consider the dimension 2 $D_5$ surface singularity.
      Notice that we choose degrees to make this homogeneous.  Considering inhomogeneous
      input (or evel local ring input) hasn't been considered much, and hasn't been tested.
    Example
      kk = ZZ/32009; -- has a root of 1.
      n = 5;
      R = kk[x,y,z, Degrees => {n-2, 2, n-1}]/(x^2*y + y^(n-1) + z^2);
    Text
      We need to provide some (Cohen-Macaulay) modules to make a {\tt MESQuiver}.
      Currently, we must provide $R^1$, as well as another indecomposable Cohen-Macaulay $R$-module.
      We could compute these ahead of time, and maybe we should.
    Example
      M = prune syzygy(2, coker vars R)
      Ms = {R^1, M}
    Text
      Now create the {\tt MESQuiver} object, and do the computation.
    Example
      Q = mesQuiver Ms
      compute Q
    Text
      Here is the information stored in $Q$.
    Example
      peek Q
    Text
      Use @TO (modules, MESQuiver)@ to get the list of modules and their indices.  It is also possible to
      use {\tt Q#"Modules"} to get the list of modules (indices are not provided with this version).

      For this example, there are six indecomposable CM modules.
    Example
      netList modules Q
      Q#"Modules"
    Text
      Use @TO (ses, MESQuiver)@ to get the list of lists of indices, indicating the
      module indices in the short exact sequences constructed.
    Example
      netList ses Q
    Text
      Here is how to read the output.  All indices refer to to the indecomposable modules {\tt modules Q},
      and zero refers to the free module $R^1$.
      Each line refers to a short exact complex, with arrows the usual Macaulay2 way, pointing left.
      In this example, and in fact in all hypersurface examples, the left/right module is the same.
      The first line gives:
      $0 \longleftarrow M_1 \longleftarrow R^1 \bigoplus M_2 \bigoplus M_3 \longleftarrow M_1 \longleftarrow 0.$
  Caveat
    (1)The name has been chosen to not interfere with Mahrud's Quiver class.

    (2)There is a chance that the code to decompose a module might fail, as one might need to create
    a field extension to see it.
  SeeAlso
    (compute, MESQuiver)
    (modules, MESQuiver)
    (ses, MESQuiver)
///

doc ///
  Key
   mesQuiver
   (mesQuiver, List)
  Headline
    initialize an MESQuiver object to compute AR Quivers
  Usage
    Q = mesQuiver Ms
  Inputs
   Ms:List
     of @ofClass Module@, all should be indecomposable CM modules over the same ring
  Outputs
   Q:MESQuiver
  Description
    Text
      The first module in the list must be the free module $R^1$.  The second is some choice
      of indecomposable CM $R$-module.
    Example
      R = ZZ/32009[x,y,z, Degrees => {3, 2, 4}]/(x^2*y + y^4 + z^2);
      M = prune syzygy(2, coker vars R)
      Ms = {R^1, M}
      Q = mesQuiver Ms
      peek Q
    Example
      compute Q
      netList modules Q
      netList ses Q
  SeeAlso
    "Using MESQuivers"
    MESQuiver
    (compute, MESQuiver)
    (modules, MESQuiver)
    (ses, MESQuiver)
///

doc ///
  Key
   compute
   (compute, MESQuiver)
   [compute, Limit]
  Headline
    compute some or all of the Auslander-Reiten Quiver of indecomposable CM modules
  Usage
    compute Q
  Inputs
   Q:MESQuiver
   Limit => ZZ
     The number of (left/right) split pairs to run before returning to the user
  Description
    Text
      This function is quite simple: it starts with a list of indecomposable CM modules,
      and one by one it computes the left and right almost split short exact sequences,
      with the next module in the list, which has not had its almost split sequence (either right or left)
      computed yet.  It finds the modules in the middle of the short exact sequence, and
      then decomposes it, possibly adding new modules to the list of undecomposables.
    Example
      R = ZZ/32009[x,y,z, Degrees => {3, 2, 4}]/(x^2*y + y^4 + z^2);
      M = prune syzygy(2, coker vars R)
      Ms = {R^1, M}
      Q = mesQuiver Ms
      peek Q
    Example
      compute Q
      peek Q
      netList modules Q
      netList ses Q
  SeeAlso
    "Using MESQuivers"
    MESQuiver
    (modules, MESQuiver)
    (ses, MESQuiver)
///

///
restart
debug loadPackage "AR"
ingoingList = {
    {0,0,1,1,1},
    {0,0,0,0,1},
    {1,0,0,0,0},
    {1,0,0,0,0},
    {1,1,0,0,0}}

tauList = {
    {1,0,0,0,0},
    {0,1,0,0,0},
    {0,0,0,1,0},
    {0,0,1,0,0},
    {0,0,0,0,1}
    }
(x1,x3,x4,x5,x7) =
    toSequence entries id_(ZZ^5)

netList apply(10,
    i-> theta(i,x7, ingoingList, tauList))
///

-*
  restart
  needsPackage "AR"
*-
TEST /// -- testing MESQuiver, Awhich?
  setRandomSeed 42
  kk = ZZ/32003
  R = kk[a,b, Degrees => {5,2}]/(a^2+b^5)
  M1 = prune ker vars R
  Q = mesQuiver {R^1, M1}
  compute Q
  peek Q
  netList ses Q
  netList modules Q

  assert(#modules Q === 3)
  assert(#ses Q === 2)
  assert(set ses Q === set {{1, {0,2}, 1}, {2, {1,2}, 2}})
///

-*
  restart
  needsPackage "AR"
*-
TEST /// -- testing MESQuiver, D5
  setRandomSeed 42
  kk = ZZ/32009 -- has a root of 1.
  n = 5
  R = kk[x,y,z, Degrees => {n-2, 2, n-1}]/(x^2*y + y^(n-1) + z^2)
  M = prune syzygy(2, coker vars R)
  Ms = {R^1, M}
  -- this version is simpler, only does Right Nodes
  elapsedTime (ses1, Ms1) = makeQuiver Ms -- .6 sec

  -- this does both left and right, and takes about twice as long
  Q = mesQuiver Ms
  elapsedTime compute Q -- 1.1 sec

  peek Q -- this is all that is contained in Q
  netList ses Q
  netList(Q#"SES")
  netList modules Q

  assert(#modules Q === 6)
  assert(#ses Q === 5)
  assert(set ses Q === set {
          {1, {0, 2, 3}, 1},
          {2, {1}, 2},
          {3, {1, 4, 5}, 3},
          {4, {3}, 4},
          {5, {3}, 5}})
///

--------------------------
-- E7, dim2 --------------
--------------------------
-*
  restart
  needsPackage "AR"
*-
TEST /// -- testing MESQuiver, D5
  setRandomSeed 42
  kk = ZZ/32009 -- has a root of 1.
  R = kk[x,y,z, Degrees => {6, 4, 9}]/(x^3 + x*y^3 + z^2)
  M = prune syzygy(2, coker vars R)
  Ms = {R^1, M}
  -- this version is simpler, only does Right Nodes
  elapsedTime (ses1, Ms1) = makeQuiver Ms -- 1.2 sec

  -- this does both left and right, and takes about twice as long
  Q = mesQuiver Ms
  elapsedTime compute Q -- 1.4 sec

  peek Q -- this is all that is contained in Q
  netList ses Q
  netList(Q#"SES")
  netList modules Q

  assert(#modules Q === 8)
  assert(#ses Q === 7)
  assert(set ses Q === set {
          {1, {0, 2}, 1},
          {2, {1, 3}, 2},
          {3, {2, 4, 5}, 3},
          {4, {3}, 4},
          {5, {3, 6}, 5},
          {6, {5, 7}, 6},
          {7, {6}, 7}})
///

--------------------------
-- Elliptic curve --------
--------------------------
-*
  restart
  needsPackage "AR"
*-
TEST ///
  setRandomSeed 42
  kk = ZZ/32009
  S = kk[x,y,z]
  R = quotient ideal(y^2*z - x*(x+z)*(x-z))
  F = res(coker vars R, LengthLimit => 4)
  M = coker F.dd_3
  assert(# summands M == 1) -- checking indecomposable.  Not sure this is definitive...

  M = coker map(R^2,, {{y, x*(x+z)}, {x-z, y*z}})
  assert(ann M == 0)
  Ms = {R^1, M}
  Q = mesQuiver Ms
  compute(Q, Limit => 3)  -- only do part of it.
  -- At this point, feel free to append modules to Q#"Modules"
  -- BUT: don't change the orders of the modules already there!
    
  assert(#modules Q == 5)
  assert(set ses Q == set {{1, {2}, 1}, {2, {1, 3}, 2}, {3, {4}, 3}})
///

end--

-* Development section *-
restart
needsPackage "AR"
check "AR"

uninstallPackage "AR"
restart
installPackage "AR"
viewHelp "AR"

-- Current example: A1 singularity
restart
debug needsPackage "AR"
kk = ZZ/32003
R = kk[x,y,z]/(x^2-y*z)
C = res(coker vars R, LengthLimit => 6)
C.dd
m = matrix"-x,-y;z,x"
M1 = coker m
C = rightAlmostSplit M1
C = rightAlmostSplit R^1
summands C_1

-- Current example: A2 singularity
restart
debug needsPackage "AR"
kk = ZZ/32003
R = kk[x,y,z,w]/(x*w-y*z)
C = res(coker vars R, LengthLimit => 6)
C.dd
m = matrix"x,y;z,w"
M1 = prune coker m
C = rightAlmostSplit M1
M2 = C_2
assert not first isIsomorphic(M1, M2)
assert first isIsomorphic(translate M1, M2) -- same
assert first isIsomorphic(translate M2, M1) -- same

-- Current example: A1 singularity, via knorr
restart
debug needsPackage "AR"
kk = ZZ/32003

R = kk[a]
phi = matrix{{a}}
(phi2, psi2) = knorr(phi, phi, symbol b, symbol c)
phi2 * psi2
R = kk[a,b]
phi = matrix{{a}}

psi = matrix{{b}}
(phi3,psi3) = knorr(phi,psi,c)
phi3 * psi3
(phi4,psi4) = knorr(phi3,psi3,d,e)
phi4 * psi4

(phi3,psi3) = knorr(phi,psi,u)
phi3 * psi3

R = kk[x,y,z,w]
phi = matrix{{x,y},{z,w}}
psi = matrix {{-w, y}, {z, -x}}
phi * psi
(phi5, psi5) = knorr(phi, psi, symbol u)
phi5 * psi5
(phi6, psi6) = knorr(phi5, psi5, symbol s, symbol t)
phi6 * psi6



C = res(coker vars R, LengthLimit => 6)
coker C.dd_3
relations coker C.dd_3
det(C.dd_3 _{0..10})
C = rightAlmostSplit M1

M2 = C_2
assert not first isIsomorphic(M1, M2)
assert first isIsomorphic(translate M1, M2) -- same
assert first isIsomorphic(translate M2, M1) -- same

-- Example: An singularity, via knorr
restart
debug needsPackage "AR"
kk = ZZ/32003
R = kk[a,b]
facs = AnFactorizations(3, R)
for f in facs list product f
facs = AnFactorizations(6, R)
for f in facs list product f

-- n = 3
restart
debug needsPackage "AR"
kk = ZZ/32003
R = kk[a,b, Degrees => {4,2}]/(a^2+b^4)
R = kk[a,b]/(a^2+b^4)
facs = AnFactorizations(3, R)
M = AnModules(3, R)
rightAlmostSplit M_1
for f in facs list product f

N = prune translate M_1
    E = Ext^1(M_1, N)
    sE := socle E;
    i := inducedMap(E, sE);
    psE := prune socle E;
    f := psE.cache.pruningMap;
    cov := inducedMap (psE, cover psE);
    prune yonedaExtension (i*o18)
M_1

-- n = 4
restart
debug needsPackage "AR"
kk = ZZ/32003
R = kk[a,b, Degrees => {5,2}]/(a^2+b^5)
facs = AnFactorizations(4, R)
M = AnModules(4, R)
M/isHomogeneous
rightAlmostSplit M_1
for f in facs list product f

N = prune translate M_1
netList (SESs = for m in M list rightAlmostSplit m)
netList for s in SESs list summands s_1

M

-- n = 5
restart
debug needsPackage "AR"
kk = ZZ/101
R = kk[a,b, Degrees => {6,2}]/(a^2+b^6)
facs = AnFactorizations(5, R)
M = AnModules(5, R)
M/isHomogeneous
for f in facs list product f
netList (SESs = for m in M list rightAlmostSplit m)
netList for s in SESs list summands s_1
for m in M list translate m
netList (SESs = for m in M list leftAlmostSplit m)
netList for s in SESs list summands s_1
C = res(coker vars R, LengthLimit => 5)
ZZ/101[x]; factor(x^2+1)
M = flatten(M/summands)
for m in M list prune translate m

-- n = 5
restart
debug needsPackage "AR"
kk = ZZ/32003
kk = ZZ/101
kk = ZZ/30013
--kk = QQ[i, DegreeRank => 0]/(i^2+1)
R = kk[x,b, Degrees => {6,2}]/(x^2+b^6)
--R = kk[a,b]/(a^2+b^6)
facs = AnFactorizations(5, R)
M = AnModules(5, R)
M = M/(m -> summands m)//flatten
M/(m -> summands(m, ExtendGroundField => 2))
--summands(M_2, ExtendGroundField => GF(32003, 2))

M/isHomogeneous
(M1, M2, N1, N2) = toSequence M
netList (SESs = for m in M list rightAlmostSplit m)
SESs/(c -> prune HH c)
netList for s in SESs list summands s_1
for m in M list translate m
netList (SESs = for m in M list leftAlmostSplit m)
netList for s in SESs list summands s_1
C = res(coker vars R, LengthLimit => 5)
ZZ/101[x]; factor(x^2+1)
M = flatten(M/summands)
for m in M list prune translate m

kk = ZZ/(nextPrime (1 + nextPrime 30000)); R = kk[x]; factor(x^2+1)
 
-- Dn, n is odd
restart
debug needsPackage "AR"
kk = ZZ/101
n = 5
R = kk[x,y, Degrees => {n-2, 2}]/(x^2*y + y^(n-1))
alpha = y
beta = x^2 + y^(n-2)
m1 = matrix{{alpha}}
m2 = matrix{{beta}}
A = coker m1
B = coker m2
-- node at A: Y1 --> A --> X1
-- node at B: X1 --> B --> Y1
  ses = rightAlmostSplit A
  summands ses_1
  Y1 = first oo
  ses = leftAlmostSplit A
  summands ses_1
  X1 = ses_1
  assert not first isIsomorphic(Y1, X1)

  -- at Y1: 
  ses = rightAlmostSplit Y1
  isIsomorphic(ses_2, X1)
  summands ses_1 -- B, N1
  N1 = last oo -- warning: might be the first element of summands
  ses = rightAlmostSplit X1
  isIsomorphic(ses_2, Y1)
  summands ses_1 -- 3 elements here: R, M1, A.
  M1 = oo_1

  -- all these give false
  isIsomorphic(M1, X1)
  isIsomorphic(M1, Y1)
  isIsomorphic(M1, N1)  

  mods = {A, B, X1, Y1, M1, N1}
  ses = rightAlmostSplit N1
  sums = summands ses_1
  isIsomorphic(sums_0, sums_1)
  for m in mods list first isIsomorphic(sums_0, m)
  for m in mods list first isIsomorphic(sums_1, m)
  X2 = sums_0
  mods = {A, B, X1, Y1, M1, N1, X2}

  ses = rightAlmostSplit X2
  isIsomorphic(ses_2, X2)
  sums = summands ses_1
  for m in mods list first isIsomorphic(sums_1, m)
  for m in mods list first isIsomorphic(sums_0, m)
