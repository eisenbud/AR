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
	"DirectSummands"
	},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {
    "canonicalDual",
    "transposeModule",
    "syzygy",
    "translate",
    "inverseTranslate",
    "socle",

    "rightAlmostSplit",
    "leftAlmostSplit",
--    "irreducibles",
    --Symbols:
    "omega",
    }

-* Code section *-
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
translate Module := Module => M -> (
    d := dim M;
    Mt := transposeModule M;
    Md := syzygy(d,Mt);
    canonicalDual Md
    )

inverseTranslate = method()
inverseTranslate Module := Module => N -> (
    d := dim N;
    R := ring N;
    dualN := canonicalDual N;
    syzygy(d,transposeModule dualN)
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
rightAlmostSplit Module := Complex => M -> (
    --produces 0->N->E->M->0 almost split
    N := translate M;
    E := Ext^1(M, N);
    sE := socle E;
    i := inducedMap(E, sE);
    psE := prune socle E;
    f := psE.cache.pruningMap;
    cov := inducedMap (psE, cover psE);
    prune yonedaExtension (i*f*cov)
    )
    
leftAlmostSplit = method()
leftAlmostSplit Module := Complex => N -> (
    --produces 0->N->E->M->0 almost split
    M := inverseTranslate N;
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

///
restart
loadPackage "AR"
///
end--
-*
-* Test section *-
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
///

end--

-* Development section *-
restart
debug needsPackage "AR"
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
summands C_1
C_1_[0]

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
