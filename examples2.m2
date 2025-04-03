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
end--

--------------------------
-- D5 dim=1 --------------
--------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009 -- has a root of 1.
n = 5
R = kk[x,y, Degrees => {n-2, 2}]/(x^2*y + y^(n-1))
M = prune syzygy(2, coker vars R)
Ms = {R^1, M}
elapsedTime (D5ses, D5) = makeQuiver Ms
netList D5ses
netList D5


elapsedTime see explore(D5 = new ARQuiver, 10, {M}, {symbol M})
Ms = vertices D5

elapsedTime (D5ses', D5') = makeQuiver Ms
assert(Ms == D5') -- the 2 quivers have same vertices
-- TODO: check that the data from 'see D5' and D5ses' matches up:
see D5
netList D5ses'

-- syzygy stuff
     -- which modules are syzygy modules?
     Ms = D5'
     for i from 1 to #Ms - 1 list (
       sums = summands syzygy(1, Ms_i);
       for m in sums list isIso(m, Ms)
       )
     netList oo
income = entries incomingMatrix(D5ses', D5')
taumat = entries translates(D5ses', D5')
In = entries id_(ZZ^(#D5' - 1))
theta(1, In_0, income, taumat)
for j from 0 to #Ms-2 list
  matrix for i from 1 to 10 list theta(i, In_j, income, taumat)
---------------

--------------------------
-- D5 dim=2 --------------
--------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009 -- has a root of 1.
n = 5
R = kk[x,y,z, Degrees => {n-2, 2, n-1}]/(x^2*y + y^(n-1) + z^2)
M = prune syzygy(2, coker vars R)
Ms = {R^1, M}
elapsedTime (D5n2ses', D5n2') = makeQuiver Ms
netList D5n2ses'
netList D5n2'

elapsedTime see explore(D5n2 = new ARQuiver, 10, {M}, {symbol M})
Ms = vertices D5n2
show D5n2 -- fails, no graphviz, apparently.

elapsedTime (D5n2ses', D5n2') = makeQuiver Ms
assert(Ms == D5n2') -- the 2 quivers have same vertices
-- TODO: check that the data from 'see D5' and D5ses' matches up:
see D5n2
netList D5n2ses'

-- syzygy stuff
     -- which modules are syzygy modules?
     Ms = D5n2'
     for i from 1 to #Ms - 1 list (
       sums = summands syzygy(1, Ms_i);
       for m in sums list isIso(m, Ms)
       )
     netList oo
income = entries incomingMatrix(D5n2ses', D5n2')
taumat = entries translates(D5n2ses', D5n2')
In = entries id_(ZZ^(#D5n2' - 1))
theta(1, In_0, income, taumat)
for j from 0 to #Ms-2 list
  matrix for i from 1 to 10 list theta(i, In_j, income, taumat)
---------------

--------------------------
-- D6 dim=1 --------------
--------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009 -- has a root of 1.
n = 6
R = kk[x,y, Degrees => {n-2, 2}]/(x^2*y + y^(n-1))
M = prune syzygy(2, coker vars R)
Ms = {R^1, M}
elapsedTime (D6ses', D6') = makeQuiver Ms
netList D6ses'
netList D6'

elapsedTime see explore(D6 = new ARQuiver, 10, {M}, {symbol M})
Ms = vertices D6
netList D6ses'

--------------------------
-- D6 dim=2 --------------
--------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009 -- has a root of 1.
n = 6
R = kk[x,y,z, Degrees => {n-2, 2, n-1}]/(x^2*y + y^(n-1) + z^2)
M = prune syzygy(2, coker vars R)
Ms = {R^1, M}
elapsedTime (D6n2ses', D6n2') = makeQuiver Ms
netList D6n2ses'
netList D6n2'

elapsedTime see explore(D6n2 = new ARQuiver, 10, {M}, {symbol M})
Ms = vertices D6n2
netList D6n2ses'

--------------------------
-- E7, dim1 --------------
--------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009
R = kk[x,y, Degrees => {6, 4}]/(x^3 + x*y^3)
M = prune syzygy(2, coker vars R)
res coker lift(relations M, ambient R)
Ms = {R^1, M}
elapsedTime (E7ses', E7') = makeQuiver Ms
netList E7ses'
netList E7'

elapsedTime see explore(E7 = new ARQuiver, 15, {M}, {symbol M})
Ms = vertices E7
netList E7ses'

--------------------------
-- E7, dim2 --------------
--------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009
R = kk[x,y,z, Degrees => {6, 4, 9}]/(x^3 + x*y^3 + z^2)
M = prune syzygy(2, coker vars R)
res coker lift(relations M, ambient R)
Ms = {R^1, M}
elapsedTime (E7d2ses', E7d2') = makeQuiver Ms
netList E7d2ses'
netList E7d2'

elapsedTime see explore(E7 = new ARQuiver, 15, {M}, {symbol M})
Ms = vertices E7
netList E7d2ses'

--------------------------
-- E8, dim1 --------------
--------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009
R = kk[x,y, Degrees => {5, 3}]/(x^3 + y^5)
M = prune syzygy(2, coker vars R)
res coker lift(relations M, ambient R)
Ms = {R^1, M}
elapsedTime (E8ses', E8') = makeQuiver Ms
netList E8ses'
netList E8'

elapsedTime see explore(E8 = new ARQuiver, 15, {M}, {symbol M})
Ms = vertices E8
netList E8'

--------------------------
-- E8, dim2 --------------
--------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009
R = kk[x,y,z, Degrees => {10, 6, 15}]/(x^3 + y^5 + z^2)
M = prune syzygy(2, coker vars R)
res coker lift(relations M, ambient R)
Ms = {R^1, M}
elapsedTime (E8d2ses', E8d2') = makeQuiver Ms
netList E8d2ses'
netList E8d2'

elapsedTime see explore(E8d2 = new ARQuiver, 15, {M}, {symbol M})
Ms = vertices E8d2
netList E8d2ses'

-------------------------
-- RNC5 -----------------
-------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009
     d = 5
     S = kk[x_0..x_d]
     mat = matrix{
	 {x_0..x_(d-1)},
	 {x_1..x_d}}
 
     I = minors(2, mat)
     R = S/I
     M = coker (mat ** R)

     elapsedTime see explore(RNC5 = new ARQuiver, 10, {M}, {symbol M})
     Ms = vertices RNC5

     elapsedTime (ses, Ms') = makeQuiver Ms
     netList ses
     netList Ms'
     
     -- which modules are syzygy modules?
     for i from 1 to #Ms - 1 list (
       sums = summands syzygy(1, Ms_i);
       for m in sums list isIso(m, Ms)
       )
     netList oo
-- +---+---+---+---+
-- |{4}|   |   |   |
-- +---+---+---+---+
-- |{4}|{4}|{4}|   |
-- +---+---+---+---+
-- |{4}|{4}|   |   |
-- +---+---+---+---+
-- |{4}|{4}|{4}|{4}|
-- +---+---+---+---+

-- the following is currently wrong...
-- maybe because I am using the wrong translate function?
income = entries incomingMatrix(ses, Ms)
taumat = entries translates(ses, Ms)
In = entries id_(ZZ^(#Ms - 1))
theta(1, In_0, income, taumat)
for j from 0 to #Ms-2 list
  matrix for i from 1 to 10 list theta(i, In_j, income, taumat)
---------------
-- Let's check translate, inverseTranslate, tau(M)...
M = Ms_1
tauM = prune canonicalDual Hom(M, R)
#summands tauM == 1
isIso(tauM, Ms)

M = Ms_2
tauM = prune canonicalDual Hom(M, R)
#summands tauM == 1
isIso(tauM, Ms)

M = Ms_3
tauM = prune canonicalDual Hom(M, R)
#summands tauM == 1
isIso(tauM, Ms)

M = Ms_4
tauM = prune canonicalDual Hom(M, R)
#summands tauM == 1
isIso(tauM, Ms)

code methods translate
code methods inverseTranslate
isIso(prune translate Ms_1, Ms) -- 4
isIso(prune inverseTranslate Ms_1, Ms) -- 2

isIso(prune translate Ms_2, Ms) -- 1
isIso(prune inverseTranslate Ms_2, Ms) -- nothing (0 module)

-------------------------
-- RNC6 -----------------
-------------------------
-------------------------
-- RNC5 -----------------
-------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009
     d = 6
     S = kk[x_0..x_d]
     mat = matrix{
	 {x_0..x_(d-1)},
	 {x_1..x_d}}
 
     I = minors(2, mat)
     R = S/I
     M = coker (mat ** R)
     Ms = {R^1, M}

     -- elapsedTime see explore(RNC5 = new ARQuiver, 10, {M}, {symbol M})
     -- Ms = vertices RNC5

     elapsedTime (ses, Ms') = makeQuiver Ms
     Ms = Ms'
     netList ses
     netList Ms'
     
     -- which modules are syzygy modules?
     for i from 1 to #Ms - 1 list (
       sums = summands syzygy(1, Ms_i);
       for m in sums list isIso(m, Ms)
       )
     netList oo

-- the following is currently wrong...
-- maybe because I am using the wrong translate function?
income = entries incomingMatrix(ses, Ms)
taumat = entries translates(ses, Ms)
In = entries id_(ZZ^(#Ms - 1))
theta(1, In_0, income, taumat)
for j from 0 to #Ms-2 list
  matrix for i from 1 to 10 list theta(i, In_j, income, taumat)
---------------





restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009
     d = 6
     S = kk[x_0..x_d]
     mat = matrix{
	 {x_0..x_(d-1)},
	 {x_1..x_d}}
 
     I = minors(2, mat)
     R = S/I

     M = coker (mat ** R)
     Ms = {R^1, M}

     elapsedTime (RNC6ses', RNC6') = makeQuiver Ms
     netList RNC6ses'
     netList RNC6'
     
     elapsedTime see explore(RNC6 = new ARQuiver, 15, {M}, {symbol M})
     Ms = vertices RNC6


     elapsedTime (RNC6ses', RNC6') = makeQuiver Ms
     netList RNC6ses'
     see RNC6
     
     for i from 1 to #Ms - 1 list (
       sums = summands syzygy(1, Ms_i);
       for m in sums list isIso(m, Ms)
       )
-- Note: only Ms_3 is a syzygy module, occurs with different weights.
-- +---+---+---+---+---+
-- |{3}|   |   |   |   |
-- +---+---+---+---+---+
-- |{3}|{3}|{3}|   |   |
-- +---+---+---+---+---+
-- |{3}|{3}|{3}|{3}|{3}|
-- +---+---+---+---+---+
-- |{3}|{3}|   |   |   |
-- +---+---+---+---+---+
-- |{3}|{3}|{3}|{3}|   |
-- +---+---+---+---+---+
     

---------------------------
-- C_(n,a): z = n-th root of unity
-- k[s,t] -- action: s |-> z*s, t |-> z^a*t
-- invariant ring R generated by all monomials:
--  s^p t^q, such that p + a*q == 0 (mod n)
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009

invariantsCna = method()
invariantsCna(ZZ, ZZ) := List => (n, a) -> (
    g := gcd(n,a);
    if g > 1 then (n,a) = (n//g, a//g);
    A = kk[s,t, Degrees => {1, a}];
    middles := for q from 1 to n-1 list (
        r := (a*q) % n;
        s^(n-r)*t^q
        );
    {s^n} | middles | {t^n}
    )

invs = invariantsCna(5,2)
invs = invs_{0,1,2,5}
invs/degree
S = kk[x,y,z,w, Degrees => invs/degree]
phi = map(A, S, invs)
I = ker phi
isHomogeneous I
R = S/I
F = res(coker vars R, LengthLimit => 4)
M = coker F.dd_3
isHomogeneous M
Ms = summands M
isIso(Ms_0, Ms_1)
Ms = {Ms_0, Ms_1}

elapsedTime see explore(Q = new ARQuiver, 15, Ms, {symbol M0, symbol M1})

Ms = vertices Q
arrows Q
triangles Q
summands (leftAlmostSplit Q_1)_1
(triangles Q)_1
show Q
Triangles


--------------------------------
restart
debug needsPackage "AR"
load "./quiver.m2"
load "./examples2.m2"

kk = ZZ/32009
S = kk[x,y,z]
R = quotient ideal(y^2*z - x*(x+z)*(x-z))
F = res(coker vars R, LengthLimit => 4)
M = coker F.dd_3
summands M

Q = new ARQuiver
elapsedTime see explore(Q, 2, {M}, {symbol M})
elapsedTime see explore(Q, 1)

-- Q_0: {}     <- 0 <- {}     |   ~> 0 ~>  
-- Q_1: {2}    <- 1 <- {2}    | 1 ~> 1 ~> 1
-- Q_2: {1, 3} <- 2 <- {1, 3} | 2 ~> 2 ~> 2
-- Q_3: {1, 5} <- 3 <- {1, 5} | 3 ~> 3 ~> 3

vertices Q
