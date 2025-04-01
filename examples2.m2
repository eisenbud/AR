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

-- the input should be ModuleDictionary, right after explore is called...
-- there is probably a better way to get this information!
moduleList = method()
moduleList MutableHashTable := (ModuleDictionary) -> (
    H := hashTable for p in pairs ModuleDictionary list p#1 => p#0;
    for k in sort keys H list H#k
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
Ms = moduleList ModuleDictionary

elapsedTime (D5ses', D5') = makeQuiver Ms
assert(Ms == D5') -- the 2 quivers have same vertices
-- TODO: check that the data from 'see D5' and D5ses' matches up:
see D5
netList D5ses'
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
Ms = moduleList ModuleDictionary

elapsedTime (D5n2ses', D5n2') = makeQuiver Ms
assert(Ms == D5n2') -- the 2 quivers have same vertices
-- TODO: check that the data from 'see D5' and D5ses' matches up:
see D5n2
netList D5n2ses'

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
Ms = moduleList ModuleDictionary
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
Ms = moduleList ModuleDictionary
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
Ms = moduleList ModuleDictionary
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
Ms = moduleList ModuleDictionary
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
Ms = moduleList ModuleDictionary
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
Ms = moduleList ModuleDictionary
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
     Ms = {R^1, M}

     elapsedTime (RNC5ses', RNC5') = makeQuiver Ms
     netList RNC5ses'
     netList RNC5'

     elapsedTime see explore(RNC5 = new ARQuiver, 10, {M}, {symbol M})
     Ms = moduleList ModuleDictionary
     netList RNC5ses'

-------------------------
-- RNC6 -----------------
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

     elapsedTime (RNC6ses', RNC6') = makeQuiver Ms
     netList RNC6ses'
     netList RNC6'
     
     elapsedTime see explore(RNC6 = new ARQuiver, 15, {M}, {symbol M})
     Ms = moduleList ModuleDictionary
     netList RNC6ses'

     elapsedTime (RNC6ses', RNC6') = makeQuiver Ms
