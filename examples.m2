-- D5
restart
debug needsPackage "AR"
load "./quiver.m2"
kk = ZZ/101
n = 5
R = kk[x,y, Degrees => {n-2, 2}]/(x^2*y + y^(n-1))
M = prune syzygy(2, coker vars R)

D5 = new ARQuiver
explore(D5, 10, {M}, {symbol M})
see D5


D5H = hashTable for p in pairs D5 list (
    (p#0, if instance(p#1, MutableList) then toList p#1 else p#1)
    )
count = 0;
H = hashTable for k in keys D5 list (count = count+1; k => count)

D5quiver = for p in pairs D5H list (
    {H#(p#0), try H#(known_D5 syzygy(1, p#0)), try H#(known_D5 translate p#0), apply(p#1, m -> H#m)}
    )
netList D5quiver

-- D5, dim2
restart
debug needsPackage "AR"
load "./quiver.m2"
kk = ZZ/101
n = 5
R = kk[x,y,z, Degrees => {n-2, 2, n-1}]/(x^2*y + y^(n-1) + z^2)
M = prune syzygy(2, coker vars R)

D5 = new ARQuiver
explore(D5, 10, {M}, {symbol M})
see D5

debug DirectSummands
tallySummands keys D5

D5H = hashTable for p in pairs D5 list (
    (p#0, if instance(p#1, MutableList) then toList p#1 else p#1)
    )
count = 0;
H = hashTable for k in keys D5 list (count = count+1; k => count)

D5quiver = for p in pairs D5H list (
    m0 := try (known_D5 p#0);
    {H#m0, try H#(known_D5 syzygy(1, p#0)), try H#(known_D5 translate p#0), apply(p#1, m -> H#m)}
    )
netList D5quiver

verts = {1,2,3,4,5,7}
ingoing = hashTable{1 => {4,5,7}, 2 => {7},
    3 => {7}, 4 => {1}, 5 => {1}, 7 => {1,2,3}}
translates = hashTable {1 => {1}, 2 => {},
    3 => {3}, 4 => {5}, 5 => {4}, 7 => {7}}

R = ZZ[x_1, x_2, x_3, x_4, x_5, x_7]
ingoing = transpose matrix{{x_4 + x_5 + x_7,
        x_7,
        x_7,
        x_1,
        x_1,
        x_1+x_2+x_3
        }}
coeffs = L -> flatten entries last coefficients(L, Monomials => gens R)
theta = method()
theta RingElement := RingElement => L -> (
    (matrix{coeffs L} * ingoing)_(0,0)
    )
tau = method()
taumatrix = transpose matrix{{
    x_1,
    0,
    x_3,
    x_5,
    x_4,
    x_7}}
tau RingElement := RingElement => L -> (
    (matrix{coeffs L} * taumatrix)_(0,0)    
    )
pos = L -> (
    cfs := coeffs L;
    (matrix{{for a in cfs list if a > 0 then a else 0}} * transpose vars R)_(0,0)
    )
neg = L -> (
    cfs := coeffs L;
    (matrix{{for a in cfs list if a < 0 then -a else 0}} * transpose vars R)_(0,0)
    ) 
theta(ZZ, RingElement) := RingElement => (i, L) -> (
    if i === 1 then return theta L;
    theta(pos theta(i-1, L)) - tau (pos theta(i-2, L))
    )
theta (x_4)
theta(1, x_4)
theta(2, x_4)
-- D6
restart
debug needsPackage "AR"
load "./quiver.m2"
kk = ZZ/101
n = 6
R = kk[x,y, Degrees => {n-2, 2}]/(x^2*y + y^(n-1))
M = prune syzygy(2, coker vars R)
summands M
setAttribute(M, ReverseDictionary, Label{symbol M, 0})
explore0(5, M)
see quiver

-- E6
restart
debug needsPackage "AR"
load "./quiver.m2"
kk = ZZ/101
R = kk[x,y, Degrees => {3, 2}]/(x^3 + x*y^3)
M = prune syzygy(2, coker vars R)
summands M
setAttribute(M, ReverseDictionary, Label{symbol M, 0})
explore0(5, M)
see quiver

Ms = keys quiver
# oo
newMs = {Ms_0}
for i from 1 to #Ms - 1 do (
    locs := isIso(Ms_i, newMs);
    if #locs == 0 then newMs = append(newMs, Ms_i);
    )

-- E7 "by hand" using AR code
restart
debug needsPackage "AR"
load "./quiver.m2"
kk = ZZ/101
R = kk[x,y, Degrees => {3, 2}]/(x^3 + x*y^3)
A = coker matrix{{x}}
B = coker matrix {{x^2 + y^3}}
M = prune syzygy(2, coker vars R)
res coker lift(relations M, ambient R)
summands M
Ms = {R^1, M}

E7 = new ARQuiver
explore(E7, 5, {M}, {symbol M}) 

ses = rightAlmostSplit Ms_1
  isIso(ses_2, Ms) -- new
  Ms = append(Ms, ses_2)
  sums = summands ses_1
  Ms = append(Ms, sums_1)
  netList Ms

ses = rightAlmostSplit Ms_2
  isIso(ses_2, Ms) -- already exists
  sums = summands ses_1
  isIso(first sums, Ms)
  Ms = append(Ms, first sums)
  netList Ms  

ses = rightAlmostSplit Ms_3
  isIso(ses_2, Ms) -- already exists
  sums = summands ses_1
  isIso(sums_0, Ms)
  isIso(sums_1, Ms) -- not new
  Ms = append(Ms, first sums)
  netList Ms  

ses = rightAlmostSplit Ms_4
  isIso(ses_2, Ms) -- already exists
  sums = summands ses_1
  isIso(sums_0, Ms)
  isIso(sums_1, Ms) -- not new
  Ms = append(Ms, first sums)
  netList Ms  

ses = rightAlmostSplit Ms_5
  isIso(ses_2, Ms) -- already exists
  sums = summands ses_1
  isIso(sums_0, Ms) -- exists
  isIso(sums_1, Ms) -- new
  isIso(sums_2, Ms) -- new
  Ms = append(Ms, sums_1)
  Ms = append(Ms, sums_2)
  netList Ms  

ses = rightAlmostSplit Ms_6
  isIso(ses_2, Ms) -- already exists
  sums = summands ses_1
  isIso(sums_0, Ms) -- new
  isIso(sums_1, Ms) -- new
  isIso(sums_2, Ms) -- old
  Ms = append(Ms, sums_0)
  Ms = append(Ms, sums_1)
  netList Ms  

ses = rightAlmostSplit Ms_7
  isIso(ses_2, Ms) -- already exists
  sums = summands ses_1
  isIso(sums_0, Ms) -- new
  isIso(sums_1, Ms) -- old
  Ms = append(Ms, sums_0)
  netList Ms  
  
ses = rightAlmostSplit Ms_8
  isIso(ses_2, Ms) -- already exists
  sums = summands ses_1
  isIso(sums_0, Ms) -- new
  isIso(sums_1, Ms) -- old
  Ms = append(Ms, sums_0)
  netList Ms  

ses = rightAlmostSplit Ms_9
  isIso(ses_2, Ms) -- new
  sums = summands ses_1
  isIso(sums_0, Ms) -- old
  Ms = append(Ms, ses_2)
  netList Ms  

ses = rightAlmostSplit Ms_10
  isIso(ses_2, Ms) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- old
  isIso(sums_1, Ms) -- new
  Ms = append(Ms, sums_1)
  netList Ms  

ses = rightAlmostSplit Ms_11
  isIso(ses_2, Ms) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- new
  isIso(sums_1, Ms) -- old
  Ms = append(Ms, sums_0)
  netList Ms  

ses = rightAlmostSplit Ms_12
  isIso(ses_2, Ms) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- old

ses = rightAlmostSplit Ms_13
  isIso(ses_2, Ms) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- old

ses = rightAlmostSplit Ms_14
  isIso(ses_2, Ms) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- old

--------------------------
-- Elliptic curve --------
--------------------------
restart
debug needsPackage "AR"
kk = ZZ/23
R = kk[x,y,z]/(y^2*z-x*(x-z)*(x-3*z))
needsPackage "RationalPoints2"
rationalPoints(ideal R, Projective => true)
pts23 = {{1, 0, 1}, {1, 6, 3}, {1, -6, 3}, {1, 5, 5}, {1, -5, 5}, {1, 8, 6}, {1, -8, 6}, {1, 2, 7}, {1, -2, 7}, {1, 0, 8}, {1, 8, 9}, {1, -8, 9}, {1, 2, 11}, {1, -2, 11}, {1, 6, -5}, {1, -6, -5}, {1, 1, -4}, {1, -1, -4}, {1, 5, -3}, {1, -5, -3}, {1, 1, -2}, {1, -1, -2}, {0, 1, 0}, {0, 0, 1}}
trim minors(2, matrix{pts23_0} || vars R)
M = prune module oo

--M = prune syzygy(4, coker vars R)
summands M
Ms = {R^1, M}

ses = rightAlmostSplit Ms_1
  isIso(ses_0, Ms_1) -- old
  isIso(ses_2, Ms_1) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- new
  Ms = append(Ms, sums_0)
  netList Ms

ses = rightAlmostSplit Ms_2
  isIso(ses_0, Ms)
  isIso(ses_2, Ms)
  sums = summands ses_1
  for x in sums list isIso(x, Ms)
  Ms = append(Ms, sums_0)

ses = rightAlmostSplit Ms_3
  isIso(ses_0, Ms)
  isIso(ses_2, Ms)
  sums = summands ses_1
  for x in sums list isIso(x, Ms)
  Ms = append(Ms, sums_0)

  
  isIso(ses_2, Ms) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- new
  Ms = append(Ms, sums_0)
  netList Ms
  


----- RNC degree 5 --------------
restart
debug needsPackage "AR"
load "./quiver.m2"
     d = 5
     S = ZZ/32003[x_0..x_d]
     mat = matrix{
	 {x_0..x_(d-1)},
	 {x_1..x_d}}
 
     I = minors(2, mat)
     R = S/I

     M = coker (mat ** R)
     RNC5 = new ARQuiver
     explore(RNC5, 5, {M}, {symbol M})
     see RNC5
         
     RS = map(R,S)
     M1 = coker (R**mat)
     M = apply(d, i -> symmetricPower(i, M1))
     M/(X -> pdim pushForward(RS, X))
