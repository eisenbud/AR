-- D5
restart
debug needsPackage "AR"
load "./quiver.m2"
kk = ZZ/101
n = 5
R = kk[x,y, Degrees => {n-2, 2}]/(x^2*y + y^(n-1))
M = prune syzygy(2, coker vars R)
summands M
setAttribute(M, ReverseDictionary, Label{symbol M, 0})
explore0(5, M)
see quiver

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
kk = ZZ/101
R = kk[x,y,z]/(y^2*z-x*(x-z)*(x-3*z))

M = prune syzygy(4, coker vars R)
summands M
Ms = {R^1, M}

ses = rightAlmostSplit Ms_1
  isIso(ses_0, Ms_1) -- old
  isIso(ses_2, Ms_1) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- new
  Ms = append(Ms, sums_0)
  netList Ms

ses = leftAlmostSplit Ms_1
  isIso(ses_0, Ms)
  isIso(ses_2, Ms)
  sums = summands ses_1
  for x in sums list isIso(x, Ms)
  
  isIso(ses_2, Ms) -- old
  sums = summands ses_1
  isIso(sums_0, Ms) -- new
  Ms = append(Ms, sums_0)
  netList Ms
  

