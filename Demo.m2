restart
load "methods.m2"

-----------------------------------------
-- EXAMPLE 1: 2x2 minors of 3x3 matrix --
-----------------------------------------
x = symbol x
R = ZZ/101[apply((1,1)..(3,3), (i,j) -> x_(10*i+j))]
M = genericMatrix(R,3,3)
I = minors(2,M)
(F,hb) = selfDualForm res I; betti F

--note: it seems that d3 = (negative antidiagonal)*(transpose d2) in selfDualForm
--and that this negative is necessary for the basis of F2 to be hyperbolic

--use an isotropic subspace belonging to the "other" component
newd2 = F.dd_3^{0..6,8}
newF = chainComplex(
    d1 = map(R^1,,dual gens trim ker dual newd2),
    d2 = map(source d1,,newd2),
    d3 = map(source d2,,gens trim ker newd2)
    )
prune HH newF
prune HH dual newF
betti newF

-----------------------------------
-- EXAMPLE 2: from Pedro's email --
-----------------------------------
R = ZZ/5[w,x,y,z];
I = inverseSystem matrix{{x^4 + y^4 + z^4 + w^4 + (x+y+z)^4 + (z+w)^4}}
(F,hb) = selfDualForm res I; betti F

newd2 = F.dd_3^{0..4,6}
newF = chainComplex(
    d1 = map(R^1,,dual gens trim ker dual newd2),
    d2 = map(source d1,,newd2),
    d3 = map(source d2,,gens trim ker newd2)
    )
prune HH newF
prune HH dual newF
betti newF

------------------------------
-- EXAMPLE 3: dga structure --
------------------------------

--(1,9,16,9,1)
x = symbol x
R = ZZ/101[apply((1,1)..(3,3), (i,j) -> x_(10*i+j))]
M = genericMatrix(R,3,3)
I = minors(2,M)
F = res I

--(1,9,16,9,1) random
R = ZZ/101[w,x,y,z];
I = inverseSystem random(R^{1:2},R^1)
F = res I

--(1,6,10,6,1) random, the lifting step takes a moment
R = ZZ/101[w,x,y,z];
I = inverseSystem random(R^{1:3},R^1)
F = res I

--(1,7,12,7,1), example 2 above, the lifting takes a while...
R = ZZ/101[w,x,y,z];
I = inverseSystem matrix{{x^4 + y^4 + z^4 + w^4 + (x+y+z)^4 + (z+w)^4}}
F = res I

--we compute a choice of multiplication by lifting in the following Schur complex on d2*
--
--  0 -> F4 ** wedge^3 F1* -> F4 ** wedge^2 F1* ** F2* -g-> F4 ** F1* ** S2F2* --> (what is next?)
--
g = (
    (id_(dual F_1)**divProd(1,1,dual F_2))*(id_(dual F_1)**(dual F.dd_2)**id_(dual F_2))*((dual wedgeProduct(1,1,F_1))**id_(dual F_2))
    );
--this lifting step can be slow depending on how complicated the matrix d2 is...
lifttest = cycletest//map(target cycletest,,g);
zero (cycletest - g*lifttest)
m11 = (1/2)*(inverse adjoint(F2Form F,F_2,F_2))*adjoint'(lifttest,exteriorPower(2,dual F_1),F_2);

--check Kustin-Miller 3.1
--(a) Leibniz
zero(F.dd_2*m11 - (F.dd_1**id_(F_1))*(dual wedgeProduct(1,1,dual F_1)))
--(b)
LHS = F.dd_1**(F2Form F) ;
RHS1 = (F2Form F)*((m11*wedgeProduct(1,1,F_1))**id_(F_2))*(id_(F_1)**F.dd_2**id_(F_2));
RHS2 = (F2Form F)*((m11*wedgeProduct(1,1,F_1))**id_(F_2))*(id_(F_1)**(flip(F_2,F_1)*(id_(F_2)**F.dd_2)));
zero(LHS-RHS1-RHS2)
--(c) is automatic since it's a map from wedge^2


--translate it to the self-dual res
(sdF,hb) = selfDualForm F
sdF.dd_2*(inverse hb)
zero(F.dd_2 - sdF.dd_2*(inverse hb))
m11' = (inverse hb)*m11;


--(a) Leibniz
zero(sdF.dd_2*m11' - (sdF.dd_1**id_(F_1))*(dual wedgeProduct(1,1,dual F_1)))
--(b)
LHS = sdF.dd_1**(F2Form sdF) ;
RHS1 = (F2Form sdF)*((m11'*wedgeProduct(1,1,F_1))**id_(F_2))*(id_(F_1)**sdF.dd_2**id_(F_2));
RHS2 = (F2Form sdF)*((m11'*wedgeProduct(1,1,F_1))**id_(F_2))*(id_(F_1)**(flip(F_2,F_1)*(id_(F_2)**sdF.dd_2)));
zero(LHS-RHS1-RHS2)
--(c) is automatic since it's a map from wedge^2


--DGF is direct sum of F_i
--D is the differential
--mm is the multiplication on DGF
(DGF, D, mm) = makeDGA(sdF,m11'); --this method assumes sdF is in self-dual form, as set up above!!

--swap
TAU = (
    sum((0,0)..(4,4), (i,j) -> (DGF_[j]**DGF_[i])*(-1)^(i*j)*flip(F_i,F_j)*(DGF^[i]**DGF^[j]))
    );
--differential on DGF**DGF
D2 = (
    D**id_(DGF)
    +
    TAU*(D**id_(DGF))*TAU
    );

--correct in bottom degree
zero(1 - DGF^[0]*mm*(DGF_[0]**DGF_[0]))

--graded commutativity
zero(mm - mm*TAU)

--Leibniz
zero(mm*D2 - D*mm)

--strict associativity
zero(mm*(mm**id_DGF) - mm*(id_DGF**mm))









