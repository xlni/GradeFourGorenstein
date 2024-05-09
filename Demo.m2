load "methods.m2"

-----------------------------------------
-- EXAMPLE 1: 2x2 minors of 3x3 matrix --
-----------------------------------------
x = symbol x
R = ZZ/101[apply((1,1)..(3,3), (i,j) -> x_(10*i+j))]
M = genericMatrix(R,3,3)
I = minors(2,M)
F = selfDualForm res I; betti F

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
R = ZZ/101[w,x,y,z];
I = inverseSystem matrix{{x^4 + y^4 + z^4 + w^4 + (x+y+z)^4 + (z+w)^4}}
F = selfDualForm res I; betti F

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
--the lifting step didn't terminate when I ran it on the earlier examples...
--here are two other examples that worked:

--example 1
R = ZZ/101[w,x,y,z];
I = inverseSystem random(R^{1:3},R^1)
F = selfDualForm res I; betti F

--example 2 (the lifting step is slow for this one)
R = ZZ/101[w,x,y,z];
I = inverseSystem random(R^{1:2},R^1)
F = selfDualForm res I; betti F


--we compute a choice of multiplication by lifting in the Schur complex
--
--  0 -> F4 ** wedge^3 F1* -> wedge^2 F1* ** F2 -g-> F1* ** S2F2 -g'-> F4* ** S3F2
--
S2F2 = target symProd(1,1,F_2);
g = (
    (id_(dual F_1)**symProd(1,1,F_2))*(id_(dual F_1)**(F.dd_3)**id_(F_2))*((dual wedgeProduct(1,1,F_1))**id_(F_2))
    );
g' = (
    symProd(1,2,F_2)*(F.dd_3**id_(S2F2))
    );
--construct cycle to be lifted
antidiag = map((dual F_4)**(F_2),(dual F_2),apply(rank F_2, i -> (i,(rank F_2)-i-1) => 1));
trivrep0 = adjoint(antidiag, R^1, dual F_2);
trivrep = symProd(1,1,F_2)*trivrep0;
cycletest = (-1/2)*(F.dd_4**trivrep);
zero (g'*cycletest) --check it's a cycle

--this lifting step can be really slow! I don't know if there's a better way of doing this...
lifttest = cycletest//map(target cycletest,,g);
m11 = adjoint'(lifttest,exteriorPower(2,dual F_1),F_2);

--DGF is direct sum of F_i
--D is the differential
--mm is the multiplication on DGF
(DGF, D, mm) = makeDGA(F,m11);

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









