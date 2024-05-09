symProd = method()
symProd (ZZ,ZZ,Module) := Matrix => (a,b,M) -> (
    R := ring M;
    d := rank M;
    if a==0 or b==0 then return id_((ring M)^(binomial(d-1+a+b,a+b)));
    LA := LB := L1 := apply(d,i->{i});
    for i from 2 to a do (
	LA = select((LA**L1)/flatten/toList, j->j_(i-1)>=j_(i-2))
	);
    for i from 2 to b do (
	LB = select((LB**L1)/flatten/toList, j->j_(i-1)>=j_(i-2))
	);
    --find the basis element of sym that corresponds to a
    --weakly increasing list of indices
    symLookup := p -> (
	binomial(d+#p-1,#p)-1-sum(#p, i -> binomial(d-(p_i)-2+#p-i,#p-i))
	);
    return map(
	R^(binomial(d-1+a+b,a+b)),R^(binomial(d-1+a,a)*binomial(d-1+b,b)),
	apply(apply(#LA,i->i)**apply(#LB,i->i),
	    i -> (symLookup sort (LA_(i_0)|LB_(i_1)), (i_0)*#LB+i_1)=>1)
	);
    )

F2Form = method()
F2Form(ChainComplex) := Matrix => F -> (
    if (F_2).cache#?"F2Form" then return (F_2).cache#"F2Form";
    G1 := directSum(F_1,F_1);
    G2 := directSum(F_2,F_1**F_1,F_2);
    G3 := directSum(F_2**F_1,F_1**F_2);
    G4 := F_2**F_2;
    -*
    0,2 1,2 2,2
         -
    0,1 1,1 2,1
         -
    0,0 1,0 2,0
    *-
    d1 := F.dd_1*G1^[0] + F.dd_1*G1^[1];
    d2 := (
    	G1_[0]*F.dd_2*G2^[0]
    	- G1_[0]*(id_(F_1)**F.dd_1)*G2^[1]
    	+ G1_[1]*(F.dd_1**id_(F_1))*G2^[1]
    	+ G1_[1]*F.dd_2*G2^[2]
    	);
    d3 := (
    	G2_[0]*(id_(F_2)**F.dd_1)*G3^[0]
    	+ G2_[1]*(F.dd_2**id_(F_1))*G3^[0]
    	- G2_[1]*(id_(F_1)**F.dd_2)*G3^[1]
    	+ G2_[2]*(F.dd_1**id_(F_2))*G3^[1]
    	);
    d4 := G3_[0]*(id_(F_2)**F.dd_2) + G3_[1]*(F.dd_2**id_(F_2));
    G := chainComplex(
    	d1 = map(R^1,,d1),
    	d2 = map(source d1,,d2),
    	d3 = map(source d2,,d3),
    	d4 = map(source d3,,d4));
    alpha1 := G.dd_1//F.dd_1;
    alpha2 := (alpha1*G.dd_2)//F.dd_2;
    alpha3 := (alpha2*G.dd_3)//F.dd_3;
    return (F_2).cache#"F2Form" = map(F_4,F_2**F_2,(alpha3*G.dd_4)//F.dd_4)    
    )

hyperbolicBasis = method()
hyperbolicBasis(Module,Matrix) := Matrix => (F2,alpha4) -> (
    if F2.cache#?"hyperbolicbasis" then return F2.cache#"hyperbolicbasis";
    R := ring alpha4;
    R' := R[a_1,a_2]; --for making lines
    --find an isotropic vector
    V := id_(F2); --start
    d := min degrees F2 + max degrees F2; F4 = R^{1:-d};
    highveclist := map(F2,R^0,0);
    lowveclist := map(F2,R^0,0);
    unbalancedpairs := number(degrees F2, i -> 2*i > d);
    alpha := alpha4;
    for paircounter from 1 to unbalancedpairs do (
    	--loop
    	--<< paircounter << endl;
    	--first deal with parts that aren't middle degree
    	maxdeg := max degrees source V;
    	highdegpart := (source V)_(positions(degrees source V,i -> i == maxdeg));
    	lowdegpart := (source V)_(positions(degrees source V,i -> i == d-maxdeg));
    	highvec0 := highdegpart_{0};
    	lowvecfound := false; i := 0;
    	while not lowvecfound do (
	    lowvec0 := lowdegpart_{i};
	    pairing := lift(((alpha*(lowvec0**highvec0)))_(0,0),coefficientRing R);
	    if not zero pairing then (
	    	lowvecfound = true;
	    	lowvec := (1/pairing)*lowvec0
	    	);
	    i = i+1
	    );
    	adj := (1/2)*(alpha*(highvec0**highvec0))_(0,0);
    	highvec := highvec0 - adj*lowvec;
    	--record new pair
    	highveclist = (V*highvec)|highveclist;
    	lowveclist = lowveclist|(V*lowvec);
    	--reduce to orthogonal complement
    	V = V*(gens trim intersect(ker map(F4,source V,alpha*(highvec**id_(source V))),ker map(F4,source V,alpha*(lowvec**id_(source V)))));
    	alpha = alpha4*(V**V);
	);
    --now deal with the middle degree part
    --maximal isotropic:
    middlepart := R^(numcols V);
    isospace := map(middlepart,R^0,0);
    middleform := alpha;
    incmiddlepart := V;
    V = id_(middlepart);
    halfdim := (numcols V)//2;
    for k from 1 to halfdim do (
    	--n=rank source V;
    	isotr := false;
    	alpha = middleform*(V**V);
    	--<< k << endl;
    	while not isotr do (
    	    RLine := random(R'^(numcols V),R'^2)*matrix{{a_1},{a_2}};
	    mp := minimalPrimes ideal(sub(alpha,R')*(RLine**RLine));
    	    if #mp == 2 then (
	    	isotr = true;
	    	vec := matrix{{-coefficient(a_2,mp_0_0)},{coefficient(a_1,mp_0_0)}};
	    	isovec := sub(sub(RLine,{a_1 => vec_(0,0), a_2 => vec_(1,0)}),R);
	    	--vec' := matrix{{-coefficient(a_2,mp_1_0)},{coefficient(a_1,mp_1_0)}};
	    	--isovec' := sub(sub(RLine,{a_1 => vec'_(0,0), a_2 => vec'_(1,0)}),R)
	    	) else if (zero mp_0) then (
	    	isotr = true;
	    	vec = matrix{{1},{0}};
	    	isovec = sub(sub(RLine,{a_1 => vec_(0,0), a_2 => vec_(1,0)}),R);
	    	--vec' = matrix{{0},{1}};
	    	--isovec' = sub(sub(RLine,{a_1 => vec_(0,0), a_2 => vec_(1,0)}),R);
	    	)
    	    );
    	--isospace'= isospace|(V*isovec');
    	isospace = isospace|(V*isovec);
    	V = map(middlepart,,gens trim intersect apply(numcols isospace, i -> ker(middleform*(isospace_{i}**id_(middlepart)))));
    	);
    --extend isotropic subspace to orthogonal flag
    n := numcols isospace;
    isoflag := isospace;
    MAX := (numcols isoflag) - 1;
    for j in reverse(0..MAX) do (
    	isotr := false;
    	n = numcols isoflag;
    	V = map(middlepart,,gens trim intersect apply(delete(j,n), i -> ker(middleform*(isoflag_{i}**id_(middlepart)))));
    	--sdim = numcols V;
    	--<< numcols V << endl;
    	alpha = middleform*(V**V);
    	while not isotr do (
    	    RLine := random(R'^(numcols V),R'^2)*matrix{{a_1},{a_2}};
	    mp := minimalPrimes ideal(sub(alpha,R')*(RLine**RLine));
    	    if #mp == 2 then (
	    	vec := matrix{{-coefficient(a_2,mp_0_0)},{coefficient(a_1,mp_0_0)}};
	    	isovec := sub(sub(RLine,{a_1 => vec_(0,0), a_2 => vec_(1,0)}),R);
	    	vec' := matrix{{-coefficient(a_2,mp_1_0)},{coefficient(a_1,mp_1_0)}};
	    	isovec' := sub(sub(RLine,{a_1 => vec'_(0,0), a_2 => vec'_(1,0)}),R);
	    	if not zero ((V*isovec)%(image isospace)) then (
		    rawvec := isovec;
		    scfactor := (middleform*((V*isovec)**isospace_{j}))_(0,0);
		    newvec := rawvec*lift(1/scfactor,R);
		    isotr = true
		    ) else if not zero ((V*isovec')%(image isospace)) then (
		    rawvec = isovec';
		    scfactor = (middleform*((V*isovec')**isospace_{j}))_(0,0);
		    newvec = rawvec*lift(1/scfactor,R);
		    isotr = true
		    );
	    	);
    	    );
    	isoflag = isoflag|(V*newvec)
    	);	 
    --put everything together
    return F2.cache#"hyperbolicbasis" = map(F2,,lowveclist|incmiddlepart*isoflag|highveclist);
    )

selfDualForm = method()
selfDualForm(ChainComplex) := ChainComplex => F -> (
    hb := hyperbolicBasis(F_2,F2Form(F));
    hbF2 := source hb;
    halfdim := (rank hbF2)//2;
    HdH := directSum(R^(halfdim-1),R^1,R^1,R^(halfdim-1));
    fullrank := false;
    perturbation := id_(HdH);
    swapcomponent := false;
    if (rank(F.dd_2*hb*perturbation*HdH_[2,3]) == halfdim) then (
	fullrank = true
	) else if (rank(F.dd_2*hb*perturbation*HdH_[1,3]) == halfdim) then (
	fullrank = true;
	swapcomponent = true
	);
    while not fullrank do (
    	ran1 := random(source map(hbF2,,HdH_[0,1]),source map(hbF2,,HdH_[2,3]));
    	ran2 := random(source map(hbF2,,HdH_[0,2]),source map(hbF2,,HdH_[1,3]));
    	skew1 := ran1 - matrix reverse transpose reverse entries ran1;
    	skew2 := ran2 - matrix reverse transpose reverse entries ran2;
    	perturbation = map(hbF2,hbF2,
    	    (id_(HdH) + HdH_[0,1]*skew1*HdH^[2,3])
    	    *(id_(HdH) + HdH_[0,2]*skew2*HdH^[1,3])
    	    );
    	if (rank(F.dd_2*hb*perturbation*HdH_[2,3]) == halfdim) then (
	    fullrank = true
	    ) else if (rank(F.dd_2*hb*perturbation*HdH_[1,3]) == halfdim) then (
	    fullrank = true;
	    swapcomponent = true
	    );
    	);
    antidiag := map(HdH,HdH,apply(2*halfdim, i -> (i,2*halfdim-i-1) => 1));
    if swapcomponent then (
    	reordering := HdH_[0]*HdH^[0]+HdH_[1]*HdH^[2]+HdH_[2]*HdH^[1]+HdH_[3]*HdH^[3];
    	) else (
    	reordering = id_(HdH)
    	);
    hb' := hb*perturbation*reordering;--*antidiag;
    newd3 := F.dd_3*dual((dual F.dd_4)//(F.dd_1**id_(dual F_4)));
    newF := chainComplex(
    	d1 := F.dd_1,
    	d2 := map(source d1,,F.dd_2*hb'),
    	d3 := map(source d2,,(inverse hb')*newd3),
    	d4 := map(source d3,,dual d1)
    	);
    (newF_2).cache#"F2Form" = map(newF_4,newF_2**newF_2,adjoint'(antidiag,dual newF_2,R^1));
    (newF_2).cache#"hyperbolicbasis" = id_(newF_2);
    return newF
    )


--THIS METHOD ASSUMES F IS IN SELF-DUAL HYPERBOLIC FORM
makeDGA = method()
makeDGA(ChainComplex,Matrix) := Sequence => (F,m11) -> (
    alpha4 := F2Form F;
    antidiag := map(dual F_2,F_2,apply(rank F_2, i -> (i,(rank F_2)-i-1) => 1));
    m12 := -(
    	adjoint'(flip(dual F_1,F_2)*adjoint(m11*wedgeProduct(1,1,F_1),F_1,F_1), F_2, dual F_1)
    	*(id_(F_1)**antidiag)
    	);
    m13 := adjoint'(id_(F_1),F_1,R^1);
    DGF := directSum(F_0,F_1,F_2,F_3,F_4);
    DIFF := (
    	DGF_[0]*F.dd_1*DGF^[1]
    	+
    	DGF_[1]*F.dd_2*DGF^[2]
    	+
    	DGF_[2]*F.dd_3*DGF^[3]
    	+
    	DGF_[3]*F.dd_4*DGF^[4]
    	);
    fullmulti = (
    	DGF_[0]*(DGF^[0]**DGF^[0])
    	+
    	DGF_[1]*(DGF^[0]**DGF^[1])
    	+
    	DGF_[2]*(DGF^[0]**DGF^[2])
    	+
    	DGF_[3]*(DGF^[0]**DGF^[3])
    	+
    	DGF_[4]*(DGF^[0]**DGF^[4])
    	+
    	DGF_[1]*(DGF^[1]**DGF^[0])
    	+
    	DGF_[2]*m11*wedgeProduct(1,1,F_1)*(DGF^[1]**DGF^[1])
    	+
    	DGF_[3]*m12*(DGF^[1]**DGF^[2])
    	+
    	DGF_[4]*m13*(DGF^[1]**DGF^[3])
    	+
    	DGF_[2]*(DGF^[2]**DGF^[0])
    	+
    	DGF_[3]*m12*flip(F_2,F_1)*(DGF^[2]**DGF^[1])
    	+
    	DGF_[4]*alpha4*(DGF^[2]**DGF^[2])
    	+
    	DGF_[3]*(DGF^[3]**DGF^[0])
    	+
    	DGF_[4]*(-1)*m13*flip(F_3,F_1)*(DGF^[3]**DGF^[1])
    	+
    	DGF_[4]*(DGF^[4]**DGF^[0])
    	);
    return (DGF,map(DGF,DGF,DIFF),map(DGF,DGF**DGF,fullmulti))
    )

-*
partialDualForm = method()
partialDualForm(ChainComplex) := ChainComplex => origF -> (
    newd3 := origF.dd_3*dual((dual origF.dd_4)//(origF.dd_1**id_(dual origF_4)));
    return chainComplex(
    	origF.dd_1,
    	origF.dd_2,
    	newd3,
    	(dual origF.dd_1)**id_(origF_4)
    	)
    )
*-
