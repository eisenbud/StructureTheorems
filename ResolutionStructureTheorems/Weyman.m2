--DefectAlgebraDual = method() --very WIP
--DefectAlgebraDual (ZZ, ChainComplex) := Module => (k, C) -> (
--    if not C.cache.?DefectCache then C.cache.DefectCache = new MutableHashTable;
--    if not C.cache.DefectCache#?k then (
--	if k == 1 then C.cache.DefectCache#k = dual C_3 ** exteriorPower(rank C.dd_1 + 1, C_1);
--	if k == 2 then C.cache.DefectCache#k = exteriorPower(2, C.cache.DefectCache#1);
--	);
--    return C.cache.DefectCache#k
--    )

--currently really inefficient
--it is completely unnecessary to compute the whole wedge2 of the previous p_i
WeymanP = method()
WeymanP (ChainComplex,ZZ) := Matrix => (C,n) -> (
    if not C.cache#?PCache then C.cache#PCache = new MutableHashTable;
    if C.cache#PCache#?n then return C.cache#PCache#n;
    r1 := rank C.dd_1; r2 := rank C.dd_2; r3 := rank C.dd_3;
    f0 := rank C_0; f1 := rank C_1; f2 := rank C_2; f3 := rank C_3;
    R := ring C;
    K := exteriorPower(r3,C_2);
    if (n <= 0) then return map(K, R^0, 0);
    if (n == 1) then (
	A3 := (dual BE2(C,2))*adjoint(wedgeProduct(r1 + 1, r2 - 1, C_1), exteriorPower(r1 + 1, C_1), exteriorPower(r2 - 1, C_1));
    	A1 := dual adjoint(wedgeProduct(r3 - 1, 1, C_3), exteriorPower(r3 - 1, C_3), C_3);
    	A2 := dual flatten id_(exteriorPower(r3-1,C_2));
    	B1 := flatten fastExteriorPower(r3 - 1,C.dd_3);
    	B2 := wedgeProduct(r3 - 1, 1, C_2);
    	return C.cache#PCache#1 = map(K, (dual C_3) ** exteriorPower(r1+1,C_1), (B1**B2)*(A1**A2**A3))
	);
    dk := dual koszul(2, dual exteriorPower(r3,C.dd_3));
    pieces := apply(n, i -> source bracketDual(r1,f1,f3,i,Ring=>R));
    Ld := directSum pieces;
    inc := fold((x,y) -> x|y,
	{map(exteriorPower(2,Ld),R^0,0)}|apply(ceiling(n/2), i->wedgeProduct(1,1,Ld)*(Ld_[i+1] ** Ld_[n-i-1]))
	);
    if (even n) then inc = inc | exteriorPowerSparse(2,Ld_[n//2]);
    pr := dual inc;
    q2 := fold((x,y) -> x|y,
	{map(exteriorPower(2,K),R^0,0)}|apply(ceiling(n/2), i->wedgeProduct(1,1,K)*(WeymanP(C,i+1)**WeymanP(C,n-i-1)))
	);
    if (even n) then q2 = q2 | exteriorPowerSparse(2,WeymanP(C,n//2));
    Q2 := q2*pr*bracketDual(r1,f1,f3,n, Ring => R);
    rawQ2 := map(exteriorPower(2,K), source Q2, Q2);
    rawdk := map(exteriorPower(2,K), source dk, dk);
    return C.cache#PCache#n = rawQ2 // rawdk
    )

BracketDualCache = new MutableHashTable

bracketDual = method(Options => {Cumulative => false, Ring => QQ}) --produces L_n -> wedge^2 L_(< n)
bracketDual (ZZ,ZZ,ZZ,ZZ) := Matrix => opts -> (r1,f1,f3,n) -> (
    R := opts#Ring;
    if opts.Cumulative then (
	h := numrows bracketDual(r1,f1,f3,n,Ring=>R);
	M := fold((x,y) -> x | y,
	    apply(n+1, i ->
	    	bracketDual(r1,f1,f3,i,Ring=>R) ||
	    	map(R^(h-numrows bracketDual(r1,f1,f3,i,Ring=>R)), source bracketDual(r1,f1,f3,i,Ring=>R),0)
	    	)
	    );
	return (M || map(R^(binomial(numcols M,2) - numrows M), source M, 0))
	);
    if (n <= 0) then return map(R^0,R^0,0);
    if (n == 1) then return map(R^0,R^(binomial(f1,r1+1) * f3),0);
    if not BracketDualCache#?R then BracketDualCache#R = new MutableHashTable;
    if BracketDualCache#R#?(r1,f1,f3,n) then return BracketDualCache#R#(r1,f1,f3,n);
    if (n == 2) then (
	F1 := R^(f1); F3 := R^(f3);
	MBP := bpFromList {
    	    (0,{1,1}) => bpFromList {
        	(0,{1}) => dual F3,
        	(1,apply(r1+1, i->1)) => F1
        	}
    	    };
	NBP := bpFromList {
    	    (0,{1,1}) => dual F3,
    	    (1,apply(r1+1, i->2)) => F1
    	    };
	g := X -> {
    	    (1,
        	tdFromList (
            	    {
                	TableauShapes => {{1,1},apply(r1+1,i->2)},
                	(0,0,0) => (dual F3)_(X#(0,0,0)#(0,0,0)),
                	(0,0,1) => (dual F3)_(X#(0,0,1)#(0,0,0))
                	}
            	    | flatten apply(r1+1, i->{
                    	    (1,0,i) => (F1)_(X#(0,0,0)#(1,0,i)),
                    	    (1,1,i) => (F1)_(X#(0,0,1)#(1,0,i))
                    	    }
                	)
            	    )
        	)
    	    };
	alpha1 := schurMap(NBP, (compileBlueprint MBP)_0, g);
	B1 := dual wedgeProduct(1,1,exteriorPower(r1+1,F1));
	B2 := id_(exteriorPower(r1+1,F1)) ** dual wedgeProduct(1,r1,F1);
	B3 := wedgeProduct(r1+1,1,F1) ** id_(exteriorPower(r1,F1));
	B4 := (schurModule(apply(r1, i->2)|{1,1},F1)).cache#"Schur"#0;
	B := B4*B3*B2*B1;
	WF1 := exteriorPower(r1+1,F1);
	MBP = bpFromList {
	    (0,{1,1}) => bpFromList {
		(0,{1}) => dual F3,
		(1,{1}) => WF1
		}
	    };
	NBP = bpFromList {
    	    (0,{2}) => F3,
    	    (1,{1,1}) => WF1
    	    };
	g = X -> {
    	    (1,
		tdFromList {
	    	    TableauShapes => {{2},{1,1}},
	    	    (0,0,0) => F3_(X#(0,0,0)#(0,0,0)),
	    	    (0,1,0) => F3_(X#(0,0,1)#(0,0,0)),
	    	    (1,0,0) => WF1_(X#(0,0,0)#(1,0,0)),
	    	    (1,0,1) => WF1_(X#(0,0,1)#(1,0,0))
	    	    }
		)
    	    };
	C := schurMap(NBP, (compileBlueprint MBP)_0, g);
	alpha2 := (id_(symmetricPower(2,F3)) ** B) * C;
	return BracketDualCache#R#(r1,f1,f3,n) = gens ker (alpha1 || alpha2);
	);
    bd := bracketDual(r1,f1,f3,n-1,Cumulative => true,Ring => R);
    pieces := apply(n, i -> source bracketDual(r1,f1,f3,i,Ring => R));
    Ld := directSum pieces;
    Ldn := fold((x,y) -> x|y,
	apply(ceiling(n/2), i->wedgeProduct(1,1,Ld)*(Ld_[i+1] ** Ld_[n-i-1]))
	);
    if (even n) then Ldn = Ldn | exteriorPowerSparse(2,Ld_[n//2]);
    --the next line takes the longest!
    M = (wedgeProduct(2,1,Ld))*(bd ** id_Ld)*(dual wedgeProduct(1,1,Ld))*Ldn;
    rawker := gens ker M;	
    return BracketDualCache#R#(r1,f1,f3,n) = gens gb (Ldn * rawker);
    )

--outputs M -> N ** L_1 to be used in construction of reps V(omega_x/y/z_{r-1})
fundamentalRepMap = method()
fundamentalRepMap (ZZ,ZZ,ZZ,String) := Matrix => (r1,f1,f3,xyz) -> (
    F1 := QQ^f1; F3 := QQ^f3;
    if xyz=="x" then (
	return flip((dual F3)**exteriorPower(r1+1,F1), F1)*
	    (id_(dual F3)**(
		    dual (schurModule({2}|apply(r1,i->1),F1)).cache#"Schur"#0 --I'm not sure this is the correct map?
		    ))
	) else if xyz=="y" then (
        return (flip(dual F3, dual F1)**(id_(exteriorPower(r1+1,F1))))*
	    (id_(dual F3)**(gens ker (
			(reshape(QQ^1,(dual F1)**F1,id_(F1))**id_(exteriorPower(r1,F1)))*
			(id_(dual F1)**(dual wedgeProduct(1,r1,F1)))
			)
		    )
		)
	) else if xyz=="z" then (
	return (gens ker (reshape(QQ^1,F3**(dual F3),id_(F3))))**id_(exteriorPower(r1+1,F1))
	) else (
	error "fundamentalRepMap: last input must be string x,y, or z"
	)
    )
