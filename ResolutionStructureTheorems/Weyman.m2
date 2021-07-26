--DefectAlgebraDual = method() --very WIP
--DefectAlgebraDual (ZZ, ChainComplex) := Module => (k, C) -> (
--    if not C.cache.?DefectCache then C.cache.DefectCache = new MutableHashTable;
--    if not C.cache.DefectCache#?k then (
--	if k == 1 then C.cache.DefectCache#k = dual C_3 ** exteriorPower(rank C.dd_1 + 1, C_1);
--	if k == 2 then C.cache.DefectCache#k = exteriorPower(2, C.cache.DefectCache#1);
--	);
--    return C.cache.DefectCache#k
--    )

P1 = method() --needs to be revisited, currently broken
P1 ChainComplex := Matrix => C -> (
    if not C.cache#?PCache then C.cache#PCache = new MutableHashTable;
    if C.cache#PCache#?1 then return C.cache#PCache#1;
    r := new MutableHashTable;
    r#1 = rank C.dd_1; r#2 = rank C.dd_2; r#3 = rank C.dd_3;
    A3 := (dual BE2(C,2))*adjoint(wedgeProduct(r#1 + 1, r#2 - 1, C_1), exteriorPower(r#1 + 1, C_1), exteriorPower(r#2 - 1, C_1));
    A1 := dual adjoint(wedgeProduct(r#3 - 1, 1, C_3), exteriorPower(r#3 - 1, C_3), C_3);
    A2 := dual flatten id_(exteriorPower(r#3-1,C_2));
    B1 := flatten fastExteriorPower(r#3 - 1,C.dd_3);
    B2 := wedgeProduct(r#3 - 1, 1, C_2);
--    C.cache#PCache#1 = map(exteriorPower(r#3, C_2), DefectAlgebraDual(1,C), (B1**B2)*(A1**A2**A3));
    return C.cache#PCache#1
    )

BracketDualCache = new MutableHashTable

bracketDual = method(Options => {Cumulative => false, Ring => ZZ}) --produces L_n -> wedge^2 L_(< n)
bracketDual (ZZ,ZZ,ZZ,ZZ) := Matrix => opts -> (r1,f1,f3,n) -> (
    R := opts#Ring;
    if opts.Cumulative then (
	LD := directSum(apply(n+1, i -> source bracketDual(r1,f1,f3,i)));
	return R**fold((x,y)->x|y,apply(1..n, i ->
		exteriorPower(2,LD_(new Array from 0..(i-1)))*bracketDual(r1,f1,f3,i)
		)
	    )
	);
    if (n <= 0) then return map(R^0,R^0,0);
    if (n == 1) then return map(R^0,R^(binomial(f1,r1+1) * f3),0);
    if BracketDualCache#?(r1,f1,f3,n) then return (R**BracketDualCache#(r1,f1,f3,n));
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
	return BracketDualCache#(r1,f1,f3,n) = gens ker (alpha1 || alpha2)
	);
    bd := bracketDual(r1,f1,f3,n-1,Cumulative => true);
    Ld := directSum(apply(n, i -> source bracketDual(r1,f1,f3,i)));
    w2part := fold((x,y)->x|y, apply(1..(floor(n/2)+1), i ->
	    wedgeProduct(1,1,Ld)*(Ld_[i] ** Ld_[n-i])
	    )
	);
    rawker := gens ker (
	wedgeProduct(2,1,Ld)
	*(bd ** id_Ld)
	*(dual wedgeProduct(1,1,Ld))
	*w2part
	);
    BracketDualCache#(r1,f1,f3,n) = gens gb (w2part*rawker);
    return (R**BracketDualCache#(r1,f1,f3,n))
    )
