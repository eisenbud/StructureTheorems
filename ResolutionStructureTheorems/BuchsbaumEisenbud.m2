BE1 = method() --first structure theorem
BE1 (ChainComplex, ZZ) := Matrix => (C, k) -> (
    if not C.cache#?BE1Cache then C.cache#BE1Cache = new MutableHashTable;
    n := length C;
    C.cache#BE1Cache#(n+1) = matrix{{1}};
    if not C.cache#BE1Cache#?k then (
   	r := new MutableHashTable; --ranks of differentials
	r#(k+1) = rank C.dd_(k+1); r#k = rank C.dd_k;
	R := ring C;
	--F is the map to be factored as A*A'
	A' := leftWedge(C_k, BE1(C,k+1), r#(k+1), r#k);
	--find a nonzero coordinate of a' and the corresponding subset
	m := (positions(flatten entries A', j -> j != 0))_0;
	Tm := (subsets(rank C_k, r#k))_m;
	DualF := transpose fastExteriorPower(r#k, (C.dd_k)_Tm);
	RawDualF := map(R^1, source DualF, DualF);
	RawA' := map(R^1, source A'_{m}, A'_{m});
	RawA := transpose(RawDualF // RawA');
	C.cache#BE1Cache#k = map(exteriorPower(r#k, C_(k-1)), R^1, RawA);
	);
    return C.cache#BE1Cache#k
    )

BE2 = method() --second structure theorem
BE2 (ChainComplex, ZZ) := Matrix => (C, k) -> (
    if not C.cache#?BE2Cache then C.cache#BE2Cache = new MutableHashTable;
    if not C.cache#BE2Cache#?k then (
	r := new MutableHashTable; --ranks of differentials
	r#(k+1) = rank C.dd_(k+1); r#k = rank C.dd_k;
	--F is the map to be factored as B*A'
	A' := leftWedge(C_k, BE1(C,k+1), r#(k+1), r#k - 1);
	--identify second highest exterior power of C_k with C_k^*
	IdentifyDual := adjoint(wedgeProduct(rank C_k - 1, 1, C_k), exteriorPower(rank C_k - 1, C_k), C_k);
    	DualA' := transpose (IdentifyDual * A');
        RawDualA' := map((ring C)^(binomial(rank C_k, r#k - 1)), source DualA', DualA');
        DualF := transpose fastExteriorPower(r#k - 1, (C.dd_k));
        RawDualF := map((ring C)^(binomial(rank C_k, r#k - 1)), source DualF, DualF);
        RawB := transpose(RawDualF // RawDualA');
	C.cache#BE2Cache#k = map(exteriorPower(r#k - 1, C_(k-1)), dual C_k, RawB);
    );
    return C.cache#BE2Cache#k
    )
