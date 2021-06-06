-- TODO:
-- circumvent determinant computations?

needsPackage "SpechtModule" --just for permutationSign

compList = method() -- takes a subset T of [n] and gives complementary one
compList (List, ZZ) := List => (T,n) -> (
    return select(n, i -> not member(i,T))
    )

exteriorDual = method() --gives the map (wedge^k M)* to wedge^(rk M - k) M, which is (x wedge -) <-> x
exteriorDual (Module, ZZ) := Matrix => (M, k) -> (
    n := rank M;
    d := binomial(n,k);
    T := subsets(n,k);
    L := apply(d, i -> permutationSign(flatten{compList(T_i,n), T_i}));
    return matrix reverse entries diagonalMatrix L
    )

BE1 = method() --first structure theorem
BE1 (ChainComplex, ZZ) := Matrix => (C, k) -> (
    if not C.cache.?multipliers then C.cache.multipliers = new MutableHashTable;
    n := length C;
    a := new MutableHashTable;
    r := new MutableHashTable;
    r#(n+1) = 0;
    for i in (reverse (k..n)) do (
	r#i = rank C_i - r#(i+1);
    	if C.cache.multipliers#?i then (
	    a#i = C.cache.multipliers#i;
	    ) else (
	    if (i == n) then (
		a#i = exteriorPower(r#n, C.dd_n);
		) else (
		m := (positions(flatten entries a#(i+1), j -> j != 0))_0;
		Tm := (subsets(rank C_i,r#(i+1)))_m;
		pm := permutationSign flatten {compList (Tm, rank C_i), Tm};
		a#i = transpose lift(matrix (pm*entries exteriorPower(r#i,transpose ((C.dd_i)_(compList(Tm, rank C_i)))) / ((a#(i+1))_(m,0))), ring C);
		);
	    C.cache.multipliers#i = a#i
	    )
	);
    return a#k
    )

end

restart
load "StructureTheorems.m2"

--exteriorPower and schur use the same basis, and the former seems to be faster.
--testing the code on a specific example
S = QQ[x,y,z]
C = res (ideal(x,y,z))^2

k = 2
BE1(C,k) * (transpose BE1(C,k+1)) * (transpose exteriorDual(C_k, rank C.dd_(k+1)))
exteriorPower(rank C.dd_k, C.dd_k)
