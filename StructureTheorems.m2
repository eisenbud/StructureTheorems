-- TODO:
-- fix sign issue
-- try exteriorPower (which seems to be faster) in place of schur
-- circumvent determinant computations?

needsPackage "SchurFunctors"
needsPackage "SpechtModule" --just for permutationSign

compList = method() --takes a filling T (in this case a subset of [n]) and gives ([n] \ T), which is the dual basis element up to sign
compList (Filling, ZZ) := List => (T,n) -> (
    return select(n, i -> not member(i,(toList T)_0))
    )

exteriorDual = method() --gives the map (wedge^k M)* to wedge^(rk M - k) M, which is (x wedge -) <-> x
exteriorDual (Module, ZZ) := Matrix => (M, k) -> (
    return schurModulesMap(schurModule(apply(k, i -> 1),M), schurModule(apply(rank M - k, i -> 1),M),
	i -> {(permutationSign flatten {compList (i, rank M),(toList i)_0},new Filling from {compList(i, rank M)})})
    )

BE1 = method()
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
		a#i = schur(apply(r#n, i -> 1), C.dd_n);
		) else (
		m := (positions(flatten entries a#(i+1), j -> j != 0))_0;
		Tm := (applyPairs((schurModule(apply(r#(i+1), j -> 1),C_i)).cache#"Schur"#3, (a,b) -> (b,a)))#m;
		pm := permutationSign flatten {(toList Tm)_0, compList (Tm, rank C_i)};
		a#i = transpose lift(matrix (pm*entries schur(apply(r#i, j -> 1),transpose ((C.dd_i)_(compList(Tm, rank C_i)))) / ((a#(i+1))_(m,0))), ring C);
		);
	    C.cache.multipliers#i = a#i
	    )
	);
    return a#k
    )

end

restart
load "StructureTheorems.m2"



--comparing exteriorPower to schur
S = QQ[x_1..x_64]
M = genericMatrix(S,x_1,8,8)
time exteriorPower(4,M);
time schur({1,1,1,1},M);
--both of the commands take anywhere from 5.5 to 9 seconds on my machine
S = QQ[a_1..a_5,b_1..b_5,c_1..c_5,d_1..d_5,e_1..e_5]
M = genericMatrix(S,a_1,5,5)
time exteriorPower(3,M)
time schur({1,1,1},M)
--looks like they use the same basis, also exteriorPower is consistently faster in this smaller computation



--testing the code on a specific example
S = QQ[x,y,z]
C = res (ideal(x,y,z))^2
time BE1(C,3)
BE1(C,2)
BE1(C,1)

--this checks out
BE1(C,2) * (transpose BE1(C,3)) * (transpose exteriorDual(C_2,rank C.dd_3))
schur(apply(rank C.dd_2, i -> 1), C.dd_2)
time exteriorPower(rank C.dd_2, C.dd_2)

--this doesn't; there is a sign issue somewhere :(
BE1(C,1) * (transpose BE1(C,2)) * (transpose exteriorDual(C_1,rank C.dd_2))
schur(apply(rank C.dd_1, i -> 1), C.dd_1)
