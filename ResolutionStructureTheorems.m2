--Current issues:
--
--figure out how to make degrees correct (using // requires the targets
--have the same degree so I set the degree to 0 before using it, but that should
--not be the final output)
--
--make it so that BE2 doesn't have to compute all the minors of the differential

newPackage(
	"ResolutionStructureTheorems",
    	Version => "0.1", 
    	Date => "June 17, 2021",
    	Authors => {
	     {Name => "Xianglong Ni", Email => "xlni@berkeley.edu"}
	     },
    	HomePage => "http://math.berkeley.edu/~xlni/",
    	Headline => "resolution structure theorems",
	AuxiliaryFiles => false -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
    "BE1",
    "BE1Cache",
    "fastExteriorPower",
    "leftWedge",
    "BE2",
    "BE2Cache"
    }
exportMutable {}

--needsPackage "SpechtModule" --just for permutationSign
needsPackage "FastLinAlg"

leftWedge = method() --the matrix representing (x wedge -) on wedge^b
leftWedge (Module, Matrix, ZZ, ZZ) := Matrix => (F, x, a, b) -> (
    return wedgeProduct(a,b,F)*(x ** id_(exteriorPower(b,F)))
    )

--nevermind, this already exists as "adjoint"
--tensorHom = method()
--tensorHom (Module, Module, Matrix) := Matrix => (U, V, M) -> (
--    m := numgens U;
--    n := numgens V;
--    adjM := matrix (flatten\pack(m, mingle pack(n, entries transpose M)));
--    return map(Hom(V,target M), U, adjM)
--    )

--just a wrapper for recursiveMinors from FastLinAlg
--hope to eventually find other optimizations/circumvent computing determinants where possible
fastExteriorPower = method()
fastExteriorPower (ZZ, Matrix) := Matrix => (k, M) -> (
    recursiveMinors(k,M);
    m := numgens target M;
    n := numgens source M;
    rows := subsets(m,k);
    cols := subsets(n,k);
    minorsList := apply(toSequence\(rows ** cols), i -> M.cache.MinorsCache#k#i);
    return map(
	exteriorPower(k, target M),
	exteriorPower(k, source M),
	matrix pack(binomial(n,k),minorsList)
	)
    )

--compList = method() -- takes a subset T of [n] and gives complementary one
--compList (List, ZZ) := List => (T,n) -> (
--    return select(n, i -> not member(i,T))
--    )

--exteriorDual = method()
--exteriorDual (Module, ZZ) := Matrix => (M, k) -> (
--    n := rank M;
--    d := binomial(n,k);
--    T := subsets(n,k);
--    L := apply(d, i -> permutationSign(flatten{compList(T_i,n), T_i}));
--    return matrix reverse entries diagonalMatrix L
--    )

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

beginDocumentation()

doc ///
    Key
    	ResolutionStructureTheorems
    Headline
    	resolution structure theorems
    Description
    	Text
	    Currently the two structure theorems of Buchsbaum and Eisenbud are
	    implemented.
///

doc ///
    Key
    	BE1
	(BE1,ChainComplex,ZZ)
	BE1Cache
    Headline
    	the first structure theorem
    Usage
    	a = BE1(C,k)
    Inputs
    	C: ChainComplex
	    a free $R$-resolution $0 \to F_n \overset{d_n}{\to} F_{n-1} \to \cdots \to F_0$
	k: ZZ
	    specifying the map $\wedge^{r_k} d_k$ to be factored
    Outputs
    	a: Matrix
	    the map $a_k$
    Description
    	Text
	    Let $r_k$ denote the rank of $d_k\colon F_k \to F_{k-1}$.
	    The first structure theorem states that there are maps $a_k$ such that
	    $\wedge^{r_k} d_k \colon \wedge^{r_k} F_k \to \wedge^{r_k} F_{k-1}$ factors as
	    
	    $$\wedge^{r_k} F_k \overset{a_{k+1} \wedge -}{\longrightarrow}
	    \wedge^{r_k + r_{k+1}} F_k \cong R \overset{a_k}{\to} \wedge^{r_k} F_{k-1}.$$
	    
	    Initially, we set $a_{n+1} = 1$, so that $a_n = \wedge^{r_n} d_n$. The isomorphism
	    $\wedge^{r_k + r_{k+1}} F_k \cong R$ is given by fixing an orientation on $F_k$:
	    namely $e_1 \wedge \cdots \wedge e_j$ corresponds to $1 \in R$ where $e_1,\ldots,e_j$
	    is the ordered basis of $F_k$.
	Example
	    R = QQ[x,y,z]; I = (ideal(x,y,z))^2; C = res I
	    BE1(C,2)
	Text
	    The result of this computation is stored in {\tt C.cache.BE1Cache#2}.
	Example
	    (BE1(C,2)
	        *map(R^1, exteriorPower(8, C_2), 1)
	        *leftWedge(C_2, BE1(C,3), 3, 5)
	        == fastExteriorPower(5, C.dd_2))
    SeeAlso
    	BE2
///

doc ///
    Key
    	fastExteriorPower
	(fastExteriorPower,ZZ,Matrix)
    Headline
    	exterior power of a map
    Usage
    	fastExteriorPower(i,f)
    Inputs
    	i: ZZ
	f: Matrix
    Outputs
    	: Matrix
	    the {\tt i}-th exterior power of {\tt f}
    Description
    	Text
	    This method is just a wrapper for @TO recursiveMinors@ from @TO FastLinAlg@ which functions the same as @TO (exteriorPower,ZZ,Matrix)@.
///

doc ///
    Key
    	BE2
	(BE2,ChainComplex,ZZ)
	BE2Cache
    Headline
    	the second structure theorem
    Usage
    	b = BE2(C,k)
    Inputs
    	C: ChainComplex
	    a free $R$-resolution $0 \to F_n \overset{d_n}{\to} F_{n-1} \to \cdots \to F_0$
	k: ZZ
	    greater than or equal to 2, specifying the map $\wedge^{r_k-1} d_k$ to be factored
    Outputs
    	b: Matrix
	    the map $b_k$
    Description
    	Text
	    Let $r_k$ denote the rank of $d_k\colon F_k \to F_{k-1}$.
	    The second structure theorem states that, for $k \geq 2$, there are maps $b_k$ such that
	    $\wedge^{r_k-1} d_k \colon \wedge^{r_k-1} F_k \to \wedge^{r_k-1} F_{k-1}$ factors as
	    
	    $$\wedge^{r_k-1} F_k \overset{a_{k+1} \wedge -}{\longrightarrow}
	    \wedge^{r_k + r_{k+1} - 1} F_k \cong F_k^* \overset{b_k}{\to} \wedge^{r_k - 1} F_{k-1}.$$
	    
	    Here $a_{k+1}$ is as in the first structure theorem @TO BE1@ and the isomorphism $\wedge^{r_k + r_{k+1} - 1} F_k \cong F_k^*$ is @TO adjoint@ to the
	    @TO wedgeProduct@ $\wedge^{r_k + r_{k+1} - 1} \otimes \wedge^1 F_k \to \wedge^{r_k + r_{k+1}} F_k \cong R$.
    	Example
	    R = QQ[x,y,z]; I = (ideal(x,y,z))^2; C = res I
	    BE2(C,2)
	Text
	    The result of this computation is stored in {\tt C.cache.BE2Cache#2}.
	Example
	    (BE2(C,2)
                *adjoint(wedgeProduct(7, 1, C_2), exteriorPower(7,C_2), C_2)
                *leftWedge(C_2, BE1(C,3), 3, 4)
                == fastExteriorPower(4, C.dd_2))
    SeeAlso
    	BE1
///

doc ///
    Key
    	leftWedge
	(leftWedge, Module, Matrix, ZZ, ZZ)
    Headline
    	wedge product with a fixed element
    Usage
    	leftWedge(M,x,a,b)
    Inputs
    	M: Module
	x: Matrix
	    representing an element of $\wedge^a M$
	a: ZZ
	b: ZZ
    Outputs
    	: Matrix
	    the map $\wedge^b M \overset{x \wedge -}{\longrightarrow} \wedge^{a+b} M$
///

--tests still need to be written

TEST /// --check #0 (BE1)
S = QQ[x,y,z];
C = res (ideal(x,y,z))^2;
for k from 1 to 3 do assert(
    BE1(C,k)
    *map(S^1, exteriorPower(rank C_k, C_k), 1)
    *leftWedge(C_k, BE1(C,k+1), rank C.dd_(k+1), rank C.dd_k) 
    == fastExteriorPower(rank C.dd_k, C.dd_k));
///

TEST /// --check #1 (BE2)
S = QQ[x,y,z];
C = res (ideal(x,y,z))^2;
for k from 2 to 3 do assert(
    BE2(C,k)
    *adjoint(wedgeProduct(rank C_k - 1, 1, C_k), exteriorPower(rank C_k - 1, C_k), C_k)
    *leftWedge(C_k, BE1(C,k+1), rank C.dd_(k+1), rank C.dd_k - 1)
    == fastExteriorPower(rank C.dd_k - 1, C.dd_k));
///

end
