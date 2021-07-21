Blueprint = new Type of HashTable
CompiledBlueprint = new Type of HashTable
TableauDiagram = new Type of MutableHashTable

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

tdFromList = method()
tdFromList (List) := TableauDiagram => L -> (
    return new TableauDiagram from hashTable L
    )

bpFromList = method()
bpFromList (List) := Blueprint => L -> (
    return new Blueprint from hashTable L
    )

coordsFromFilling = method()
coordsFromFilling Filling := List => F -> (
    L := toList F;
    L = L/(i -> pack(2, mingle(toList(0..(#i-1)),i))); --y coords
    L = pack(2, mingle(toList(0..(#L-1)),L)); --x coords
    L = flatten (L/(i -> ({i_0} ** i_1)/flatten)); --organize into triples
    return L/(i -> (0,i_0,i_1)=>i_2) --format
    )

bdSchur = method()
bdSchur (List,Module) := Module => (p,M) -> (
    N := schurModule(p,M);
    if M.cache.?BasisDict then (
	N.cache.BasisDict = applyPairs(N.cache#"Schur"#3,
	    (k,v) -> 
	    (v,hashTable ((coordsFromFilling k)/(i -> i#0 => M.cache.BasisDict#(i#1)))))
	) else (
	N.cache.BasisDict = applyPairs(N.cache#"Schur"#3, (k,v)->(v,hashTable coordsFromFilling k))
	);
    return N
    )

--inputs to this should be outputs of bdSchur; this should NOT be directly applied to modules
bdTensor = method(Dispatch => Thing)
bdTensor Sequence := Module => L -> (
    l := #L;
    if l>1 then N := tensor L else error "tensor: input sequence length <= 1";
    BasisElts := new MutableHashTable;
    for i from 0 to l-1 do (
	if not (L_i).cache.?BasisDict then error (L_i, "does not have a BasisDict");
	BasisElts#i = (values (L_i).cache.BasisDict)/
	(h -> ((pairs h)/(m -> (i,m#0_1,m#0_2)=>m#1)))
	);
    --form list of basis elts for tensorprod
    X := tensor(toSequence apply(l, i -> BasisElts#i))/flatten/hashTable;
    N.cache.BasisDict = hashTable apply(#X, i -> i=>X_i);
    return N
    )

--the blueprint BP should be a MutableHashTable for use in straightening.
--assemble = BP -> (
--    if (class BP === Module) then return BP;
--    if #BP > 1 then return bdTensor (
--	toSequence values hashTable apply(pairs BP, (k,v) ->
--	    (k_0, bdSchur(k_1, assemble v))
--	    )
--	) else return (
--	(values hashTable apply(pairs BP, (k,v) ->
--	    (k_0, bdSchur(k_1, assemble v))
--	    ))_0
--	)
--    )
compileBlueprint = method()
compileBlueprint Module := {} => M -> (
    return (M,new CompiledBlueprint)
    )
compileBlueprint Blueprint := (Module, CompiledBlueprint) => BP -> (
    X := new CompiledBlueprint from hashTable apply(pairs BP, (k,v) -> (
	    Y := compileBlueprint v;
	    return ((k_0,k_1,bdSchur(k_1,Y_0)),Y_1)
	    )
	);
    if #X > 1 then return (
	(bdTensor(toSequence values applyPairs(X, (k,v) -> (k_0, k_2))),X)
	) else return (
	((keys X)#0#2, X)
	)
    )

--z is tensor index of H, p is partition, M is module.
tableauStraighten = method()
tableauStraighten (ZZ, TableauDiagram, List) := {} => (z,H,p) -> (
    M := module H#(z,0,0);
    p' := toList conjugate(new Partition from p); --by columns
    cols := #p';
    tens := (ring H#(z,0,0))^1_0;
    for x from 0 to cols-1 do (
	wedge := exteriorPower(p'#x, matrix apply(p'#x, y -> H#(z,x,y))); --TODO: allow options to control which "exterior power" method is used?
	tens = tens ** (wedge_0); --wedge_0 to get wedge as module element
	);
    output := ((schurModule(p,M)).cache#"Schur"#0)*tens;
    return output
    )
tableauStraighten (ZZ, TableauDiagram, List, Module) := {} => (z,H,p,N) -> (
    M := module H#(z,0,0);
    p' := toList conjugate(new Partition from p); --by columns
    cols := #p';
    tens := (ring H#(z,0,0))^1_0;
    for x from 0 to cols-1 do (
	wedge := exteriorPower(p'#x, matrix apply(p'#x, y -> H#(z,x,y))); --TODO: allow options to control which "exterior power" method is used?
	tens = tens ** (wedge_0); --wedge_0 to get wedge as module element
	);
    output := (N.cache#"Schur"#0)*tens;
    return output
    )

interpret = method()
interpret Thing := {} => (H') -> (
    if not (class H' === TableauDiagram) then return H';
    H := copy H'; --safety because idk what modifies the original input
    plist := H#TableauShapes;
    for z from 0 to #plist-1 do (
	for y from 0 to #plist#z-1 do (
	    for x from 0 to plist#z#y-1 do (
		H#(z,x,y) = interpret(H#(z,x,y));
		);
	    );
	);
    tens := tableauStraighten(0,H,plist#0);
    for z from 1 to #plist-1 do (
	tens = tens ** tableauStraighten(z,H,plist#z);
	);
    return tens
    )
interpret (Thing, CompiledBlueprint) := {} => (H',BP) -> (
    if not (class H' === TableauDiagram) then return H';
    H := copy H'; --safety because idk what modifies the original input
    bp := hashTable apply(keys BP, k -> k_0 => (k_1,k_2));
    plist := H#TableauShapes;
    for z from 0 to #plist-1 do (
	for y from 0 to #plist#z-1 do (
	    for x from 0 to plist#z#y-1 do (
		H#(z,x,y) = interpret(H#(z,x,y), BP#(z,bp#z#0,bp#z#1));
		);
	    );
	);
    tens := tableauStraighten(0,H,plist#0, bp#0#1);
    for z from 1 to #plist-1 do (
	tens = tens ** tableauStraighten(z,H,plist#z, bp#z#1);
	);
    return tens
    )

--X must have basis dictionary!!
schurMap = method()
schurMap (Blueprint,Module,Function) := Matrix => (BP', X, F) -> (
    (Y,BP) := compileBlueprint BP';
    M := map(Y,0,0);
    for i from 0 to #X.cache.BasisDict-1 do (
	img := F(X.cache.BasisDict#i);
	M = M | sum(apply(#img, j -> img#j#0 * matrix(interpret(img#j#1,BP))));
	);
    return map(Y,X,M);
    )