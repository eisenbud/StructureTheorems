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

exteriorPowerSparseHT = method() --WIP
exteriorPowerSparseHT (ZZ,Matrix) := Matrix => (k, M) -> (
    --get nonzero entries
    if not M.cache.?NZCache then M.cache.NZCache = new MutableHashTable;
    if not M.cache.NZCache#?1 then (
	L := apply(entries M, i -> positions(i, j -> j != 0));
    	nonz := flatten apply(numrows M, i -> (L_i)/(j -> (i,j)));
    	M.cache.NZCache#1 = hashTable apply(nonz, pos -> pos => M_pos)
	);
    if not M.cache.NZCache#?ByRows then (
	M.cache.NZCache.ByRows = new MutableHashTable;
	scan(keys M.cache.NZCache#1,
    	    k -> (
		if M.cache.NZCache.ByRows#?(k_0) then (
	    	    M.cache.NZCache.ByRows#(k_0) = M.cache.NZCache.ByRows#(k_0) | {k_1}
	    	    ) else (
	    	    M.cache.NZCache.ByRows#(k_0) = {k_1}
	    	    )
		)
    	    );
	M.cache.NZCache.NZRows = sort keys M.cache.NZCache.ByRows
	);
    --with some adjustments to formatting this separate block for k=2 wouldn't be needed
    if (k >= 2 and not M.cache.NZCache#?2) then (
        print ("working on minors of size", 2);
	subs2 := toSequence\subsets(keys M.cache.NZCache#1,2);
    	M.cache.NZCache#2 = new MutableHashTable;
    	tempf := (a,b) -> (
	    X := sort unique {a_0,b_0};
	    Y := sort unique {a_1,b_1};
	    if (length X != 2) or (length Y != 2) then return;
	    contribution := (-1)^(number({a_0<b_0, a_1<b_1}, i -> i)) * M_a * M_b;
	    if not M.cache.NZCache#2#?(X,Y) then M.cache.NZCache#2#(X,Y) = 0;
	    M.cache.NZCache#2#(X,Y) = M.cache.NZCache#2#(X,Y) + contribution
	    );
    	--I haven't the slightest clue whether the following multithreading is actually helping
	taskList := apply(subs2,
	    (a,b) -> schedule(tempf, (a,b))
	    );
    	while true do (
            nanosleep 100000000;
            if (all(taskList, t->isReady(t))) then break
            )
    	);
    --for k at least 3:
    for r from 3 to k do (
    	if not M.cache.NZCache#?r then (
	    print ("working on minors of size", r);
	    M.cache.NZCache#r = new MutableHashTable;
	    --do cofactor expansion along top row
	    cofactor := (entry, minor) -> (
		sgn := position(minor_1, i -> i >= entry_1);
		if sgn === null then sgn = #(minor_1);
	    	--throw out bad pairs (entry_0 >= minor_0_0 already ensured)
	    	if (sgn < #(minor_1) and minor_1_sgn == entry_1) then return;
	    	X := insert(0,entry_0,minor_0);
	    	Y := insert(sgn,entry_1,minor_1);
	    	contribution := (-1)^sgn * M_entry * M.cache.NZCache#(r-1)#minor;
	    	if not M.cache.NZCache#r#?(X,Y) then M.cache.NZCache#r#(X,Y) = 0;
		M.cache.NZCache#r#(X,Y) = M.cache.NZCache#r#(X,Y) + contribution
	    	);
	     prevminors := new MutableHashTable;
	     scan(keys M.cache.NZCache#(r-1),
    		 k -> (
		     if prevminors#?(k_0_0) then (
	    		 prevminors#(k_0_0) = prevminors#(k_0_0) | {(drop(k_0,1),k_1)}
	    		 ) else (
	    		 prevminors#(k_0_0) = {(drop(k_0,1),k_1)}
	    		 )
		     )
    		 );
	     relevantrows := drop(M.cache.NZCache.NZRows, 1-r);
	     relevantpairs := {};
	     for m in relevantrows do (
    		 --clean up prevminors by deleting all keys up to m
    		 remove(prevminors,m);
    		 relevantpairs = relevantpairs | (
		     toSequence\ ((M.cache.NZCache.ByRows#m)/(i -> (m,i)) **
	    		 flatten apply(keys prevminors,
			     k -> (prevminors#k)/((x,y) -> ({k}|x,y))
			     )
	    		 )
		     )
    		 );
	    taskList := apply(
	        relevantpairs,
		x -> schedule(cofactor,(x_0,x_1))
		);
	    while true do (
            	nanosleep 100000000;
            	if (all(taskList, t->isReady(t))) then break
            	)
	    )
    	)
    )

exteriorPowerSparse = method()
exteriorPowerSparse (ZZ,Matrix) := Matrix => (k, M) -> (
    if (k <= 0 or k > rank M) then return map(exteriorPower(k,target M), exteriorPower(k,source M),0);
    if (k == 1) then return M;
    exteriorPowerSparseHT(k,M);
    print "done computing individual minors, now assembling map";
    wedgelookup := L -> (
    	sum(#L,i -> binomial(L_i,i+1))
    	);
    return map(exteriorPower(k,target M), exteriorPower(k,source M),
	apply(pairs M.cache.NZCache#k, (x,v) -> (wedgelookup(x_0),wedgelookup(x_1)) => v)
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
