EnvelopingData = new Type of HashTable

--L should be a direct sum 0 ++ L1 ++ L2 ++ ... ++ LN, matrix is bracket wedge^2 L -> L
initEnvelopingData = method()
initEnvelopingData (Module,Matrix) := EnvelopingData => (L,M) -> (
    N := max indices L;
    brkt := {};
    for i from 1 to N//2 do (
	for j from i+1 to N-i do (
	    brkt = brkt | {(i,j) => 
		(L^[i+j])*M*wedgeProduct(1,1,L)*(L_[i]**L_[j])
		}
	    )
	);
    for i from 1 to N//2 do (
	brkt = brkt | {(i,i) =>
	    (L^[2*i])*M*exteriorPowerSparse(2,L_[i])*wedgeProductConditional((components L)_i)
	    }
	);
    return new EnvelopingData from hashTable {
	Ring => QQ,
	LieAlgebra => hashTable toList apply(1..N, i -> i => (components L)_i),
	Bracket => hashTable brkt,
	Grading => new MutableHashTable,
	Multiplication => new MutableHashTable,
	}
    )

multi = method()
multi (ZZ,List,EnvelopingData) := Matrix => (m,p,U) -> (
    N := max keys U.LieAlgebra;
    if m > N then return map(symGraded(m,U), 0, 0);
    if #p==0 then return (symGraded(m,U))_[{m}];
    if U.Multiplication#?(m,p) then return U.Multiplication#(m,p);
    pL := select(p, i -> i > m);
    pR := select(p, i -> i < m);
    pC := select(p, i -> i ==m);
    p' := pL | pC | {m} | pR;
    --the nonbracket term
    multmap := U.Multiplication#(m,p) = ((symGraded(sum p',U))_[p'])*
        (id_(symPartition(pL,U))**symProd(1,#pC,U.LieAlgebra#m)**id_(symPartition(pR,U)))*
        (flip(U.LieAlgebra#m, symPartition(pL,U))**id_(symPartition(pC|pR,U)));
    --the bracket terms...
    (sLL, sL, c, sR, sRR) := ({},{},p_0,drop(select(p, i -> i == p_0),1),delete(p_0,p));
    while c >= m do (
	--the bracket term
	multmap = multmap + (
	    multi(sLL|sL,m+c+sum(sR)+sum(sRR),U)*
	    (id_(symPartition(sLL|sL,U))**multi(m+c,sR|sRR,U))*
	    (id_(symPartition(sLL|sL,U))**bracketConditional(m,c,U)**id_(symPartition(sR|sRR,U)))*
	    (flip(U.LieAlgebra#m,symPartition(sLL|sL,U))**id_(U.LieAlgebra#c)**id_(symPartition(sR|sRR,U)))*
	    ((id_(U.LieAlgebra#m))**id_(symPartition(sLL,U))**
		((id_(symPartition(sL,U))**symSplit(1,#sR,U.LieAlgebra#c))*
		    symSplit(#sL,#sR+1,U.LieAlgebra#c))**
		id_(symPartition(sRR,U)))
    	    );
	--update sLL,sL,c,sR,sRR
	if #sR>0 then (
	    sL = sL|{c};
	    sR = drop(sR,1)
	    ) else if #sRR>0 then (
	    sLL = sLL|sL|{c};
	    sL = {};
	    c = sRR_0;
	    sR = drop(select(sRR, i->i==c),1);
	    sRR = delete(c,sRR)
	    ) else (
	    break
	    )
	);
    return U.Multiplication#(m,p) = multmap
    )

--L_m x U_n -> ...
multi (ZZ,ZZ,EnvelopingData) := Matrix => (m,n,U) -> (
    if U.Multiplication#?(m,n) then return U.Multiplication#(m,n);
    return U.Multiplication#(m,n) = sum(
	toList\partitions(n,max keys U.LieAlgebra),
	p -> multi(m,p,U)*(id_(U.LieAlgebra#m) ** (symGraded(n,U))^[p])
	)
    )

--L_p x U_n -> ...
multi (List,ZZ,EnvelopingData) := Matrix => (p, n,U) -> (
    if U.Multiplication#?(p,n) then return U.Multiplication#(p,n);
    if #p == 0 then return id_(symGraded(n,U));
    if #p == 1 then return multi(p_0,n,U);
    --break off last "letter" from word
    degs := unique p;
    pow := apply(degs, i -> number(p, j -> j==i));
    d := last degs; s := last pow;
    p' := drop(p,-1);
    p'' := delete(d,p);
    split := multi(p',n+d,U)*(id_(symPartition(p',U))**multi(d,n,U));
    split = split*(id_(symPartition(p'',U))**symSplit(s-1,1,U.LieAlgebra#d)**id_(symGraded(n,U)));
    return U.Multiplication#(p,n) = split
    )

symPartition = method()
symPartition (List,EnvelopingData) := Module => (p,U) -> (
    if #p == 0 then return QQ^1;
    if U.Grading#?p then return U.Grading#p;
    --return U.Grading#p = (symPartitionCBP p)_0
    degs := unique p;
    pow := apply(degs, i -> number(p, j -> j==i));
    comps := toSequence apply(#degs, i -> QQ^(binomial(rank U.LieAlgebra#(degs_i) - 1 + pow_i, pow_i)));
    if #comps > 1 then return U.Grading#p = tensor toSequence comps else return U.Grading#p = comps_0
    )

symGraded = method()
symGraded (ZZ,EnvelopingData) := Module => (n,U) -> (
    if U.Grading#?n then return U.Grading#n;
    N := max keys U.LieAlgebra;
    return U.Grading#n = directSum(
	apply(toList\partitions(n,N), p ->
	    p => symPartition(p,U)
	    )
	)
    )

--L_p -> .. break off words before a'th letter
--"mathematically" nonsense! but useful combinatorially
symSplit = method()
symSplit (ZZ,ZZ,Module) := Matrix => (a,b,M) -> (
    d := rank M;
    bases := {};
    increment := x -> (
	--increment the last entry possible
	i := position(x, i -> i < d-1, Reverse => true);
	if i === null then return "done";
	return take(x,i) | apply(#x-i, j -> x_i + 1)
	);
    x := apply(a+b, i->0);
    while true do (
	bases = append(bases, x);
	x = increment x;
	if x === "done" then break
	);
    entrylist := {};
    --find the basis element of sym that corresponds to a
    --weakly increasing list of indices
    symLookup := p -> (
	binomial(d+#p-1,#p)-1-sum(#p, i -> binomial(d-p_i-2+#p-i,#p-i))
	);
    for u in bases do (
	entrylist = append(entrylist,
	    ((symLookup take(u,a))*binomial(d-1+b,b) + symLookup take(u,-b),symLookup u) => 1
	    )
	);
    return map(QQ^(binomial(d-1+a,a))**QQ^(binomial(d-1+b,b)),QQ^(binomial(d-1+a+b,a+b)), entrylist)
    )

symProd = method()
symProd (ZZ,ZZ,Module) := Matrix => (a,b,M) -> (
    d := rank M;
    basesA := {};
    basesB := {};
    increment := x -> (
	--increment the last entry possible
	i := position(x, i -> i < d-1, Reverse => true);
	if i === null then return "done";
	return take(x,i) | apply(#x-i, j -> x_i + 1)
	);
    x := apply(a, i->0);
    y := apply(b, i->0);
    while true do (
	basesA = append(basesA, x);
	x = increment x;
	if x === "done" then break
	);
    while true do (
	basesB = append(basesB, y);
	y = increment y;
	if y === "done" then break
	);
    entrylist := {};
    --find the basis element of sym that corresponds to a
    --weakly increasing list of indices
    symLookup := p -> (
	binomial(d+#p-1,#p)-1-sum(#p, i -> binomial(d-p_i-2+#p-i,#p-i))
	);
    for u in basesA**basesB do (
	entrylist = append(entrylist,
	    (symLookup sort (u_0 | u_1), (symLookup u_0)*binomial(d-1+b,b) + symLookup u_1) => 1
	    )
	);
    return map(QQ^(binomial(d-1+a+b,a+b)),QQ^(binomial(d-1+a,a))**QQ^(binomial(d-1+b,b)), entrylist)
    )

--sends i x j to i ^ j if i > j, and 0 otherwise
wedgeProductConditional = method()
wedgeProductConditional Module := Matrix => M -> (
    entrylist := {};
    d := rank M;
    wedgeLookup := L -> (
    	sum(#L,i -> binomial(L_i,i+1))
    	);
    for l in subsets(d,2) do (
	entrylist = append(entrylist,
	    (wedgeLookup l, l_1*d + l_0) => 1
	    )
	);
    return map(exteriorPower(2,M), M**M, entrylist)
    )

bracketConditional = method()
bracketConditional (ZZ,ZZ,EnvelopingData) := Matrix => (a,b,U) -> (
    N := max keys U.LieAlgebra;
    if U.Bracket#?(a,b) then (
	return U.Bracket#(a,b)
	) else if (a+b>N and a<=b) then (
	return map(QQ^0,U.LieAlgebra#a ** U.LieAlgebra#b,0)
	) else (
	error ("attempted to use bracket "|net (a,b))
	)
    )
