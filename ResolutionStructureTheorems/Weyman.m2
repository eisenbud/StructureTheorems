DefectAlgebraDual = method() --very WIP
DefectAlgebraDual (ZZ, ChainComplex) := Module => (k, C) -> (
    if not C.cache.?DefectCache then C.cache.DefectCache = new MutableHashTable;
    if not C.cache.DefectCache#?k then (
	if k == 1 then C.cache.DefectCache#k = dual C_3 ** exteriorPower(rank C.dd_1 + 1, C_1);
	if k == 2 then C.cache.DefectCache#k = exteriorPower(2, C.cache.DefectCache#1);
	);
    return C.cache.DefectCache#k
    )

P1 = method()
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
    C.cache#PCache#1 = map(exteriorPower(r#3, C_2), DefectAlgebraDual(1,C), (B1**B2)*(A1**A2**A3));
    return C.cache#PCache#1
    )
