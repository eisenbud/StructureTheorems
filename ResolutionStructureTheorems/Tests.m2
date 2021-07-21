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
