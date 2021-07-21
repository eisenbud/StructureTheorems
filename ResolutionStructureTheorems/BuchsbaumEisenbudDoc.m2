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
