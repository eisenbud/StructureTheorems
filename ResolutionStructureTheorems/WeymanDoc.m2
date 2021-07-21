doc ///
    Key
    	P1
	(P1, ChainComplex)
    Headline
    	structure map p1
    Usage
    	P1(C)
    Inputs
    	C: ChainComplex
	    a resolution of length 3
    Outputs
    	: Matrix
    Description
    	Text
	    (Under construction) Currently implemented as
	    $$F_3^* \otimes R \otimes \wedge^{r_1 + 1} F_1 \to \wedge^{r_3-1}F_3 \otimes (\wedge^{r_3-1}F_2^* \otimes \wedge^{r_3-1}F_2) \otimes F_2$$
	    using @TO BE2@{\tt(C,2)} in the last factor, followed by
	    $$(\wedge^{r_3-1}F_3 \otimes \wedge^{r_3-1}F_2^*) \otimes (\wedge^{r_3-1}F_2 \otimes F_2) \to R \otimes \wedge^{r_3} F_2$$
	    using the submaximal minors of $d_3$ in the first factor. See p. 13 in "Structure of Free Resolutions of Length 3."
///