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

doc ///
    Key
        tdFromList
        (tdFromList, List)
    Headline
        make a tableau diagram from a list
    Usage
        tdFromList L
    Inputs
        L: List
            formatted as for a @TO HashTable@
    Outputs
        : TableauDiagram
    Description
        Text
            (TODO: write explanation of formatting) Below we create the tableau diagram for the element $(a \otimes b) \wedge (c \otimes d)$
            in $\wedge^2 (M \otimes N)$, and then @TO interpret@ it as an element of the module.
        Example
            M = QQ^3; N = QQ^2; a = M_0; b = N_0; c = M_1; d = N_1;
            X = tdFromList {
                TableauShapes => {{1,1}},
                (0,0,0) => tdFromList {
                    TableauShapes => {{1},{1}},
                    (0,0,0) => a,
                    (1,0,0) => b
                    },
                (0,0,1) => tdFromList {
                    TableauShapes => {{1},{1}},
                    (0,0,0) => c,
                    (1,0,0) => d
                    }
                }
            interpret X
///

doc ///
    Key
    	compileBlueprint
	(compileBlueprint, Blueprint)
	Blueprint
	CompiledBlueprint
    Headline
    	assemble a module from pieces
    Usage
    	compileBlueprint(BP)
    Inputs
    	BP: Blueprint
    Outputs
    	: Module
    	: CompiledBlueprint
    Description
    	Text
	    A {\tt Blueprint} is a nested @TO HashTable@ that details the construction
	    of a module. For example, we build a blueprint for
	    $\wedge^2(U \otimes \wedge^2 V) \otimes W$ as follows:
	Example
	    U = QQ^3; V = QQ^3; W = QQ^3;
	    BP = bpFromList {
		(0,{1,1}) => bpFromList {
		    (0,{1}) => U,
		    (1,{1,1}) => V
		    },
		(1,{1}) => W
		}
	Text
	    The keys are pairs {\tt (i,p)} where {\tt i} indexes the tensor factor and
	    {\tt p} is the partition for the Schur functor applied in that factor. The
	    associated value is either another blueprint or a @TO Module@.
	    
	    {\tt compileBlueprint} assembles the module and also outputs a {\tt CompiledBlueprint}
	    @TO HashTable@ where the keys also record the partially constructed module
	    up to that point.
	Example
	    (A,CBP) = compileBlueprint BP
	Text
	    The module {\tt A}, as well as the modules appearing in the keys of {\tt CBP},
	    have a @TO BasisDict@ cache, showing the module's basis elements.
	Example
	    A.cache.BasisDict
///

doc ///
    Key
        schurMap
        (schurMap, Blueprint, Module, Function)
    Headline
        construct a map using a function on tableaux
    Usage
        schurMap(N,M,F)
    Inputs
        N: Module
            a @TO Blueprint@ for the @TO target@ of the desired map
        M: Module
            the @TO source@ of the desired map, which must have a @TO BasisDict@ cache
        F: Function
            a function on tableaux, taking as input values from {\tt M}'s @TO BasisDict@
            and outputting a list of pairs {\tt (c,T)} where {\tt T} is a @TO TableauDiagram@
            encoding an element of {\tt N}
    Outputs
        : Matrix
            the map from {\tt M} to {\tt N} sending each basis element of {\tt M}
            to the corresponding  $\sum c_i T_i$
    Description
        Text
            (TODO: perhaps find a way to represent stuff in a more compact / user-friendly
            format)
            This method is for making maps between modules constructed by tensor products
            and Schur functors. Its functionality generalizes @TO schurModulesMap@ and @TO schur@
            from the @TO SchurFunctors@ package, although it is also significantly slower.
	    
	    As an example, we compute the multiplication map
	    $\wedge^2 A \otimes \wedge^2 A \to \wedge^4 A$.
        Example
            A = QQ^5; M = bdTensor(bdSchur({1,1},A),bdSchur({1,1},A));
            N = bpFromList {
                (0,{1,1,1,1}) => A
                }
            M.cache.BasisDict#0 --what a basis element of M looks like
            F = X -> {
                (1,
                    tdFromList {
                        TableauShapes => {{1,1,1,1}},
                        (0,0,0) => A_(X#(0,0,0)),
                        (0,0,1) => A_(X#(0,0,1)),
                        (0,0,2) => A_(X#(1,0,0)),
                        (0,0,3) => A_(X#(1,0,1))
                        }
                    )
                }
	    time G = schurMap(N,M,F);
	    time G' = wedgeProduct(2,2,A); --much faster, unsurprisingly
            G == G'
///
