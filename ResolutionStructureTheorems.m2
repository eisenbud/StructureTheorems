--Current issues:
--
--make it so that BE2 doesn't have to compute all the minors of the differential?

newPackage(
	"ResolutionStructureTheorems",
    	Version => "0.1", 
    	Date => "June 17, 2021",
    	Authors => {
	     {Name => "Xianglong Ni", Email => "xlni@berkeley.edu"}
	     },
    	HomePage => "http://math.berkeley.edu/~xlni/",
    	Headline => "resolution structure theorems",
	AuxiliaryFiles => true -- set to true if package comes with auxiliary files
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
    --Schur
    "Blueprint",
    "CompiledBlueprint",
    "TableauDiagram",
    "fastExteriorPower",
    "leftWedge",
    "tdFromList",
    "bpFromList",
    "coordsFromFilling",
    "bdSchur",
    "bdTensor",
    "compileBlueprint",
    "interpret",
    "tableauStraighten",
    "schurMap",
    "BasisDict",
    "TableauShapes",
    
    --BuchsbaumEisenbud
    "BE1",
    "BE1Cache",
    "BE2",
    "BE2Cache",
    
    --Weyman
    "Q1Coeff",
    "PCache",
    "P1",
    "DefectAlgebraDual",
    "DefectCache"
    }
exportMutable {}

--needsPackage "SpechtModule" --just for permutationSign
needsPackage "FastLinAlg"
needsPackage "SchurFunctors"

load "./ResolutionStructureTheorems/Schur.m2"
load "./ResolutionStructureTheorems/BuchsbaumEisenbud.m2"
load "./ResolutionStructureTheorems/Weyman.m2"

beginDocumentation()

doc ///
    Key
    	ResolutionStructureTheorems
    Headline
    	resolution structure theorems
    Description
    	Text
	    Currently the two structure theorems of Buchsbaum and Eisenbud are
	    implemented, alongside some framework for defining maps between tensor
	    products and composites of Schur modules.
///

load "./ResolutionStructureTheorems/SchurDoc.m2"
load "./ResolutionStructureTheorems/BuchsbaumEisenbudDoc.m2"
load "./ResolutionStructureTheorems/WeymanDoc.m2"

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

end--
restart
uninstallPackage "ResolutionStructureTheorems"
installPackage "ResolutionStructureTheorems"
needsPackage "SchurFunctors"
	Example
	    A = QQ^5; M = bdSchur({1},A);
	    N = bpFromList {
	        (0,{1,1}) => A
		}
	    N' = (compileBlueprint N)_0;
	    F = X -> {
		(1,
		    N'_0
		    )
		}
	    schurMap(N,M,F)
U = QQ^3; V = QQ^3; W = QQ^3;

BP = bpFromList {
         (1,{1})
         (0,{1}) => W
         }

apply(pairs BP, (k,v) -> (
	    Y := compileBlueprint v;
	    return ((k_0,k_1,bdSchur(k_1,Y_0)),Y_1)
	    )
	)

BP = bpFromList {
         (0,{1,1}) => bpFromList {
             (0,{1}) => U,
             (1,{1,1}) => V
             },
         (1,{1}) => W
         }
