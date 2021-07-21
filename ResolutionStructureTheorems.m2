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
load "./ResolutionStructureTheorems/Tests.m2"

end--
restart
uninstallPackage "ResolutionStructureTheorems"
installPackage "ResolutionStructureTheorems"
needsPackage "SchurFunctors"

F_1 = QQ^4;
F_3 = QQ^2;
r_1 = 1;
MBP = bpFromList {
    (0,{1,1}) => bpFromList {
        (0,{1}) => dual F_3,
        (1,apply(r_1+1, i->1)) => F_1
        }
    }
NBP = bpFromList {
    (0,{1,1}) => dual F_3,
    (1,apply(r_1+1, i->2)) => F_1
    }
f = X -> {
    (1,
        tdFromList (
            {
                TableauShapes => {{1,1},apply(r_1+1,i->2)},
                (0,0,0) => (dual F_3)_(X#(0,0,0)#(0,0,0)),
                (0,0,1) => (dual F_3)_(X#(0,0,1)#(0,0,0))
                }
            | flatten apply(r_1+1, i->{
                    (1,0,i) => (F_1)_(X#(0,0,0)#(1,0,i)),
                    (1,1,i) => (F_1)_(X#(0,0,1)#(1,0,i))
                    }
                )
            )
        )
    }
time schurMap(NBP, (compileBlueprint MBP)_0, f)
