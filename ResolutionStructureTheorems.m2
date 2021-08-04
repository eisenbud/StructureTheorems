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
    "MinorsCache",
    "MinorsProgress",
    "RemainingPairs",
    "Blueprint",
    "CompiledBlueprint",
    "TableauDiagram",
    "fastExteriorPower",
    "exteriorPowerSparseHT",
    "exteriorPowerSparse",
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
    "Cumulative",
    "Q1Coeff",
    "WeymanP",
    "PCache",
    "BracketDualCache",
    "bracketDual",
    
    --GradedEnvelopingAlgebra
    "Bracket",
    "Multiplication",
    "Grading",
    "LieAlgebra",
    "EnvelopingData",
    "initEnvelopingData",
    "multi",
    "symProd",
    "wedgeProductConditional"
    }
exportMutable {}

--needsPackage "SpechtModule" --just for permutationSign
--needsPackage "FastLinAlg"
needsPackage "SchurFunctors"

load "./ResolutionStructureTheorems/Schur.m2"
load "./ResolutionStructureTheorems/BuchsbaumEisenbud.m2"
load "./ResolutionStructureTheorems/Weyman.m2"
load "./ResolutionStructureTheorems/GradedEnvelopingAlgebra.m2"

beginDocumentation()

doc ///
    Key
        ResolutionStructureTheorems
    Headline
        resolution structure theorems
    Description
        Text
            Currently implemented: some framework for defining maps between tensor
            products and composites of Schur modules, the structure theorems of Buchsbaum
	    and Eisenbud, and (to some extent) Weyman's defect Lie algebra.
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
--needsPackage "SchurFunctors"
p=3;q=3;r=3;
r1 = p-1; f1 = p+q; f3 = r-1; n = 2;
for n from 1 to 6 do print (n |": "| net time source bracketDual(r1,f1,f3,n,Ring=>ZZ));


needsPackage "RandomIdeals"
S = ZZ/101[x,y,z]
setRandomSeed "blahblah"
I = randomIdeal({2,2,2,2},basis(1,S))
C = res I
for n from 1 to 3 do print ("p"|n|": "| net source WeymanP(C,n) | " ---> " | net target WeymanP(C,n))

M = (directSum(QQ^30,QQ^5,QQ^30))_[1];
a  = time exteriorPower(3,M);
a' = time fastExteriorPower(3,M); --recursiveMinors from the FastLinAlg package
a''= time exteriorPowerSparse(4,M);
exteriorPowerSparse(4,M) == exteriorPower(4,M);
a == a''

for i from 1 to 8 do print (i|" => "|peek M.cache.MinorsCache#i)

--it's even competitive for non-sparse matrices
S = QQ[x,y,z]
setRandomSeed "blahblah"
M = random(S^(apply(8, i->2)),S^8)
time exteriorPower(7,M);
time exteriorPowerSparse(7,M);

M = directSum(QQ^0,QQ^5,QQ^5,QQ^5,QQ^5,QQ^5)
plist = select(toList\conjugate\partitions(5,3), i -> #i==3)
f = p -> (
    tensor toSequence((unique p)/(i-> exteriorPower(number(p, j -> j==i),(components M)_i)))
    )
f\plist

--enveloping tests
p=2;q=3;r=5;
r1 = p-1; f1 = p+q; f3 = r-1; n = 2;
for n from 1 to 6 do print (n |": "| net time source bracketDual(r1,f1,f3,n));
M = dual bracketDual(r1,f1,f3,5,Cumulative=>true);
L = directSum(QQ^0,QQ^40,QQ^30,QQ^20,QQ^10,QQ^4)
UE8 = initEnvelopingData(L,M);

--example
multi(1,1,UE8);
formation UE8.Grading#2
nonbracketpart = (UE8.Grading#2)_[{1,1}]*symProd(1,1,UE8.LieAlgebra#1);
bracketpart = (UE8.Grading#2)_[{2}]*
    (dual bracketDual(r1,f1,f3,2))*
    wedgeProductConditional(UE8.LieAlgebra#1); --i ** j -> i ^ j if i > j, else 0
bracketpart + nonbracketpart == multi(1,1,UE8)
