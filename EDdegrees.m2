newPackage(
    "EDdegrees",
    Version => "0.2.2",
    Headline => "A test package for EDdegree computations",
    PackageExports => {"FMPIntersectionTheory"}
    )

needsPackage "FMPIntersectionTheory"

export {
    "isoQ",
    "gEDdeg",
    "EDdegSmooth",
    "EDdegChiMa",
    -- "tEDdegChi",
    -- "timedEDdegChi",
    "EDdeg",
    "EDdegHypersurface",
    "EDdegCurve",
    -- "EDdegCurve2",
    -- "conormalVariety",
    -- "eddContributionAtQ",
    -- "ratNormCurve",
    -- "eddFermat",
    -- "fermatHypersurface",
    "Smooth",
    "FieldExt"
    -- "Verbose"
    }


gEDdeg = method(TypicalValue => ZZ)
gEDdeg Ideal := X -> (
    {*
        Returns the "generic" ED degree of X, that is, the ED degree of a general translate
        sumPolarRanks is a function from the package FMPIntersectionTheory
    *}
    return sumPolarRanks(X)
    )

    
EDdeg = method(TypicalValue => ZZ,
               Options => {Smooth=>false, 
                           FieldExt=>false,
                           Verbose=>false})
EDdeg(Ideal) := opts -> (X) -> (return EDdeg(X,isoQ X))
EDdeg(Ideal,List) := opts -> (X,L) -> (return EDdeg(X,ideal(matrix{L} * transpose(matrix{terms (isoQ(X))_0}))))
EDdeg(Ideal,Ideal) := opts -> (X,Q) -> (
    {*
        computes ED degree of X using the algebraic formulation via Lagrange multipliers
    *}
    R := ring X;
    C := first(R#baseRings);
    -- can't just set c:=codim X because codim is buggy over field extensions
    c := dim ring X - dim quotient X;
    -- JQ := sum flatten entries jacobian Q;
    M := matrix {for i from 1 to numgens R list 
        random(13,191)}|| transpose(jacobian(Q)) ||transpose(jacobian(X));
    J := ideal ();
    if opts.Smooth then (
        J = saturate(X+minors(c + 2, M), Q);
    ) else (
        sing := saturate trim minors(c, jacobian X);
        J = saturate(X+minors(c + 2, M), sing*Q);
    );
    -- if (codim(J) != numgens(R)) then error "Something went wrong.. got infinitely many critical points";
    if opts.FieldExt then (
        if opts.Verbose then << "computing degree over field extension..." << endl;
        return degreeOverFieldExt(J,Verbose=>opts.Verbose)
    ) else (
        if opts.Verbose then << "computing degree normally..." << endl;
        return degree J
    )
)


EDdegSmooth = method(TypicalValue => ZZ,
    Options => {Verbose => false})    
EDdegSmooth(Ideal) := opts -> (X) -> (return EDdegSmooth(X,isoQ(X),opts))
EDdegSmooth(Ideal,RingElement) := opts ->  (X,q) -> (return EDdegSmooth(X,ideal q,opts))
EDdegSmooth(Ideal,Ideal) := opts -> (X,Q) -> (
    {*
        Formula following Theorem 5.1
        
                                    (1+2h) c(T*X x O(2h)) 
        EDdeg(X) = gEDdeg(X) - \int ---------------------  s(J(X \cap Q), X)
                                            1+h
    *}
    if dim ideal singularLocus X > 0 then error "Expected a smooth variety";
    c := cotangentTensorLineBundle(X,2);
    h := (gens ring c)#1; -- hyperplane class in PPn
    numer := (1+2*h)*c;
    denom := sum (for i from 0 to length(gens ring h) list (-h)^i);
    if opts.Verbose then << "Computing contribution (Segre class) now..." << endl;
    contrib := integral (numer*denom*sub(segreQ(X,Q),ring c));
    if opts.Verbose then << "Computing generic ED degree now..." << endl;
    g := gEDdeg(X);
    if opts.Verbose then << g - contrib << " = " << g << " - " << contrib << endl;
    return g - contrib
    -- return (numer,denom,sub(segreQ(X),ring c))
    )
    

EDdegChiMa = method(TypicalValue => ZZ,
    Options => {Verbose => false})    
EDdegChiMa Ideal := opts -> X -> (
    {*
        Formula following Proposition 3.1
        
        EDdeg(X) = chiMa(X) - chiMa(X \cap Q) - chiMa(X \cap H) + chiMa(X \cap H \cap Q)
    *}
    R := ring X;
    H := ideal sum ((gens R) / (i-> random(13,223)*i));
    Q := isoQ(X);
    chiMaX := if dim X > 0 then integral chernMather(X) else return 0;
    chiMaXH := if dim (X+H) > 0 then integral chernMather(X+H) else 0;
    chiMaXQ := if dim (X+Q) > 0 then integral chernMather(X+Q) else 0;
    chiMaXHQ := if dim (X+H+Q) > 0 then integral chernMather(X+H+Q) else 0;
    if opts.Verbose then << "EDdeg(X) = (-1)^" << dim variety X << " ( " << chiMaX << " - " << chiMaXH << " - " << chiMaXQ << " + " << chiMaXHQ << " )" << endl;
    return (-1)^(dim variety X)*(chiMaX - chiMaXH - chiMaXQ + chiMaXHQ)
    -- return (X,H,Q)
    )

EDdegHypersurface = method(TypicalValue => ZZ,
    Options => {Verbose => false})    
EDdegHypersurface Ideal := opts -> X -> (
    {*
        returns EDdegree of smooth hypersurface X
    *}
    s := sumPolarRanks(X);
    c := eddContributionAtQ(X);
    EDdeg := s - c;
    << EDdeg << " = " << s << " - " << c << endl;
    return EDdeg
    )
    
EDdegCurve = method(TypicalValue => ZZ,
    Options => {Verbose => false})    
EDdegCurve Ideal := opts -> C ->  (
    {*
        In the plane, the main formula can be made quite simple
        
        EDdeg(C) = deg(C)*(deg(C)-2) + #(C \cap Q)
        
        and the last term can be computed as the number of (distinct) factors of a bivariate polynomial
    *}
    R := ring C;
    F := coefficientRing R;
    S' := F(monoid[getSymbol "i"]);
    S := (S'/(S'_0^2+1))(monoid[getSymbol "s",getSymbol "t"]);
    i := sub(S'_0,S);
    s := S_0;
    t := S_1;
    f := [s^2-1,2*s,i*(s^2+1)];
    m := for j to (numgens R - 1) list (R_j => f#j);
    d := degree C;
    p := if isSubset(C,ideal(R_0^2+R_2^2,R_1)) then (
        1 + degreeOverFieldExt(radical sub(C,m))
    ) else (
        degreeOverFieldExt(radical sub(C,m))
    );
    if opts.Verbose then << d << "(" << d << "-2) + " << p << endl;
    return d*(d-2) + p
    )


--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--
-----------------------------------------------------------
-- --  Utility functions 
-----------------------------------------------------------
--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--


degreeOverFieldExt = method(TypicalValue => ZZ,
Options => {Verbose => false})
degreeOverFieldExt Ideal := opts -> p -> (
    HS := numerator reduceHilbert hilbertSeries p;
    if opts.Verbose then << HS << endl;
    degs := gens ring HS;
    return sub(HS,{first degs => 1} | (drop(degs,1) / (i -> i => 0)))
)

-- ith chern class, given the total chern class c
ci = (c,i) -> (someTerms(c,-i-1,1))

cotangentTensorLineBundle = (X,d) -> (
    n := dim X;
    XX := projectiveScheme X;
    H := XX#Hyperplane;
    cTX := if codim X == #(XX#Equations) then (
        H^(codim X) * product(XX#Equations / (e -> 1 - (first degree e)*H))
    ) else (
        chernMather X
    );
    cX := sub(cycleClass projectiveScheme X, ring cTX);
    cTX = cTX // cX;
    -- << cTX << endl;
    h := (gens ring cTX)#1;
    cT'X := sub(cTX,{h=>-h});
    firstCoeff := sub(first flatten entries (coefficients someTerms(cT'X,-1,1))#1,ZZ);
    cT'X = if firstCoeff > 0 then cT'X else -1*cT'X;
    cL := 1 + d*h;
    sum (for i from 0 to n list ( ci(cT'X,i) * cL^(n-1-i) ))
    )

segreQ = (X,Q)-> (
    return segreClass(ideal singularLocus(X+Q), X)
    )

isoQ = X -> (
    return ideal sum ((i -> i^2) \ gens ring X)
    )

conormalVariety = X -> (
    R := ring X;
    C := coefficientRing R;
    n := numgens R;
    RxRdual := C(monoid[toSequence(gens R)| ((i -> (getSymbol "a")_i) \ (0..n-1)) ]);
    I := saturate(sub(X,RxRdual),take(flatten entries gens RxRdual,numgens R));
    J := saturate(sub(jacobian X,RxRdual),take(flatten entries gens RxRdual,numgens R));
    y := (i->{RxRdual_i}) \ drop(vars RxRdual, numgens R);
    return saturate(I + minors(2,matrix{(i->{RxRdual_i}) \(n..2*n-1)}| J),minors(1,J))
    )

eddContributionAtQ = X -> (
    {*
        EDdeg(X) = gEDdeg(X) - \int (1+h)^n s(J(X \cap Q), X)
    *}
    R := ring X;
    n := dim R - 1;
    Q := isoQ(X);
    s := segreClass(ideal singularLocus(X+Q), X);
    C := ring s;
    h := (gens ring s)#1;
    return integral ((1+h)^n * s)
    )

--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--
-----------------------------------------------------------
-- --  Utility functions for experiments
-----------------------------------------------------------
--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--*--

-------------------------
-- Rational normal curves
-------------------------
ratNormCurve = d -> (
    -- x := getSymbol "x";
    -- vrs := vars(0..d);
    -- R := QQ(monoid[vrs]);
    -- R := QQ(monoid[x_0..x_d]);
    R := QQ(monoid[(0..d) / (i -> (getSymbol "x")_i)]);
    -- M := matrix{{vrs_0..vrs_(d-1)},{vrs_1..vrs_d}};
    -- M := matrix{{x_0..x_(d-1)},{x_1..x_d}};
    -- M := matrix{{R_0,R_1},{R_1,R_2}};
    M := matrix{take(gens R,{0,d-1}),take(gens R,{1,d})};
    V := minors(2,M);
    << M << endl;
    << timing EDdeg(V,Smooth=>true) << endl;
    << timing EDdegChiMa(V) << endl;
    << timing EDdegSmooth(V) << endl;
    )
    
-------------------------
-- Fermat Hypersurfaces
-------------------------
fermatHypersurface = (n,d) -> (
    R := QQ(monoid[(i -> (getSymbol "x")_i) \ (0..n)]);
    X := ideal sum ( (gens R) / (i -> i^d) );
    return X
    )

eddFermat = (n,d) -> (
    R := QQ(monoid[(i -> (getSymbol "x")_i) \ (0..n)]);
    gbd := sum apply(n,i->d*(d-1)^i);
    F := sum apply(n+1,i->(gens R)_i^2);
    M := matrix{apply(n+1,i->((gens R)_i)^(d-1))}||matrix{gens R};
    I := ideal(F)+minors(2,M);
    eddeg := gbd-(degree I)*(dim I);
    << eddeg << " = " << gbd << " - " << degree I << " * " << dim I << endl;
    return eddeg
    )

beginDocumentation()

doc ///
Key
  EDdegrees
Headline
  A package for computing Euclidean distance degrees
Description
  Text
    This package implements formulas found in [AH17] as well as the general formula from [DHO+17]
Caveat
SeeAlso
///

doc ///
Key
  EDdeg
  (EDdeg,Ideal)
Headline
  Computes ED degree of any projective variety
Usage
  EDdeg X
Inputs
  X:Ideal
  FieldExt=>Boolean
    Determines whether to modify the way points are counted
  Smooth=>Boolean
    If X is smooth, we can skip computing the jacobian ideal, which saves time
  Verbose=>Boolean
Outputs
  :ZZ
Description
  Example
    PP3 = QQ[w,x,y,z];
    X = minors(2,matrix{{w,x,y},{x,y,z}})
    EDdeg X
///

doc ///
Key
  EDdegCurve
  (EDdegCurve,Ideal)
Headline
  Computes the ED degree of a smooth plane curve
Usage
  EDdegCurve X
Inputs
  X:Ideal
  Verbose=>Boolean
Outputs
  :ZZ
Description
  Text
    In the plane, the main formula can be made quite simple:
    EDdeg(C) = deg(C)*(deg(C)-2) - #(C \cap Q)
    and the last term can be computed as the number of (distinct) factors of a bivariate polynomial
  Example
    PP2 = QQ[x,y,z];
    C = ideal "x5+y5+z5";
    EDdegCurve C
///

doc ///
Key
  EDdegHypersurface
Headline
  Computes the ED degree of a smooth hypersurface
Usage
  EDdegHypersurface X
Inputs
  X:Ideal
  Verbose=>Boolean
Outputs
  :ZZ
///

doc ///
Key
  EDdegChiMa
Headline
  Computes the ED degree of a general translate of a smooth variety
Usage
  EDdegChiMa X
Inputs
  X:Ideal
Outputs
  :ZZ
///

doc ///
Key
  EDdegSmooth
Headline
  Computes the ED degree of any smooth variety
Usage
  EDdegSmooth X
  Verbose=>Boolean
Inputs
  X:Ideal
Outputs
  :ZZ
///

doc ///
Key
  isoQ
Headline
  Ideal of isotropic quadric in same ambient as X
Usage
  isoQ X
Inputs
  X:Ideal
Outputs
  :Ideal
///

doc ///
Key
  gEDdeg
Headline
  ED degree of a general translate of X
Usage
  gEDdeg X
Inputs
  X:Ideal
Outputs
  :ZZ
///

doc ///
Key
  FieldExt
Headline
  Option to indicate X is defined in a field extension
///

doc ///
Key
  Smooth
Headline
  Option to indicate X is known to be smooth
///


TEST ///
d = eddFermat(2,5)
F = fermatHypersurface(2,5)
assert(d == EDdeg(F))
assert(d == EDdeg(F,Smooth=>true))
-- EDdegChi(fermatHypersurface(2,5))
assert(d == EDdegSmooth(F))

d = eddFermat(2,6)
F = fermatHypersurface(2,6)
assert(d == EDdeg(F,Smooth=>true))
-- EDdegChi(fermatHypersurface(2,5))
assert(d == EDdegSmooth(F))
assert(d == EDdegHypersurface(F))

d = eddFermat(2,7)
F = fermatHypersurface(2,7)
assert(d == EDdeg(F,Smooth=>true))
-- EDdegChi(fermatHypersurface(2,5))
assert(d == EDdegSmooth(F))
assert(d == EDdegHypersurface(F))
///

TEST ///
for i from 3 to 20 do (
    assert(eddFermat(2,i) == EDdegCurve fermatHypersurface(2,i))
    )
///

TEST ///
PP3 = QQ[x_0..x_3]
C = minors(2,matrix{{x_0..x_2},{x_1..x_3}})
assert(7 == EDdeg(C,Smooth=>true))
assert(7 == EDdegChiMa(C))
assert(7 == EDdegSmooth(C))

PP4 = QQ[y_0..y_4]
C = minors(2, matrix{{y_0..y_3},{y_1..y_4}})
assert(10 == EDdeg(C,Smooth=>true))
assert(10 == EDdegChiMa(C))
assert(10 == EDdegSmooth(C))

PP5 = QQ[x_0..x_5]
C = minors(2, matrix{{x_0..x_4},{x_1..x_5}})
assert(13 == EDdegChiMa(C))
assert(13 == EDdegSmooth(C))
///

TEST ///
R = QQ[x,y,z]
q = x^2 + y^2 + z^2

C = ideal(q - 2*z^2)
assert(2 == EDdeg(C,Smooth=>true))
assert(2 == EDdegHypersurface(C))
assert(2 == EDdegSmooth(C))
C = ideal(x*q+y^3)
assert(5 == EDdeg(C,Smooth=>true))
assert(5 == EDdegHypersurface(C))
assert(5 == EDdegSmooth(C))
C = ideal(x*y*q+z^4)
assert(10 == EDdeg(C,Smooth=>true))
assert(10 == EDdegHypersurface(C))
assert(10 == EDdegSmooth(C))
C = ideal(x*y*(x+y)*q+z^5)
assert(17 == EDdeg(C,Smooth=>true))
assert(17 == EDdegHypersurface(C))
assert(17 == EDdegSmooth(C))
///

TEST ///
R = QQ[x,y,z,w]
q = x^2 + y^2 + z^2 + w^2

I = ideal(q+y^2)
assert(2 == EDdeg(I,Smooth=>true))
assert(2 == EDdegHypersurface(I))
assert(2 == EDdegSmooth(I))
I = ideal(q+x*y)
assert(4 == EDdeg(I,Smooth=>true))
assert(4 == EDdegHypersurface(I))
assert(4 == EDdegSmooth(I))
I = ideal(w*q+x*y*z)
assert(15 == EDdeg(I,Smooth=>true))
assert(15 == EDdegHypersurface(I))
assert(15 == EDdegSmooth(I))
///

TEST ///
R = QQ[a,b,c,d,e]
q = sum(gens R / (i -> i^2))
-- nonsingular
I = ideal(q + a^2)
assert(2 == EDdeg(I,Smooth=>true))
assert(2 == EDdegHypersurface(I))
assert(2 == EDdegSmooth(I))
I = ideal(q + a*b)
assert(4 == EDdeg(I,Smooth=>true))
assert(4 == EDdegHypersurface(I))
assert(4 == EDdegSmooth(I))
I = ideal(q + a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e)
assert(2 == EDdeg(I,Smooth=>true))
assert(2 == EDdegHypersurface(I))
assert(2 == EDdegSmooth(I))
I = ideal(e*q + a^3+b^3+c^3+d^3)
assert(45 == EDdeg(I,Smooth=>true))
assert(45 == EDdegHypersurface(I))
assert(45 == EDdegSmooth(I))
///

TEST ///
PP5 = QQ[x_0..x_5]
m = matrix{
    {x_0,x_1,x_2},
    {x_1,x_3,x_4},
    {x_2,x_4,x_5}}
S = minors(2,m)
assert(13 == EDdeg(S,Smooth=>true))
assert(13 == EDdegChiMa(S))
assert(13 == EDdegSmooth(S))
///

TEST ///
sleep 5
///

end

restart
uninstallPackage("EDdegrees")
load("EDdegrees.m2")
installPackage("EDdegrees",RemakeAllDocumentation=>true,RerunExamples=>true)

