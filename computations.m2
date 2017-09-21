oldEDdegCurve = X -> (
    {*
        computes ED degree of smooth X using the algebraic formulation via Lagrange multipliers
    *}
    W = gens ring X / (i -> 1);
    R = ring X;
    C = first(R#baseRings);
    gs = flatten entries gens X;
    Q = ideal(matrix({W}) * matrix (for i in gens R list {i^2}));
    M = matrix {for i from 1 to numgens R list 
        random(13,191)}||matrix {gens R}||transpose(jacobian(X));
    J = saturate(X+minors(3, M), Q);
    return degree J
)

newEDdegCurve = C ->  (
    {*
        oldEDdegCurve(C) = deg(C)*(deg(C)-2) + #(C \cap Q)
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
    HS := numerator reduceHilbert hilbertSeries radical sub(C,m);
    degs := gens ring HS;
    p := sub(HS,{first degs => 1} | (drop(degs,1) / (i -> i => 0)));
    if isSubset(C,ideal(R_0^2+R_2^2,R_1)) then (
        p = p+1
    );
    return d*(d-2) + p
)

fermatHypersurface = (n,d) -> (
    {*
        returns ideal(x_0^d + ... + x_n^d)
    *}
    R := QQ(monoid[(i -> (getSymbol "x")_i) \ (0..n)]);
    X := ideal sum ( (gens R) / (i -> i^d) );
    return X
)


times1 = {}
times2 = {}
numTrials = 3
a = 30
b = 40
for T from 1 to numTrials do (
    t1 = 0;
    t2 = 0;
    for i from a to b do (
        C = fermatHypersurface(2,i);
        t1 = t1 + (timing newEDdegCurve(C))#0;
    );
    << "t1: " << t1 << endl;
    for i from a to b do (
        C = fermatHypersurface(2,i);
        t2 = t2 + (timing oldEDdegCurve(C))#0;
    );
    << "t2: " << t2 << endl;
    times1 = append(times1,t1);
    times2 = append(times2,t2);
)
times1
times2

end

restart
load "computations.m2"
