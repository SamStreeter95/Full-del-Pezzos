///////////////////////////////////////////////////////////////////////////////////////
// THIS FILE CONTAINS CODE FOR THE PAPER "CLASSIFICATION OF FULL DEL PEZZO SURFACES" //
///////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////
// ALGORITHM 1: FINDING FULL DEL PEZZO SURFACES/PARTIAL CLASSIFICATION UP TO ISOMORPHISM //
///////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////
// SETTING UP AMBIENT STUFF //
//////////////////////////////
TestParams:=[9]; //INSERT THE SELECTION OF q TO RUN OVER
for Q in [1..#TestParams] do
q:=TestParams[Q];
k := GF(q);
AffStart := Set(k) diff {k!0, k!1};
AllPts := Sort([[x,y] : x,y in AffStart | x ne y]);

// COMPUTE ALL 24 PGL3 MATRICES FROM S4 ACTION ON STANDARD POINTS
function S4Matrices(k)
    perms := [];
    for sigma in Permutations({1,2,3,4}) do
        Append(~perms, [sigma[i]:i in [1..4]]);
    end for;
    StandardPoints := [[k!1,k!0,k!0],[k!0,k!1,k!0],[k!0,k!0,k!1],[-k!1,-k!1,-k!1]];
    mats := [];
    for perm in perms do
        cols := [StandardPoints[perm[i]] : i in [1..3]];
        M := Matrix(k,3,3,[cols[1][1],cols[2][1],cols[3][1],
                           cols[1][2],cols[2][2],cols[3][2],
                           cols[1][3],cols[2][3],cols[3][3]]);
        Append(~mats, M);
    end for;
    return mats;
end function;

// APPLY A PGL3 MATRIX TO AN AFFINE POINT [x,y]
function ApplyMatrix(M, pt, k)
    v := M * Matrix(k,3,1,[pt[1],pt[2],k!1]);
    assert v[3][1] ne 0;
    return [v[1][1]/v[3][1], v[2][1]/v[3][1]];
end function;

// BUILD ORBIT REPRESENTATIVES AND PRECOMPUTE ORBITS
Mats := S4Matrices(k);
AllPtsSet := Seqset(AllPts);
Seen := {};
Reps := [];
Orbits := [];
for pt in AllPts do
    if pt in Seen then continue; end if;
    orbit := {};
    for M in Mats do
        img := ApplyMatrix(M, pt, k);
        Include(~orbit, img);
    end for;
    for p in orbit do
        Include(~Seen, p);
    end for;
    Append(~Reps, pt);
    Append(~Orbits, orbit);
end for;
U := Sort(Reps);
print "Number of S4-orbits:", #U;

// PRECOMPUTE CUMULATIVE EXCLUDED SETS
// ExcludedUpTo[ii] = union of orbits of U[1],...,U[ii-1]
// ExcludedUpTo[1] = {} (nothing excluded before processing U[1])
// ExcludedUpTo[ii+1] = ExcludedUpTo[ii] union orbit of U[ii]
ExcludedUpTo := [];
excl := Orbits[1] diff Orbits[1];  // typed empty set
Append(~ExcludedUpTo, excl);
for ii in [1..#U] do
    excl join:= Orbits[ii];
    Append(~ExcludedUpTo, excl);
end for;

//////////////////////
// USEFUL FUNCTIONS //
//////////////////////

// FUNCTIONS FOR COEFFICIENTS OF CURVES

// VERONESE (TERNARY QUADRATIC MONOMIALS IN THE ORDER X^2, Y^2, Z^2, X*Y, X*Z, Y*Z)
function Veronese(P)
    return [
        P[1]^2,
        P[2]^2,
        P[3]^2,
        P[1]*P[2],
        P[1]*P[3],
        P[2]*P[3]
    ];
end function;

// THREEUPLE (TERNARY CUBIC MONOMIALS IN THE ORDER X^3, Y^3, Z^3, X^2*Y, X^2*Z, X*Y^2, Y^2*Z, X*Z^2, Y*Z^2, X*Y*Z)
function ThreeUple(P);
    return [
        P[1]^3,
        P[2]^3,
        P[3]^3,
        P[1]^2*P[2],
        P[1]^2*P[3],
        P[1]*P[2]^2,
        P[2]^2*P[3],
        P[1]*P[3]^2,
        P[2]*P[3]^2,
        P[1]*P[2]*P[3],
    ];
end function;

/// FUNCTIONS FOR CURVES

// GENERIC LINE FROM A 2-TUPLE OF POINTS
function LineFromPoints(T);
    A:=T[1];
    B:=T[2];
    Coeffs:=[A[2]*B[3]- A[3]*B[2],A[3]*B[1]-A[1]*B[3],A[1]*B[2] - A[2]*B[1]];
    return Coeffs;
end function;

// GENERIC CONIC FROM A 5-TUPLE OF POINTS
function ConicFromPoints(T);
    A := Veronese(T[1]);
    B := Veronese(T[2]);
    C := Veronese(T[3]);
    D := Veronese(T[4]);
    E := Veronese(T[5]);
    M := Transpose(Matrix(k,5,6,[
    A[1],A[2],A[3],A[4],A[5],A[6],
    B[1],B[2],B[3],B[4],B[5],B[6],
    C[1],C[2],C[3],C[4],C[5],C[6],
    D[1],D[2],D[3],D[4],D[5],D[6],
    E[1],E[2],E[3],E[4],E[5],E[6]
    ]));
    V := [];
    for j in [1..6] do
        Mj := RemoveRow(M,j);
        Append(~V, (-1)^(j+1)*Determinant(Mj));
    end for;
    Coeffs:=Vector(k,V);
    return Coeffs;
end function;

// PRECOMPUTE 4-POINT PART OF CONIC MATRIX
function ConicMatrixFromFour(T);
    A := Veronese(T[1]);
    B := Veronese(T[2]);
    C := Veronese(T[3]);
    D := Veronese(T[4]);
    return Matrix(k,4,6,[
    A[1],A[2],A[3],A[4],A[5],A[6],
    B[1],B[2],B[3],B[4],B[5],B[6],
    C[1],C[2],C[3],C[4],C[5],C[6],
    D[1],D[2],D[3],D[4],D[5],D[6]
    ]);
end function;

// COMPLETE CONIC FROM PRECOMPUTED 4-POINT MATRIX AND 5TH POINT
function ConicFromMatrixAndPoint(M4, P);
    E := Veronese(P);
    M := Transpose(VerticalJoin(M4, Matrix(k,1,6,[E[1],E[2],E[3],E[4],E[5],E[6]])));
    V := [];
    for j in [1..6] do
        Mj := RemoveRow(M,j);
        Append(~V, (-1)^(j+1)*Determinant(Mj));
    end for;
    return Vector(k,V);
end function;

// PRECOMPUTE 6-POINT PART OF CUBIC MATRIX
function CubicMatrixFromSix(T);
    A := ThreeUple(T[1]);
    B := ThreeUple(T[2]);
    C := ThreeUple(T[3]);
    D := ThreeUple(T[4]);
    E := ThreeUple(T[5]);
    F := ThreeUple(T[6]);
    return Matrix(k,6,10,[
    A[1],A[2],A[3],A[4],A[5],A[6],A[7],A[8],A[9],A[10],
    B[1],B[2],B[3],B[4],B[5],B[6],B[7],B[8],B[9],B[10],
    C[1],C[2],C[3],C[4],C[5],C[6],C[7],C[8],C[9],C[10],
    D[1],D[2],D[3],D[4],D[5],D[6],D[7],D[8],D[9],D[10],
    E[1],E[2],E[3],E[4],E[5],E[6],E[7],E[8],E[9],E[10],
    F[1],F[2],F[3],F[4],F[5],F[6],F[7],F[8],F[9],F[10]
    ]);
end function;

// COMPLETE CUBIC FROM PRECOMPUTED 6-POINT MATRIX, 7TH POINT, AND SINGULAR POINT
function CubicFromMatrixAndPoint(M6, T, i);
    G := ThreeUple(T[7]);
    P := T[i];
    M := Transpose(VerticalJoin(M6, Matrix(k,4,10,[
    G[1],G[2],G[3],G[4],G[5],G[6],G[7],G[8],G[9],G[10],
    3*P[1]^2,0,0,2*P[1]*P[2],2*P[1]*P[3],P[2]^2,0,P[3]^2,0,P[2]*P[3],
    0,3*P[2]^2,0,P[1]^2,0,2*P[1]*P[2],2*P[2]*P[3],0,P[3]^2,P[1]*P[3],
    0,0,3*P[3]^2,0,P[1]^2,0,P[2]^2,2*P[1]*P[3],2*P[2]*P[3],P[1]*P[2]
    ])));
    return Basis(Kernel(M))[1];
end function;

/////////////////////
//// ACTUAL LOOP ////
/////////////////////
t0:=Cputime();
SplitCount:= 0;
FullCount := 0;
FullTuples := [];
FourPoints:=[[1,0,0],[0,1,0],[0,0,1],[1,1,1]];

// FIFTH POINT LOOP
for i in [1..#U] do
    u:=U[i];
    // Available: AllPts minus orbits of U[1],...,U[i-1]
    // Used only for selecting 6th and 7th points
    Available := [t : t in AllPts | t notin ExcludedUpTo[i]];
    FiveBad:={};
    a:=u[1];
    b:=u[2];
    FivePoints:=FourPoints cat [[a,b,1]];
    // FiveBad: computed over ALL of AllPts
    for ii in [1..4] do
    // Removing lines
        FiveLineCoeffs:=LineFromPoints([FivePoints[ii],[a,b,1]]);
        FiveBad join:= {v: v in AllPts | FiveLineCoeffs[1]*v[1]+FiveLineCoeffs[2]*v[2]+FiveLineCoeffs[3] eq 0};
    end for;
    // Removing conic
    C:={v: v in AllPts | (b-a)*v[1]*v[2] + b*(a-1)*v[1] eq a*(b-1)*v[2]};
    FiveBad join:= C;
    // V: candidates for 6th point — in Available and not in FiveBad
    V := [t : t in Available | t notin FiveBad];
    Vset := {t : t in V};
    // FullV: ALL points surviving FiveBad (for fullness check)
    FullV := {t : t in AllPts | t notin FiveBad};
// SIXTH POINT LOOP
    for j in [1..#Available] do
        v:=Available[j];
        if v notin Vset then continue; end if;
        SixBad:={};
        c:=v[1];
        d:=v[2];
        SixPoints:=FivePoints cat [[c,d,1]];
        // SixBad: computed over ALL of AllPts
        for jj in [1..5] do
        // Removing lines - over FullV
            SixLineCoeffs := LineFromPoints([SixPoints[jj],[c,d,1]]);
            SixBad join:= {w : w in AllPts | SixLineCoeffs[1]*w[1] + SixLineCoeffs[2]*w[2] + SixLineCoeffs[3] eq 0};
        // Removing conics - over FullV
            SixConicCoeffs := ConicFromPoints([SixPoints[l]: l in [1..5] | l ne jj] cat [[c,d,1]]);
            SixBad join:= {w : w in AllPts | SixConicCoeffs[1]*w[1]^2 + SixConicCoeffs[2]*w[2]^2 + SixConicCoeffs[3] + SixConicCoeffs[4]*w[1]*w[2] + SixConicCoeffs[5]*w[1] + SixConicCoeffs[6]*w[2] eq 0};
        end for;
        // W: candidates for 7th point — in Available, not in FiveBad, not in SixBad
        W := [t : t in Available | t notin FiveBad and t notin SixBad];
        Wset := {t : t in W};
        // FullW: ALL points surviving FiveBad and SixBad (for fullness check)
        FullW := FullV diff SixBad;
// PRE-COMPUTATION FOR SEVENTH POINT CURVES
        // Pre-compute conic 4-point matrices given SixPoints
        ConicIdx:=AssociativeArray();
        for I in [1..6] do
            for J in [I+1..6] do
                ConicIdx[<I,J>]:=ConicMatrixFromFour([SixPoints[L]: L in [1..6] | L ne I and L ne J]);
            end for;
        end for;
        // Pre-compute cubic 6-point matrices given SixPoints
        CubicMat6:=CubicMatrixFromSix(SixPoints);
//SEVENTH POINT LOOP
        for l in [1..#Available] do
            w:=Available[l];
            if w notin Wset then continue; end if;
            // symmetry breaking: avoid double counting {u,v,w} and {u,w,v}
            if Position(AllPts, w) le Position(AllPts, v) then continue; end if;
            SevenBad:={};
            e:=w[1];
            f:=w[2];
            SevenPoints:=SixPoints cat [[e,f,1]];
            //Removing lines — over FullW
            for ll in [1..6] do
                lc:=LineFromPoints([SixPoints[ll],[e,f,1]]);
                SevenBad join:= {z:z in FullW | lc[1]*z[1]+lc[2]*z[2]+lc[3] eq 0};
            end for;
            //Removing conics — over FullW
            for I in [1..6] do
                for J in [I+1..6] do
                    cc := ConicFromMatrixAndPoint(ConicIdx[<I,J>], [e,f,1]);
                    SevenBad join:= {z: z in FullW | cc[1]*z[1]^2 + cc[2]*z[2]^2 + cc[3] + cc[4]*z[1]*z[2] + cc[5]*z[1] + cc[6]*z[2] eq 0};
                end for;
            end for;
            //Removing cubics — over FullW
            for A in [1..7] do
                ca := CubicFromMatrixAndPoint(CubicMat6, SevenPoints, A);
                SevenBad join:= {z:z in FullW | ca[1]*z[1]^3 + ca[2]*z[2]^3 + ca[3] + ca[4]*z[1]^2*z[2] + ca[5]*z[1]^2 + ca[6]*z[2]^2*z[1] + ca[7]*z[2]^2 + ca[8]*z[1] + ca[9]*z[2] + ca[10]*z[1]*z[2] eq 0};
            end for;
            // X: points in FullW not covered by any curve through the 7 points
            X := FullW diff SevenBad;
            if #X eq 0 then
                FullCount := FullCount + 1;
                //[a,b,c,d,e,f];
                Append(~FullTuples,[a,b,c,d,e,f]);
            end if;
            SplitCount:=SplitCount+1;
            if SplitCount mod 10000 eq 0 then
                print "Split count =", SplitCount, ", Full Count =", FullCount, ", Elapsed =", Cputime(t0);
            end if;
        end for;
    end for;
    print "Completed loop", i, "in", Cputime(t0); 
end for;
print "#FullTuples =", #FullTuples;
print "SplitCount =", SplitCount;
end for;

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////
// ALGORITHM 2: FINDING THE BRANCH QUARTIC IN CHARACTERISTIC NOT 2 OR 3 //
//////////////////////////////////////////////////////////////////////////
function SevenTupleToQuartic(a, b, c, d, e, f, k)
    SevenPoints := [[k!1,k!0,k!0],[k!0,k!1,k!0],[k!0,k!0,k!1],[k!1,k!1,k!1],
                    [k!a,k!b,k!1],[k!c,k!d,k!1],[k!e,k!f,k!1]];
/////////////////////////////////////////////////////////////////////
// STEP 1: FIND A BASIS FOR THE NET OF CUBICS THROUGH THE 7 POINTS //
/////////////////////////////////////////////////////////////////////    
    function ThreeUple(P)
        return [P[1]^3,P[2]^3,P[3]^3,P[1]^2*P[2],P[1]^2*P[3],P[1]*P[2]^2,
                P[2]^2*P[3],P[1]*P[3]^2,P[2]*P[3]^2,P[1]*P[2]*P[3]];
    end function;
    M := Transpose(Matrix(k,7,10,&cat[ThreeUple(P) : P in SevenPoints]));
    KB := Basis(Kernel(M));
    assert #KB eq 3;
    
    R<X,Y,Z> := PolynomialRing(k,3);
    mons3 := [X^3,Y^3,Z^3,X^2*Y,X^2*Z,X*Y^2,Y^2*Z,X*Z^2,Y*Z^2,X*Y*Z];
    F0 := &+[KB[1][i]*mons3[i] : i in [1..10]];
    F1 := &+[KB[2][i]*mons3[i] : i in [1..10]];
    F2 := &+[KB[3][i]*mons3[i] : i in [1..10]];
/////////////////////////////////////////////////////////////////////////////////////////////////////////    
//STEP 2: COMPUTE THE JACOBIAN CURVE (REQUIRES CHARACTERISTIC NOT 2 OR 3 TO AVOID RAMIFICATION ISSUES) //
/////////////////////////////////////////////////////////////////////////////////////////////////////////
    dF := [[Derivative(Fi,j) : Fi in [F0,F1,F2]] : j in [1..3]];   // dF[j] = the j-th partials
    if Characteristic(k) ne 3 then
        J := Determinant(Matrix(R,3,3, dF[1] cat dF[2] cat dF[3]));        // old gradient block
    else
        Mz := Determinant(Matrix(R,3,3, [F0,F1,F2] cat dF[1] cat dF[2]));  // value, d/dx, d/dy
        J  := ExactQuotient(Mz, R.3);                                       // divide by Z -> degree 6
    end if;

////////////////////////////////////////////////////////    
//STEP 3: COLLECT SMOOTH POINTS ON J AND THEIR IMAGES //
////////////////////////////////////////////////////////
    function QuarticMons(v)
        l0 := v[1]; l1 := v[2]; l2 := v[3];
        return [l0^4, l0^3*l1, l0^3*l2, l0^2*l1^2, l0^2*l1*l2, l0^2*l2^2,
                l0*l1^3, l0*l1^2*l2, l0*l1*l2^2, l0*l2^3,
                l1^4, l1^3*l2, l1^2*l2^2, l1*l2^3, l2^4];
    end function;
    ImagePts := [* *];
    ext_deg := 1;
    while true do
        kext := GF(Characteristic(k), ext_deg*Degree(k));
        Pext := ProjectivePlane(kext);
        Rext<X,Y,Z> := CoordinateRing(Pext);
        Jext := Evaluate(J, [Rext.1, Rext.2, Rext.3]);
        assert Degree(Jext) gt 0;
        Jcurve := Curve(Pext, Jext);
        pts := RationalPoints(Jcurve);
        for pt in pts do
            p := [kext!pt[1], kext!pt[2], kext!pt[3]];
            img := [Evaluate(F0,p), Evaluate(F1,p), Evaluate(F2,p)];
            // Skip base points where map is undefined
            if &and[img[i] eq 0 : i in [1..3]] then continue; end if;
            i := 1; while img[i] eq 0 do i +:= 1; end while;
            img := [img[j]/img[i] : j in [1..3]];
            Append(~ImagePts, img);
        end for;
        // Check rank
        if #ImagePts ge 14 then
            kext := GF(Characteristic(k), ext_deg*Degree(k));
            rows := [];
            for pt in ImagePts do
                Append(~rows, QuarticMons([kext!pt[1], kext!pt[2], kext!pt[3]]));
            end for;
            Mq := Matrix(kext, rows);
            if Rank(Mq) eq 14 then break; end if;
        end if;
        //print ext_deg, "insufficient";
        ext_deg +:= 1;
    end while;

    kext := GF(Characteristic(k), ext_deg*Degree(k));
    rows := [];
    for pt in ImagePts do
        Append(~rows, QuarticMons([kext!pt[1], kext!pt[2], kext!pt[3]]));
    end for;
    Mq := Matrix(kext, rows);
    KB2 := Basis(Kernel(Transpose(Mq)));
    assert #KB2 ge 1;
    coeffs := KB2[1];
    
    S<l0,l1,l2> := PolynomialRing(k,3);
    mons4 := [l0^4, l0^3*l1, l0^3*l2, l0^2*l1^2, l0^2*l1*l2, l0^2*l2^2,
              l0*l1^3, l0*l1^2*l2, l0*l1*l2^2, l0*l2^3,
              l1^4, l1^3*l2, l1^2*l2^2, l1*l2^3, l2^4];
    quartic := &+[k!(coeffs[i])*mons4[i] : i in [1..15]];
    
    return quartic;
end function;

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////
// ALGORITHM 3: FIND ALL ISOMORPHISMS FROM ALGORITHM 1 OUTPUT //
////////////////////////////////////////////////////////////////

////////////////////////////////////
// STEP 1: CONSTRUCT THE QUARTICS //
////////////////////////////////////
FullQuartics := [];
for g in FullTuples do
    Q := SevenTupleToQuartic(g[1],g[2],g[3],g[4],g[5],g[6],k);
    Append(~FullQuartics, Q);
end for;

//////////////////////////////////////
// STEP 2: FIND ISOMORPHISM CLASSES //
//////////////////////////////////////
// Find isomorphism classes
PP := ProjectivePlane(k);
FullQuarticClasses := [];
Remaining := [1..#FullQuartics];
while #Remaining gt 0 do
    i := Remaining[1];
    Ci := Curve(PP, FullQuartics[i]);
    class := [i];
    NewRemaining := [];
    for j in Remaining[2..#Remaining] do
        Cj := Curve(PP, FullQuartics[j]);
        iso, _ := IsIsomorphic(Ci, Cj);
        if iso then
            Append(~class, j);
        else
            Append(~NewRemaining, j);
        end if;
    end for;
    Append(~FullQuarticClasses, class);
    print "Class complete in", Cputime(t0);
    Remaining := NewRemaining;
    print #Remaining;
end while;
print "Number of isomorphism classes:", #FullQuarticClasses;
for i in [1..#FullQuarticClasses] do
    print "Class", i, "has", #FullQuarticClasses[i], "members";
end for;

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////
// ALGORITHM 4: NORMALISE 7-TUPLES //
/////////////////////////////////////

// STEP 1: PUT POINTS IN A CANONICAL FORM
NormPt := function(p)
    i := 1; while p[i] eq 0 do i +:= 1; end while;
    return [p[j]/p[i] : j in [1..3]];
end function;

keyPt := function(pt)
    q := NormPt(pt);
    return &cat[[Integers()!c : c in Eltseq(q[j])] : j in [1..3]];
end function;

// PGL3 canonical form: lex-min over all ordered 4-frames -> standard frame, rest sorted
function Normalize7Tuple(T, k)
    best := []; n := 7;
    for i1 in [1..n] do for i2 in [1..n] do
      if i2 eq i1 then continue; end if;
      for i3 in [1..n] do
        if i3 in {i1,i2} then continue; end if;
        for i4 in [1..n] do
          if i4 in {i1,i2,i3} then continue; end if;
          P1:=T[i1]; P2:=T[i2]; P3:=T[i3]; P4:=T[i4];
          B := Matrix(k,3,3,[P1[1],P2[1],P3[1], P1[2],P2[2],P3[2], P1[3],P2[3],P3[3]]);
          if Determinant(B) eq 0 then continue; end if;
          lam := B^-1 * Matrix(k,3,1,[P4[1],P4[2],P4[3]]);
          if lam[1][1] eq 0 or lam[2][1] eq 0 or lam[3][1] eq 0 then continue; end if;
          Bp := Matrix(k,3,3,[lam[1][1]*P1[1],lam[2][1]*P2[1],lam[3][1]*P3[1],
                              lam[1][1]*P1[2],lam[2][1]*P2[2],lam[3][1]*P3[2],
                              lam[1][1]*P1[3],lam[2][1]*P2[3],lam[3][1]*P3[3]]);
          M := Bp^-1;
          rest := [j : j in [1..n] | j notin {i1,i2,i3,i4}];
          imgs := [];
          for j in rest do
              v := M * Matrix(k,3,1,[T[j][1],T[j][2],T[j][3]]);
              Append(~imgs, keyPt([v[1][1],v[2][1],v[3][1]]));
          end for;
          Sort(~imgs);
          if IsEmpty(best) or imgs lt best then best := imgs; end if;
        end for;
      end for;
    end for; end for;
    return best;
end function;


// Build the 7-point projective tuple from a FullTuples entry [a,b,c,d,e,f]
SevenTuple := function(g, k)
    return [[k!1,k!0,k!0],[k!0,k!1,k!0],[k!0,k!0,k!1],[k!1,k!1,k!1],
            [k!g[1],k!g[2],k!1],[k!g[3],k!g[4],k!1],[k!g[5],k!g[6],k!1]];
end function;

// PGL3 REDUCTION
// OUTPUT: Reps (one FullTuples entry per PGL3 class) and the bucket map.
function ReduceToPGL3Classes(FullTuples, k)
    buckets := AssociativeArray();
    reps := [];
    for idx in [1..#FullTuples] do
        key := Normalize7Tuple(SevenTuple(FullTuples[idx], k), k);
        if IsDefined(buckets, key) then
            Append(~buckets[key], idx);
        else
            buckets[key] := [idx];
            Append(~reps, FullTuples[idx]);
        end if;
    end for;
    return reps, buckets;
end function;

///////////////////////
//END OF ALGORITHM 4 //
///////////////////////

// QUADRATIC TRANSFORMATION
sigma := function(q) return [q[2]*q[3], q[1]*q[3], q[1]*q[2]]; end function;

function ApplyCremona(T, trip, k)   // quadratic transformation at a triple of the 7 points
    a:=trip[1]; b:=trip[2]; c:=trip[3];
    A := Matrix(k,3,3,[T[a][1],T[b][1],T[c][1],
                       T[a][2],T[b][2],T[c][2],
                       T[a][3],T[b][3],T[c][3]]);
    if Determinant(A) eq 0 then return T, false; end if;
    M := A^-1;
    others := [j : j in [1..7] | j notin trip];
    newT := [[k!1,k!0,k!0],[k!0,k!1,k!0],[k!0,k!0,k!1]];
    for j in others do
        v := M * Matrix(k,3,1,[T[j][1],T[j][2],T[j][3]]);
        Append(~newT, sigma([v[1][1],v[2][1],v[3][1]]));
    end for;
    return newT, true;
end function;

// CREMONA MERGE
// Merge a list of PGL3-class reps (each in FullTuples format [a,b,c,d,e,f]) under Cremona
function CremonaMerge(Reps, k)
// Step 1: Make an array indexed by canonical PGL-reps
    ClassReps := [];
    for g in Reps do
        Append(~ClassReps, [[k!1,k!0,k!0],[k!0,k!1,k!0],[k!0,k!0,k!1],[k!1,k!1,k!1],
            [k!g[1],k!g[2],k!1],[k!g[3],k!g[4],k!1],[k!g[5],k!g[6],k!1]]);
    end for;
    nc := #ClassReps;
    keyToClass := AssociativeArray();
    for i in [1..nc] do keyToClass[Normalize7Tuple(ClassReps[i],k)] := i; end for;
// Step 2: Find the "Cremona neighbours" of each tuple
    triples := [Sort([x : x in s]) : s in Subsets({1..7},3)];   // C(7,3) = 35
    nbrs := [[Integers()|] : i in [1..nc]];
    for i in [1..nc] do
        for trip in triples do
            newT, ok := ApplyCremona(ClassReps[i], trip, k);
            if not ok then continue; end if;
            key := Normalize7Tuple(newT, k);
            if IsDefined(keyToClass, key) then
                j := keyToClass[key];
                if j notin nbrs[i] then Append(~nbrs[i], j); end if;
            else
                print "  [!] Cremona left the rep set from class", i;
            end if;
        end for;
    end for;
// Step 3: Group into connected components under Cremona equivalence
    comp := [0 : i in [1..nc]]; ncomp := 0;
    for start in [1..nc] do
        if comp[start] ne 0 then continue; end if;
        ncomp +:= 1; stack := [start];
        while #stack gt 0 do
            x := stack[#stack]; Prune(~stack);
            if comp[x] ne 0 then continue; end if;
            comp[x] := ncomp;
            for y in nbrs[x] do if comp[y] eq 0 then Append(~stack, y); end if; end for;
        end while;
    end for;
    // One FullTuples-format rep per connected component
    classReps := [];
    seen := {};
    for i in [1..nc] do
        if comp[i] notin seen then Include(~seen, comp[i]); Append(~classReps, Reps[i]); end if;
    end for;
    return ncomp, comp, classReps;
end function;

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////
// ALGORITHM 5: SIEVE BY PGL3 AND CREMONA //
////////////////////////////////////////////
reps, buckets := ReduceToPGL3Classes(FullTuples, k);              // FullTuples -> PGL3-class reps
printf "PGL3 classes: %o\n", #reps;
ncomp, comp, classReps := CremonaMerge(reps, k);                // PGL3 classes -> Cremona classes
printf "Cremona classes: %o\n", ncomp;

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////
// ALGORITHM 6: COMPUTE A AND B IN CHARACTERISTIC 2 //
//////////////////////////////////////////////////////

// Input: g = [a,b,c,d,e,f] in FullTuples format; k = GF(2^n).
// Output: A (conic), B (quartic).
function ComputeABFull(g, k)
    R<X,Y,Z>   := PolynomialRing(k, 3);
    S<l0,l1,l2>:= PolynomialRing(k, 3);
    GF2    := GF(Characteristic(k));
    d      := Degree(k);
    kbasis := [k.1^i : i in [0..d-1]];

    SevenPoints := [[k!1,k!0,k!0],[k!0,k!1,k!0],[k!0,k!0,k!1],[k!1,k!1,k!1],
                    [k!g[1],k!g[2],k!1],[k!g[3],k!g[4],k!1],[k!g[5],k!g[6],k!1]];
    function ThreeUple(P)
        return [P[1]^3,P[2]^3,P[3]^3,P[1]^2*P[2],P[1]^2*P[3],P[1]*P[2]^2,
                P[2]^2*P[3],P[1]*P[3]^2,P[2]*P[3]^2,P[1]*P[2]*P[3]];
    end function;
    Mnet := Transpose(Matrix(k,7,10,&cat[ThreeUple(P) : P in SevenPoints]));
    KB   := Basis(Kernel(Mnet));
    mons3 := [X^3,Y^3,Z^3,X^2*Y,X^2*Z,X*Y^2,Y^2*Z,X*Z^2,Y*Z^2,X*Y*Z];
    F0 := &+[KB[1][i]*mons3[i] : i in [1..10]];
    F1 := &+[KB[2][i]*mons3[i] : i in [1..10]];
    F2 := &+[KB[3][i]*mons3[i] : i in [1..10]];

    // STEP 1: OBTAIN A AS IMAGE OF JACOBIAN CURVE
    JM := Matrix(R,3,3,[Derivative(F0,1),Derivative(F0,2),Derivative(F0,3),
                        Derivative(F1,1),Derivative(F1,2),Derivative(F1,3),
                        Derivative(F2,1),Derivative(F2,2),Derivative(F2,3)]);
    J := Determinant(JM);
    ImagePts := [* *]; ext_deg := 1;
    while #ImagePts lt 10 and ext_deg le 4 do
        kext := GF(Characteristic(k), ext_deg*Degree(k));
        for x0 in kext do for y0 in kext do
            pt := [kext!x0, kext!y0, kext!1];
            if Evaluate(J, pt) eq 0 then
                img := [Evaluate(F0,pt),Evaluate(F1,pt),Evaluate(F2,pt)];
                if not (img[1] eq 0 and img[2] eq 0 and img[3] eq 0) then
                    i := 1; while img[i] eq 0 do i +:= 1; end while;
                    Append(~ImagePts, [img[j]/img[i] : j in [1..3]]);
                end if;
            end if;
        end for; end for;
        if #ImagePts lt 10 then ext_deg +:= 1; end if;
    end while;
    kext := Parent(ImagePts[#ImagePts][1]);
    Mc := Matrix(kext, #ImagePts, 6,
        &cat[[p[1]^2,p[2]^2,p[3]^2,p[1]*p[2],p[1]*p[3],p[2]*p[3]]
             : p in [[kext!q[j] : j in [1..3]] : q in ImagePts]]);
    KBc := Basis(Kernel(Transpose(Mc)));
    mons2S := [l0^2,l1^2,l2^2,l0*l1,l0*l2,l1*l2];
    A := &+[k!(KBc[1][i])*mons2S[i] : i in [1..6]];

    // STEP 2: OBTAIN B BY F2-LINEAR ALGEBRA
    A_phi  := Evaluate(A, [F0,F1,F2]);
    mons6  := MonomialsOfDegree(R, 6);
    mons12 := MonomialsOfDegree(R, 12);
    mons4  := MonomialsOfDegree(S, 4);
    Im_phi := Matrix(k, 15, #mons12,
        [[MonomialCoefficient(Evaluate(m,[F0,F1,F2]),mon) : mon in mons12]
         : m in mons4]);
    KBKer   := Basis(Kernel(Transpose(Im_phi)));
    Aphi_mj := [A_phi*mons6[j] : j in [1..#mons6]];
    mj2     := [mons6[j]^2     : j in [1..#mons6]];
    n_vars  := #mons6 * d;
    ConstrK := Matrix(k, #KBKer, n_vars,
        [[ &+[KBKer[r][t]*MonomialCoefficient(
                kbasis[m]^2*mj2[j] + kbasis[m]*Aphi_mj[j], mons12[t])
              : t in [1..#mons12]]
           : m in [1..d], j in [1..#mons6]]   // m fastest, matches (j-1)*d+m
         : r in [1..#KBKer]]);
    ConstrF2 := Matrix(GF2, #KBKer*d, n_vars,
        [[Eltseq(ConstrK[r][c])[s] : c in [1..n_vars]]
         : r in [1..#KBKer], s in [1..d]]);
    KerConstr := Kernel(Transpose(ConstrF2));
    FiFs := [F0^2,F0*F1,F0*F2,F1^2,F1*F2,F2^2];
    FiF_GF2vecs := [];
    for f in FiFs do for m in [1..d] do
        gg := kbasis[m]*f;
        Append(~FiF_GF2vecs,
            Vector(GF2, &cat[Eltseq(MonomialCoefficient(gg,mons6[j]))
                             : j in [1..#mons6]]));
    end for; end for;
    FiFspace := sub<VectorSpace(GF2,n_vars) | FiF_GF2vecs>;
    B := S!0;
    for bv in Basis(KerConstr) do
        if bv in FiFspace then continue; end if;
        coeffs := [ &+[k!(GF2!bv[(j-1)*d+m])*kbasis[m] : m in [1..d]]
                    : j in [1..#mons6] ];
        w := &+[coeffs[j]*mons6[j] : j in [1..#mons6]];
        cand := w^2 + A_phi*w;
        flag, sol := IsConsistent(Im_phi, Vector(k,
                        [MonomialCoefficient(cand,mon) : mon in mons12]));
        if flag then
            Bc := &+[sol[i]*mons4[i] : i in [1..15]];
            if Evaluate(Bc,[F0,F1,F2]) eq cand then B := Bc; break; end if;
        end if;
    end for;
    return A, B;
end function;

// FUNCTION TO DECIDE ISOMORPHISM
function IsIsoDP2(g1, g2, k)
    R<X,Y,Z> := PolynomialRing(k,3);
    S<l0,l1,l2> := PolynomialRing(k,3);
    GF2 := GF(Characteristic(k));
    d := Degree(k);
    kbasis := [k.1^i : i in [0..d-1]];
    mons2 := [l0^2,l1^2,l2^2,l0*l1,l0*l2,l1*l2];
    mons4 := MonomialsOfDegree(S,4);

    GF2vec := function(F)   // degree-4 form -> GF2 vector of length 15*d
        return Vector(GF2, &cat[Eltseq(MonomialCoefficient(F,mon)) : mon in mons4]);
    end function;

    ComputeAB := function(g)
        SevenPoints := [[k!1,k!0,k!0],[k!0,k!1,k!0],[k!0,k!0,k!1],[k!1,k!1,k!1],
                        [k!g[1],k!g[2],k!1],[k!g[3],k!g[4],k!1],[k!g[5],k!g[6],k!1]];
        TU := function(P)
            return [P[1]^3,P[2]^3,P[3]^3,P[1]^2*P[2],P[1]^2*P[3],P[1]*P[2]^2,
                    P[2]^2*P[3],P[1]*P[3]^2,P[2]*P[3]^2,P[1]*P[2]*P[3]];
        end function;
        Mnet := Transpose(Matrix(k,7,10,&cat[TU(P) : P in SevenPoints]));
        KB := Basis(Kernel(Mnet));
        mons3 := [X^3,Y^3,Z^3,X^2*Y,X^2*Z,X*Y^2,Y^2*Z,X*Z^2,Y*Z^2,X*Y*Z];
        F0 := &+[KB[1][i]*mons3[i] : i in [1..10]];
        F1 := &+[KB[2][i]*mons3[i] : i in [1..10]];
        F2 := &+[KB[3][i]*mons3[i] : i in [1..10]];
        JM := Matrix(R,3,3,[Derivative(F0,1),Derivative(F0,2),Derivative(F0,3),
                            Derivative(F1,1),Derivative(F1,2),Derivative(F1,3),
                            Derivative(F2,1),Derivative(F2,2),Derivative(F2,3)]);
        J := Determinant(JM);
        ImagePts := [* *]; ext_deg := 1;
        while #ImagePts lt 10 and ext_deg le 4 do
            kext := GF(Characteristic(k), ext_deg*Degree(k));
            for x0 in kext do for y0 in kext do
                pt := [kext!x0, kext!y0, kext!1];
                if Evaluate(J, pt) eq 0 then
                    img := [Evaluate(F0,pt),Evaluate(F1,pt),Evaluate(F2,pt)];
                    if not (img[1] eq 0 and img[2] eq 0 and img[3] eq 0) then
                        i := 1; while img[i] eq 0 do i +:= 1; end while;
                        Append(~ImagePts, [img[j]/img[i] : j in [1..3]]);
                    end if;
                end if;
            end for; end for;
            if #ImagePts lt 10 then ext_deg +:= 1; end if;
        end while;
        kext := Parent(ImagePts[#ImagePts][1]);
        Mc := Matrix(kext, #ImagePts, 6,
            &cat[[p[1]^2,p[2]^2,p[3]^2,p[1]*p[2],p[1]*p[3],p[2]*p[3]]
                 : p in [[kext!q[j] : j in [1..3]] : q in ImagePts]]);
        KBc := Basis(Kernel(Transpose(Mc)));
        A := &+[k!(KBc[1][i])*mons2[i] : i in [1..6]];
        A_phi := Evaluate(A, [F0,F1,F2]);
        mons6  := MonomialsOfDegree(R, 6);
        mons12 := MonomialsOfDegree(R, 12);
        Im_phi := Matrix(k, 15, #mons12,
            [[MonomialCoefficient(Evaluate(m,[F0,F1,F2]),mon) : mon in mons12]
             : m in mons4]);
        KBKer := Basis(Kernel(Transpose(Im_phi)));
        Aphi_mj := [A_phi*mons6[j] : j in [1..#mons6]];
        mj2     := [mons6[j]^2     : j in [1..#mons6]];
        n_vars  := #mons6 * d;
        ConstrK := Matrix(k, #KBKer, n_vars,
            [[ &+[KBKer[r][t]*MonomialCoefficient(
                    kbasis[m]^2*mj2[j] + kbasis[m]*Aphi_mj[j], mons12[t])
                  : t in [1..#mons12]]
               : m in [1..d], j in [1..#mons6]]
             : r in [1..#KBKer]]);
        ConstrF2 := Matrix(GF2, #KBKer*d, n_vars,
            [[Eltseq(ConstrK[r][c])[s] : c in [1..n_vars]]
             : r in [1..#KBKer], s in [1..d]]);
        KerConstr := Kernel(Transpose(ConstrF2));
        FiFs := [F0^2,F0*F1,F0*F2,F1^2,F1*F2,F2^2];
        FiF_GF2vecs := [];
        for f in FiFs do for m in [1..d] do
            gg := kbasis[m]*f;
            Append(~FiF_GF2vecs,
                Vector(GF2, &cat[Eltseq(MonomialCoefficient(gg,mons6[j]))
                                 : j in [1..#mons6]]));
        end for; end for;
        FiFspace := sub<VectorSpace(GF2,n_vars) | FiF_GF2vecs>;
        B := S!0;
        for bv in Basis(KerConstr) do
            if bv in FiFspace then continue; end if;
            coeffs := [ &+[k!(GF2!bv[(j-1)*d+m])*kbasis[m] : m in [1..d]]
                        : j in [1..#mons6] ];
            w := &+[coeffs[j]*mons6[j] : j in [1..#mons6]];
            cand := w^2 + A_phi*w;
            flag, sol := IsConsistent(Im_phi, Vector(k,
                            [MonomialCoefficient(cand,mon) : mon in mons12]));
            if flag then
                Bc := &+[sol[i]*mons4[i] : i in [1..15]];
                if Evaluate(Bc,[F0,F1,F2]) eq cand then B := Bc; break; end if;
            end if;
        end for;
        return A, B;
    end function;

    A1,B1 := ComputeAB(g1);
    A2,B2 := ComputeAB(g2);

    PtsConic := function(A)
        pts := [];
        for x in k do for y in k do
            if Evaluate(A,[x,y,k!1]) eq 0 then Append(~pts,[x,y,k!1]); end if;
        end for; end for;
        for x in k do
            if Evaluate(A,[x,k!1,k!0]) eq 0 then Append(~pts,[x,k!1,k!0]); end if;
        end for;
        if Evaluate(A,[k!1,k!0,k!0]) eq 0 then Append(~pts,[k!1,k!0,k!0]); end if;
        return pts;
    end function;
    pts1 := PtsConic(A1); pts2 := PtsConic(A2);
    if #pts1 ne #pts2 then return false; end if;   // different conic type (e.g. smooth vs singular)
    if #pts1 ne (#k + 1) then return false; end if; // both must be smooth conics

    BuildM := function(src, tgt)
        As := Matrix(k,3,3,[src[1][1],src[2][1],src[3][1],
                            src[1][2],src[2][2],src[3][2],
                            src[1][3],src[2][3],src[3][3]]);
        if Determinant(As) eq 0 then return false, As; end if;
        v := As^-1 * Matrix(k,3,1,[src[4][1],src[4][2],src[4][3]]);
        if v[1][1] eq 0 or v[2][1] eq 0 or v[3][1] eq 0 then return false, As; end if;
        Ms := Matrix(k,3,3,[v[1][1]*src[1][1],v[2][1]*src[2][1],v[3][1]*src[3][1],
                            v[1][1]*src[1][2],v[2][1]*src[2][2],v[3][1]*src[3][2],
                            v[1][1]*src[1][3],v[2][1]*src[2][3],v[3][1]*src[3][3]]);
        At := Matrix(k,3,3,[tgt[1][1],tgt[2][1],tgt[3][1],
                            tgt[1][2],tgt[2][2],tgt[3][2],
                            tgt[1][3],tgt[2][3],tgt[3][3]]);
        if Determinant(At) eq 0 then return false, At; end if;
        w := At^-1 * Matrix(k,3,1,[tgt[4][1],tgt[4][2],tgt[4][3]]);
        if w[1][1] eq 0 or w[2][1] eq 0 or w[3][1] eq 0 then return false, At; end if;
        Mt := Matrix(k,3,3,[w[1][1]*tgt[1][1],w[2][1]*tgt[2][1],w[3][1]*tgt[3][1],
                            w[1][1]*tgt[1][2],w[2][1]*tgt[2][2],w[3][1]*tgt[3][2],
                            w[1][1]*tgt[1][3],w[2][1]*tgt[2][3],w[3][1]*tgt[3][3]]);
        return true, Mt*Ms^-1;
    end function;

    NormP := function(p)
        i := 1; while p[i] eq 0 do i +:= 1; end while;
        return [p[j]/p[i] : j in [1..3]];
    end function;
    pts1set := {NormP(p) : p in pts1};

    // Image of Artin-Schreier operator wp(Q) = Q^2 + A2*Q over quadratics, as GF2-subspace
    gens := [];
    for i in [1..6] do for m in [1..d] do
        Rform := kbasis[m]*mons2[i];
        Append(~gens, GF2vec(Rform^2 + A2*Rform));
    end for; end for;
    ImWp := sub<VectorSpace(GF2, 15*d) | gens>;

    coeffsA2 := [MonomialCoefficient(A2, mon) : mon in mons2];
    i0 := 1; while coeffsA2[i0] eq 0 do i0 +:= 1; end while;

    s := pts2; n := #pts2;
    s1:=s[1]; s2:=s[2]; s3:=s[3]; s4:=s[4]; s5:=s[5];
    for i1 in [1..n] do for i2 in [1..n] do
      if i2 eq i1 then continue; end if;
      for i3 in [1..n] do
        if i3 in {i1,i2} then continue; end if;
        for i4 in [1..n] do
          if i4 in {i1,i2,i3} then continue; end if;
          tgt := [pts1[i1],pts1[i2],pts1[i3],pts1[i4]];
          ok, M := BuildM([s1,s2,s3,s4], tgt);
          if not ok then continue; end if;
          im5 := M * Matrix(k,3,1,[s5[1],s5[2],s5[3]]);
          if NormP([im5[1][1],im5[2][1],im5[3][1]]) notin pts1set then continue; end if;
          lc := [&+[M[a][b]*S.b : b in [1..3]] : a in [1..3]];
          gA1 := Evaluate(A1, lc);
          c := MonomialCoefficient(gA1, mons2[i0]) / coeffsA2[i0];
          if c eq 0 or gA1 ne c*A2 then continue; end if;
          gB1 := Evaluate(B1, lc);
          T := gB1 / c^2 + B2;
          if GF2vec(T) in ImWp then return true; end if;
        end for;
      end for;
    end for; end for;
    return false;
end function;
/////////////////////////

// FINAL: APPLICATION

for i in [1..#classReps] do                 // display (A,B) of each iso-class rep
    A, B := ComputeABFull(classReps[i], k);
    printf "Class %o:\n  A = %o\n  B = %o\n", i, A, B;
end for;

for i in [1..#classReps] do                  // independent iso cross-check on the reps
    for j in [i+1..#classReps] do
        printf "rep %o vs rep %o isomorphic: %o\n", i, j,
               IsIsoDP2(classReps[i], classReps[j], k);
    end for;
end for;