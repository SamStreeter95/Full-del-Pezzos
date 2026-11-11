///////////////////////////////////////////////////////////////////////////////////////
// THIS FILE CONTAINS CODE FOR THE PAPER "CLASSIFICATION OF FULL DEL PEZZO SURFACES" //
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
// ALGORITHM 1: FINDING FULL DEL PEZZO SURFACES/PARTIAL CLASSIFICATION UP TO ISOMORPHISM //
///////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////
// SETTING UP AMBIENT STUFF //
//////////////////////////////
// Edit this list to select the fields to run over.
TestParams := [9,11,13,16,17,19,23];
// Results[q] = <field, full tuples, split count, PGL3 representatives,
//               component labels, isomorphism representatives, models>.
Results := AssociativeArray();
for Q in [1..#TestParams] do
    q:=TestParams[Q];
    k := GF(q);
    printf "\nProcessing q = %o\n", q;
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
    excl := AllPtsSet diff AllPtsSet;  // Empty, with the correct point universe.
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
    function ThreeUple(P)
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
        P[1]*P[2]*P[3]
        ];
    end function;
    /// FUNCTIONS FOR CURVES
    // GENERIC LINE FROM A 2-TUPLE OF POINTS
    function LineFromPoints(T)
        A:=T[1];
        B:=T[2];
        Coeffs:=[A[2]*B[3]- A[3]*B[2],A[3]*B[1]-A[1]*B[3],A[1]*B[2] - A[2]*B[1]];
        return Coeffs;
    end function;
    // GENERIC CONIC FROM A 5-TUPLE OF POINTS
    function ConicFromPoints(T)
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
    function ConicMatrixFromFour(T)
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
    function ConicFromMatrixAndPoint(M4, P)
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
    function CubicMatrixFromSix(T)
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
    function CubicFromMatrixAndPoint(M6, T, i)
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
                // Removing lines - over AllPts
                SixLineCoeffs := LineFromPoints([SixPoints[jj],[c,d,1]]);
                SixBad join:= {w : w in AllPts | SixLineCoeffs[1]*w[1] + SixLineCoeffs[2]*w[2] + SixLineCoeffs[3] eq 0};
                // Removing conics - over AllPts
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
    // The outer field loop continues through classification and model recovery.
    ////////////////////////
    // END OF ALGORITHM 1 //
    ////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    /////////////////////////////////////
    // ALGORITHM N: NORMALISE 7-TUPLES //
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
    //END OF ALGORITHM N //
    ///////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////
    // ALGORITHM 2: MERGE UNDER PGL3 AND CREMONA //
    ///////////////////////////////////////////////
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
                assert IsDefined(keyToClass, key);
                j := keyToClass[key];
                if j notin nbrs[i] then Append(~nbrs[i], j); end if;
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
    ////////////////////////////////////////////
    // ACTUAL ALGORITHM //
    ////////////////////////////////////////////
    reps, buckets := ReduceToPGL3Classes(FullTuples, k);              // FullTuples -> PGL3-class reps
    printf "PGL3 classes: %o\n", #reps;
    ncomp, comp, classReps := CremonaMerge(reps, k);                // PGL3 classes -> Cremona classes
    printf "Cremona classes: %o\n", ncomp;
    ////////////////////////
    // END OF ALGORITHM 2 //
    ////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////
    // ALGORITHM 3: COMPUTING ANTICANONICAL MODELS //
    /////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////////
    // STEP 1: FIND A BASIS FOR THE NET OF CUBICS THROUGH THE 7 POINTS //
    /////////////////////////////////////////////////////////////////////
    function AnticanonicalModel(SevenPoints, k)
        assert #SevenPoints eq 7;
        M := Transpose(Matrix(k,7,10,&cat[ThreeUple(P) : P in SevenPoints]));
        KB := Basis(Kernel(M));
        assert #KB eq 3;
        R<X,Y,Z> := PolynomialRing(k,3);
        mons3 := [X^3,Y^3,Z^3,X^2*Y,X^2*Z,X*Y^2,Y^2*Z,X*Z^2,Y*Z^2,X*Y*Z];
        F0 := &+[KB[1][i]*mons3[i] : i in [1..10]];
        F1 := &+[KB[2][i]*mons3[i] : i in [1..10]];
        F2 := &+[KB[3][i]*mons3[i] : i in [1..10]];
        ///////////////////////////////////////
        //STEP 2: COMPUTE THE JACOBIAN CURVE //
        ///////////////////////////////////////
        dF := [[Derivative(Fi,j) : Fi in [F0,F1,F2]] : j in [1..3]];   // dF[j] = the j-th partials
        if Characteristic(k) ne 3 then
            J := Determinant(Matrix(R,3,3, dF[1] cat dF[2] cat dF[3]));        // Ordinary Jacobian determinant
        else
            Mz := Determinant(Matrix(R,3,3, [F0,F1,F2] cat dF[1] cat dF[2]));  // value, d/dx, d/dy
            J  := ExactQuotient(Mz, R.3);                                       // divide by Z -> degree 6
        end if;
        ////////////////////////////////////////
        // STEP 3: COMPUTE THE BRANCH DIVISOR //
        ////////////////////////////////////////
        if Characteristic(k) ne 2 then
            // F0, F1, F2 and J belong to R = k[X,Y,Z].
            R := Parent(F0);
            k := BaseRing(R);
            S<x,y,z> := PolynomialRing(k, 3);
            // The 15 quartic monomials in the target coordinates.
            QuarticMons := [S | ];
            for i in [0..4] do
                for j in [0..4-i] do
                    Append(~QuarticMons, x^i*y^j*z^(4-i-j));
                end for;
            end for;
            // The 91 degree-12 monomials in the source coordinates.
            SourceMons := [R | ];
            for i in [0..12] do
                for j in [0..12-i] do
                    Append(~SourceMons, R.1^i*R.2^j*R.3^(12-i-j));
                end for;
            end for;
            // Substitute the three cubics into each quartic monomial.
            Pullbacks := [Evaluate(m, [F0,F1,F2]) : m in QuarticMons];
            // Express all pullbacks and J^2 in the same monomial basis.
            M := Matrix(k, [[MonomialCoefficient(g, m) : m in SourceMons]: g in Pullbacks]);
            v := Vector(k, [MonomialCoefficient(J^2, m) : m in SourceMons]);
            assert Rank(M) eq 15;
            coeffs := Solution(M, v);
            // Recover the branch quartic.
            f := &+[coeffs[i]*QuarticMons[i] : i in [1..15]];
            assert Evaluate(f, [F0,F1,F2]) eq J^2;
            return f;
        else
            // F0, F1, F2 and J belong to R = k[X,Y,Z].
            R := Parent(F0);
            k := BaseRing(R);
            assert Characteristic(k) eq 2;
            S<x,y,z> := PolynomialRing(k, 3);
            // The six quadratic monomials in the target coordinates.
            QuadMons := [x^2, y^2, z^2, x*y, x*z, y*z];
            // The 28 sextic monomials in the source coordinates.
            SourceMons := [R | ];
            for i in [0..6] do
                for j in [0..6-i] do
                    Append(~SourceMons, R.1^i*R.2^j*R.3^(6-i-j));
                end for;
            end for;
            // Substitute the three cubics into each quadratic monomial.
            Pullbacks := [Evaluate(m, [F0,F1,F2]) : m in QuadMons];
            // Express the pullbacks and J in the same monomial basis.
            M := Matrix(k, [[MonomialCoefficient(g, m) : m in SourceMons]: g in Pullbacks]);
            v := Vector(k, [MonomialCoefficient(J, m) : m in SourceMons]);
            assert Rank(M) eq 6;
            coeffs := Solution(M, v);
            // Recover the branch conic.
            A := &+[coeffs[i]*QuadMons[i] : i in [1..6]];
            assert Evaluate(A, [F0,F1,F2]) eq J;
            ////////////////////////////////
            // STEP 4: COMPUTE THE SEXTIC //
            ////////////////////////////////
            // The original seven points, as coordinate sequences.
            Pts := SevenPoints;
            // SourceMons is still the list of 28 sextic monomials.
            // Impose vanishing of the value and first derivatives.
            DoubleRows := [];
            for m in SourceMons do
                row := [k | ];
                for P in Pts do
                    row := row cat [Evaluate(m, P)] cat [
                    Evaluate(Derivative(m, r), P) : r in [1..3]
                    ];
                end for;
                Append(~DoubleRows, row);
            end for;
            V6 := Nullspace(Matrix(k, DoubleRows));
            assert Dimension(V6) eq 7;
            // M is still the 6 x 28 matrix of quadratic pullbacks.
            QuadSpace := RowSpace(M);
            // Choose a sextic outside their span.
            T := R!0;
            for vec in Basis(V6) do
                if vec notin QuadSpace then
                    T := &+[vec[i]*SourceMons[i] : i in [1..28]];
                    break;
                end if;
            end for;
            assert T ne 0;
            /////////////////////////////////
            // STEP 5: RECOVER THE QUARTIC //
            /////////////////////////////////
            QuarticMons := [S | ];
            for i in [0..4] do
                for j in [0..4-i] do
                    Append(~QuarticMons, x^i*y^j*z^(4-i-j));
                end for;
            end for;
            Degree12Mons := [R | ];
            for i in [0..12] do
                for j in [0..12-i] do
                    Append(~Degree12Mons, R.1^i*R.2^j*R.3^(12-i-j));
                end for;
            end for;
            // Unknowns: mu, followed by the 15 coefficients of B0.
            RelationForms := [J*T] cat [
            Evaluate(m, [F0,F1,F2]) : m in QuarticMons
            ];
            N := Matrix(k, [
            [MonomialCoefficient(g, m) : m in Degree12Mons]
            : g in RelationForms
            ]);
            rhs := Vector(k, [
            MonomialCoefficient(T^2, m) : m in Degree12Mons
            ]);
            assert Rank(N) eq 16;
            sol := Solution(N, rhs);
            mu := sol[1];
            assert mu ne 0;
            // Rescale to retain exactly the previously computed A.
            B := &+[
            (sol[i+1]/mu^2)*QuarticMons[i] : i in [1..15]
            ];
            Tnormal := (mu^-1)*T;
            assert Tnormal^2
            + Evaluate(A, [F0,F1,F2])*Tnormal
            + Evaluate(B, [F0,F1,F2]) eq 0;
            return A, B;
        end if;
    end function;
    // Compute one anticanonical model per isomorphism class.
    // Store f in odd characteristic, and <A, B> in characteristic 2.
    Models := [* *];  // Models may belong to separately constructed polynomial rings.
    for idx in [1..#classReps] do
        if Characteristic(k) eq 2 then
            A, B := AnticanonicalModel(SevenTuple(classReps[idx], k), k);
            Append(~Models, <A, B>);
            printf "q = %o, class %o: w^2 + A*w + B = 0\nA = %o\nB = %o\n", q, idx, A, B;
        else
            f := AnticanonicalModel(SevenTuple(classReps[idx], k), k);
            Append(~Models, f);
            printf "q = %o, class %o:\nw^2 = %o\n", q, idx, f;
        end if;
    end for;
    // Retain the output separately for every field in TestParams.
    Results[q] := <k, FullTuples, SplitCount, reps, comp, classReps, Models>;
end for; // End of the outer loop over TestParams.
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
