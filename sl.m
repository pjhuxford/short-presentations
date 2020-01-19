forward SL2Matrices;

PresentationForAn := function (n)
   F := SLPGroup (2);
   a := F.1; b := F.2;
   if IsOdd (n) then
      // n odd:  a=(1,2,3), b=(1,2,...,n),
      R := [a^3, b^n, (a*b^2)^((n-1) div 2)];
      for j in [2..n - 2] do Append (~R, ((b*a)^j*b^-j)^2); end for;
   else
      // n even:  a=(1,2,3), b=(2,...,n),
      R := [ a^3, b^(n-1), (b^2*a^-1)^(n div 2), (b*a^-1)^(n-1)];
      for j in [1..n div 2 - 1] do
         Append (~R, ((b^-1*a*b^-1)^j*(b^2*a^-1)^j)^2);
         if j le n div 2 - 2 then
            Append (~R, ((b^-1*a*b^-1)^j*(a^-1*b^2)^j*a^-1)^2);
         end if;
      end for;
   end if;
   return R;
end function;

GeneratorsForAn := function (n)
   G := Alt(n);
   if IsOdd (n) then
      return [G ! (1,2,3), G ! ([2..n] cat [1])];
   else
      return [G ! (1,2,3), G ! ([1] cat [3..n] cat [2])];
   end if;
end function;

DoubleBracket := function (u, h, c)
   Z := Integers ();
   c := [Z!x : x in c];
   if #c gt 1 then
      product := &*[u^c[i] * h^-1: i in [1..#c - 1]];
      product *:= u^c[#c] * h^(#c - 1);
   else
      product := u^c[#c] * h^(#c - 1);
   end if;
   return product;
end function;

SL2Presentation := function (q : z := PrimitiveElement(GF(q)))
   f, p := IsPrimePower (q);
   assert f;

   G := SLPGroup (3);
   F := GF (q);

   if q lt 11 then
      w := PrimitiveElement (F);
      if q eq 2 then
         F := Group<a,b,c | a^2, b^2, c, (b * a)^3>;
      else
         M := SL2Matrices (q : z := w);
         H := sub<GL(2, q) | M>;
         F := FPGroup (H);
      end if;
      phi := hom<F -> G | [G.i: i in [1..Ngens (G)]]>;
      rels := Relations (F);
      rels := [LHS (x) * RHS(x)^-1: x in rels];
      rels := [phi (r): r in rels];
      return rels, w;
   end if;

   u := G.1; t := G.2; h := G.3;

   flag := exists(x){<k, l>: k in [1..q - 1], l in [1..q - 1] |
   sub< F | z^(2 * k)> eq F and
   IsSquare (z^(2*k) - 1) and z^(2*k) - 1 eq z^(2 * l)};

   k := x[1]; l := x[2];
   assert z^(2 * k) eq z^(2 *l) + 1;

   d := Gcd (k, l);

   assert F eq sub<F | z^(2 * d)>;

   K := sub<F | z^(2 * d)>;

   m<x> := MinimalPolynomial (z^(2 * d), GF(p));

   rels := [u^p = 1, u^(h^k) = u * u^(h^l), u^(h^k) = u^(h^l) * u,
           (t^2, u) = 1,
             h^t = h^-1, t = u * u^t * u];

   // 3
   c := Coefficients (m);
   Append (~rels, DoubleBracket (u, h^d, c) = 1);

   // 4
   c := Eltseq (K!(z^2));
   Append (~rels, DoubleBracket (u, h^d, c) = u^h);

   // 8
   c := Eltseq (K!(z^-1));
   p1 := DoubleBracket (u, h^d, c);
   c := Eltseq (K!(z^1));
   p2 := DoubleBracket (u, h^d, c)^t;
   Append (~rels, h * t = p1 * p2 * p1);

   rels := [LHS (x) * RHS(x)^-1: x in rels];

   return rels;
end function;

SL3Presentation := function (q : z := PrimitiveElement(GF(q)), Add := false)
   f, p := IsPrimePower (q);
   assert f;

   G := SLPGroup (4);
   u := G.1; t := G.2; h := G.3; c := G.4;

   R := SL2Presentation (q : z := z);
   H := Universe (R);
   tau := hom<H -> G | u, t, h>;
   R := [tau (r): r in R];

   F := GF (q);

   rels := [c^(t) = t^2 * c^2,
            h * h^c * h^(c^2) = 1,
            (u, u^c) = (u^-1)^(t * c^2)];

   if q in {2,3,4,7,13,16,19} then
      Append (~rels, (u, (u^-1)^(t * c^2)) = 1);
      Append (~rels, (u^c, (u^-1)^(t * c^2)) = 1);
   else
      Append (~rels, (u * u^c, (u^-1)^(t * c^2)) = 1);
   end if;
   if q eq 4 then
      Append (~rels, (u, u^(c * h^-1)) = u^(c * t * h^1));
      Append (~rels, (u, u^(c * t * h^-1)) = 1);
      Append (~rels, (u^(c*t), u^(c * t * h^-1)) = 1);
   end if;

   // 4
   // K := sub< F | z^2>;
   // coeffs := Eltseq (K!z^-1);
   // rhs := DoubleBracket (u, h, coeffs);
   // Append (~rels, u^(h^c) * rhs^-1);

   // 4 -- equivalent and comprehensible
   K := sub< F | z^2>;
   I := Integers ();
   k := Eltseq (K!z^-1);
   k := [I ! c: c in k];
   Append (~rels, u^(h^c) = &*[(u^(h^(i - 1)))^k[i]: i in [1..#k]]);

   // these seem to be needed to make it finite
   if Add then "add"; rels cat:= [u^(h^c) = u^(h^(c^2))];
   //      (u^(t*h))^(h^c) = (u^(t*h))^(h^(c^2))];
   end if;

   rels := [LHS (x) * RHS (x)^-1: x in rels];

   R cat:= rels;
   return R;
end function;

SL2Matrices := function (q : z := PrimitiveElement(GF(q)))
   u := GL(2, q) ! [1,1,0,1];
   t := GL(2, q)! [0,1,-1,0];
//   if q eq 2 then h := u * t; else
   h := GL(2, q)! [z^-1, 0, 0, z];
//   end if;
   return [u, t, h];
end function;

SL3Matrices := function (q : z := PrimitiveElement(GF(q)))
   MA := MatrixAlgebra (GF(q), 3);
   id := Identity (MA);
   X := SL2Matrices (q : z := z);
   u := GL(3, q) ! InsertBlock (id, X[1], 1, 1);
   t := GL(3, q) ! InsertBlock (id, X[2], 1, 1);
   h := GL(3, q) ! InsertBlock (id, X[3], 1, 1);
   c := GL(3, q)! [0,1,0,0,0,1,1,0,0];
   return [u, t, h, c];
end function;

SLPresentation := function (n, q : z := PrimitiveElement(GF(q)), Add := false, FineTune := true, Projective := false)
   assert n ge 4;
   R := SL3Presentation (q : Add := Add);
   F := Universe (R);
   S := PresentationForAn (n);
   T := Universe (S);

   if FineTune then
      G := SLPGroup (3 + Ngens(T));
      X := [G.i : i in [1..3]];
   else
      G := SLPGroup (4 + Ngens(T));
      X := [G.i : i in [1..4]];
   end if;
   Y := [G.i : i in [#X+1..#X+Ngens(T)]];

   u := X[1];
   t := X[2];
   h := X[3];
   y1 := Y[1];
   y2 := Y[2];
   if FineTune then
      // See (3) below for the reason we use c = (1,2,3) instead of c = (3,2,1).
      c := y1;
      X[4] := c;
   else
      c := X[4];
   end if;

   // construct (2,3,4)
   if IsOdd(n) then
      // a = (1,2,3), b = (1,2,...,n)
      c234 := y1 ^ y2;
   else
      //a = (1,2,3), b = (2,...,n)
      c234 := (y1^-1)^(y2 * y1^-1);
   end if;

   // construct (1,3)(2,4) and tau = (1,2)(3,4)
   c13c24 := y1 * c234;
   tau := c234 * y1;

   // construct matrices a,f
   f := c^-1 * t * c^-1;
   if (q eq 5) or (q eq 17) then
      a := u;
   else
      // The following definition relies on the following conjecture:
      // G := SL(2, q) = <uh, (uh)^f> where q is a prime power not equal to 5 or 17.
      // This has been verified for q <= 10^6.
      a := u * h;
   end if;

   // construct sigma in An
   // sigma swaps 1 and 2
   // <tau, sigma> = stabilizer of the set {1,2}
   if IsOdd(n) then
      // sigma = (1,2)(4,...,n)
      sigma := y2 * y1 * y2^-1 * y1^-1 * y2;
   else
      // sigma = (1,2)(3,...,n)
      sigma := y2 * y1;
   end if;

   rels := [];

   // (3)
   // In Guralnick et. al. the relation reads c = (3,2,1).
   // We use c = (1,2,3) instead, so that both permutation and matrix actions are viewed as right actions.
   // In other words, we disagree on the order which permutations should be multiplied.
   if not FineTune then
      Append(~rels, c * y1^-1);
   end if;

   // (4)
   if n ne 4 or (not FineTune) then
      Append(~rels, a^sigma * (a^f)^-1);
   end if;

   // (5)
   Append(~rels, a^tau * (a^f)^-1);

   // (6)
   if n ge 6 or (not FineTune) then
      Append(~rels, (a^f)^sigma * a^-1);
   end if;

   // (7)
   Append(~rels, (a, a^c13c24));

   // (8)
   if (n eq 4) or (n eq 5) then
      Append(~rels, (a^f, a^c13c24));
   end if;

   if Projective then
      if IsOdd(n) then
         h1n := (h^-1)^(y2^-1);
         h2n := (h^-1)^(y2^-1 * y1);
      else
         h1n := h^(y2^-1);
         h2n := h^(y2^-1 * y1);
         h3n := h2n ^ y1;
      end if;

      m := (q-1) div Gcd(n, q-1);

      if IsOdd(n) then
         cycle := y2^2 * y1^-1 * y2^-1;
         Append(~rels, h1n^m * (h2n^m * cycle)^(n-2));
      elif n eq 4 then
         Append(~rels, h1n^m * h2n^m * h3n^m);
      else
         cycle := y2^2 * y1^-1 * y2^-1 * y1^-1;
         Append(~rels, h1n^m * h2n^m * (h3n^m * cycle)^(n-3));
      end if;

   end if;

   // In Theorem 6.1
   // SL(3,q) = F = <X | R>
   // An = T = <Y | S>
   phi := hom<F -> G | X>;
   theta := hom<T -> G | Y>;

   return phi(R) cat theta(S) cat rels;
end function;

SLMatrices := function (n, q : z := PrimitiveElement(GF(q)), FineTune := true)
   MA := MatrixAlgebra (GF(q), n);
   id := Identity (MA);
   X := [GL(n, q) ! InsertBlock (id, x, 1, 1) : x in SL3Matrices (q : z := z)];
   if FineTune then
      Prune(~X);
   end if;
   Y := [GL(n, q) ! PermutationMatrix (GF(q), g) : g in GeneratorsForAn (n)];
   return X cat Y;
end function;

SLEval := function (n, q : z := PrimitiveElement(GF(q)), Add := false, FineTune := true, Projective := false)
   return Evaluate (SLPresentation (n, q : z := z, Add := Add, FineTune := FineTune, Projective := Projective),
                    SLMatrices (n, q : z := z, FineTune := FineTune));
end function;

SLEvalRange := function (N, Q : Add := false, FineTune := true, Projective := false)
   for n in [4..N], q in [2..Q] do
      if IsPrimePower (q) then
         R := SLEval (n, q : Add := Add, FineTune := FineTune, Projective := Projective);
         if Projective then
            scalar := R[#R];
            topleft := scalar[1, 1];
            Prune(~R);
         end if;

         if Set (R) ne { Id(SL(n,q)) } then
            return n, q;
         elif Projective then
            if scalar ne ScalarMatrix (n, topleft) or Order (topleft) ne Gcd (n, q-1) then
               return n, q;
            end if;
         end if;
      end if;
   end for;
   return true;
end function;
