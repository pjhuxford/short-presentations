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


WeylGroupPresentation := function (n)
   R := PresentationForAn (n);
   G := SLPGroup (3);
   Q := Universe (R);
   phi := hom<Q -> G | [G.i : i in [1..3]]>;
   rels := [phi (r): r in R];

   a := G.1; b := G.2; s := G.3;
   R := [s^2];
   if IsOdd (n) then
      T := [a^(b^2), b * a^-1, (a^b) * a];
   elif IsEven (n) and n ge 6 then
      T := [(a^-1, b), a^(b^2) * a^(b), b * a^-1 * (a^-1)^b];
   elif n eq 4 then
      T := [(a^-1, b)];
   end if;

   R cat:= [(s, t): t in T];
   sigma := a^-1;
   R cat:= [s * s^(sigma) * s^(sigma^2)];
   return rels cat R;
end function;

WeylGroupMatrices := function (n, q)
   d := 2 * n;
   F := GF (q);
   MA := MatrixAlgebra (F, d);
   M := MatrixAlgebra (F, 2);
   x := M![0,1,1,0];
   s := Zero (MA);
   for i in [1..2] do
      InsertBlock (~s, x, (i - 1) * 2 + 1, (i - 1) * 2 + 1);
   end for;
   for i in [3..n] do
      InsertBlock (~s, x^0, (i - 1) * 2 + 1, (i - 1) * 2 + 1);
   end for;

   x := M![1,0,0,1];
   a := Zero (MatrixAlgebra (F, 6));
   InsertBlock (~a, x, 1, 3);
   InsertBlock (~a, x, 3, 5);
   InsertBlock (~a, x, 5, 1);
   a := DiagonalJoin (a, Identity (MatrixAlgebra (F, d - 6)));

   b := Zero (MA); x := M![1,0,0,1];
   if IsOdd (n) then
      for i in [1..n - 1] do
         InsertBlock (~b, x, (i - 1) * 2 + 1, (i) * 2 + 1);
      end for;
      InsertBlock (~b, x, d - 1, 1);
   else
      InsertBlock (~b, x, 1, 1);
      for i in [2..n - 1] do
         InsertBlock (~b, x, (i - 1) * 2 + 1, (i) * 2 + 1);
      end for;
      InsertBlock (~b, x, d - 1, 3);
   end if;

   return [GL(d, F) | a,b,s];
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

SL2InOmega4 := function (q, w)
   F := GF (q);
   // w := PrimitiveElement (F);
   G := GL(4, F);
   if Characteristic (F) eq 2 then
      s := G![1,0,1,0,0,1,0,0,0,0,1,0,0,1,0,1];
   else
      s := G![1,0,1,0,0,1,0,0,0,0,1,0,0,-1,0,1];
   end if;
   delta := G!DiagonalMatrix ([w, w^-1, w^-1, w^1])^-1;
   y := G![0,0,1,0, 0,0,0,1, -1, 0,0,0, 0,-1,0,0];
   return [s, y, delta];
   // correspond to u, t, h in Kassabov et al. SL2q presentation
end function;

SL3InOmega6 := function (q, z)
   F := GF (q);
   H := SL2InOmega4 (q, z);
   MA := MatrixAlgebra (GF(q), 6);
   id := Identity (MA);
   u := GL(6, q) ! InsertBlock (id, H[1], 1, 1);
   t := GL(6, q) ! InsertBlock (id, H[2], 1, 1);
   h := GL(6, q) ! InsertBlock (id, H[3], 1, 1);
   c := GL(6, q)! PermutationMatrix (GF (q), Sym (6)!(1,3,5)(2,4,6));
   return [u, t, h, c];
end function;

// revised Kantor presentation for Omega+(2n, q)
// following CRLG conversion to our generators

OmegaPresentation := function (n, q: MinGens := true)

"oct 24 Kantor revised presentation";

//    if n eq 4 or n eq 8 then return [], []; end if;
   d := 2 * n;
   p := Characteristic (GF(q));

if MinGens then
   G := SLPGroup (6);
else
   G := SLPGroup (6 + 7);
end if;

if q eq 2 then

words := [
 G.6 * G.2^-1, G.2^-1 * G.5^-1 * G.6^-1 * G.5 * G.2 * G.1^-1 * G.2^-1 * G.5^-1
* G.6 * G.5 * G.2, G.2^-1 * G.5^-1 * G.6^-1 * G.5 * G.2 * G.3^-1 * G.2^-1 *
G.5^-1 * G.6 * G.5 * G.2, G.2, G.1, G.3^-1, Id(G), G.5 * G.2 ];

else

words := [ G.6 * G.2^-1, G.2^-1 * G.5^-1 * G.6^-1 * G.5 * G.2 * G.1^-1 * G.2^-1 * G.5^-1
* G.6 * G.5 * G.2, G.2^-1 * G.5^-1 * G.6^-1 * G.5 * G.2 * G.3^-1 * G.2^-1 *
G.5^-1 * G.6 * G.5 * G.2, G.2, G.1, G.3^-1, Id(G), G.5 * G.2 ];

end if;

if IsOdd (n) then
words[2] := words[2]^words[1];
end if;

rels := [];

if MinGens then
   s := words[1]; t := words[2]; delta := words[3]; s1 := words[4];
   t1 := words[5]; delta1 := words[6]; v := words[8];
if IsOdd (n) then v := G.5; end if;
if IsOdd (n) then words[8] := G.5; end if;
else
 offset := 6;
 s := G.(offset + 1); t := G.(offset + 2); delta := G.(offset + 3);
 s1 := G.(offset + 4); t1 := G.(offset + 5); delta1 := G.(offset + 6);
 v := G.(offset + 7);
  Append (~rels, s = words[1]);
  Append (~rels, t = words[2]);
  Append (~rels, delta = words[3]);
  Append (~rels, s1 = words[4]);
  Append (~rels, t1 = words[5]);
  Append (~rels, delta1 = words[6]);
  Append (~rels, v = words[8]);
   rels := [LHS (r) * RHS (r)^-1: r in rels];
end if;

rels := [];

   u := s1;

   S := s * s1;
   S34 := S^(v^2);

   c := s1^v * s1;

 g := s * s1;
 g1 := (s1^2)^c * s1;

// if IsOdd (q) then
//    Z := s1^2 * (s1)^(c^2) * (s1)^(c^2 * v);
// else
//    Z := u^(c^2) * u^(c^2 * v);
// end if;

/*

if IsEven (n) and n ge 8 and IsEven (q) then
r := v * (c^2)^(v^2) * v^3;
tau := u * u^(v^2) * u^r * s^(v^5);
elif IsEven (n) and n ge 8 and IsOdd (q) then
r := v * (c^2)^(v^2) * v^3;
tau := s1 * s1^(v^2) * (s1^2)^(c^2) * s1^r * (s^1)^(v^5) * (s1^2)^(c^2 * v^4);
elif IsOdd (q) then
tau := s1 * s1^(v^2) * (s1^2)^(c^2);
elif IsEven (q) then
tau := u * u^(v^2);
end if;

if IsOdd (n) then
 // sigma := S * (v * c^-1)^((s * s1)^v);
 sigma := (v * c^-1)^((s * s1)^v) * S;
else
 // sigma := S * (v  * (u^(v^2) * u^v * u)^-1)^(S34);
 sigma := (v  * (u^(v^2) * u^v * u)^-1)^(S34) * S;
end if;

*/

   // SL3
   R := SL3Presentation (q);
   Q := Universe (R);
   phi := hom<Q -> G | [G.i: i in [1..4]]>;
   rels cat:= [phi (r): r in R];

   // W
   R := WeylGroupPresentation (n);
   Q := Universe (R);
   phi := hom<Q -> G | [G.i : i in [4..6]]>;
   rels cat:= [phi (r): r in R];

   R := rels;
rels := [];

u := G.1; t := G.2; // h := G.3;
if q eq 2 then h:=G.0; else h := G.3; end if;

// a := u * t;
//   a1 := (u^t)^-1;
//   a2 := (u^t)^+1;
// elif q eq 4 then
//    a :=  u * t * h;
//    a1 := h^2 * t * u * h * u;
//    a2 := a1;

if IsEven (q) then
   a := u * t * h;
   a1 := u * t * u * h * t;
   a2 := a1;
elif IsOdd (q) then
   a :=  u * t * h;
   a1 := u * t * u * h * t;
   a2 := u^(p-1)  * t * u^(p-1) * h * t;
end if;

if IsPrime (q) and IsEven (q) then
   a := u * t;
   a1 := (u^t)^-1;
   a2 := (u^t);
end if;

if q eq 2 then
   a := t^u;
   a1 := u;
   a2 := u;
elif q eq 3 then
a := h * u * t * u;
a1 := u^2;
a2 := u;
// a := u * t * u;
// a1 := h * u^2;
// a2 := h * u;
end if;

// a1 = a^g and a2 = a^(g') in Bill's notation
if q eq 2 then
   a := u;
   a1 := u * t * u;
   a2 := u * t * u;
elif q eq 4 then
   a := t * u * h;
   a1 := u * h * t;
   a2 := u * h * t;
elif q eq 3 then
   a := u;
   a1 := u^2 * t * u^2;
   a2 :=  h * u * t * u;
elif q eq 9 then
   a :=  t * u *h;
   a1 := u * h * t;
   a2 := h^4 * u^2 * h * t;
end if;

if n eq 4 then
   w1 := G.4 * G.5;  // Bill (1,3)(2,4)  --> (1,5)(3,7)(2,6)(4,8) EOB
   w2 := G.5 * G.4;  // Bill (1,2)(3,4)  -->  (1,3)(5,7)(2,4)(6,8) EOB
elif n eq 5 then
 w1 := (G.5 * G.4 * G.5^-1)^2 * G.4 * G.5^2 * G.4;
 w2 := G.5 * G.4 * G.5^-1 * G.4^2 * G.5^2 * G.4^2;
elif n eq 6 then
w1 :=
G.5^2 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 * G.4 *
G.5^-2 * G.4 * G.5^3;
w2 := G.5^2 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 *
G.4^-1 * G.5^-1 * G.4 * G.5 * G.4 * G.5^2 * G.4;
elif n eq 7 then
 w1 :=
G.5^2 * G.4^-1 * G.5^-1 * G.4 * G.5^2 * G.4 * G.5^-2 * G.4^2 * G.5^2 * G.4 *
G.5^-3 * G.4 * G.5^2 * G.4 * G.5^2 * G.4 ;
 w2 := G.5^2 * G.4^-1 * G.5^-1 * G.4 * G.5^2 * G.4 * G.5^-1 * G.4
  * G.5^-2 * G.4^2 * G.5 * G.4 * G.5^3 * G.4^2;
elif n eq 8 then
w1 :=
G.5^4 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 *
G.4^-1 * G.5^-1 * G.4^-1 * G.5^2 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^2 * G.4^-1 *
G.5^-1 * G.4^-1 * G.5^-1 * G.4 * G.5 * G.4 * G.5 * G.4 * G.5^-4 * G.4 * G.5^5
;
w2 :=
G.5^4 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^-1 * G.4 * G.5 * G.4 * G.5 * G.4^-1 *
G.5^-1 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^-1 * G.4 * G.5 * G.4 *
G.5^-1 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^2 *
G.4^-1 * G.5^-1 * G.4^-1 * G.5^2 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^-1 * G.4 * G.5
* G.4 * G.5^-1 * G.4 * G.5^-2 * G.4 * G.5^3 * G.4 * G.5^2 * G.4
;
end if;

tau := w2;
if n eq 8 then
tau := G.5^4 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^-2 * G.4 * G.5 * G.4 * G.5^-1 * G.4 *
G.5^-1 * G.6 * G.5 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^2 * G.4 * G.5
* G.4 * G.5^-1 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^-1 * G.4 * G.5 * G.4 * G.5^-1 *
G.4 * G.5^-1 * G.6 * G.5 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 * G.4 *
G.5 * G.4 * G.5 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^-1 * G.4 * G.5 * G.4 * G.5^-2 *
G.4 * G.5 * G.4 * G.5^-1 * G.4 * G.5^-1 * G.6 * G.5 * G.4^-1 * G.5 * G.4^-1 *
G.5^-1 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 *
G.4^-1 * G.5^2 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^2 * G.4^-1 * G.5^-1 * G.4^-1 *
G.5^-1 * G.4 * G.5 * G.4 * G.5^-1 * G.4 * G.5^-2 * G.4 * G.5^3 * G.4 * G.5^2 *
G.4;
end if;


  s12 := G.6; // (-1,-1,1,...,1);

if n eq 4 then
  sigma := s12;
elif n eq 5 then
  sigma := s12 * G.5 * G.4^2 * G.5^-1 * G.4^2 * G.6 * G.4 * G.5;
elif n eq 6 then
   sigma := s12 * G.5^2 * G.4 * G.5 * G.6 * G.4 * G.5^2;
elif n eq 7 then
   sigma := s12 * G.5 * G.4^2 * G.5^-1 * G.4^2 * G.6 * G.4 * G.5;
elif n eq 8 then
  sigma := s12 * G.5^3 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 * G.4^-1 * G.5^2 * G.4 * G.5 * G.6 * G.4 * G.5^2;
end if;

/*

// DEFN of w2 DO NOT HOLD For n = 6
if n in {4, 6} then
    w1 := G.4 * G.5;  // (1,3)(2,4)
if n eq 4 or n eq -6 then
   w2 := G.5 * G.4;  // (1,2)(3,4)
elif n eq 6 then
w2 := G.5^2 * G.4^-1 * G.5^-1 * G.4^-1 * G.5 * G.4^-1 * G.5^-1 *
G.4^-1 * G.5^-1 * G.4 * G.5 * G.4 * G.5^2 * G.4;
//   w3 := G.4^2 * G.6 * G.4 * G.5 * G.6 * G.4; // (1,-2)(3,-4)
//   w4 := G.4^(G.5^2); // (3,4,5)
end if;
else
 w1 := (G.5 * G.4 * G.5^-1)^2 * G.4 * G.5^2 * G.4; // (1,3)(2,4)
if n eq 5 then
 w2 := G.5 * G.4 * G.5^-1 * G.4^2 * G.5^2 * G.4^2; // (1,2)(3,4)
else
 w2 := G.5^2 * G.4^-1 * G.5^-1 * G.4 * G.5^2 * G.4 * G.5^-1 * G.4
  * G.5^-2 * G.4^2 * G.5 * G.4 * G.5^3 * G.4^2;
end if;
// w3 := G.6 * G.5 * G.4 * G.5^-1 * G.4^2 * G.6 * G.5^2 * G.4 * G.6 * G.4; // (3,-4)
//   w4 := G.4^(G.5^2); // (3,4,5)
end if;
*/


   s23 := G.4^2 * G.6 * G.4; // (1,-1,-1,1, ..., 1)

"#RL ", #R, #rels;
   // rels 4
   Append (~rels, a^sigma = a1);
   if n gt 4 then Append (~rels, (a1)^sigma = a); end if;

   // rels 5
  Append (~rels, a^tau = a2);

   // 6
   Append (~rels, (a, a^s23) = 1);
   Append (~rels, (a1, a^s23) = 1);

  // 7
  Append (~rels, (a, a^w1) = 1);

  // 8
  if n in {4,5} then
    Append (~rels, (a2, a^w1) = 1);
  end if;

  // 9
  if n in {4,6} then
    Append (~rels, (S34, a) = 1);
  end if;

  // 10
  if n eq 4 then
  // X[6] * X[4] * X[6] * X[5] * X[6] * X[4] * X[5];
  s24 := G.6 * G.4 * G.6 * G.5 * G.6 * G.4 * G.5;
  mu := s24 * w1;
  Append (~rels, (a, a^mu) = 1);
"#R is ", #rels;
  Append (~rels, (a, a2^mu) = 1);
  Append (~rels, (a2, a2^mu) = 1);
else s24 := G.0;
  end if;


/*
  if q in {2,3,4} then
     Append (~rels, w2 = tau);
  end if;
*/

// MY ADD RELS
// needed even for n = 4
/*
if IsEven (q) then
   Append (~rels, a^w2 = a1);
end if;
*/

//  s12 := G.6; // (-1,-1,1,...,1);
// needed for n >= 5?
  Append (~rels, a^sigma = a^s12);

// Yet another add
//  Append (~rels, a^tau = a^w2);

   // Kwords := [a, a1, w1, w2, w3, w4, s23, S34, a2, S];
   Kwords := [a, a1, a2, w1, w2, s12, s23, s24, S34, S, sigma, tau];
"#R #rels", #R, #rels;
   R cat:= [LHS (r) * RHS (r)^-1: r in rels];
   return R, words, Kwords;
   return R;
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
