// This contains various presentations of alternating and symmetric groups
// Functions ending in '_Presentation' return Relations and an SLPGroup
// Functions ending in '_Words' are helper functions for '_Presentation'
// Functions ending in '_Gens' return Generators and a PermutationGroup
// Functions ending in '_Eval' check if the generators satisfy the relations
// Functions ending in '_Test' run a coset enumeration on a one-point stabilizer
// The Theorem/Corollary/Lemma numbers in Function names refer to those in GKKL

SetGlobalTCParameters (: CosetLimit:=10^7, Hard, Print := 10^6);

SLPToFP := function (S, R)
   F := FreeGroup (Ngens (S));
   tau := hom <S -> F | [F.i: i in [1 .. Ngens (F)]]>;
   Q := quo <F | tau (R)>;
   return Q;
end function;

// Examples 3.18(1) of GKKL
// Example 2.2 of my dissertation
// Presentation of Alt(p+3) based on SLP(2,p) for primes p > 3
// 3 generators, 7 relations, bit-length O(log p)
// Optional parameter j
// j must satisfy Fp* = <j>
// if p = 1 mod 3, then j must be even
// In my dissertation, we describe this as Alt(Omega)
// where Omega = Fp U {infinity, star, bullet}.
// Here we use the bijection Omega -> {1,...,p+3} given by
// a |-> a for a in Fp
// infinity |-> p+1, star |-> p+2, bullet |-> p+3

Examples_3_18_1_Primitive_Element := function (p)
    j := IntegerRing() ! PrimitiveElement (GF(p));
    if (p mod 3 eq 1) and (j mod 2 eq 1) then
	j := j - p;
    end if;
    return j;
end function;

Examples_3_18_1_h_Word := function (p, x, y :
				    j := Examples_3_18_1_Primitive_Element (p))
    j_ := InverseMod (j, p);
    k := p mod 3;
    h := y^j_ * (y^j)^x * y^j_ * x^((-1)^k);
    return h;
end function;

Examples_3_18_1_Gens := function (p)
    G := Sym (p+3);

    X := [];
    for a in [1..p-1] do
	X[a] := InverseMod (-a, p);
    end for;
    X cat:= [p+1,p,p+2,p+3];
    x := G ! X;

    y := G ! ([2..p] cat [1] cat [p+1,p+2,p+3]);
    z := G ! (p+1,p+2,p+3);

    return [x,y,z], G;
end function;

Examples_3_18_1_Presentation := function (p :
					  j := Examples_3_18_1_Primitive_Element (p))
    S<x,y,z> := SLPGroup (3);

    h := Examples_3_18_1_h_Word (p, x, y : j := j);

    e := (p+1) div 2;
    f := 2 * (p div 3);

    R := [
	x^2 * (x*y)^(-3),
	(x * y^4 * x * y^e)^2 * y^p * x^f,
	z^3,
	(z * z^x)^2,
	(y, z),
	(h, z),
	(h * z^(x*y) * z^(x*y^j))^e
    ];
    return R, S;
end function;

Examples_3_18_1_Eval := function (p :
				  j := Examples_3_18_1_Primitive_Element (p))
    return Evaluate (Examples_3_18_1_Presentation (p : j := j),
		     Examples_3_18_1_Gens (p));
end function;

Examples_3_18_1_Test := function (p :
				  j := Examples_3_18_1_Primitive_Element (p))
    R, S := Examples_3_18_1_Presentation (p : j := j);
    Q<x,y,z> := SLPToFP (S, R);
    j_ := InverseMod (j, p);

    k := p mod 3;

    h := Examples_3_18_1_h_Word (p, x, y : j := j);

    // H should be the stabilizer of the point infinity
    H := sub <Q | y, h, z^x>;
    I := CosetImage(Q, H);
    return I;
end function;


// Corollary 3.8 (ii) of GKKL
// Theorem 2.22 of my dissertation
// Presentation of Alt(p+2) based on AGL(1,p)^(2) for primes p = 11 mod 12
// 2 generators, 4 relations, bit-length O(log p)
// Optional parameters r, s, alpha
// r must satisfy Fp*^2 = <r>,
// s must satisfy s(r-1) = -1 mod p
// alpha must satisfy alpha^3 = r mod p

Corollary_3_8_ii_Words := function (p, a, g)
    b := g^3;
    z := g^((p-1) div 2);
    h := (b * z^a * z^(a^-1))^((p+1) div 2);

    return b, z, h;
end function;

Corollary_3_8_ii_Presentation := function (p :
					   r := IntegerRing() !
						(PrimitiveElement (GF (p))^2),
					   s := InverseMod (1-r, p))
    assert p mod 12 eq 11;
    S<a,g> := SLPGroup (2);

    b, z, h := Corollary_3_8_ii_Words (p, a, g);

    R := [
	a^p * b^((1-p) div 2),
	(a^s)^b * a^(1-s),
	(z * z^a)^2,
	h
    ];

    return R, S;
end function;

Corollary_3_8_ii_Gens := function (p :
				   r := IntegerRing() !
					(PrimitiveElement (GF (p))^2),
				   alpha := r ^ InverseMod (3, p-1))
    assert p mod 12 eq 11;
    S := Alt(p+2);

    A := []; G := [];

    for i in [1 .. p-1] do
	A[i] := i+1;
    end for;
    A[p] := 1;
    A[p+1] := p+1;
    A[p+2] := p+2;

    for i in [1 .. p-1] do
	G[i] := alpha * i mod p;
    end for;
    G[p] := p+2;
    G[p+1] := p;
    G[p+2] := p+1;

    a := S ! A; g := S ! G;

    return [a,g], S;
end function;

Corollary_3_8_ii_Eval := function (p : r := IntegerRing() !
					    (PrimitiveElement (GF (p))^2),
				       s := InverseMod (1-r, p),
				       alpha := r ^ InverseMod (3, p-1))
    return Evaluate (Corollary_3_8_ii_Presentation (p : r := r, s := s),
		     Corollary_3_8_ii_Gens (p : r := r, alpha := alpha));
end function;

Corollary_3_8_ii_Test := function (p : r := IntegerRing() !
					    (PrimitiveElement (GF (p))^2),
				       s := InverseMod (1-r, p))
    R, S := Corollary_3_8_ii_Presentation (p : r := r, s := s);
    Q<a,g> := SLPToFP (S, R);
    b, z := Corollary_3_8_ii_Words (p, a, g);

    // H is the stabilizer of p
    H := sub<Q | b, z^a>;
    I := CosetImage (Q, H);
    return I;
end function;

// Corollary 3.13 (iii) of GKKL
// Theorem 2.30 of my dissertation
// Presentation of Sym(p+2) based on AGL(1,p)^(2) for odd primes p = 2 mod 3
// 2 generators, 4 relations, bit-length O(log p)
// Optional parameters r, s, alpha
// r must satisfy Fp* = <r>,
// s must satisfy s(r-1) = -1 mod p
// alpha must satisfy alpha^3 = r mod p

Corollary_3_13_iii_Words := function (p, a, g : r := IntegerRing() !
						     PrimitiveElement (GF (p)))
    b := g^3;
    z := g^(p-1);
    h := (b^2 * z^a * z^(a^r))^((p+1) div 2);

    return b, z, h;
end function;

Corollary_3_13_iii_Presentation := function (p :
					     r := IntegerRing() !
						  PrimitiveElement (GF (p)),
					     s := InverseMod (1-r, p))
    assert (p mod 3 eq 2) and (p gt 2);
    S<a,g> := SLPGroup (2);

    b, z, h := Corollary_3_13_iii_Words (p, a, g : r := r);

    R := [
	a^p * b^(1-p),
	(a^s)^b * a^(1-s),
	(z * z^a)^2,
	h
    ];

    return R, S;
end function;

Corollary_3_13_iii_Gens := function (p :
				     r := IntegerRing() !
					  PrimitiveElement (GF (p)),
				     alpha := r ^ InverseMod (3, p-1))
    assert (p mod 3 eq 2) and (p gt 2);
    S := Sym(p+2);

    A := []; G := [];

    for i in [1 .. p-1] do
	A[i] := i+1;
    end for;
    A[p] := 1;
    A[p+1] := p+1;
    A[p+2] := p+2;

    for i in [1 .. p-1] do
	G[i] := alpha * i mod p;
    end for;
    G[p] := p+1;
    G[p+1] := p+2;
    G[p+2] := p;

    a := S ! A; g := S ! G;

    return [a,g], S;
end function;

Corollary_3_13_iii_Eval := function (p :
				     r := IntegerRing() !
					  PrimitiveElement (GF (p)),
				     s := InverseMod (1-r, p),
				     alpha := r ^ InverseMod (3, p-1))
    return Evaluate (Corollary_3_13_iii_Presentation (p : r := r, s := s),
		     Corollary_3_13_iii_Gens (p : r := r, alpha := alpha));
end function;

Corollary_3_13_iii_Test := function (p :
				     r := IntegerRing() !
					  PrimitiveElement (GF (p)),
				     s := InverseMod (1-r, p))
    R, S := Corollary_3_13_iii_Presentation (p : r := r, s := s);
    Q<a,g> := SLPToFP (S, R);
    b, z := Corollary_3_13_iii_Words (p, a, g : r := r);

    // H is the stabilizer of p
    H := sub<Q | b, z^a>;
    I := CosetImage (Q, H);
    return I;
end function;

// Remark 3.11 of GKKL
// Lemma 2.39 in my dissertation
// The following functions all have inputs which must be
// - a positive integer p
// - elements a, z of the same group.
// There will possibly be other inputs i,j.
// We describe the outputs when a = (1,2,...,p) and z = (p,p+1,p+2),
// in some permtuation group acting on a set which contains {1..p+2}.
// However, both a, z may be elements of any group (e.g. an SLPGroup).

// Returns a word in a, z which has bit-length O(log p).
// If a = (1,2,...,p), z = (p,p+1,p+2), and 1 <= i <= p, then
// this returns (i,p+1,p+2). If i is replaced by an equivalent residue mod p
// then the resulting permutation is unchanged.
Remark_3_11_Three_Cycle := function (p, a, z, i)
    return z^(a^i);
end function;

// Returns a word in a, z which has bit-length O(log p).
// If a = (1,2,...,p), z = (p,p+1,p+2), 1 <= i,j <= p and i != j, then
// this returns (i,j)(p+1,p+2). If i,j are replaced by equivalent residues mod p
// then the resulting permutation is unchanged.
Remark_3_11_Double_Transposition := function (p, a, z, i, j)
    z_ := function (k)
	return Remark_3_11_Three_Cycle (p, a, z, k);
    end function;

    return z_(i) * z_(j)^-1 * z_(i);
end function;

// Returns a word in a, z which has bit-length O(log p).
// If a = (1,2,...,p), z = (p,p+1,p+2), and 1 <= i <= j <= p-2, then
// this returns (i,i+1,...j)(p+1,p+2)^(j-i).
Remark_3_11_Cycle := function (p, a, z, i, j)
    assert (1 le i) and (i le j) and (j le p+2);
    ThisFunction := $$;

    c_ := function (k, l)
	return ThisFunction (p, a, z, k, l);
    end function;

    d_ := function (k, l)
	return Remark_3_11_Double_Transposition (p, a, z, k, l);
    end function;

    if j le p-1 then
	x := d_(0, 1);
	return a^-j * (a*x)^(j-i) * a^i;
    elif i eq j then
	return Id(Parent(a));
    elif j eq p then
	if i eq p-1 then
	    return d_(i, j);
	else // i <= p-2 and j = p
	    return z^((z*a)^-2) * c_(i, p-2);
	end if;
    elif j eq p+1 then
	if i eq p then
	    return z^-1;
	else // i <= p-1 and j = p+1
	    return z^((z*a)^-1) * c_(i, p-1);
	end if;
    else // j = p+2
	if i eq p+1 then
	    return Id(Parent(a));
	else
	    return z * c_(i, p);
	end if;
    end if;
end function;

// Remark 3.16 of GKKL
// Lemma 2.39 in my dissertation
// The following functions all have inputs which must be
// - a positive integer p
// - elements a, b, z of the same group.
// There will possibly other inputs i, j.
// We describe the outputs when a = (1,2,...p), z = (p,p+1,p+2), and
// b maps x |-> rx for x in Fp* = {1..p-1}, and fixes {p+1,p+2},
// in some permtuation group acting on a set which contains {1..p+2}.
// However, a, b, z may be elements of any group (e.g. an SLPGroup).

// Returns a word in a, b, z which has bit-length O(log p)
// If a, b, z are the above permutations and p = 3 mod 4,
// then this returns (p+1,p+2).
Remark_3_16_Transposition := function (p, a, b, z)
    d_ := function (i, j)
	return Remark_3_11_Double_Transposition (p, a, z, i, j);
    end function;

    c_ := function (i, j)
	return Remark_3_11_Cycle (p, a, z, i, j);
    end function;

    cbullet := c_(1, (p-1) div 2) * c_((p+1) div 2, p-1)^-1;
    v := (d_(1, -1) * cbullet)^((p-1) div 2);
    t := v * b^((p-1) div 2);

    return t;
end function;

// Returns a word in a, b, z which has bit-length O(log p)
// If a, b, z are the above permutations, p = 3 mod 4, and
// 1 <= i <= j <= p+2, then this returns (i,i+1,...j).
Remark_3_16_Cycle := function (p, a, b, z, i, j)
    assert (1 le i) and (i le j) and (j le p+2);

    cycle := Remark_3_11_Cycle (p, a, z, i, j);
    if (j - i) mod 2 eq 0 then
	return cycle;
    else
	t := Remark_3_16_Transposition (p, a, b, z);
	return cycle * t;
    end if;
end function;

// Returns the smallest prime p = 11 mod 12 which is at least (n+2)/2
Section_3_5_Gluing_Prime := function (n)
    p := NextPrime ((n+1) div 2);
    while p mod 12 ne 11 do
	p := NextPrime (p);
    end while;
    return p;
end function;

// Lemma 3.32 of GKKL
// Theorem 2.44 of my dissertation
// Part of the proof of this lemma describes how to express
// y as a word w of bit-length O(log p) in X U X^y

// Helper function for Section_3_5_Sym_Words
Lemma_3_32_Sym_y_Expression := function (p, k, a, y, z, d_, t)
    assert k le p+1;

    if k eq p+1 then
	w := t^(y*z);
    elif k eq p then
	w := z^(y*z^-1) * z^(y*z);
    elif k eq p-1 then
	w := z^(a*y*a^-1*z^-1) * z^(a*y*a^-1*z) * (d_(1, p) * t)^(y*a^-1);
    else
	xtilde := (d_(1, k+2) * d_(2, k+1)) ^ (d_(1, k+2)^y * d_(2, k+1)^y);
	u := (z*a) * (z*a)^y;
	if k mod 2 eq 1 then
	    w := (xtilde * u^-2)^((p-k) div 2) * xtilde * u^(p-k);
	else
	    w := t^(z*a*y*(z*a)^-1) * (xtilde * u^-2) ^ ((p-k-1) div 2)
		 * xtilde * u^(p-k-1);
	end if;
    end if;

    return w;
end function;

// Helper function for Section_3_5_Alt_Words
Lemma_3_32_Alt_y_Expression := function (p, k, a, y, z, z_, d_)
    assert k le p;

    if k eq p then
	w := z^(y*z^-1) * z^(y*z);
    else
	xtilde := (d_(1, k+2) * d_(2, k+1)) ^ (d_(1, k+2)^y * d_(2, k+1)^y);
	u := (z*a) * (z*a)^y;
	if k mod 2 eq 1 then
	    w := (xtilde * u^-2)^((p-k) div 2) * xtilde * u^(p-k);
	else
	    w := d_(1, -1) ^ (z*a*y*a^-1*z^-2*a^-1) * (z_(1)^-1) ^ (y*a^-1*z^-1)
		 * (xtilde * u^-2) ^ ((p-k-3) div 2) * xtilde * u^(p-k-3);
	end if;
    end if;

    return w;
end function;

// Section 3.5 of GKKL
// Theorem 2.55 of my dissertation
// Defines an explicit presentation of Sym(n)
// where either 14 <= n <= 20, 26 <= n <= 44, or n >= 50.
// Optional parameters p, r, s
// p must be a prime with p = 11 mod 12, and (n+2)/2 <= p <= n-3
// r must satisfy Fp* = <r>,
// s must satisfy s(r-1) = -1 mod p
// Modify parameters at your own risk

Section_3_5_Sym_Words := function (p, k, a, g, y :
				   r := IntegerRing() !
					PrimitiveElement (GF (p)))

    // (2)
    b, z, h := Corollary_3_13_iii_Words (p, a, g : r := r);

    // (3)
    z_ := function (i)
	return Remark_3_11_Three_Cycle (p, a, z, i);
    end function;
    d_ := function (i, j)
	return Remark_3_11_Double_Transposition (p, a, z, i, j);
    end function;

    // (4)
    c_ := function (i, j)
	return Remark_3_11_Cycle (p, a, z, i, j);
    end function;

    // (5)
    t := Remark_3_16_Transposition (p, a, b, z);

    // (6)
    atilde := z_(3)^(z_(2) * z_(1));
    if k mod 2 eq 1 then
	c := c_(2, k) * t;
	e := z * a * t * c_(3, k+1)^-1;
    else
	c := c_(1, k) * t;
	e := z * a * t * c_(2, k+1)^-1;
    end if;
    d := c_(5, p+2);

    // (7)
    w := Lemma_3_32_Sym_y_Expression (p, k, a, y, z, d_, t);

    return atilde, c, d, e, w;
end function;

Section_3_5_Sym_Presentation := function (n :
					  p := Section_3_5_Gluing_Prime(n),
					  r := IntegerRing() !
					       PrimitiveElement (GF (p)),
					  s := InverseMod (1-r, p))
    // the required prime does not exist for n < 14, n = 21..25, and n = 45..49
    assert p le n-3;

    // (1)
    S<a,g,y> := SLPGroup(3);

    k := 2*p + 4 - n;

    atilde, c, d, e, w := Section_3_5_Sym_Words (p, k, a, g, y : r := r);

    R, J := Corollary_3_13_iii_Presentation (p : r := r, s := s);
    pi := hom <J -> S | S.1, S.2>;
    R := pi(R);
    h := R[#R];
    Prune(~R);

    R cat:= [
	atilde^-1 * (atilde * h)^y,
	c^-1 * c^y,
	(d, e^y),
	y^-1 * w
    ];

    return R, S;
end function;

// Optional parameters p, r, alpha
// p must be a prime with p = 11 mod 12, and (n+2)/2 <= p <= n-3
// r must satisfy Fp* = <r>, alpha must satisfy alpha^3 = r mod p
// Modify parameters at your own risk
Section_3_5_Sym_Gens := function (n :
				  p := Section_3_5_Gluing_Prime (n),
				  r := IntegerRing() !
				       PrimitiveElement (GF (p)),
				  alpha := r ^ InverseMod (3, p-1))
    // the required prime does not exist for n < 14, n = 21..25, and n = 45..49
    assert p le n-3;
    k := 2*p + 4 - n;

    G := Sym({-p+k-1..p+2});

    Gens := Corollary_3_13_iii_Gens (p : r := r, alpha := alpha);
    a := G ! ([-p+k-1..0] cat Eltseq (Gens[1]));
    g := G ! ([-p+k-1..0] cat Eltseq (Gens[2]));
    y := Id(G);
    for i in [k+1..p+2] do
	y := y * G ! (k+1-i,i);
    end for;

    return [a, g, y], G;
end function;

Section_3_5_Sym_Eval := function (n :
				  p := Section_3_5_Gluing_Prime (n),
				  r := IntegerRing() !
				       PrimitiveElement (GF (p)),
				  s := InverseMod (1-r, p),
				  alpha := r ^ InverseMod (3, p-1))
    return Evaluate (Section_3_5_Sym_Presentation (n : p := p, r := r, s := s),
		     Section_3_5_Sym_Gens (n : p := p, r := r, alpha := alpha));
end function;

// The coset enumeration does not halt
Section_3_5_Sym_Test := function (n :
				  p := Section_3_5_Gluing_Prime (n),
				  r := IntegerRing() !
				       PrimitiveElement (GF (p)),
				  s := InverseMod (1-r, p),
				  alpha := r ^ InverseMod (3, p-1))
    R, S := Section_3_5_Sym_Presentation (n : p := p, r := r, s := s);
    Q<a,g,y> := SLPToFP (S, R);
    b := g^3;
    z := g^(p-1);

    // H is the stabilizer of p
    H := sub<Q | b, z^a, y>;
    I := CosetImage (Q, H);
    return I;
end function;

Section_3_5_Sym_Words_Check := function (n :
					 p := Section_3_5_Gluing_Prime (n),
					 r := IntegerRing() !
					      PrimitiveElement (GF (p)),
					 alpha := r ^ InverseMod (3, p-1))
    k := 2*p + 4 - n;
    Gens, G := Section_3_5_Sym_Gens (n : p := p, r := r, alpha := alpha);
    a := Gens[1];
    g := Gens[2];
    y := Gens[3];
    atilde, c, d, e, w := Section_3_5_Sym_Words (p, k, a, g, y : r := r);

    assert atilde eq G ! (1,2,3);
    assert Support (c) subset {1..k};
    assert Support (d) subset {4..p+2};
    assert Support (e^y) subset {-p+k-1..3};
    assert #sub<G | atilde, c> eq #Sym({1..k});
    assert #sub<G | G!(4,5), d> eq #Sym({4..p+2});
    assert #sub<G | atilde, e^y> eq #Sym({-p+k-1..3});
    assert w eq y;
    return true;
end function;


// Section 3.5 of GKKL
// Theorem 2.56 of my dissertation
// States an explicit presentation of Alt(n) could be defined
// where either 14 <= n <= 20, 26 <= n <= 44, or n >= 50.

Section_3_5_Alt_Words := function (p, k, a, g, y)
    // (2)
    b, z, h := Corollary_3_8_ii_Words (p, a, g);

    // (3)
    z_ := function (i)
	return Remark_3_11_Three_Cycle (p, a, z, i);
    end function;
    d_ := function (i, j)
	return Remark_3_11_Double_Transposition (p, a, z, i, j);
    end function;

    // (4)
    c_ := function (i, j)
	return Remark_3_11_Cycle (p, a, z, i, j);
    end function;

    // (5)
    atilde := z_(3)^(z_(2) * z_(1));
    if k mod 2 eq 1 then
	c := c_(1, k);
	e := z * a * c_(2, k+1)^-1;
    else
	c := c_(2, k);
	e := z * a * c_(3, k+1)^-1;
    end if;
    d := c_(5, p+2);

    // (6)
    w := Lemma_3_32_Alt_y_Expression (p, k, a, y, z, z_, d_);

    return atilde, c, d, e, w;
end function;

// Optional parameters p, r, s
// p must be a prime with p = 11 mod 12, and (n+2)/2 <= p <= n-3
// r must satisfy Fp*^2 = <r>,
// s must satisfy s(r-1) = -1 mod p
// Modify parameters at your own risk
Section_3_5_Alt_Presentation := function (n :
					  p := Section_3_5_Gluing_Prime(n),
					  r := IntegerRing() !
					       (PrimitiveElement (GF (p))^2),
					  s := InverseMod (1-r, p))
    // the required prime does not exist for n < 15, n = 21..26, and n = 45..50
    assert p le n-4;

    // (1)
    S<a,g,y> := SLPGroup(3);

    k := 2*p + 4 - n;

    atilde, c, d, e, w := Section_3_5_Alt_Words (p, k, a, g, y);

    R, J := Corollary_3_8_ii_Presentation (p : r := r, s := s);
    pi := hom <J -> S | S.1, S.2>;
    R := pi(R);
    h := R[#R];
    Prune(~R);

    R cat:= [
	atilde^-1 * (atilde * h)^y,
	c^-1 * c^y,
	(d, e^y),
	y^-1 * w
    ];

    return R, S;
end function;

// Optional parameters p, r, alpha
// p must be a prime with p = 11 mod 12, and (n+2)/2 <= p <= n-3
// r must satisfy Fp*^2 = <r>, alpha must satisfy alpha^3 = r mod p
// Modify parameters at your own risk
Section_3_5_Alt_Gens := function (n :
				  p := Section_3_5_Gluing_Prime (n),
				  r := IntegerRing() !
				       (PrimitiveElement (GF (p))^2),
				  alpha := r ^ InverseMod (3, p-1))
    // the required prime does not exist for n < 15, n = 21..26, and n = 45..50
    assert p le n-4;
    k := 2*p + 4 - n;

    G := Sym({-p+k-1..p+2});

    Gens := Corollary_3_8_ii_Gens (p : r := r, alpha := alpha);
    a := G ! ([-p+k-1..0] cat Eltseq (Gens[1]));
    g := G ! ([-p+k-1..0] cat Eltseq (Gens[2]));
    y := Id(G);
    for i in [k+1..p] do
	y := y * G ! (k+1-i,i);
    end for;
    if n mod 2 eq 1 then
	y := y * G ! (-p-1+k,p+2)(-p+k,p+1);
    else
	y := y * G ! (-p-1+k,p+2,-p+k,p+1);
    end if;

    assert Sign (a) eq 1;
    assert Sign (g) eq 1;
    assert Sign (y) eq 1;

    return [a, g, y], G;
end function;

Section_3_5_Alt_Eval := function (n :
				  p := Section_3_5_Gluing_Prime (n),
				  r := IntegerRing() !
				       (PrimitiveElement (GF (p))^2),
				  s := InverseMod (1-r, p),
				  alpha := r ^ InverseMod (3, p-1))
    return Evaluate (Section_3_5_Alt_Presentation (n : p := p, r := r, s := s),
		     Section_3_5_Alt_Gens (n : p := p, r := r, alpha := alpha));
end function;

Section_3_5_Alt_Test := function (n :
				  p := Section_3_5_Gluing_Prime (n),
				  r := IntegerRing() !
				       (PrimitiveElement (GF (p))^2),
				  s := InverseMod (1-r, p),
				  alpha := r ^ InverseMod (3, p-1))
    R, S := Section_3_5_Sym_Presentation (n : p := p, r := r, s := s);
    Q<a,g,y> := SLPToFP (S, R);
    b := g^3;
    z := g^((p-1) div 2);

    // H is the stabilizer of p
    H := sub<Q | b, z^a, y>;
    I := CosetImage (Q, H);
    return I;
end function;

Section_3_5_Alt_Words_Check := function (n :
					 p := Section_3_5_Gluing_Prime (n),
					 r := IntegerRing() !
					      (PrimitiveElement (GF (p))^2),
					 alpha := r ^ InverseMod (3, p-1))
    k := 2*p + 4 - n;
    Gens, G := Section_3_5_Alt_Gens (n : p := p, r := r, alpha := alpha);
    a := Gens[1];
    g := Gens[2];
    y := Gens[3];
    atilde, c, d, e, w := Section_3_5_Alt_Words (p, k, a, g, y);

    assert atilde eq G ! (1,2,3);
    assert Support (c) subset {1..k};
    assert Support (d) subset {4..p+2};
    assert Support (e^y) subset {-p+k-1..3};
    assert #sub<G | atilde, c> eq #Sym({1..k}) div 2;
    assert #sub<G | G!(4,5,6), d> eq #Sym({4..p+2}) div 2;
    assert #sub<G | atilde, e^y> eq #Sym({-p+k-1..3}) div 2;
    assert w eq y;
    return true;
end function;
