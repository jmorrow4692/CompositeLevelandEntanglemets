////////////////////////////////////////////////////////////////////////////////////
// Computations for X_{H,106}(48)
////////////////////////////////////////////////////////////////////////////////////
/////

SetAutoColumns(false);
SetColumns(100);
SetEchoInput(true);
Attach("routines1.m");
load "entanglements.m";

A1<s,x> := AffineSpace(Rationals(),2);
P<t> := PolynomialRing(Integers());
PP<T> := PolynomialRing(Rationals());

////////////////////////////////////////////////////////////////////////////////
// assumes the bitangent is x = Ay + Bz = A + B*t
// if this doesn't find them all, either replace f with a random linear change of coordinates, or switch out the commented lines.
////////////////////////////////////////////////////////////////////////////////

computeBitangents :=  function(f)
  L := BaseRing(Parent(f));
  P<C,D,E,B,A> := PolynomialRing(L, 5);
  PP := AffineSpace(P);
  Q<t>  := PolynomialRing(P,1);
  //eqns :=Coefficients(Evaluate(f,[A+B*t,1,t]) - E*(t^2 + C*t + D)^2 );
  //eqns :=Coefficients(Evaluate(f,[1,A+B*t,t]) - E*(t^2 + C*t + D)^2 );
  eqns :=Coefficients(Evaluate(f,[1,t,A+B*t]) - E*(t^2 + C*t + D)^2 );
  return [[DefiningEquations(cpt)[4],DefiningEquations(cpt)[5]] : cpt in IrreducibleComponents(Scheme(PP,eqns))];
end function;

// returns tuples of the form [a,b] where a and b are the equations for A and B such that the bitangent is x = Ay + Bz

  //////////////////////////////////////////////////////////////////////////////////////////
  // This code comes from David Zureick-Brown
  //////////////////////////////////////////////////////
  // The Jacobian of a general curve isn't implemented in Magma.
  //////////////////////////////////////////////////////////////////////////////////////////
  // This function computes the order of a divisor D.
  // Optional paramater: N is a known multiple of the order of D
  // Optional paramater: B, give up after B
  //////////////////////////////////////////////////////////////////////////////////////////

  order := function(D : N := 0, B := N eq 0 select 500 else N)
    currentBound := 0;
    found := false;
    if N eq 0 then
      while not found and currentBound le B do
        currentBound := currentBound + 1;
        found := IsPrincipal(currentBound * D);
      end while;
        return found select currentBound else 0, found;
    else
      for n in Divisors(N) do
        found := IsPrincipal(n*(D));
        if found then
          currentBound := n; break;
        end if;
      end for;
      return currentBound, found;
     end if;
  end function;

////////////////// X_{H_{106}(48)////////////////////////////
Factorization(Numerator(jmap(106)));
Factorization(Denominator(jmap(106)));
Factorization(Numerator(jmap(106))*Denominator(jmap(106))^2);
C := Curve(A1, s^3 - (x^4 + 8*x^2 + 8)^2);
assert (Genus(C) eq 3) and (IsHyperelliptic(C) eq false);

// The above curve is isomorphic to the curve below
C := Curve(A1, s^3 - (x^4 + 8*x^2 + 8));
assert (RankBound(T^4 + 8*T^2 + 8,3) eq 1);

// We can see that C will map C: s^3 = (x^2 + 8*x + 8)^2.
C1 := Curve(A1, s^3 - ((x^2 + 8*x + 8)^2));
Genus(C1);
E := EllipticCurve(ProjectiveClosure(C1),PointSearch(ProjectiveClosure(C1),1000)[1]);
assert (Rank(E) eq  1);
TorsionSubgroup(E);

// This is a good candidate for Chabauty's method 

Phi:= CanonicalMap(C);
CQ<X,Y,Z> := CanonicalImage(C,Phi);
P<X,Y,Z> := PolynomialRing(Rationals(),3);
boo, DQ := IsCoercible(P,DefiningPolynomial(CQ));

// Try computing what the torsion is

torsOrders := {@@};
bad := [2,3];
bool := false; p := 2;
while  p le 30 do
  p :=  NextPrime(p);        
  p := p in bad select NextPrime(p) else p;
  pvalues := {@@};
  Cp := Curve(Reduction(C,p));
  numH := Numerator(ZetaFunction(Cp));  
  torsOrders :=   torsOrders join  {@ Evaluate(numH,1) @};
  [p,GCD(torsOrders)];
  Invariants(ClassGroup(Cp));
  "*******************";
end while;

// We see that the torsion is at most Z/2 x Z/2, but we already found a part of the two torsion coming from the elliptic curve. 

// We claim that the torsion of J is Z/2 which follows by computing the bitangents

Bit:= computeBitangents(DQ);

// coerce the bitangents into divisors by hand
P<T> := PolynomialRing(Rationals());
f1 := T^2 - 1/2*T + 1/4;
S1 := SplittingField(f1);

f2 :=  T^2 - T - 1/8;
S2 := SplittingField(f2);
_<x1> := PolynomialRing(S2);
f22 := x1^2 - S2.1; 
S3 := SplittingField(f22);

f4 := T^2 + 1/8;
S4 := SplittingField(f4);
_<x2> := PolynomialRing(S4);
f5 := x2^2 + S4.1 + 1/2;
S5 := SplittingField(f5);

f6 := T^4 + T^3 + 9/8*T^2 - 1/8*T + 1/64;
S6 := SplittingField(f6);
_<x3> := PolynomialRing(S6);
f7 := x3^2 - 8/9*S6.1^3 + 1/9;
S7 := SplittingField(f7);

f8 := T^4 - 1/8*T^2 + 1/64;
S8 := SplittingField(f8);
_<x4> := PolynomialRing(S8);
f9 := x4^2 - 8*S8.1^3 + 1/2;
S9 := SplittingField(f9);

FF := f1*DefiningPolynomial(S3)*DefiningPolynomial(S5)*DefiningPolynomial(S7)* DefiningPolynomial(S9);
SF := SplittingField(FF);
_<q> := PolynomialRing(SF);
CQF := BaseChange(CQ,SF);

PP<X,Y,Z> := AmbientSpace(CQF);

b1 := Scheme(PP, X - 1/2*Y);
irr := IrreducibleComponents(b1 meet CQF);
B1 := Divisor(CQF,b1 meet CQF);
Degree(B1);

b2 := Scheme(PP, X );
irr := IrreducibleComponents(b2 meet CQF);
B2 := Divisor(CQF,b2 meet CQF);
Degree(B2);

r3 := Roots(q^2 - 1/2*q+1/4);
b3 := Scheme(PP, X - (r3[1,1]*Y));
irr := IrreducibleComponents(b3 meet CQF);
B3 := Divisor(CQF,b3 meet CQF);
Degree(B3);

r4 := Roots(q^2 - q - 1/8);
r5 := Roots(q^2 - r4[1,1]);
b4 := Scheme(PP, X - (r4[1,1]*Y + r5[1,1]*Z));
irr := IrreducibleComponents(b4 meet CQF);
B4 := Divisor(CQF,b4 meet CQF);
Degree(B4);

r6 := Roots(q^2 + 1/8);
r7 := Roots(q^2 + r6[1,1] + 1/2);
b5 := Scheme(PP, X - (r6[1,1]*Y + r7[1,1]*Z));
irr := IrreducibleComponents(b5 meet CQF);
B5 := Divisor(CQF,b5 meet CQF);
Degree(B5);

r8 := Roots(q^4 + q^3 + 9/8*q^2 - 1/8*q + 1/64);
r9 := Roots(q^2 - 8/9*r8[1,1]^3 + 1/9);
b6 := Scheme(PP, X - (r8[1,1]*Y + r9[1,1]*Z));
irr := IrreducibleComponents(b6 meet CQF);
B6 := Divisor(CQF,b6 meet CQF);
Degree(B6);

r10 := Roots(q^4 - 1/8*q^2 + 1/64);
r11 := Roots(q^2 - 8*r10[1,1]^3 + 1/2);
b7 := Scheme(PP, X - (r10[1,1]*Y + r11[1,1]*Z));
irr := IrreducibleComponents(b6 meet CQF);
B7 := Divisor(CQF,b7 meet CQF);
Degree(B7);

BB := [B1,B2,B3,B4,B5,B6,B7];

B := 1;
while B lt 2 do
B := B + 1;
for c in [c : c in CartesianPower([-B..B],7)] do
  D := &+[c[i]*BB[i] : i in [1..7]];
  if (Degree(D) eq 0) and (order(D : B := 2) eq 2) then
    D;
  end if;
end for;
end while;





// Let's verify that claims about the mod 5 image
CQ5 := Curve(Reduction(CQ,5));
pts5 := Points(CQ5);
assert (#pts5 eq 6);
ptsCQ := PointSearch(CQ,1000);
D := Divisor(ptsCQ[1]) - Divisor(ptsCQ[2]);
Dp := Divisor(pts5[1]) - Divisor(pts5[6]); 

// verifying that only two points contribute to the Abel--Jacobi mod 5
for p in pts5 do 
order(Divisor(p) - Divisor(pts5[6]));
end for;


// Try to find expression for 6D
CQS := Scheme(AmbientSpace(CQ),DQ);
ptsCQS := PointSearch(CQS,1000);
D1 := Divisor(ptsCQS[1]);
D2 := Divisor(ptsCQS[2]);
DD1 := Divisor(CQS, CQS meet Scheme(AmbientSpace(CQS),Ideal(D1)));
DD2 := Divisor(CQS, CQS meet Scheme(AmbientSpace(CQS),Ideal(D2)));
D := DD1 - DD2;
ND := 6*D + 2*DD2;
boo, QD := IsLinearSystemNonEmpty(ND);
assert (boo eq true);
Ideal(QD);
225^2/3375;
Factorization(15*23048);

// the second case
ND2 := 6*D + 2*DD1;
boo, QD2 := IsLinearSystemNonEmpty(ND2);
assert (boo eq true);
Ideal(QD2);
2704^2/140608;
Factorization(52*6054255);


// let's work with differentials and expand with the local coordinate t = y
DD := BasisOfHolomorphicDifferentials(CQ);
DD;
QQ<q> := PowerSeriesRing(pAdicField(5,40));
f1 := (1/(q^4 + 8*q^2 + 8)*q^2); f1;
f2 := (1/(q^4 + 8*q^2 + 8)*q); f2;
f3 := (1/(q^4 + 8*q^2 + 8)); f3;







