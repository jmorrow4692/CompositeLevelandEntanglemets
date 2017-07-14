////////////////////////////////////////////////////////////////////////////////////
// Computations for X_{H,105}(48)
////////////////////////////////////////////////////////////////////////////////////

SetAutoColumns(false);
SetColumns(100);
SetEchoInput(true);
Attach("routines1.m");
load "fns.m";
load "entanglements.m";


A1<s,x> := AffineSpace(Rationals(),2);
P<t> := PolynomialRing(Integers());
PP<T> := PolynomialRing(Rationals());
////////////////// X_{H_{105}(48)////////////////////////////
Factorization(P!Numerator(jmap(105)));
Factorization(P!Denominator(jmap(105)));
Factorization(P!Numerator(jmap(105))*Denominator(jmap(105))^2);
C := Curve(A1, s^3 - (x^4 - 8*x^2 + 8)^2);
CC := Curve(A1, s^3 - (x^4 - 8*x^2 + 8));
assert (Genus(C) eq 3) and (IsHyperelliptic(C) eq false);


// We can see that C will map C: s^3 = (x^2 - 8*x + 8)^2.
C1 := Curve(A1, s^3 - (x^4 - 16*x^3 + 80*x^2 - 128*x + 64));
Genus(C1);
E := EllipticCurve(ProjectiveClosure(C1),PointSearch(ProjectiveClosure(C1),1000)[1]);
assert (Rank(E) eq  1);
TorsionSubgroup(E);

// Thus, C maps to a rank 1 elliptic curve with 2-torsion

// In the best case, C maps to a genus > 1 curve over some number field

Poly := [t^2 - t + 1, t^2 + 1, t^2 - 2, t^2 + 2, t^2 - 3, t^2 - 6 , t^2 + 6];
for i in [1..#Poly] do
K := NumberField(t);
CK := BaseChange(C,K);
aut := AutomorphismGroup(CK);
i, #aut;
"**************";
end for;

// Over some large number field we have more automorphisms

K := NumberField(t^4 - 8*t^2 + 8);
CK := BaseChange(C,Compositum(K,CyclotomicField(3)));
aut := AutomorphismGroup(CK);

Q1,q1 := CurveQuotient(AutomorphismGroup(CK,[(aut.1)])); 
Genus(Q1); 
Q2,q2 := CurveQuotient(AutomorphismGroup(CK,[(aut.2)])); 
Genus(Q2);
Q3,q3 := CurveQuotient(AutomorphismGroup(CK,[(aut.1)*(aut.1)])); 
Genus(Q3);
Q4,q4 := CurveQuotient(AutomorphismGroup(CK,[aut.1*aut.2])); 
Genus(Q4);
Q5,q5 := CurveQuotient(AutomorphismGroup(CK,[(aut.1)*(aut.2)*(aut.1)])); 
Genus(Q5);

// Thus, we get nothing new from the extending the number field and taking quotients.

// Let's try to determine the abelian surface A appearing in the Jacobian of C
// The code below verifies that A is simple over Q 

for p in [5,11,17] do
"*******************************";
p;  
F := FiniteField(p);
A1<x,s> := AffineSpace(F,2);
C:= Curve(A1, s^3 - (x^4 - 8*x^2 + 8)^2);
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!-240790815720,F!-14497977626517951489924,F!1350439562298791009867513328,F!165435463601628701337359492978815353072,F!0]) )) );
Factorization(num);
end for;

// The abelian variety should factor over a quadratic extension

for p in [5,11,17,19] do
"*******************************";
p;  
F := FiniteField(p^2);
A1<x,s> := AffineSpace(F,2);
C:= Curve(A1, s^3 - (x^4 - 8*x^2 + 8)^2);
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!-240790815720,F!-14497977626517951489924,F!1350439562298791009867513328,F!165435463601628701337359492978815353072,F!0]) )) );
Factorization(num);
end for;

// Let's try to find this extension and the elliptic curves
discs := {-1,2,-2,3,-3,6,-6};
for d in discs do
d;
[LegendreSymbol(d,p) : p in [5,11,17,19]];
"***********************************";
end for;
//This tells us that the field is most likely QuadraticField(-3)
//We can check to see that C has extra automorphisms over that quadratic field
for d in discs do
  F := QuadraticField(d);
  A1<x,s> := AffineSpace(F,2);
  C:= Curve(A1, s^3 - (x^4 - 8*x^2 + 8));
[d,#AutomorphismGroup(C)];
end for;

// We gain extra automorphisms over the quadratic extension with discriminant 6, but these extra automorphisms do not yield fruitful curve quotients so we instead look for the number field with Legendre symbols matching those corresponding to the factorization of zeta functions

P<t> := PolynomialRing(Rationals());
K<a>:= NumberField(t^2 - 2);
O := MaximalOrder(K);
SetVerbose("ECSearch",3);
GRcurves:= Eltseq(EllipticCurveWithGoodReductionSearch(2*3*O,500)); 

// We find that this list is not sufficient, in the sense that, not all known techniques are used. If we try to implement all known techniques using Effort := 400, we will get an error since these techniques are not implemented for elliptic curves with j = 0 over this field. 

EK := BaseChange(E,K);
Possible := {@@};
for p in [17] do
  pvalues := {@@};
  p;  
  F := FiniteField(p);
  A1<x,s> := AffineSpace(F,2);
  C:= Curve(A1, s^3 - (x^4 - 8*x^2 + 8));
  allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!-240790815720,F!-14497977626517951489924,F!1350439562298791009867513328,F!165435463601628701337359492978815353072,F!0]) )) );
  exists(c){c : c in curves | IsDivisibleBy(num,Numerator(ZetaFunction(c)) ) };
   for i in [1..#GRcurves] do
     g:= ChangeRing(IntegralModel(GRcurves[i]),O);  	
     R,phi:=ResidueClassField(Decomposition(O,p)[1][1]);
     G<X,Y,Z> := BaseChange(g,phi); 
       if ZetaFunction(G) eq ZetaFunction(c) then
         pvalues := pvalues join {i}; 
       end if;
    end for;
  Possible := Possible join {@pvalues@};
end for;


Possible2 := {@@};
for p in [5] do
  pvalues := {@@};
  p;  
  F := FiniteField(p^2);
  A1<x,s> := AffineSpace(F,2);
  C:= Curve(A1, s^3 - (x^4 - 8*x^2 + 8));
  allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!-240790815720,F!-14497977626517951489924,F!1350439562298791009867513328,F!165435463601628701337359492978815353072,F!0]) )) );
  exists(c){c : c in curves | IsDivisibleBy(num,Numerator(ZetaFunction(c)) ) };
   for i in [1..#Possible[1]] do
     g:= ChangeRing(IntegralModel(GRcurves[Possible[1,i]]),O); 
     R,phi:=ResidueClassField(Decomposition(O,p)[1][1]);
     G<X,Y,Z> := BaseChange(g,phi); 
       if ZetaFunction(G) eq ZetaFunction(c) then
         pvalues := pvalues join {i}; 
       end if;
    end for;
  Possible2 := Possible2 join {@pvalues@};
end for;
 

Possible3 := {@@};
for p in [11] do
  pvalues := {@@};
  p;  
  F := FiniteField(p^2);
  A1<x,s> := AffineSpace(F,2);
  C:= Curve(A1, s^3 - (x^4 - 8*x^2 + 8));
  allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!-240790815720,F!-14497977626517951489924,F!1350439562298791009867513328,F!165435463601628701337359492978815353072,F!0]) )) );
  exists(c){c : c in curves | IsDivisibleBy(num,Numerator(ZetaFunction(c)) ) };
   for i in [1..#Possible2[1]] do
     g:= ChangeRing(IntegralModel(GRcurves[Possible2[1,i]]),O);  	
     R,phi:=ResidueClassField(Decomposition(O,p)[1][1]);
     G<X,Y,Z> := BaseChange(g,phi); 
       if ZetaFunction(G) eq ZetaFunction(c) then
         pvalues := pvalues join {i}; 
       end if;
    end for;
  Possible3 := Possible3 join {@pvalues@};
end for;

Possible4 := {@@};
for p in [19] do
  pvalues := {@@};
  p;  
  F := FiniteField(p^2);
  A1<x,s> := AffineSpace(F,2);
  C:= Curve(A1, s^3 - (x^4 - 8*x^2 + 8));
  allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!-240790815720,F!-14497977626517951489924,F!1350439562298791009867513328,F!165435463601628701337359492978815353072,F!0]) )) );
  exists(c){c : c in curves | IsDivisibleBy(num,Numerator(ZetaFunction(c)) ) };
   for i in [1..#Possible3[1]] do
     g:= ChangeRing(IntegralModel(GRcurves[Possible3[1,i]]),O);  	
     R,phi:=ResidueClassField(Decomposition(O,p)[1][1]);
     G<X,Y,Z> := BaseChange(g,phi); 
       if ZetaFunction(G) eq ZetaFunction(c) then
         pvalues := pvalues join {i}; 
       end if;
    end for;
  Possible4 := Possible4 join {@pvalues@};
end for;

// This procedure did not yield a useful result. One can run similar computations for other number fields, which we omit here.
// So instead of a going down approach we attempt a going up approach
// We want to compute a smooth plane model of PC

A1<s,x> := AffineSpace(Rationals(),2);
P<t> := PolynomialRing(Integers());
C := Curve(A1, s^3 - (x^4 - 8*x^2 + 8)^2);
CC := Curve(A1, s^3 - (x^4 - 8*x^2 + 8));
Phi:= CanonicalMap(C);
CQ<X,Y,Z> := CanonicalImage(C,Phi);
P<X,Y,Z> := PolynomialRing(Rationals(),3);
boo, DQ := IsCoercible(P,DefiningPolynomial(CQ));

q1 := (2*Y^2 + Y*Z);
q2 := (X^2 - 4*Y^2);
q3 := (4*Y^2 - 2*Y*Z + Z^2);
if DQ eq q2^2 - (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;

//Computing possible torsion orders of Jacobians
torsOrders := {@@};
bool := false; p := 3;
while  p le 50 do
  p :=  NextPrime(p);        
  pvalues := {@@};
  F := FiniteField(p);
  PF<A> := PolynomialRing(F);
  Hp := Curve(Reduction(CQ,p));
  numH := Numerator(ZetaFunction(Hp));  
  torsOrders :=   torsOrders join  {@ Evaluate(numH,1) @};
  [p,GCD(torsOrders)];
  Invariants(ClassGroup(Hp));
  "*******************";
end while;

// This suggests that the torsion of the Jacobian of CQ is Z/2 + Z/4Z

// We are now in a position to implement Nils’ Bruins algorithm to determine the rational points on our original curve PC

Qx<S>:=PolynomialRing(Rationals());
P2<u,v,w>:=ProjectiveSpace(Rationals(),2);
Q1:=(2*v^2 + v*w);
Q2:=(u^2 - 4*v^2);
Q3:=(4*v^2 - 2*v*w + w^2);
Factorisation(BadPrimes([Q1,Q2,Q3]));
//Only bad primes are 2,3. That leaves 1,-1,2,-2,3,-3,6,-6 as possible
//values for delta
//In fact, there are more bad primes for PC than there are where Q1,Q2,Q3
//simultaneously vanish:
Factorisation(BadPrimes(DefiningEquations(SingularSubscheme(Curve(P2,Q1*Q3-Q2^2)))));
//This computation does give any additional bad primes

P4<U,V,W,R,S> := ProjectiveSpace(Rationals(),4);

d:=-1;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
Dpl:=Curve(Projection(Projection(D)));
//verify that negative d lead to D(R) being empty
assert (HasRealPoints(Dpl) eq false);

d:=2;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
//verify that D is not locally solvable at 2
assert (IsLocallySolvable(D,2:AssumeIrreducible,AssumeNonsingular) eq false);

d:=6;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
//verify that D is not locally solvable at 3
assert (IsLocallySolvable(D,3:AssumeIrreducible,AssumeNonsingular) eq false);

d:=-2;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
//verify that D is not locally solvable at 2
assert (IsLocallySolvable(D,2:AssumeIrreducible,AssumeNonsingular) eq false);

d:=-6;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
//verify that D is locally solvable at 3, but not at 2
assert (IsLocallySolvable(D,3:AssumeIrreducible,AssumeNonsingular) eq true);
assert (IsLocallySolvable(D,2:AssumeIrreducible,AssumeNonsingular) eq false);

d:=-3;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
Dpl:=Curve(Projection(Projection(D)));
//verify that D is not locally solvable at 3
HasRealPoints(Dpl);
assert (IsLocallySolvable(D,2:AssumeIrreducible,AssumeNonsingular) eq false);
assert (IsLocallySolvable(D,3:AssumeIrreducible,AssumeNonsingular) eq false);

d:=1;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
Dpl:=Curve(Projection(Projection(D)));
//verify that D is not locally solvable at 3
HasRealPoints(Dpl);
assert (IsLocallySolvable(D,2:AssumeIrreducible,AssumeNonsingular) eq true);
assert (IsLocallySolvable(D,3:AssumeIrreducible,AssumeNonsingular) eq true);

d:=3;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
Dpl:=Curve(Projection(Projection(D)));
//verify that D is not locally solvable at 3
HasRealPoints(Dpl);
assert (IsLocallySolvable(D,3:AssumeIrreducible,AssumeNonsingular) eq true);
assert (IsLocallySolvable(D,2:AssumeIrreducible,AssumeNonsingular) eq true);

//We compute that only two of the twist have no rational points by local computations

d:=3;
pi3,xpolmap3,J3:=Prym(P2,3*Q1,3*Q2,3*Q3);
D3<U,V,W,R,S>:=Domain(pi3);
PD3 := PointSearch(D3,1000);
P4:=Ambient(D3);
C3:=Codomain(pi3);
// RankBound(J3); positive rank, namely 2 so we actually can't perform Chabauty on the Prym!

// We lose for this twist

d:=1;
pi1,xpolmap1,J1:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi1);
P4:=Ambient(D);
C1:=Codomain(pi1);
// RankBound(J1);

// We win for this twist since it has rank 0!

TorsionSubgroup(J1);
PD := PointSearch(D,1000);
#PP;

// We can provably compute the points on the trivial twist

// Let's just check that each of the points in D maps to different points in J1
xpolmap1(PP[1],PP[1]);
xpolmap1(PP[1],PP[2]);
xpolmap1(PP[1],PP[3]);
xpolmap1(PP[1],PP[4]);
xpolmap1(PP[2],PP[3]);
P4<U,V,W,R,S> := ProjectiveSpace(Rationals(),4);

// IF we new that these 8 points were the only ones on D3, then we could conclude our result that the known points on C are the only rational points.

PD3;
PointSearch(C1,1000);

