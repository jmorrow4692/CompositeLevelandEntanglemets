////////////////////////////////////////////////////////////////////////////////////
// Computations for X_{107}(48)
////////////////////////////////////////////////////////////////////////////////////
/////We only have to consider the case when rho_{E,3} is conjugate to a subgroup of N_{nsp(3), so by abuse of notation, we will denote our modular curves by X_{H_#} for some number/////

SetAutoColumns(false);
SetColumns(100);
SetEchoInput(true);
Attach("routines1.m");
load "entanglements.m";

A1<s,x> := AffineSpace(Rationals(),2);
P<t> := PolynomialRing(Rationals());

////////////////// X_{H_{107}(48)////////////////////////////
jmap(107);
Factorization(Numerator(jmap(107)));
Factorization(Denominator(jmap(107)));
Factorization(Numerator(jmap(107))*Denominator(jmap(107))^2);
C := Curve(A1, s^3 - (x^4 - x^2 + 1/8)^2);
assert (Genus(C) eq 3) and (IsHyperelliptic(C) eq false);

C := Curve(A1, s^3 - (x^4 - x^2 + 1/8));

//float an 8 = 2^3 throughout to get an equation with integral coefficients
CC := Curve(A1, s^3 - (8*x^4 - 8*x^2 + 1)); 
assert (RankBound(8*t^4 - 8*t^2 + 1,3) eq 3);


// We can see that C will map C: s^3 = (x^2 - x + 1/8)^2.
C1 := Curve(A1, s^3 - ((x^2 - x + 1/8)^2));
assert (Genus(C1) eq 1);
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

K := NumberField(t^4 -t^2 + 1/8);
CK := BaseChange(C,Compositum(K,CyclotomicField(3)));
aut := AutomorphismGroup(CK);
assert (#aut eq 6);

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
C:= Curve(A1, s^3 - (x^4 - x^2 + 1/8)^2);
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!416,F!-39208,F!140608,F!-23762752,F!0]) )) );
Factorization(num);
end for;

// The abelian variety should factor over a quadratic extension

for p in [5,11,17,19] do
"*******************************";
p;  
F := FiniteField(p^2);
A1<x,s> := AffineSpace(F,2);
C:= Curve(A1, s^3 - (x^4 - x^2 + 1/8)^2);
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!16,F!-88,F!0,F!192,F!0]) )) );
Factorization(num);
end for;

// Let's try to find this extension and the elliptic curves
discs := {-1,2,-2,3,-3,6,-6};
for d in discs do
d;
[LegendreSymbol(d,p) : p in [5,11,17,19]];
"***********************************";
end for;

//This tells us that the field is most likely QuadraticField(2) or QuadraticField(-3)
//We can check to see that C has extra automorphisms over that quadratic field

for d in discs do
  F := QuadraticField(d);
  A1<x,s> := AffineSpace(F,2);
  C:= Curve(A1, s^3 - (x^4  -x^2 + 1/8));
[d,#AutomorphismGroup(C)];
end for;

// We gain extra automorphisms over the quadratic extension with discriminant 6, but these extra automorphisms do not yield fruitful curve quotients so we instead look for the number field with Legendre symbols matching those corresponding to the factorization of zeta functions

P<t> := PolynomialRing(Rationals());
K<a>:= NumberField(t^2 + 2);
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
  C:= Curve(A1, s^3 - (x^4 + 8*x^2 + 8));
  allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!16,F!-88,F!0,F!192,F!0]) )) );
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
  C:= Curve(A1, s^3 - (x^4 + 8*x^2 + 8));
  allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!16,F!-88,F!0,F!192,F!0]) )) );
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
  C:= Curve(A1, s^3 - (x^4 + 8*x^2 + 8));
  allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!16,F!-88,F!0,F!192,F!0]) )) );
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
  C:= Curve(A1, s^3 - (x^4 + 8*x^2 + 8));
  allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(C))) !( Numerator(ZetaFunction(C)) / Numerator(ZetaFunction( EllipticCurve([F!16,F!-88,F!0,F!192,F!0]) )) );
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
C := Curve(A1, s^3 - (x^4 - x^2 + 1/8)^2);
Phi:= CanonicalMap(C);
CQ<X,Y,Z> := CanonicalImage(C,Phi);
P<X,Y,Z> := PolynomialRing(Rationals(),3);
boo, DQ := IsCoercible(P,DefiningPolynomial(CQ));

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

// Let's minimize the plane quartic

PQ<X,Y,Z> := MinimizeReducePlaneQuartic(DQ);
PQ;
q1 := (2*Y*Z + 2*Z^2);
q2 := (X^2 - 2*Z^2);
q3 := (Y^2 - Y*Z + Z^2);
if PQ eq q2^2 - (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;


// We are now in a position to implement Nils’ Bruins algorithm to determine the rational points on our original curve PC

Qx<S>:=PolynomialRing(Rationals());
P2<u,v,w>:=ProjectiveSpace(Rationals(),2);
Q1:=(2*v*w + 2*w^2);
Q2:=(u^2 - 2*w^2);
Q3:=(v^2 - v*w + w^2);
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
assert (IsLocallySolvable(D,3:AssumeIrreducible,AssumeNonsingular) eq false);
assert (IsLocallySolvable(D,2:AssumeIrreducible,AssumeNonsingular) eq false);

d:=-3;
pi,xpolmap,J:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi);
Dpl:=Curve(Projection(Projection(D)));
//verify that D is not locally solvable at 3
assert (HasRealPoints(Dpl) eq  false);
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
assert (HasRealPoints(Dpl) eq true);
assert (IsLocallySolvable(D,3:AssumeIrreducible,AssumeNonsingular) eq false);
assert (IsLocallySolvable(D,2:AssumeIrreducible,AssumeNonsingular) eq false);

//We compute that one twist has local points

d:=1;
pi1,xpolmap1,J1:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi1);
P4:=Ambient(D);
C1:=Codomain(pi1);
assert (RankBound(J1) eq 1);

ptsD := PointSearch(Curve(D),1000);
ptsD;
ptsC := PointSearch(C1,1000);
ptsC;

