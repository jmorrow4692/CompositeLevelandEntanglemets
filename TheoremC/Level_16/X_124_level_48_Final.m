////////////////////////////////////////////////////////////////////////////////////
// Computations for the mod 16 and mod 3 simultaneous computations
////////////////////////////////////////////////////////////////////////////////////
/////

SetAutoColumns(false);
SetColumns(100);
SetEchoInput(true);
Attach("routines1.m");
load "entanglements.m";

A1<s,x> := AffineSpace(Rationals(),2);
P<t> := PolynomialRing(Rationals());

////////////////// X_{H_{124}(48)////////////////////////////

jmap(124);
Factorization(Numerator(jmap(124)));
Factorization(Denominator(jmap(124)));
Factorization(Numerator(jmap(124))*Denominator(jmap(124))^2);
C := Curve(A1, s^3 - 2*(x^4 + 4*x^2 + 2)^2);
assert (Genus(C) eq 3) and (IsHyperelliptic(C) eq false);

// We can see that C will map C: s^3 = 2*(x^2 + 4*x^2 + 2)^2.
C1 := Curve(A1, s^3 - 2*(x^2 + 4*x + 2)^2);
assert (Genus(C1) eq 1);
E := EllipticCurve(ProjectiveClosure(C1),PointSearch(ProjectiveClosure(C1),1000)[1]);
assert (Rank(E) eq  1);
TorsionSubgroup(E);

Phi:= CanonicalMap(C);
CQ<X,Y,Z> := CanonicalImage(C,Phi);
CQ;
P<X,Y,Z> := PolynomialRing(Rationals(),3);
boo, DQ := IsCoercible(P,DefiningPolynomial(CQ));
q1 := (2*Y*Z + 2*Y^2);
q2 := (X^2 + 2*Y^2);
q3 := (Y^2 - Y*Z + Z^2);
if DQ eq q2^2 - (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;

// We are now in a position to implement Nils’ Bruins algorithm to determine the rational points on our original curve PC

Qx<S>:=PolynomialRing(Rationals());
P2<u,v,w>:=ProjectiveSpace(Rationals(),2);
Q1:=(2*v*w + 2*v^2);
Q2:=(u^2 + 2*v^2);
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
assert (IsLocallySolvable(D,3:AssumeIrreducible,AssumeNonsingular) eq false);


//We compute that one twist has local points

d:=1;
pi1,xpolmap1,J1:=Prym(P2,d*Q1,d*Q2,d*Q3);
D<U,V,W,R,S>:=Domain(pi1);
P4:=Ambient(D);
C1:=Codomain(pi1);
assert (RankBound(J1) eq 0);
#TorsionSubgroup(J1);
ptsJ1 := RationalPoints(J1 : Bound := 1000);

ptsD := PointSearch(Curve(D),1000);
ptsD;
xpolmap1(ptsD[1],ptsD[1]);
xpolmap1(ptsD[1],ptsD[2]);
xpolmap1(ptsD[1],ptsD[3]);
xpolmap1(ptsD[1],ptsD[4]);

// Let's check that the 4 points on D map to the 4 points on J1

ptsC := PointSearch(C1,1000);
ptsC;

Evaluate(jmap(124),0);