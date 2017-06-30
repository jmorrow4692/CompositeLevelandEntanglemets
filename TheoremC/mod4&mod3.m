////////////////////////////////////////////////////////////////////////////////////
// Computations for the mod 4 and mod 3 simultaneous computations
////////////////////////////////////////////////////////////////////////////////////

load "entanglements.m";
GG:= GL(2,2);



/*-----Level 4, applicable subgroups that do contain G_3 in kernel of reduction----*/
G3:=[i : i in [1..#newsublist] | newsublist[i][2] eq 4 and #{GG!g : g in newsublist[i][3]} eq 3]; 
//We exclude the subgroups whose modular curve is a pointless conic
Bad := [21];
G3 := [i : i in G3 | not (i in Bad)]; G3;
for i in G3 do
  [i,jmap(i)];
end for;
assert (#G3 eq 0);

/*-----Level 4, applicable subgroups that do contain G_2 in kernel of reduction-----*/
G2:=[i : i in [1..#newsublist] | newsublist[i][2] eq 4 and #{GG!g : g in newsublist[i][3]} eq 2 ]; 
for i in G2 do
  [i,jmap(i)];
end for;

/*-----Level 4, applicable subgroups that do contain {I} in kernel of reduction-----*/
G1:=[i : i in [1..#newsublist] | newsublist[i][2] eq 4 and #{GG!g : g in newsublist[i][3]} eq 1]; 
//We exclude the subgroups whose modular curve is a pointless conic
Bad := [58,59];
G1 := [i : i in G1 | not (i in Bad)];
for i in G1 do
  [i,jmap(i)];
end for;

/*
The above and previous results tell us that there are (9*4) + (2*1) = 38 possibilities for the mixed-(4,3) image of Galois to be simultaneously non-surjective. We check which of these possibilities occur. In many cases, we will use a nice model for the Picard curves to determine their rational points. 

In some cases, we will find that this model is isomorphic to a P^1, in which we will need to conduct a more thorough analysis. However, in some cases, we find that this model is an elliptic curve with rank 0. In these latter cases, we will simply denote the subgroup appearing in the modular curve notation by G. 

The functions J_1,J_2,J_4 are all cubes so we consider them all at once! 
*/


Q<X> := PolynomialRing(Integers());
_<t> := FunctionField(Rationals());

//Equations coming from Zywina
J3:=[
	27*(t+1)^3*(t+3)^3*(t^2+3)^3/(t^3*(t^2+3*t+3)^3),
	27*(t+1)^3*(t-3)^3/t^3,
	27*(t+1)*(t+9)^3/t^3,
	t^3
	];


A2<s,t> := AffineSpace(Rationals(),2);
AA<a,b> := CoordinateRing(A2);

////////////////////////////////////////////////////////////
// Level 3 entry is G_4 
////////////////////////////////////////////////////////////

/*----------------------------X_{H_9, G_4}(12)----------------------------------*/
jmap(9);
C:= Curve(A2, s^3*(t^2 + 64) - (t^6 + 144*t^4 + 6912*t^2 + 110592));
IsSingular(C);
ptsC := PointSearch(C,1000);ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
assert (Degree(DD) eq 3);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
E,psi := EllipticCurve(canC,phi(pts[2]));
MordellWeilShaInformation(E);
assert (Rank(E) eq 0);
ptsE := RationalPoints(E : Bound := 1000);

Phi := phi*Extend(psi);
for p in ptsE do
Points(p@@Phi);
end for;

// X_{H_9, G_4}(12) is a rank 0 elliptic curve with only a CM point 

/*----------------------------X_{H_10,G_4}(12)----------------------------------*/
C:= Curve(A2, s^3*(t^6 + 2*t^4 + t^2) - (1728*t^6 - 1728*t^4 + 576*t^2 - 64));
PP:= Curve(A2, s^3*(t^3 + 2*t^2 + t) - (1728*t^3 - 1728*t^2 + 576*t^1 - 64));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
assert (Genus(C) eq 1);
PC := ProjectiveClosure(C);
RationalPoints(SingularSubscheme(PC));
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] -  X[3]);
D := Divisor(PC,L meet PC);
D := Support(D)[1];
Degree(D); // 3
      phi := DivisorMap(Divisor(D));
      canC := Image(phi);
E,p1 := EllipticCurve(canC,PointSearch(canC,1000)[1]);
assert (Rank(E) eq 0);
MordellWeilShaInformation(E);
ptsE:= RationalPoints(E : Bound := 100000);
Phi := phi*p1;
for p in ptsE do
Points(p@@Phi);
end for;

//X_{H_10,G}(12) is a rank 0 elliptic curve

/*----------------------------X_{H_11, G_4}(12)----------------------------------*/
C:= Curve(A2, s^3*t^2 - (t^6 - 48*t^4 + 768*t^2 - 4096));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 0);
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[2]),Curve(P1)); //takes some time

// X_{H_11, G_4}(12) is a P^1

/*----------------------------X_{H_12, G_4}(12)----------------------------------*/
C:= Curve(A2, s^3*t^2 - (t^6 + 48*t^4 + 768*t^2 + 4096));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] +  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 0);
pt := canC!phi(pts[1]);

//X_{H_12, G_4}(12) is a P^1

/*For a parametrization, run over night
L := Scheme(P2,X[1] -  X[3]);
D := Divisor(PC,L meet PC);
D := Support(D)[1];
      phi := DivisorMap(Divisor(D));
      canC := Image(phi);
      canC;	
assert (Genus(canC) eq 0);
pts:=PointSearch(canC,100); 
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(canC,pt,Curve(P1)); */

/*----------------------------X_{H_13, G_4}(12)----------------------------------*/
C:= Curve(A2, (t^6 - 144*t^4 + 6912*t^2 - 110592) - s^3*(t^2 - 64));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 1);
E,p1 := EllipticCurve(canC,PointSearch(canC,10000)[2]);
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 6); 
ptsE := RationalPoints(EE : Bound := 1000);
Factorization(HyperellipticPolynomials(EE));
q4 := EE![-5184,0,1];
q6 := q4 + ptsE[2];
for i in [1..6] do
ptsE := ptsE join {i*q6};
end for;

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(66^3));

// X_{H_13, G}(12) is an elliptic curve with rank 0 and 3 CM points

/*----------------------------X_{H_23, G_4}(12)----------------------------------*/
C:= Curve(A2, (-64*t^12 + 384*t^10 - 192*t^8 - 1792*t^6 + 576*t^4 + 3456*t^2 + 1728) - s^3*(t^8 - 4*t^6 + 6*t^4 - 4*t^2 +1));
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
E,p1 := EllipticCurve(PC,PointSearch(PC,1000)[2]);
EE,p2 := WeierstrassModel(E);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 6); 
ptsE := RationalPoints(EE : Bound := 100000);
[Order(p) : p in ptsE];
Factorization(HyperellipticPolynomials(EE));
q5 := EE![-147456,0,1];
ptsE := ptsE join {q5,ptsE[2] + q5,ptsE[3] + q5};

Phi := p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(23),3)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(23),-3)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(23),0)));

// X_{H_23, G_4}(12) is a rank 0 elliptic curve and has 3 CM points

/*----------------------------X_{H_26,G_4}(12)----------------------------------*/
C:= Curve(A2, (-64*t^12 - 384*t^10 - 192*t^8 + 1792*t^6 + 576*t^4 - 3456*t^2 + 1728) - (s^3*(t^8 + 4*t^6 + 6*t^4 + 4*t^2 + 1)));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,100);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
RationalPoints(SingularSubscheme(PC));
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 1);
E,p1 := EllipticCurve(canC,phi(pts[4]));
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 2); 
ptsE := RationalPoints(EE : Bound := 1000);

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(26),1)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(26),-1)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(26),0)));

// X_{H_26,G}(12) is a rank 0 elliptic curve and has 3 CM points

/*----------------------------X_{H_27,G_4}(12)----------------------------------*/ 
// Not needed since it covers X_{H_10, G_4}(12)

/*----------------------------X_{H_60,G_4}(12)----------------------------------*/ 
// Not needed since it covers X_{H_27, G_4}(12)


////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Level 3 entry is G_3 
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////

/*----------------------------X_{H_9,G_3}(12)------------------------------------*/
C:= Curve(A2, s^3*(t^6 + 144*t^4 + 6912*t^2 + 110592) - (27*(s+1)*(s+9)^3*(t^2+64)));
IsSingular(C);
ptsC := PointSearch(C,1000);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
      phi := DivisorMap(Divisor(DD));
      canC := Image(phi);
assert (Genus(canC) eq 0);
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[1]),Curve(P1));

//X_{H_9,G_3}(12) is a P^1

/*----------------------------X_{H_10,G_3}(12)----------------------------------*/
C:= Curve(A2, s^3*(1728*t^6 - 1728*t^4 + 576*t^2 - 64) - (27*(s+1)*(s+9)^3*(t^6 + 2*t^4 + t^2)));
IsSingular(C);
ptsC := PointSearch(C,1000);ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[3];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 0);
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[2]),Curve(P1)); //takes some time

//X_{H_10,G_3 is a P^1

/*----------------------------X_{H_11, G_3}(12)--------------------------------------*/
C:= Curve(A2, s^3*(t^6 - 48*t^4 + 768*t^2 - 4096) - (27*(s+1)*(s+9)^3*t^2));
P1 := Curve(A2, s^3*(t^3 - 48*t^2 + 768*t^1 - 4096) - (27*(s+1)*(s+9)^3*t));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,1000);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[3];
Degree(DD);
      phi := DivisorMap(Divisor(DD));
      canC := Image(phi);
assert (Genus(canC) eq 1);
EE,p1 := EllipticCurve(canC,phi(pts[3]));
E,p2 := WeierstrassModel(EE);
MordellWeilShaInformation(EE);
ptsE := RationalPoints(E : Bound := 1000);
Factorization(HyperellipticPolynomials(E));
q0 := ptsE[1];
q1 := E![256000/36472996377170786403,0,1];
q2 := E![179200/36472996377170786403,0,1];
q3 := E![-435200/36472996377170786403,0,1]; 
Factorization(DivisionPolynomial(E,4));
q4 := E![486400/36472996377170786403,16384000/14130386091738734504764811067,1];
q1 eq 2*q4;
q5 := 3*q4;
q6 := q2+q4;
q7 := q2 + 3*q4;
ptsE := ptsE join {q1,q2,q3,q4,q5,q6,q7};

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(11),4)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(11),-4)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(11),-16)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(11),16)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(11),1)));

Evaluate(jmap(11),0);

//X_{H_11, G_3}(12) is a rank 0 elliptic curve with 6 CM points and 1 cuspidal point


/*----------------------------X_{H_12, G_3}(12)----------------------------------*/
C:= Curve(A2, s^3*(t^6 + 48*t^4 + 768*t^2 + 4096) - (27*(s+1)*(s+9)^3*t^2));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[2];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 1);
E,p1 := EllipticCurve(canC,phi(pts[1]));
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 4); 
ptsE := RationalPoints(EE : Bound := 100000);
Factorization(HyperellipticPolynomials(EE));
q1 := EE![435200/36472996377170786403,0,1];
q2 := EE![-179200/36472996377170786403,0,1];
q3 := EE![-256000/36472996377170786403,0,1]; 
ptsE := ptsE join {q1,q2,q3};
Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;
pts;

Evaluate(jmap(12),0);

//X_{H_12, G_3}(12) is a rank 0 elliptic curve with only a cuspidal point

/*----------------------------X_{H_13, G_3}(12)----------------------------------*/
jmap(13);
C:= Curve(A2, s^3*(t^6 - 144*t^4 + 6912*t^2 - 110592) - (27*(s+1)*(s+9)^3*(t^2-64)));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[2];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 0);
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[1]),Curve(P1));

//X_{H_13, G_3}(12) is a P^1

/*----------------------------X_{H_23, G_3}(12)----------------------------------*/ 
// Not necessary since it covers X_{H_11, G_3}(12)

/*----------------------------X_{H_24,G_3}(12)----------------------------------*/
C:= Curve(A2, s^3*(256*t^12 + 768*t^10 + 1536*t^8 + 1792*t^6 + 1536*t^4 + 768*t^2 + 256) - (27*(s+1)*(s+9)^3*(t^8 + 2*t^6 + t^4)));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
Genus(C);
PC := ProjectiveClosure(C);
//pts := PointSearch(PC,100);
pts:=RationalPoints(SingularSubscheme(PC));
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[3] + X[2]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[2];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 1);
E,p1 := EllipticCurve(canC,phi(pts[2]));
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 4); 
ptsE := RationalPoints(EE : Bound := 1000);
Factorization(HyperellipticPolynomials(EE));
q1 := EE![135150652/774034155408942101862118871339283,0,1];
q2 := EE![-38614472/774034155408942101862118871339283,0,1];
q3 := EE![-96536180/774034155408942101862118871339283,0,1];
ptsE := ptsE join {@q1, q2, q3@};
[Order(ptsE[i])  : i in [1..#ptsE]];

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

Evaluate(jmap(24),0);

//X_{H_24,G_3}(12) is a rank 0 elliptic curve with only 1 cuspidal point


/*----------------------------X_{H_25, G_3}(12)----------------------------------*/ 
// Not necessary since it covers X_{H_12, G_3}(12)

/*----------------------------X_{H_26, G_3}(12)----------------------------------*/ 
// Not necessary since it covers X_{H_11, G_3}(12)

/*----------------------------X_{H_27, G_3}(12)----------------------------------*/ 
// Not necessary since it covers X_{H_11, G_3}(12)

/*----------------------------X_{H_60, G_3}(12)----------------------------------*/ 
// Not needed since it covers X_{H_27, G_3}(12)


////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
// Level 3 entry is G_2 and G_1
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////

/*----------------------------X_{H_9, G_2}(12)----------------------------------*/
jmap(9);
C92:= Curve(A2, s^3*(t^6 + 144*t^4 + 6912*t^2 + 110592) - (t^2 + 64)*27*(s+1)^3*(s-3)^3);

// Notice that the all of the s terms appear to a cube and so we float a (t^2 + 64)^3 to both sides
C := Curve(A2, s^3 - (t^10 + 272*t^8 + 29440*t^6 + 1585152*t^4 + 42467328*t^2 + 452984832));
PointSearch(C,1000);
IsSingular(C92);
RationalPoints(SingularSubscheme(C92));
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
//pts:=RationalPoints(SingularSubscheme(PC));
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] + X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 1);
ptscC := PointSearch(canC,1000);
E,p1 := EllipticCurve(canC,ptscC[2]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 2);
ptsE := RationalPoints(E : Bound := 1000);

assert (#ptsE eq 2);
Phi := phi*p1;
for p in ptsE do 
Points(p@@Phi);
end for;

Evaluate(jmap(9),10);

// This is a rank 0 elliptic curve with a CM point

/*----------------------------X_{H_9, G_1}(12)----------------------------------*/
// Not needed since it covers X_{H_9, G_2}(12)


/*----------------------------X_{H_10,G_2}(12)----------------------------------*/
jmap(10);
C102:= Curve(A2, s^3*(t^6 + 2*t^4 + t^2) - ((1728*t^6 - 1728*t^4 + 576*t^2 - 64)*27*(s+1)^3*(s-3)^3));
CC102:= Curve(A2, s^3*(t^3 + 2*t^2 + t^1) - ((1728*t^3 - 1728*t^2 + 576*t^1 - 64)*27*(s+1)^3*(s-3)^3));
assert (Genus(CC102) eq 2);
boo, H102, phi := IsHyperelliptic(CC102);
assert (boo eq true);
HH102,phi2 := SimplifiedModel(H102);

assert (IsIsomorphic(HH92,HH102) eq true);

// Therefore, this is a rank 0 elliptic curve with a CM point


/*----------------------------X_{H_10, G_1}(12)----------------------------------*/
// Not needed since it covers X_{H_10, G_2}(12)


/*----------------------------X_{H_11, G_2}(12)----------------------------------*/
C:= Curve(A2, 27*(s+1)^3*(s-3)^3*t^2 - s^3*(t^6 - 48*t^4 + 768*t^2 - 4096));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,1000);ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] + X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(Divisor(DD)); //3
phi := DivisorMap(Divisor(DD));
      canC := Image(phi);
assert (Genus(canC) eq 1);
EE,p1 := EllipticCurve(canC,phi(pts[2]));
E,p2 := WeierstrassModel(EE);
MordellWeilShaInformation(E);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 4); 
ptsE := RationalPoints(E : Bound := 1000);
Factorization(HyperellipticPolynomials(E));
q1 := E![77530955920724061/400000000,0,1];
q2 := E![-11075850845817723/200000000,0,1];
q3 := E![-11075850845817723/80000000,0,1]; 
ptsE := ptsE join {q1,q2,q3};
Phi := phi*p1*p2;
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(11),4)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(11),-4)));

Evaluate(jmap(11),0);

//X_{H_11, G_2}(12) has 4 CM points and 1 cuspidal point


/*----------------------------X_{H_11, G_1}(12)----------------------------------*/
// not necessary since it covers X_{H_11, G_2}(12)


/*----------------------------X_{H_12, G_2}(12)----------------------------------*/
jmap(12);
C:= Curve(A2, 27*(s+1)^3*(s-3)^3*t^2 - s^3*(t^6 + 48*t^4 + 768*t^2 + 4096));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] + X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
      phi := DivisorMap(Divisor(DD));
      canC := Image(phi);
assert (Genus(canC) eq 1);
E,p1 := EllipticCurve(canC,phi(pts[5]));
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 8); 
ptsE := RationalPoints(EE : Bound := 1000);
Factorization(HyperellipticPolynomials(EE));
q0 := ptsE[1];
q1 := EE![3013602175584000,0,1];
q2 := EE![1205440870233600,0,1];
q3 := EE![-4219043045817600,0,1]; 
Factorization(DivisionPolynomial(EE,4));
q4 := EE![6629924786284800,461325017661217661952000,1];
q1 eq 2*q4;
q5 := 3*q4;
q6 := q2+q4;
q7 := q2 + 3*q4;
ptsE := ptsE join {q1,q2,q3,q4,q5,q6,q7};

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(12),8)));
HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(12),-8)));

Evaluate(jmap(12),0);

//X_{H_12, G_2}(12) has 4 CM points and 1 cusp



/*----------------------------X_{H_12, G_1}(12)----------------------------------*/
// Not necessary since it covers X_{H_12, G_2}(12)


/*----------------------------X_{H_13, G_2}(12)----------------------------------*/
C:= Curve(A2, 27*(s+1)^3*(s-3)^3*(t^2 - 64) - s^3*(t^6 - 144*t^4 + 6912*t^2 - 110592));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
assert (Genus(C) eq 1);
PC := ProjectiveClosure(C);
E,p1 := EllipticCurve(PC,PointSearch(PC,1000)[2]);
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 6); 
ptsE := RationalPoints(EE : Bound := 1000);
Factorization(HyperellipticPolynomials(EE));
q2 := EE![2507653251072,0,1]; // 2-torsion point
Factorization(DivisionPolynomial(EE,3));
IsSquare(Evaluate(HyperellipticPolynomials(EE),3761479876608));
q3 := EE![3761479876608, 2807929681968365568, 1];
ptsE := {q2,2*q2,q3,2*q3,q2+q3,q2+2*q3};

Phi := p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

Evaluate(jmap(13),8);

// X_{H_13, G_2}(12) is a rank 0 elliptic curve has 2 cuspidal points


/*----------------------------X_{H_13, G_1}(12)----------------------------------*/
// Not needed since it covers X_{H_13, G_2}(12) 

/*----------------------------X_{H_23, G_3}(12)----------------------------------*/ 
//Not needed since it covers X_{H_11, G_3}(12)

/*----------------------------X_{H_23, G_1}(12)----------------------------------*/ 
//Not needed since it covers X_{H_23, G_2}(12)

/*----------------------------X_{H_27,G_2}(12)----------------------------------*/ 
// Not needed since it covers X_{H_10,G_2}(12)

/*----------------------------X_{H_27,G_1}(12)----------------------------------*/ 
// Not needed since it covers X_{H_27,G_2}(12)

/*----------------------------X_{H_60,G_2}(12)----------------------------------*/ 
// Not needed since it covers X_{H_27, G_2}(12)

/*----------------------------X_{H_60,G_1}(12)----------------------------------*/ 
// Not needed since it covers X_{H_60, G_2}(12)


