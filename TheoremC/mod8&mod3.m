////////////////////////////////////////////////////////////////////////////////////
// Computations for the mod 8 and mod 3 simultaneous computations
////////////////////////////////////////////////////////////////////////////////////

load "entanglements.m";
A2<s,t> := AffineSpace(Rationals(),2);
GG:= GL(2,ResidueClassRing(4));



/*--Level 8, applicable subgroups that do contain level 4 subgroups of order 16 in kernel of reduction--*/
G16:=[i : i in [1..#newsublist] | newsublist[i][2] eq 8 and #{GG!g : g in newsublist[i][3]} eq 16];

//Now we exclude the groups that do not appear as a composite-(4,3) image of Galois where the mod 3 is G_3
BorelBad := [28,29,30,31,35,38,39,40,41,43,45,46,47,49,50,51,52,53,54,63,70,71,72,77,81,82,88,89,90,91,93,97,125,126,128,130, 131, 133, 137, 138, 143, 144, 145, 147,201,265,266];

//Now we exclude the groups that do not appear as a composite-(4,3) image of Galois where the mod 3 is G_4
NBad := [32,33,34,36,37,38,42,44,46,48,55,72,75,78,79,84,85,86,88,102,125,126,128,130, 131, 
133, 137, 138, 143, 144, 145, 147, 197,199,201,202,265,266];

//Possible for composite-(8,3) where rho_{E,3}~G_3(3)
G16B := [i : i in G16 | not (i in BorelBad) ]; 

//Possible subgroups for mixed-(8,3) where rho_{E,3}~G_4(3)
G16N := [i : i in G16 | not (i in NBad) ];


///////////////////////////////////////////////////
///////////////////////////////////////////////////
//Computations with level 3 being G_4
///////////////////////////////////////////////////
///////////////////////////////////////////////////


///////////////////////////////////////////////////
//Computations for subgroups lying above H11 x G4
///////////////////////////////////////////////////

/*----------------------------X_{H_28,G_4}(24)----------------------------------*/
jmap(28);
C:= Curve(A2, s^3*(t^4+ 8*t^2 + 16) - (16*t^12 + 384*t^10 + 3648*t^8 + 17408*t^6 + 43776*t^4 + 55296*t^2 + 27648));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,100);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
E,p1 := EllipticCurve(PC,pts[1]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 2); 
ptsE := RationalPoints(E : Bound := 1000);

for p in ptsE do
Points(p@@p1);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(28),0)));

// X_{H_28,G}(12) is a rank 0 elliptic curve with 1 CM point

/*----------------------------X_{H_29,G_4}(24)----------------------------------*/
jmap(29);
C:= Curve(A2, s^3*(t^12 + 4*t^10 - 4*t^8 - 32*t^6 - 16*t^4 + 64*t^2 + 64)- (1728*t^12 - 34560*t^10 + 251136*t^8 - 788480*t^6 + 1004544*t^4 - 552960*t^2 + 110592));
ptsC := PointSearch(C,100);
assert (Genus(C) eq 2);
boo,H,p := IsHyperelliptic(C);
assert (boo eq true);
ptsH := RationalPoints(H : Bound := 100);

//Now we want to show that the only points on H are the 2 known ones
J:= Jacobian(H);
assert (RankBound(J) eq 1);

//We attempt Chabauty's method. First, we need a generator of the free part of Jac
ptsJ := RationalPoints(J : Bound := 1000);
PJ := ptsJ[4];
heightconst := HeightConstant(J : Effort:=2, Factor); 
LogarithmicBound := Height(PJ) + heightconst;  // Bound on h(Q)
AbsoluteBound := Ceiling(Exp(LogarithmicBound));
PtsUpToAbsBound := Points(J : Bound:=AbsoluteBound );  
ReducedBasis([ pt : pt in PtsUpToAbsBound ]);
Height(PJ);

//This shows there are no points in J(Q) with canonical height smaller than that of PJ, so PJ is a generator 

Chabauty(PJ);

for q in ptsH do 
  Points(q@@p);
end for;

// X_{H_29,G_4}(24) is a genus 2 rank 1 curve with a 1 CM point

/*----------------------------X_{H_35,G_4}(24)----------------------------------*/
jmap(35);
C:= Curve(A2, s^3*(t^4 + 16*t^2 + 64)- (t^12 + 48*t^10 + 912*t^8 + 8704*t^6 + 43776*t^4 + 110592*t^2 + 110592));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,100);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
E,p1 := EllipticCurve(PC,pts[2]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 2); 
ptsE := RationalPoints(E : Bound := 1000);

for p in ptsE do
Points(p@@p1);
end for;

//X_{H_35,G_4}(24) is a rank 0 elliptic curve with 1 CM point


/*----------------------------X_{H_39,G_4}(24)----------------------------------*/
jmap(39);
C:= Curve(A2, s^3*(t^8- 32*t^6 + 384*t^4 - 2048*t^2 + 4096)
- (-t^12 + 48*t^10 - 192*t^8 - 14336*t^6 + 36864*t^4 + 1769472*t^2 + 7077888));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,100);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
E,p1 := EllipticCurve(PC,pts[2]);
EE,p2 := WeierstrassModel(E);
assert (Rank(EE) eq 1) and (#TorsionSubgroup(EE) eq 2); 

// X_{H_39,G_4}(24) is an elliptic curve with rank 1


/*----------------------------X_{H_41,G_4}(24)----------------------------------*/ 
jmap(41);
C:= Curve(A2, s^3*(t^12 - 4*t^10 - 4*t^8 + 32*t^6 - 16*t^4 - 64*t^2 + 64)
- (1728*t^12 + 34560*t^10 + 251136*t^8 + 788480*t^6 + 1004544*t^4 + 552960*t^2 + 
    110592));
assert (Genus(C) eq 2);
ptsC:= PointSearch(C,1000);
boo,H,p := IsHyperelliptic(C);
assert (boo eq true);
ptsH := RationalPoints(H : Bound := 100);

J := Jacobian(H);
assert (RankBound(J) eq 1);

A,m := AutomorphismGroup(H);
AA := [m(a) : a in A];
E,phi := CurveQuotient(AutomorphismGroup(H,[AA[4]]));
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 2);
ptsE := RationalPoints(E :Bound := 1000);
for P in ptsE do
  Points(P @@ phi);
end for;

for q in ptsH do
Points(q@@p);
end for;

//X_{H_41,G_4}(24) is a rank 1 genus 2 curve with only 1 CM point

/*----------------------------X_{H_43,G_4}(24)----------------------------------*/ 
jmap(43);
C:= Curve(A2, s^3*(t^4 - 8*t^2 + 16) - (16*t^12 - 384*t^10 + 3648*t^8 - 17408*t^6 + 43776*t^4 - 55296*t^2 + 27648));
ptsC := PointSearch(C,100);
IsSingular(C);
RationalPoints(SingularSubscheme(C));
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
E,p1 := EllipticCurve(PC,pts[2]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 6); 
ptsE := RationalPoints(E : Bound := 1000);
ptsE := ptsE join {ptsE[2] + ptsE[3], ptsE[2] + 2*ptsE[3]};

for p in ptsE do
Points(p@@p1);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(255^3));

// X_{H_43, G}(12) is a rank 0 elliptic curve with 3 CM points
 

/*----------------------------X_{H_45,G_4}(24)----------------------------------*/ 
jmap(45);
C:= Curve(A2, s^3*(t^4 - 16*t^2 + 64) - (t^12 - 48*t^10 + 912*t^8 - 8704*t^6 + 43776*t^4 - 110592*t^2 + 110592));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,100);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
E,p1 := EllipticCurve(PC,pts[2]);
EE,p2 := WeierstrassModel(E);
assert (Rank(EE) eq 1) and (#TorsionSubgroup(EE) eq 2); 

//X_{H_45,G_4}(24) is a rank 1 elliptic curve


/*----------------------------X_{H_47,G_4}(24)----------------------------------*/ 
jmap(47);
C:= Curve(A2, s^3*(t^8) - (-1024*t^12 + 768*t^8 - 192*t^4 + 16));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 0);
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[1]),Curve(P1)); 

//X_{H_47,G_4}(24) is a P^1


/*----------------------------X_{H_49,G_4}(24)----------------------------------*/ 
jmap(49);
C:= Curve(A2, s^3*(t^8+ 32*t^6 + 384*t^4 + 2048*t^2 + 4096) - (-t^12 - 48*t^10 - 192*t^8 + 14336*t^6 + 36864*t^4 - 1769472*t^2 + 7077888));
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
E,p1 := EllipticCurve(canC,phi(pts[2]));
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 2); 
ptsE := RationalPoints(EE : Bound := 1000);

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(49),0)));

//X_{H_49,G_4}(24) is a rank 0 elliptic curve with 1 CM point


/*----------------------------X_{H_50,G_4}(24)----------------------------------*/ 
jmap(50);
C:= Curve(A2, s^3*(t^4) - (t^12 - 48*t^8 + 768*t^4 - 4096));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,-15*X[2] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[2];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 0);
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[3]),Curve(P1)); //takes some time

//X_{H_50,G_4}(24) is a P^1

/*----------------------------X_{H_53,G_4}(24)----------------------------------*/ 
X53:= EllipticCurve([ 0, 0, 0, -4, 0 ]);
assert (Rank(X53) eq 0);

/*----------------------------X_{H_54,G_4}(24)----------------------------------*/ 
X54:= EllipticCurve([ 0, 0, 0, -1, 0 ]);
assert (Rank(X54) eq 0);



///////////////////////////////////////////////////
//Computations for subgroups lying above H12 x G4
///////////////////////////////////////////////////


/*----------------------------X_{H_30,G_4}(24)----------------------------------*/
jmap(30);
C:= Curve(A2, s^3*t^4- (t^12 + 48*t^8 + 768*t^4 + 4096));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,1000);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,17*X[1] +  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 0);
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[3]),Curve(P1));

//X_{H_30,G_4}(24) is a P^1


/*----------------------------X_{H_31,G_4}(24)----------------------------------*/
jmap(31);
C:= Curve(A2, s^3*t^8- (1024*t^12 + 768*t^8 + 192*t^4 + 16));
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
Phi := Parametrization(canC,canC!phi(pts[3]),Curve(P1));

//X_{H_31,G_4}(24) is a P^1

/*----------------------------X_{H_40,G_4}(24)----------------------------------*/ 
jmap(40);
C:= Curve(A2, s^3*(t^12 + 4*t^11 + 25/4*t^10 + 9/2*t^9 + 63/64*t^8 - 5/8*t^7 - 
    57/128*t^6 - 5/64*t^5 + 63/4096*t^4 + 9/1024*t^3 + 25/16384*t^2 + 1/8192*t +
    1/262144)
- (8000*t^12 + 9600*t^11 + 5040*t^10 + 2672*t^9 + 1587*t^8 + 636*t^7 + 413/2*t^6 +
    159/2*t^5 + 1587/64*t^4 + 167/32*t^3 + 315/256*t^2 + 75/256*t + 
    125/4096));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
Genus(C);
boo,H,p := IsHyperelliptic(C);
ptsH := RationalPoints(H : Bound := 1000);
assert boo eq true;

//Now we want to show that the only points on H are the 2 known ones
J:= Jacobian(H);
assert (RankBound(J) eq 2); 

//Since Rank = Genus, we cannot use Chabauty. Instead, notice that the hyper elliptic polynomial factors
P<x> := PolynomialRing(Integers());
Factorization(2*x^6 + 2);

//This code tells us what the decomposition of the Jacobian is, namely E x E’ where E,E’ have rank 1
A,m := AutomorphismGroup(H);
AA := [m(a) : a in A];
for a in AA do
E,phi := CurveQuotient(AutomorphismGroup(H,[a]));
if Genus(E) eq 1 then
MordellWeilShaInformation(E);
E;
end if;
end for;

//We now proceed with etale descent
A2<x1,y> := AffineSpace(Rationals(),2);
A3<x2,y1,y2> := AffineSpace(Rationals(),3);
for d in [1,-1,2,-2,3,-3,6,-6] do 
D := Curve(A3 , [d*y1^2 - 2*(x2^4 - x2^2 + 1) , d*y2^2 - (x2^2 + 1)]); //our double cover
Hd1 := QuadraticTwist(HyperellipticCurve(2*(x^4 - x^2 + 1)),d);
Hd2 := ProjectiveClosure(Curve(A2, d*y^2 - (x1^2 + 1)));
assert (Genus(Hd2) eq 0);
  if not IsLocallySolvable(Hd1,2) then
    "The twist of Hd1 by", d,"is not locally solvable at", 2;
  elif  not IsLocallySolvable(Hd1,3) then
    "The twist of Hd1 by", d, "is not locally solvable at", 3;
  else
    J1 := Jacobian(Hd1);
    [d,RankBound(J1)];
  end if;
  if not IsLocallySolvable(Hd2,2) then
    "The twist of Hd2 by", d,"is not locally solvable at", 2;
  elif  not IsLocallySolvable(Hd2,3) then
    "The twist of Hd2 by", d, "is not locally solvable at", 3;
  else 
    "The twist of Hd2 by",d,"is isomorphic to a P^1";
  end if;
  "*************************************";
end for;

//This tells us that the points on D must map to Hd1 where d = 2
d:=2;
ProHd1 := ProjectiveClosure(Curve(A2, d*y^2 - 2*(x1^4 - x1^2 +1)));
assert (Genus(ProHd1) eq 1);
ptsHd1 := Points(ProHd1);

//We now want to analyze the rational points on Hd1 twisted by 2
E,phi := EllipticCurve(ProHd1,Points(ProHd1)[1]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 8);
ptsE := RationalPoints(E : Bound := 1000);
[Order(ptsE[i]) : i in [1..#ptsE]];

//Now we pull back to points on Hd1 twisted by 2
for P in ptsE do
  Points(P @@ phi);
end for;
ptsHd1;

//We now pull back these points to D twisted by 2
D := Curve(A3 , [d*y1^2 - 2*(x2^4 - x2^2 + 1) , d*y2^2 - (x2^2 + 1)]);
Hd1:= Curve(A2, d*y^2 - 2*(x1^4 - x1^2 + 1));
pr := map<D -> Hd1 | [x2,y1]>;
ptsHd1 := {@ Hd1![1,1] , Hd1![0,-1], Hd1![0,1] , Hd1![-1,1], Hd1![1,-1], Hd1![-1,-1]@};
ptsD := {@@};
for P in ptsHd1 do
  ptsD := ptsD join {Points(P @@ pr)};
end for;
ptsD;

//One can check that the points on D map down to the points on H, hence we have found the points on C.

for q in ptsH do
Points(q@@p);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(20^3));

//X_{H_40,G_4}(24) is a rank 2, genus 2 curve with 3 CM points


/*----------------------------X_{H_51,G_4}(24)----------------------------------*/ 
//The model for X_{H51} is an elliptic curve
X51 := EllipticCurve([ 0, 0, 0, 4, 0 ]);
assert (Rank(X51) eq 0);

/*By Remark 7.1 of RZB, X51 only has CM or cuspidal points, therefore the fibered
product must only contain these points, so it is uninteresting to us */

/*----------------------------X_{H_52,G_4}(24)----------------------------------*/ 
X52:= EllipticCurve([ 0, 0, 0, 1, 0 ]);
assert (Rank(X52) eq 0);

/*----------------------------X_{H_63,G_4}(24)----------------------------------*/ 
// Not needed since it covers X_{H_35,G_4}(24)

/*----------------------------X_{H_70,G_4}(24)----------------------------------*/ 
C:= Curve(A2, s^3*(t^24 + 8*t^22 + 8*t^20 - 96*t^18 - 272*t^16 + 256*t^14 + 1792*t^12 + 1024*t^10 - 4352*t^8 - 6144*t^6 + 2048*t^4 + 8192*t^2 + 4096) - (1728*t^24 - 69120*t^22 + 1046016*t^20 - 7690240*t^18 + 32560128*t^16 - 104448000*t^14 + 234307584*t^12 - 417792000*t^10 + 520962048*t^8 - 492175360*t^6 + 267780096*t^4 - 70778880*t^2 + 7077888));
IsSingular(C);
ptsC := PointSearch(C,1000); ptsC;
assert (Genus(C) eq 2);
boo,H,p := IsHyperelliptic(C);
ptsH := RationalPoints(H : Bound := 1000);
assert boo eq true;
assert (RankBound(Jacobian(H)) eq 1);

//We find that the curve C maps to an elliptic curve with rank 0
A,m:=AutomorphismGroup(H);
AA := [m(a) : a  in A];
for a in AA do
E,phi := (CurveQuotient(AutomorphismGroup(H,[a])));
if Genus(E) eq 1 then
a;
MordellWeilShaInformation(E);
end if;
"**************************";
end for;

E,phi := (CurveQuotient(AutomorphismGroup(H,[AA[4]])));
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 2);
ptsE := RationalPoints(E : Bound :=1000);
for P in ptsE do
  Points(P @@ phi);
end for;

for q in ptsH do
Points(q@@p);
end for;

//X_{H_70,G_4}(24) is a genus 2, rank 1 curve has 1 CM point

/*----------------------------X_{H_71,G_4}(24)----------------------------------*/ 
// Not needed since it covers X_{H_43,G_4}(24)


/*----------------------------X_{H_77,G_4}(24)----------------------------------*/ 
// Not needed since it covers X_{H_29,G_4}(24)

/*----------------------------X_{H_81,G_4}(24)----------------------------------*/ 
// Not needed since it covers X_{H_28,G_4}(24)

/*----------------------------X_{H_82,G_4}(24)----------------------------------*/ 
// Not needed since it covers X_{H_35,G_4}(24)

/*----------------------------X_{H_89,G_4}(24)----------------------------------*/ 
jmap(89);
C:= Curve(A2, s^3*(t^20 - 4*t^19 - 10*t^18 + 60*t^17 + 17*t^16 - 384*t^15 + 208*t^14 + 1344*t^13 -1456*t^12 - 2688*t^11 + 4480*t^10 + 2688*t^9 - 7840*t^8 + 7936*t^6 - 3072*t^5 - 4096*t^4 + 3072*t^3 + 512*t^2 - 1024*t + 256) - (t^24 - 24*t^22 + 1032*t^20 - 3072*t^19 - 9440*t^18 + 46080*t^17 + 217584*t^16 - 1867776*t^15 + 4066560*t^14+ 2605056*t^13 - 9840896*t^12 - 164069376*t^11 + 1131869184*t^10 - 3816325120*t^9 + 8412270336*t^8 - 13212057600*t^7 + 15286355968*t^6 - 13151502336*t^5 + 8350402560*t^4 - 3814457344*t^3 + 1189453824*t^2 -227278848*t + 20123648));
assert (IsSingular(C) eq true);
assert (Genus(C) eq 2);
ptsC:=PointSearch(C,1000);

boo, h, phi1 := IsHyperelliptic(C);
assert (boo eq true);

//Now we want to determine the points on H and compute their pre-images
H,phi2 := SimplifiedModel(h);
J:= Jacobian(H);
assert (RankBound(J) eq 0);

//We can use Chabauty to compute the points on H
ptsH := Chabauty0(J);

//Then we compute the pre-images of these points on C
psi := phi1*phi2;
for P in ptsH do
  Points(P @@ psi);
end for;

//X_{H_89,G_4}(24) is a rank 0 genus 2 curve with no points

/*----------------------------X_{H_90,G_4}(24)----------------------------------*/ 
// Not needed since it covers X_{H_28,G_4}(24)

/*----------------------------X_{H_91,G_4}(24)----------------------------------*/ 
jmap(91);
C:= Curve(A2, s^3*(t^20 - 16*t^18 + 112*t^16 - 448*t^14 + 1120*t^12 - 1792*t^10 + 1792*t^8 - 1024*t^6 + 256*t^4) - (-t^24 + 24*t^22 + 504*t^20 - 10528*t^18 - 118512*t^16 + 1254144*t^14 + 12859648*t^12 + 5016576*t^10 - 1896192*t^8 - 673792*t^6 + 129024*t^4 + 24576*t^2 - 4096));
ptsC := PointSearch(C,1000);
IsSingular(C);
assert (Genus(C) eq 2);
boo, h, phi1 := IsHyperelliptic(C);
assert (boo eq true);

//Now we want to determine the points on H and compute their pre-images
H,phi2 := SimplifiedModel(h);
J:= Jacobian(H);
assert (RankBound(J) eq 1);

//We attempt Chabauty's method. First, we need a generator of the free part of Jac
ptsJ := RationalPoints(J : Bound := 1000);
ptsH := RationalPoints(H : Bound := 1000);
[J![ptsH[i],ptsH[1]] : i in [2..#ptsH]];
PJ := ptsJ[4];
heightconst := HeightConstant(J : Effort:=2, Factor); 
LogarithmicBound := Height(PJ) + heightconst;  // Bound on h(Q)
AbsoluteBound := Ceiling(Exp(LogarithmicBound));
PtsUpToAbsBound := Points(J : Bound:=AbsoluteBound );  
PJ := J!ReducedBasis([ pt : pt in PtsUpToAbsBound ])[1];

//This shows there are no points in J(Q) with canonical height smaller than that of PJ, so PJ is a generator 

Chabauty(PJ);

//Now we compute pre-images
psi := phi1*phi2;
for P in ptsH do
  Points(P @@ psi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(255^3));

// X_{H_91,G_4}(24) is a rank 1, genus 2 curve with only 4 CM points

/*----------------------------X_{H_93,G_4}(24)----------------------------------*/ 
jmap(93);
C:= Curve(A2, s^3*(t^16 + 8*t^15 + 20*t^14 - 8*t^13 - 130*t^12 - 200*t^11 + 108*t^10 + 648*t^9 + 577*t^8 - 384*t^7 - 1128*t^6 - 704*t^5 + 248*t^4 + 640*t^3 + 416*t^2 + 128*t + 16) - (t^24 - 24*t^22 + 312*t^20 + 192*t^19 - 2240*t^18 - 2880*t^17 + 9504*t^16 + 24576*t^15 - 70656*t^13 -106496*t^12 + 24576*t^11 + 466944*t^10 + 1269760*t^9 + 2221056*t^8 + 2949120*t^7 + 3186688*t^6 + 2850816*t^5 + 2088960*t^4 + 1245184*t^3 + 589824*t^2 + 196608*t + 32768));
ptsC := PointSearch(C,1000);

boo, h, phi1 := IsHyperelliptic(C);
assert (boo eq true);

//Now we want to determine the points on H and compute their pre-images
H,phi2 := SimplifiedModel(h);
J:= Jacobian(H);
assert (RankBound(J) eq 0);

//We use Chabauty to determine the points on H
ptsH:= Chabauty0(J);

//Now we take the pre-images of these known points
psi := phi1*phi2;
for P in ptsH do
  Points(P @@ psi);
end for;

//X_{H_93,G_4}(24) is a rank 0, genus 2 curve with no points


/*----------------------------X_{H_97,G_4}(24)----------------------------------*/ 
jmap(97);
C:= Curve(A2, s^3*(t^24 - 4*t^23 - t^22 + 23*t^21 - 143/8*t^20 - 
    195/4*t^19 + 1027/16*t^18 + 693/16*t^17 - 23185/256*t^16 - 301/32*t^15 + 7807/128*t^14 - 757/128*t^13 - 
    20521/1024*t^12 + 757/512*t^11 + 7807/2048*t^10 + 301/2048*t^9 - 23185/65536*t^8 - 693/16384*t^7 + 
    1027/65536*t^6 + 195/65536*t^5 - 143/524288*t^4 - 23/262144*t^3 - 1/1048576*t^2 + 1/1048576*t + 1/16777216) - (1728*t^24 + 34560*t^23 + 256320*t^22 + 866240*t^21 + 1388376*t^20 + 1219920*t^19 + 320580*t^18 - 374220*t^17 - 
    1529163/4*t^16 - 51850*t^15 + 182565/2*t^14 + 52275/2*t^13 - 279891/16*t^12 - 52275/8*t^11 + 182565/32*t^10 
    + 25925/32*t^9 - 1529163/1024*t^8 + 93555/256*t^7 + 80145/1024*t^6 - 76245/1024*t^5 + 173547/8192*t^4 - 
    13535/4096*t^3 + 4005/16384*t^2 - 135/16384*t + 27/262144));
ptsC := PointSearch(C,1000);
assert (Genus(C) eq 2);
boo, h, phi := IsHyperelliptic(C);
assert (boo eq true);

//We handled the rational points on this curve in X(H40,G4)

//We check that the known points on H pull-back to our known points on C
ptsH:= RationalPoints(h : Bound := 1000);
for P in ptsH do
  Points(P @@ phi);
end for;
ptsC;

//_{H_97,G_4}(24) is a rank 2, genus 2 curve with 3 CM points


///////////////////////////////////////////////////
///////////////////////////////////////////////////
//Computations with level 3 being G_3
///////////////////////////////////////////////////
///////////////////////////////////////////////////

///////////////////////////////////////////////////
//Computations for subgroups lying above H9 x G3
///////////////////////////////////////////////////

/*----------------------------X_{H_37,G_3}(24)----------------------------------*/ 
C:= Curve(A2, 27*(s+1)*(s+9)^3*(t^12 + 5*t^11 + 11*t^10 + 113/8*t^9 + 759/64*t^8 + 221/32*t^7 + 23/8*t^6 + 221/256*t^5 + 759/4096*t^4 + 113/4096*t^3 + 11/4096*t^2 + 5/32768*t + 1/262144)- s^3*(10976*t^12 + 28224*t^11 + 37128*t^10 + 32616*t^9 + 42297/2*t^8 + 10602*t^7 + 16807/4*t^6 + 5301/4*t^5 + 42297/128*t^4 + 4077/64*t^3 + 4641/512*t^2 + 441/512*t + 343/8192));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,10000);
Genus(C);

//Let's change the lay of the land
SN := SubfieldLattice(SplittingField(Numerator(jmap(37))));
SD := SubfieldLattice(SplittingField(Denominator(jmap(37))));
P<x> := PolynomialRing(Rationals());
NN := NumberField(x^2 + x + 1/8);

Q2<A> := PolynomialRing(NN);
Factorization(Q2!Denominator(jmap(37)));
CN<a,b> := BaseExtend(C,NN);
IsSingular(CN);
ptsC := RationalPoints(SingularSubscheme(CN));

PC := ProjectiveClosure(CN);
pts:= {@PC![0,-NN.1 - 1,1],PC![0,NN.1,1]@};
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
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 2); 
ptsE := RationalPoints(EE : Bound := 1000);

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(49),0)));

//X_{H_49,G_4}(24) is a rank 0 elliptic curve with only 1 CM point

///////////////////////////////////////////////////
//Computations for subgroups lying above H10 x G3
///////////////////////////////////////////////////

/*----------------------------X_{H_42,G_3}(24)----------------------------------*/ 
C:= Curve(A2, 27*(s+1)*(s+9)^3*(t^12 + 16*t^11 + 112*t^10 + 384*t^9 + 192*t^8 - 4096*t^7 - 
    18432*t^6 - 32768*t^5 + 12288*t^4 + 196608*t^3 + 458752*t^2 + 524288*t + 262144)- s^3*(128*t^12 - 3072*t^11 + 303104*t^9 + 417792*t^8 - 11403264*t^7 - 58720256*t^6 - 91226112*t^5 + 26738688*t^4 + 
    155189248*t^3 - 100663296*t + 33554432));
PointSearch(C,100);
PC<S,T,Z> := ProjectiveClosure(C);
pts := Points(PC);
assert (Genus(PC) eq 1);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 1);
E := Jacobian(canC);
assert (Rank(E) eq 0);
//E,phi := EllipticCurve(PC,pts[1]);

//There is probably some point on this curve that we must find by hand then we can map to a probably rank 0 curve and determine the points from there


///////////////////////////////////////////////////
//Computations for subgroups lying above H13 x G3
///////////////////////////////////////////////////

/*----------------------------X_{H_32,G_3}(24)----------------------------------*/ 
C:= Curve(A2, 27*(s+1)*(s+9)^3*(t^4 + 16*t^2) - s^3*(t^12 + 48*t^10 + 816*t^8 + 5632*t^6 + 13056*t^4 + 12288*t^2 + 4096));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,100);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
E,p1 := EllipticCurve(PC,pts[2]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 4); 
ptsE := RationalPoints(E : Bound := 1000);
Factorization(HyperellipticPolynomials(E));
p0 := E![2613645484861685760,0,1];
p2 := E![1725198983926382592,0,1];
p3 := E![1429050150281281536,0,1];
ptsE := ptsE join {p0,p2,p3};

for p in ptsE do
Points(p@@p1);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(32),0)));

//X_{H_49,G_4}(24) is a rank 0 elliptic curve with 1 cuspidal point


/*----------------------------X_{H_33,G_3}(24)----------------------------------*/ 
C:= Curve(A2, 27*(s+1)*(s+9)^3*(t^4 + 8*t^2) - s^3*(16*t^12 + 384*t^10 + 3264*t^8 + 11264*t^6 + 13056*t^4 + 6144*t^2 + 1024));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,100);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
RationalPoints(SingularSubscheme(PC));
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
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
q1 := EE![12400927/3643620828036547425256544429016,0,1];
q2 := EE![-1771561/1821810414018273712628272214508,0,1];
q3 := EE![-8857805/3643620828036547425256544429016,0,1];
ptsE := ptsE  join {q1,q2,q3};
Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

HasComplexMultiplication(EllipticCurveWithjInvariant(Evaluate(jmap(49),0)));

//X_{H_33,G_3}(24) is a rank 0 elliptic curve with 1 cuspidal point


/*----------------------------X_{H_34,G_3}(24)----------------------------------*/ 
C:= Curve(A2, 27*(s+1)*(s+9)^3*(t^4 - 2*t^2) - s^3*(4096*t^12 - 24576*t^10 + 52224*t^8 - 45056*t^6 + 13056*t^4 - 1536*t^2 + 64));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,100);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
RationalPoints(SingularSubscheme(PC));
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
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
q1 := EE![8857805/955153338344812688246451582799970304,0,1];
q2 := EE![1771561/477576669172406344123225791399985152,0,1];
q3 := EE![-12400927/955153338344812688246451582799970304,0,1];
ptsE := ptsE  join {q1,q2,q3};
Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

//X_{H_34,B}(24) is a rank 0 elliptic curve with 1 cuspidal point

/*----------------------------X_{H_36,G_3}(24)----------------------------------*/ 
C:= Curve(A2, 27*(s+1)*(s+9)^3*(t^4 - 16*t^2) - s^3*(t^12 - 48*t^10 + 816*t^8 - 5632*t^6 + 13056*t^4 - 12288*t^2 + 4096));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,1000);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
RationalPoints(SingularSubscheme(PC));
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD);
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(canC) eq 1);
E,p1 := EllipticCurve(canC,phi(pts[2]));
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 8); 
ptsE := RationalPoints(EE : Bound := 1000);
Factorization(HyperellipticPolynomials(EE));
q1 := EE![512000/788144978714283523382427,0,1];
q2 := EE![204800/788144978714283523382427,0,1];
q3 := EE![-102400/112592139816326217626061,0,1];
Factorization(DivisionPolynomial(EE,4));
q4 := EE![1126400/788144978714283523382427,65536000/44885496419288200145279031944980041,1];
q5 := EE![-102400/788144978714283523382427,65536000/134656489257864600435837095834940123,1 ];
q6 := -q4;
q7 := -q5;
ptsE := ptsE join {q1,q2,q3,q4,q5,q6,q7};

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

//X_{H_36,B}(24) is a rank 0 elliptic curve with 3 cuspidal points


/*----------------------------X_{H_44,G_3}(24)----------------------------------*/ 
C:= Curve(A2, 27*(s+1)*(s+9)^3*(t^10 - 8*t^8 + 24*t^6 - 32*t^4 + 16*t^2)- s^3*(8*t^12 + 672*t^10 + 18912*t^8 + 180992*t^6 + 75648*t^4 + 10752*t^2 + 512));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,1000);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
RationalPoints(SingularSubscheme(PC));
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] - X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
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
q1 := EE![256748383655686997168430007569404738795497326161049818234880,0,1];
q2 := EE![102699353462274798867372003027761895518198930464419927293952,0,1];
q3 := EE![-359447737117961796035802010597166634313696256625469745528832,0,1];
ptsE := ptsE join {q1,q2,q3};

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

//X_{H_44,B}(24) is a rank 0 elliptic curve with 1 cuspidal point

/*----------------------------X_{H_48,G_3}(24)----------------------------------*/ 
C:= Curve(A2, 27*(s+1)*(s+9)^3*(t^10 + 8*t^8 + 24*t^6 + 32*t^4 + 16*t^2)
- s^3*(-8*t^12 + 672*t^10 - 18912*t^8 + 180992*t^6 - 75648*t^4 + 10752*t^2 - 512));
IsSingular(C);
RationalPoints(SingularSubscheme(C));
ptsC := PointSearch(C,1000);
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
E,p1 := EllipticCurve(canC,phi(pts[1]));
EE,p2 := WeierstrassModel(E);
MordellWeilShaInformation(EE);
assert (Rank(EE) eq 0) and (#TorsionSubgroup(EE) eq 4); 
ptsE := RationalPoints(EE : Bound := 1000);
Factorization(HyperellipticPolynomials(EE));
q1 := EE![256748383655686997168430007569404738795497326161049818234880,0,1];
q2 := EE![102699353462274798867372003027761895518198930464419927293952,0,1];
q3 := EE![-359447737117961796035802010597166634313696256625469745528832,0,1];
ptsE := ptsE join {q1,q2,q3};

Phi := phi*p1*Extend(p2);
for p in ptsE do
Points(p@@Phi);
end for;

// X_{H_48,B}(24) is a rank 0 elliptic curve 



