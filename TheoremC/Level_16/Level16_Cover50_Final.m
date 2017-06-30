load "entanglements.m";
curgp := [152,154,155,156,171];
jMap := {@@};

P<x,y,z> := PolynomialRing(Rationals(),3);
X11 := eval Read("eq11.txt");
X50 := eval Read("eq50.txt");
a50 := X50.1;
b50 := X50.2;
map50to11 := map<X50 -> X11 | [a50^2,b50^2]>;


X6 := eval Read("eq6.txt");
X11 := eval Read("eq11.txt");
a11 := X11.1;
b11 := X11.2;
map11to6 := map<X11 -> X6 | [a11^2 - 16*b11^2,b11^2]>;

X1 := eval Read("eq1.txt");
X6 := eval Read("eq6.txt");
a6 := X6.1;
b6 := X6.2;
map6to1 := map<X6 -> X1 | [a6^3,a6*b6^2 + 16*b6^3]>;


for i in [1..#curgp] do
covernum := newsublist[curgp[i]][7];
filename1 := Sprintf("%omap%o.txt",curgp[i],covernum);
maptocover := eval Read(filename1);
X := Domain(maptocover);
f1 := map<X6 -> X1  | DefiningEquations(map6to1)>;
f2 := map<X11 -> X6  | DefiningEquations(map11to6)>;
f3 := map<X50 -> X11  | DefiningEquations(map50to11)>;
f4 := map<X -> X50  | DefiningEquations(maptocover)>;
D:=DefiningEquations(f4*f3*f2*f1);
jMap := jMap join {@[curgp[i],P!DefiningEquation(X),P!D[1],P!D[2]]@};
end for;

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


A3<x,y,s> := AffineSpace(Rationals(),3);
QQ<T> := PolynomialRing(Rationals());


/*----------------------------X_{H_152,N_{ns}}(48)----------------------------------*/
assert (152 eq curgp[1]);
C1 := Scheme(A3 , [Evaluate(jMap[1][2],[x,y,1]), Evaluate(jMap[1][3],[x,1,1]) - s^3*Evaluate(jMap[1][4],[x,1,1])]);
PC1<X,Y,S,Z> := Curve(ProjectiveClosure(C1));
assert (Genus(PC1) eq 3);
boo, h1 , phi1 := IsHyperelliptic(PC1); 
assert (boo eq true);
J1 := Jacobian(h1);
// assert (RankBound(J1) eq 0); This stalls

//Quotients is the easiest way to find the points

A2<A,B> := AffineSpace(Rationals(),2);
c1 := Curve(A2 , A^2 - (-2*B^7 - 16*B));
Pc1<a,b,c> := ProjectiveClosure(c1); 
aut1 := AutomorphismGroup(Pc1);
q1,phiq1 := CurveQuotient(AutomorphismGroup(Pc1,[aut1.1]));
Quo1,phiq2 := CurveQuotient(AutomorphismGroup(Pc1,[aut1.2]));
assert (Genus(q1) eq 0) and (Genus(Quo1) eq 2);
Jq2 := Jacobian(Quo1);
assert (RankBound(Jq2) eq 0);
ptsq2 := Chabauty0(Jq2);
for P in ptsq2 do 
  Points(P@@phiq2);
end for;
ptsh := RationalPoints(h1 : Bound := 1000); //Only known points
for P in ptsh do
  Points(P@@phi1);
end for;

// X_{H_152,N_{ns}}(48) is a genus 3 hyperelliptic curve

/*----------------------------X_{H_154,N_{ns}}(48)----------------------------------*/
assert (154 eq curgp[2]);
C2 := Scheme(A3 , [Evaluate(jMap[2][2],[x,y,1]), Evaluate(jMap[2][3],[x,1,1]) - s^3*Evaluate(jMap[2][4],[x,1,1])]);
C2 := Curve(C2);
assert (Genus(C2) eq 3);
boo, h2 , phi2 := IsHyperelliptic(C2); 
assert (boo eq true);
J2 := Jacobian(h2);
aut, m := AutomorphismGroup(h2);
assert (#aut eq 4); // we have extra automorphisms
//assert (RankBound(J2) eq 0);

// We rewrite the equation in affine space since Magmas intrinsics for automorphisms of hyper elliptic curves is a bit strange

A2<A,B> := AffineSpace(Rationals(),2);
c2 := Curve(A2 , A^2 - (-B^7 + 8*B));
Pc2<a,b,c> := ProjectiveClosure(c2); 
aut2 := AutomorphismGroup(Pc2);
q1,phiq1 := CurveQuotient(AutomorphismGroup(Pc2,[aut2.1]));
Quo2,phiq2 := CurveQuotient(AutomorphismGroup(Pc2,[aut2.2]));
assert (Genus(q1) eq 0) and (Genus(Quo2) eq 1);
assert (Rank(Quo2) eq 0);
ptsq2 := RationalPoints(Quo2 : Bound := 1000);
for P in ptsq2 do 
  Points(P@@phiq2);
end for;
ptsh := RationalPoints(h2 : Bound := 1000); //Only known points
for P in ptsh do
  Points(P@@phi2);
end for;

// X_{H_154,N_{ns}}(48 is a genus 3 hyperelliptic curve

/*----------------------------X_{H_155,N_{ns}}(48)----------------------------------*/
assert (155 eq curgp[3]);
C3 := Scheme(A3 , [Evaluate(jMap[3][2],[x,y,1]), Evaluate(jMap[3][3],[x,1,1]) - s^3*Evaluate(jMap[3][4],[x,1,1])]);
PC3<X,Y,S,Z> := Curve(ProjectiveClosure(C3));
assert (Genus(PC3) eq 3);
boo, h3 , phi3 := IsHyperelliptic(PC3); 
assert (boo eq true);
J3 := Jacobian(h3);
// assert (RankBound(J3) eq 3);

//Taking quotients does not resolve our problem

//We now proceed with etale descent
Factorization(PolynomialRing(Integers())!HyperellipticPolynomials(h3));
AA2<x1,y> := AffineSpace(Rationals(),2);
AA3<x2,y1,y2> := AffineSpace(Rationals(),3);
P<t> := PolynomialRing(Rationals());
for d in [1,-1,2,-2,3,-3,6,-6] do 
D := Curve(AA3 , [d*y1^2 - x2*(x2^2 - 2) , d*y2^2 - 2*(x2^4 + 2*x2^2 + 4)]); //our double cover
Hd1 := QuadraticTwist(HyperellipticCurve(t*(t^2 - 2) ),d);
Hd2 := QuadraticTwist(HyperellipticCurve(2*(t^4 + 2*t^2 + 4)),d);
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
     J2 := Jacobian(Hd2);
    [d,RankBound(J2)];
  end if;
  "*************************************";
end for;

//This tells us that the points on D must map to Hd1 and Hd2 where d = 2
d:=2;
E := QuadraticTwist(EllipticCurve(t*(t^2 - 2)),d);
assert (Rank(E) eq 0);
ptsE := RationalPoints(E : Bound := 1000);
assert (#TorsionSubgroup(E) eq #ptsE);

Hd2 := ProjectiveClosure(Curve(AA2, d*y^2 - 2*(x1^4 + 2*x1^2 +4)));
assert (Genus(Hd2) eq 1);
ptsHd2 := Points(Hd2);
E2,phiE2 := EllipticCurve(Hd2,ptsHd2[2]);
ptsE2 := RationalPoints(E2 : Bound := 1000);
assert (RankBound(E2) eq 0);
assert (#TorsionSubgroup(E2) eq #ptsE2);
ptsHd2 := {@@};
for P in ptsE2 do
  ptsHd2 := ptsHd2 join {Points(P@@phiE2)};
end for;
ptsHd2 := ptsHd2[1];

D := Curve(AA3 , [d*y1^2 - x2*(x2^2 - 2) , d*y2^2 - 2*(x2^4 + 2*x2^2 + 4)]); 
Hd1:= Curve(AA2, d*y^2 - x1*(x1^2 - 2));
Hd2:= Curve(AA2, d*y^2 - 2*(x1^4 + 2*x1^2 + 4));
pr1 := map<D -> Hd1 | [x2,y1]>;
pr2 := map<D -> Hd2 | [x2,y2]>;
ptsHd1 := {@ Hd1![0,0]@};
ptsHd2 := {@ Hd2![0,-2] , Hd2![0,2]@};
ptsD := {@@};
for P in ptsHd1 do
  ptsD := ptsD join {Points(P @@ pr1)};
end for;
for P in ptsHd2 do
  ptsD := ptsD join {Points(P @@ pr2)};
end for;
ptsD;

ptsh3 := RationalPoints(h3 : Bound := 1000);
for P in ptsh3 do
  Points(P@@phi3);
end for;

// X_{H_155,N_{ns}}(48) is a genus 3 hyperelliptic curve
// These points are CM and correspond to elliptic curves with j-invariant = 0.


/*----------------------------X_{H_156,N_{ns}}(48)----------------------------------*/
A3<x,y,s> := AffineSpace(Rationals(),3);
assert (156 eq curgp[4]);
C4 := Scheme(A3 , [Evaluate(jMap[4][2],[x,y,1]), Evaluate(jMap[4][3],[x,1,1]) - s^3*Evaluate(jMap[4][4],[x,1,1])]);
PC4<X,Y,S,Z> := Curve(ProjectiveClosure(C4));
assert (Genus(PC4) eq 3);
boo, h4 , phi4 := IsHyperelliptic(PC4); 
assert (boo eq true);
J4 := Jacobian(h4);
assert (RankBound(J4) eq 3);

/*Our initial attempt is using etale descent. Since we have a linear factors x from h4, we can simply consider the twisted genus 2 hyperelliptic curve t^6 + 8. We determine the points on these twist then pull back */

AA2<x1,y> := AffineSpace(Rationals(),2);
AA3<x2,y1,y2> := AffineSpace(Rationals(),3);
D := Curve(AA3 , [y1^2 - x2 , y2^2 - (-x2^6 - 8)]);
PP<t> := PolynomialRing(Rationals());
/*It suffices to study the points on the hyper elliptic curve y^2 = -x^6 - 8. */

//Checking which twists we need to analyze
for d in [1,-1,2,-2,3,-3,6,-6] do 
Hd2:= QuadraticTwist(HyperellipticCurve(-t^6 - 8),d);   
if not IsLocallySolvable(Hd2,2) then
    "The twist of Hd2 by", d,"is not locally solvable at", 2;
  elif  not IsLocallySolvable(Hd2,3) then
    "The twist of Hd2 by", d, "is not locally solvable at", 3;
  else
     J2 := Jacobian(Hd2);
    [d,RankBound(J2)];
  end if;
  "*************************************";
end for;
/*It suffices to study the points on the hyper elliptic curve y^2 = -x^6 - 8. */


//Finding points on twist by -1
d:=-1;
H2 := Curve(AA2, d*y^2 - (-x1^6 - 8));
h2 := ProjectiveClosure(H2);
aut := AutomorphismGroup(h2);
E,phi := (CurveQuotient(AutomorphismGroup(h2,[Generators(aut)[2]])));
assert (Rank(E) eq 0);
ptsE := RationalPoints(E : Bound := 1000);
assert (#TorsionSubgroup(E) eq #ptsE);
for P in ptsE do
  Points(P@@phi);
end for;

//Finding points on twist by -2
d:= -2;
Hd2:= QuadraticTwist(HyperellipticCurve(-t^6 - 8),d);
J:=Jacobian(Hd2);
assert (RankBound(J) eq 1);
//We attempt Chabauty's method. First, we need a generator of the free part of Jac
ptsJ := RationalPoints(J : Bound := 1000);
PJ := ptsJ[2];
heightconst := HeightConstant(J : Effort:=2, Factor); 
LogarithmicBound := Height(PJ) + heightconst;  // Bound on h(Q)
AbsoluteBound := Ceiling(Exp(LogarithmicBound));
PtsUpToAbsBound := Points(J : Bound:=AbsoluteBound );  
ReducedBasis([ pt : pt in PtsUpToAbsBound ]);
Height(PJ);
PJ := ReducedBasis([ pt : pt in PtsUpToAbsBound ])[1];
Chabauty(PJ);
ptsHd2 := RationalPoints(Hd2 : Bound := 1000); //These are all of the points

//Pulling back points to D
d:= [-1,-2];
H1 := Curve(AA2, -y^2 - (-x1^6 - 8));
ptsH1 := {H1![-1,3], H1![1,3], H1![-1,-3], H1![1,-3]};
H2 := Curve(AA2, -2*y^2 - (-x1^6 - 8));
ptsH2 := {H2![0,-2], H2![0,2] , H2![-2,-6], H2![-2,6], H2![2,-6], H2![2,6]};
ptsD1 := {@@};
for P in ptsH1 do
  d:= -1;
  D := Curve(AA3 , [d*y1^2 - x2 , d*y2^2 - (-x2^6 - 8)]);
  pr1 := map<D -> H1 | [x2,y2]>;
  ptsD1 := ptsD1 join {Points(P @@ pr1)};
end for;
ptsD2:={@@};
for P in ptsH2 do
  d:= -2;
  D := Curve(AA3 , [d*y1^2 - x2 , d*y2^2 - (-x2^6 - 8)]);
  pr2 := map<D -> H2 | [x2,y2]>;
  ptsD2 := ptsD2 join {Points(P @@ pr2)};
end for;

//Check by hand that these points do come from h4
ptsD1;
ptsD2;
ptsh4 := RationalPoints(h4 : Bound := 1000);

for P in ptsh4 do
  Points(P@@phi4);
end for;

v1 := Evaluate(jMap[4][3],[1,-3,1])/Evaluate(jMap[4][4],[1,-3,1]);
v2 := Evaluate(jMap[4][3],[1,3,1])/Evaluate(jMap[4][4],[1,3,1]);
v3 := Evaluate(jMap[4][3],[8,-24,1])/Evaluate(jMap[4][4],[8,-24,1]);
v4 := Evaluate(jMap[4][3],[8,24,1])/Evaluate(jMap[4][4],[8,24,1]);

assert (v1 eq v2) and (v1 eq -15^3);
assert (v3 eq v4) and (v3 eq 255^3);

// X_{H_156,N_{ns}}(48) is a genus 3 hyperelliptic curve
// Both of these are CM points

/*----------------------------X_{H_171,N_{ns}}(48)----------------------------------*/
A3<x,y,s> := AffineSpace(Rationals(),3);
assert (171 eq curgp[5]);
C5 := Scheme(A3 , [Evaluate(jMap[5][2],[x,y,1]), Evaluate(jMap[5][3],[x,1,1]) - s^3*Evaluate(jMap[5][4],[x,1,1])]);
C5 := Curve(C5);
assert (Genus(C5) eq 6);
boo, h5 , phi5 := IsHyperelliptic(C5); 
assert (boo eq true);
J5 := Jacobian(h5);
// assert (RankBound(J5) eq 0);
ptsh5 := RationalPoints(h5 : Bound:=1000);


//Computing possible torsion orders of Jacobians
torsOrders := {@@};
bad := BadPrimes(h5);
bool := false; p := 2;
while  p le 30 do
  p :=  NextPrime(p);        
  p := p in bad select NextPrime(p) else p;
  pvalues := {@@};
  F := FiniteField(p);
  PF<A> := PolynomialRing(F);
  Hp := HyperellipticCurve(-A^13 + 64*A);
  numH := Numerator(ZetaFunction(Hp));  
  torsOrders :=   torsOrders join  {@ Evaluate(numH,1) @};
  [p,GCD(torsOrders)];
  Invariants(ClassGroup(Hp));
  "*******************";
end while;

// From these results, it appears that J5[tor] = (Z/2)^6
// all of the two torsion comes from the splitting field of the defining equation, and so 
// if we can identify all of the torsion in J5, we can easily conclude 

S := SplittingField(HyperellipticPolynomials(h5));
P<w> := PolynomialRing(S);
R := Roots(-w^13 + 64*w);
p0 := BaseChange(h5,S)![1,0,0];
p1 := BaseChange(h5,S)![R[1,1],0,1];
p2 := BaseChange(h5,S)![R[2,1],0,1];
p3 := BaseChange(h5,S)![R[3,1],0,1];
p4 := BaseChange(h5,S)![R[4,1],0,1];
p5 := BaseChange(h5,S)![R[5,1],0,1];
p6 := BaseChange(h5,S)![R[6,1],0,1];
p7 := BaseChange(h5,S)![R[7,1],0,1];
p8 := BaseChange(h5,S)![R[8,1],0,1];
p9 := BaseChange(h5,S)![R[9,1],0,1];
p10 := BaseChange(h5,S)![R[10,1],0,1];
p11 := BaseChange(h5,S)![R[11,1],0,1];
p12 := BaseChange(h5,S)![R[12,1],0,1];
p13 := BaseChange(h5,S)![R[13,1],0,1];

D := DivisorGroup(BaseChange(h5,S));
d0 := D!Divisor(p0);
d1 := D!Divisor(p1);
d2 := D!Divisor(p2);
d3 := D!Divisor(p3);
d4 := D!Divisor(p4);
d5 := D!Divisor(p5);
d6 := D!Divisor(p6);
d7 := D!Divisor(p7);
d8 := D!Divisor(p8);
d9 := D!Divisor(p9);
d10 := D!Divisor(p10);
d11 := D!Divisor(p11);
d12 := D!Divisor(p12);
d13 := D!Divisor(p13);

// Checking that we have linearly independent generators for the torsion

D1 := d1 - d0;
assert (order(D1) eq 2);

D2 := d2 - d0;
assert (order(D2) eq 2);
assert (IsLinearlyEquivalent(D2,D1) eq false);

D3 := d3 - d0;
assert (order(D3) eq 2);
assert (IsLinearlyEquivalent(D3,D1) eq false);
assert (IsLinearlyEquivalent(D3,D2) eq false);
assert (IsLinearlyEquivalent(D3,D1+D2) eq false);

D4 := d4 - d0;
assert (order(D4) eq 2);
assert (IsLinearlyEquivalent(D4,D1) eq false);
assert (IsLinearlyEquivalent(D4,D2) eq false);
assert (IsLinearlyEquivalent(D4,D3) eq false);
assert (IsLinearlyEquivalent(D4,D1+D2) eq false);
assert (IsLinearlyEquivalent(D4,D1+D3) eq false);
assert (IsLinearlyEquivalent(D4,D3+D2) eq false);
assert (IsLinearlyEquivalent(D4,D3+D2+D1) eq false);

D5 := d5 - d0;
assert (order(D5) eq 2);
assert (IsLinearlyEquivalent(D5,D1) eq false);
assert (IsLinearlyEquivalent(D5,D2) eq false);
assert (IsLinearlyEquivalent(D5,D3) eq false);
assert (IsLinearlyEquivalent(D5,D4) eq false);
assert (IsLinearlyEquivalent(D5,D1+D2) eq false);
assert (IsLinearlyEquivalent(D5,D1+D3) eq false);
assert (IsLinearlyEquivalent(D5,D1+D4) eq false);
assert (IsLinearlyEquivalent(D5,D2+D3) eq false);
assert (IsLinearlyEquivalent(D5,D2+D4) eq false);
assert (IsLinearlyEquivalent(D5,D3+D4) eq false);
assert (IsLinearlyEquivalent(D5,D3+D2+D1) eq false);
assert (IsLinearlyEquivalent(D5,D4+D2+D1) eq false);
assert (IsLinearlyEquivalent(D5,D4+D2+D3) eq false);
assert (IsLinearlyEquivalent(D5,D4+D1+D3) eq false);
assert (IsLinearlyEquivalent(D5,D3+D2+D1+D4) eq false);


D6 := d6 - d0;
assert (order(D6) eq 2);
assert (IsLinearlyEquivalent(D6,D1) eq false);
assert (IsLinearlyEquivalent(D6,D2) eq false);
assert (IsLinearlyEquivalent(D6,D3) eq false);
assert (IsLinearlyEquivalent(D6,D4) eq false);
assert (IsLinearlyEquivalent(D6,D5) eq false);
assert (IsLinearlyEquivalent(D6,D1+D2) eq false);
assert (IsLinearlyEquivalent(D6,D1+D3) eq false);
assert (IsLinearlyEquivalent(D6,D1+D4) eq false);
assert (IsLinearlyEquivalent(D6,D1+D5) eq false);
assert (IsLinearlyEquivalent(D6,D2+D3) eq false);
assert (IsLinearlyEquivalent(D6,D2+D4) eq false);
assert (IsLinearlyEquivalent(D6,D2+D5) eq false);
assert (IsLinearlyEquivalent(D6,D3+D4) eq false);
assert (IsLinearlyEquivalent(D6,D3+D5) eq false);
assert (IsLinearlyEquivalent(D6,D4+D5) eq false);
assert (IsLinearlyEquivalent(D6,D3+D2+D1) eq false);
assert (IsLinearlyEquivalent(D6,D4+D2+D1) eq false);
assert (IsLinearlyEquivalent(D6,D5+D2+D1) eq false);
assert (IsLinearlyEquivalent(D6,D4+D1+D3) eq false);
assert (IsLinearlyEquivalent(D6,D5+D1+D3) eq false);
assert (IsLinearlyEquivalent(D6,D1+D5+D4) eq false);
assert (IsLinearlyEquivalent(D6,D4+D2+D3) eq false);
assert (IsLinearlyEquivalent(D6,D5+D2+D3) eq false);
assert (IsLinearlyEquivalent(D6,D4+D5+D3) eq false);
assert (IsLinearlyEquivalent(D6,D4+D5+D3+D1) eq false);
assert (IsLinearlyEquivalent(D6,D4+D5+D2+D1) eq false);
assert (IsLinearlyEquivalent(D6,D4+D3+D2+D1) eq false);
assert (IsLinearlyEquivalent(D6,D5+D3+D2+D1) eq false);
assert (IsLinearlyEquivalent(D6,D5+D3+D2+D1+D4) eq false);

// Thus, we can pull back the torsion to prove that the only points h5 are the known two!
// Pull these back further to the original curve

for p in ptsh5 do
  Points(p@@phi5);
end for;

// X_{H_171,N_{ns}}(48) is a genus 6 hyperelliptic curve of rank 0


