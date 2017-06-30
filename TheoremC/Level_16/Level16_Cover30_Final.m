load "entanglements.m";

P<x,y,z> := PolynomialRing(Rationals(),3);

curgp := [162,163,164,167,172,174];
jMap := {@@};
X12 := eval Read("eq12.txt");
X30 := eval Read("eq30.txt");
a30 := X30.1;
b30 := X30.2;
map30to12 := map<X30 -> X12 | [-a30^2,b30^2]>;

X6 := eval Read("eq6.txt");
X12 := eval Read("eq12.txt");
a12 := X12.1;
b12 := X12.2;
map12to6 := map<X12 -> X6 | [-a12^2 - 16*b12^2,b12^2]>;

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
f2 := map<X12 -> X6  | DefiningEquations(map12to6)>;
f3 := map<X30 -> X12  | DefiningEquations(map30to12)>;
f4 := map<X -> X30  | DefiningEquations(maptocover)>;
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

/*----------------------------X_{H_162,G_4}(48)----------------------------------*/
assert (162 eq curgp[1]);
C1 := Scheme(A3 , [Evaluate(jMap[1][2],[x,y,1]), Evaluate(jMap[1][3],[x,1,1]) - s^3*Evaluate(jMap[1][4],[x,1,1])]);
PC1<X,Y,S,Z> := Curve(ProjectiveClosure(C1));
assert (Genus(PC1) eq 3);
boo, h1 , phi1 := IsHyperelliptic(PC1); 
assert (boo eq true);
J1 := Jacobian(h1);
//assert (RankBound(J1) eq 1);
A2<A,B> := AffineSpace(Rationals(),2);
c1 := Curve(A2 , A^2 - (-B^7 + 4*B^4 - 8*B));
Pc1<a,b,c> := ProjectiveClosure(c1); 
aut1 := AutomorphismGroup(Pc1);
q,_ := CurveQuotient(AutomorphismGroup(Pc1,[aut1.1]));
Quo1,phi2 := CurveQuotient(AutomorphismGroup(Pc1,[aut1.2]));
assert (Genus(q) eq 0) and (Genus(Quo1) eq 2);
Jq2 :=Jacobian(Quo1);
assert (RankBound(Jq2) eq 0);
ptsQuo1 := Chabauty0(Jq2);
for P in ptsQuo1 do 
  Points(P@@phi2);
end for;
ptsh := RationalPoints(h1 : Bound := 1000); //Only known points
for P in ptsh do
  Points(P@@phi1);
end for;

//This point is cuspidal


/*----------------------------X_{H_163,G_4}(48)----------------------------------*/
assert (163 eq curgp[2]);
C2 := Scheme(A3 , [Evaluate(jMap[2][2],[x,y,1]), Evaluate(jMap[2][3],[x,1,1]) - s^3*Evaluate(jMap[2][4],[x,1,1])]);
PC2<X,Y,S,Z> := Curve(ProjectiveClosure(C2));
assert (Genus(PC2) eq 3);
boo, h2 , phi1 := IsHyperelliptic(PC2); //time = 39.5
assert (boo eq true);
J2 := Jacobian(h2);
assert (RankBound(J2) eq 1);
A2<A,B> := AffineSpace(Rationals(),2);
c2 := Curve(A2 , A^2 - (-2*B^7 + 8*B^4 - 16*B));
Pc2<a,b,c> := ProjectiveClosure(c2); 
aut := AutomorphismGroup(Pc2);
q1,phiq1 := CurveQuotient(AutomorphismGroup(Pc2,[aut.1]));
Quo2,phiq2 := CurveQuotient(AutomorphismGroup(Pc2,[aut.2]));
assert (Genus(q1) eq 0) and (Genus(Quo2) eq 2);
Jq2 :=Jacobian(Quo2);
assert (RankBound(Jq2) eq 0);
ptsq2 := Chabauty0(Jq2);
for P in ptsq2 do 
  Points(P@@phiq2);
end for;
ptsh := RationalPoints(h2 : Bound := 1000); //Only known points
for P in ptsh do
  Points(P@@phi1);
end for;

//This point is cuspidal, hence there are no rational points on our curve

/*----------------------------X_{H_164,G_4}(48)----------------------------------*/
assert (164 eq curgp[3]);
C3 := Scheme(A3 , [Evaluate(jMap[3][2],[x,y,1]), Evaluate(jMap[3][3],[x,1,1]) - s^3*Evaluate(jMap[3][4],[x,1,1])]);
PC3<X,Y,S,Z> := Curve(ProjectiveClosure(C3));
assert (Genus(PC3) eq 3);
assert (IsIsomorphic(PC2,PC3) eq false);
boo, h3, phi1 := IsHyperelliptic(PC3);
assert (boo eq true);
J3 := Jacobian(h3);
assert (RankBound(J3) eq 1);

A2<A,B> := AffineSpace(Rationals(),2);
c3 := Curve(A2 , A^2 - (-B^7 - 4*B^4 - 8*B));
Pc3<a,b,c> := ProjectiveClosure(c3); 
aut3 := AutomorphismGroup(Pc3);
q1,phiq1 := CurveQuotient(AutomorphismGroup(Pc3,[aut3.1]));
Quo3,phiq2 := CurveQuotient(AutomorphismGroup(Pc3,[aut3.2]));
assert (Genus(q1) eq 0) and (Genus(Quo3) eq 2);
Jq2 := Jacobian(Quo3);
assert (RankBound(Jq2) eq 0);
ptsq2 := Chabauty0(Jq2);
for P in ptsq2 do 
  Points(P@@phiq2);
end for;
ptsh := RationalPoints(h3 : Bound := 1000); //Only known points
for P in ptsh do
  Points(P@@phi1);
end for;

//This point is cuspidal, hence there are no rational points on our curve



/*----------------------------X_{H_167,G_4}(48)----------------------------------*/
assert (167 eq curgp[4]);
C4 := Scheme(A3 , [Evaluate(jMap[4][2],[x,y,1]), Evaluate(jMap[4][3],[x,1,1]) - s^3*Evaluate(jMap[4][4],[x,1,1])]);
PC4<X,Y,S,Z> := Curve(ProjectiveClosure(C4));
assert (Genus(PC4) eq 3);
assert (IsIsomorphic(PC2,PC4) eq false);
assert (IsIsomorphic(PC3,PC4) eq false);
boo, H4, phi4 := IsHyperelliptic(PC4);
assert (boo eq true);

//We use etale descent
P<t> := PolynomialRing(Rationals());
AA2<x1,y> := AffineSpace(Rationals(),2);
AA3<x2,y1,y2> := AffineSpace(Rationals(),3);
d:=1;
D := Curve(AA3 , [d*y1^2 - x2 , d*y2^2 - (-2*x2^6 - 8*x2^3 - 16)]);

/*It suffices to study the points on the hyper elliptic curve y^2 = -2x^6 - 8x^3 - 16 */

//Checking which twists we need to analyze
for d in [1,-1,2,-2,3,-3,6,-6] do 
Hd2:= QuadraticTwist(HyperellipticCurve(-2*t^6 - 8*t^3 - 16),d);   
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

//Finding points on twists
dd := [-1,-2];

for d in dd do
  Hd:= QuadraticTwist(HyperellipticCurve(-2*t^6 - 8*t^3 - 16),d);  
  Jd := Jacobian(Hd);
  assert (RankBound(Jd) eq 0);
  Chabauty0(Jd);
end for;

//All of the points on Hd2 are cuspidal

//Pulling back points to D
d:= [-1,-2];
H1 := Curve(AA2, -y^2 - (-2*x1^6 - 8*x1^3 - 16));
ptsH1 := {H1![0,4],H1![0,-4]};
H2 := Curve(AA2, -2*y^2 - (-2*x1^6 - 8*x1^3 - 16));
ptsD1 := {@@};
for P in ptsH1 do
  d:= -1;
  D := Curve(AA3 , [d*y1^2 - x2 , d*y2^2 - (-2*x2^6 - 8*x2^3 - 16)]);
  pr1 := map<D -> H1 | [x2,y2]>;
  ptsD1 := ptsD1 join {Points(P @@ pr1)};
end for;


//Check by hand that these points do come from H4
ptsD1;
ptsH4 := RationalPoints(H4 : Bound := 1000);

for P in ptsH4 do
  Points(P@@phi4);
end for;

//This point is cuspidal



/*----------------------------X_{H_172,G_4}(48)----------------------------------*/
assert (172 eq curgp[5]);
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
  Hp := HyperellipticCurve(-A^13 - 64*A);
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
R := Roots(-w^13 - 64*w);
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


/*----------------------------X_{H_174,G_4}(48)----------------------------------*/
assert (174 eq curgp[6]);
C6 := Scheme(A3 , [Evaluate(jMap[6][2],[x,y,1]), Evaluate(jMap[6][3],[x,1,1]) - s^3*Evaluate(jMap[6][4],[x,1,1])]);
PC6<X,Y,S,Z> := Curve(ProjectiveClosure(C6));
assert (Genus(PC6) eq 6);
assert (IsIsomorphic(PC5,PC6) eq true);



