load "entanglements.m";

P<x,y,z> := PolynomialRing(Rationals(),3);

curgp := [149,150,151,153];
jMap45 := {@@};
X11 := eval Read("eq11.txt");
X45 := eval Read("eq45.txt");
a45 := X45.1;
b45 := X45.2;
map45to11 := map<X45 -> X11 | [-a45^2 + 8*b45^2,b45^2]>;

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
f3 := map<X45 -> X11  | DefiningEquations(map45to11)>;
f4 := map<X -> X45  | DefiningEquations(maptocover)>;
D:=DefiningEquations(f4*f3*f2*f1);
jMap45 := jMap45 join {@[curgp[i],P!DefiningEquation(X),P!D[1],P!D[2]]@};
end for;

A3<x,y,s> := AffineSpace(Rationals(),3);
P<t> := PolynomialRing(Rationals());

/*----------------------------X_{H_149,N_{ns}}(48)----------------------------------*/
assert (149 eq curgp[1]);
C1 := Scheme(A3 , [Evaluate(jMap45[1][2],[x,y,1]), Evaluate(jMap45[1][3],[x,1,1]) - s^3*Evaluate(jMap45[1][4],[x,1,1])]);
PC1<xx,Y,S,Z> := Curve(ProjectiveClosure(C1));
assert (Genus(PC1) eq 4);
boo,_,_ := IsHyperelliptic(PC1);
assert (boo eq false);

j149 := jMap45[1][3]/jMap45[1][4];
E1:=EllipticCurve([0,-1,0,-13,21]);
assert (Rank(E1) eq 0);
pt0 := E1![0,1,0];
pt1 := E1![3,0,1];
v0 := Evaluate(Denominator(j149),Eltseq(pt0)); 
v1:= Evaluate(j149,Eltseq(pt1));
pt1C1 := C1![3,0,12];

// X_{H_149,N_{ns}}(48) is a genus 4 non-hyp curve

/*----------------------------X_{H_150,N_{ns}}(48)----------------------------------*/
X150 := eval Read("eq150.txt");
assert (150 eq curgp[2]);
C2 := Curve(A3 , [Evaluate(jMap45[2][2],[x,y,1]), Evaluate(jMap45[2][3],[x,y,1]) - s^3*Evaluate(jMap45[2][4],[x,y,1])]);
assert (Genus(C2) eq 4);

//For simplicity we use the Canonical image
Phi1 := CanonicalMap(C2);
PC22<A,B,C,D> := CanonicalImage(C2,Phi1);
boo,_,_ := IsHyperelliptic(PC22);
assert (boo eq false);

//We find factors of the Jacobian of PC22

aut2 := AutomorphismGroup(PC22);
Quo2,q2 := CurveQuotient(aut2);
pts2 := PointSearch(Quo2,100);
E2 := WeierstrassModel(EllipticCurve(Quo2,pts2[5]));

E1 := EllipticCurve([0,6262062317568]);
E2 := EllipticCurve([0,1,0,-13,-21]);
assert (Rank(E1) eq 1);
assert (Rank(E2) eq 1);
assert (IsIsogenous(E1,E2) eq false);

//Verifying that Jac_{PC22,Q} ~ E1 x E2 x A where A is some simple abelian surface.

// The code below suggest that A is simple over Q (pesky 7!)

for p in [5,7,11,17,19,23] do
"*******************************";
p;  
F := FiniteField(p);
A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC22)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC22)[2],[x1,y1,z1,s1])]);
num := Parent(Numerator(ZetaFunction(CC))) !(Numerator(ZetaFunction(CC)) / Numerator(ZetaFunction( EllipticCurve([F!-0,F!-0,F!0,F!0,F!6262062317568])))*Numerator(ZetaFunction( EllipticCurve([F!0,F!1,F!0,F!-13,F!-21]))) );
Factorization(num);
end for;

discs := {-1,2,-2,3,-3,6,-6};
for d in discs do
d;
[LegendreSymbol(d,p) : p in [5,7,11,13]];
  F := QuadraticField(d);
  A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
  CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC22)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC22)[2],[x1,y1,z1,s1])]);
[d,#AutomorphismGroup(CC)];
"***********************************";
end for;


//We find other sub-factor over a quadratic extension

K := NumberField(t^2 - 6);
O := MaximalOrder(K);
GRcurves:= Eltseq(EllipticCurveWithGoodReductionSearch(2*3*O,700)); 
p := 3; 
Possible := {@@};
while p le 4 do
  p := NextPrime(p); 
"*******************************";
p;  
F := FiniteField(p^2);
 pvalues := {@@};
A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC22)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC22)[2],[x1,y1,z1,s1])]);
allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(CC))) !( Numerator(ZetaFunction(CC))/ (Numerator(ZetaFunction(EllipticCurve([F!0,F!6262062317568])))* Numerator(ZetaFunction(EllipticCurve([F!0,F!1,F!0,F!-13,F!-21])))) );
Factorization(num);
exists(c){c : c in curves | IsDivisibleBy(num,Numerator(ZetaFunction(c)) ) };
for i in [1..#GRcurves] do
g:= ChangeRing(IntegralModel(GRcurves[i]),O);  	 R,phi:=ResidueClassField(Decomposition(O,p)[1][1]);
   G<X,Y,Z> := BaseChange(g,phi); 
   if ZetaFunction(G) eq ZetaFunction(c) then
    pvalues := pvalues join {i}; 
    end if;
  end for;
  Possible := Possible join {@pvalues@};
end while;

// We don't find any new curves
// We can find extra curve quotients over Q(\sqrt{-3})

d:=-3;
F := QuadraticField(d);
A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC22)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC22)[2],[x1,y1,z1,s1])]);
aut := AutomorphismGroup(CC);
Quo1 := CurveQuotient(AutomorphismGroup(CC,[aut.1]));
PointSearch(ChangeRing(Quo1,Rationals()),100);
EQ1 := EllipticCurve(Quo1,Quo1![9,0,1/9,0,1,0]);
Quo2,phi2 := CurveQuotient(AutomorphismGroup(CC,[aut.2]));
PointSearch(ChangeRing(Quo2,Rationals()),100);
EQ2,phiEQ2 := EllipticCurve(Quo2,Quo2![0,9,1]);
Quo3 := CurveQuotient(AutomorphismGroup(CC,[aut.1*aut.2]));
assert (Genus(Quo3) eq 0);
Quo4 := CurveQuotient(AutomorphismGroup(CC,[aut.1*aut.2*aut.2]));
assert (Genus(Quo4) eq 0);
Quo5,phi5 := CurveQuotient(AutomorphismGroup(CC,[aut.2^2]));
PointSearch(ChangeRing(Quo5,Rationals()),100);
EQ5 := EllipticCurve(Quo5,Quo5![0,9,1]);
Quo,phiQ := CurveQuotient(aut);

//Let's check to make sure that we actually get additional factors of the Jacobian

E3 := EllipticCurve([0,0,-117649/4412961507515625000000,0,-13841287201/155793834134516620826876953125000000000000000]);
assert (IsIsomorphic(BaseChange(E3,F),EQ1));
E4 := EllipticCurve([0,-5000/81,0,3125000/6561,0]);
assert (IsIsomorphic(BaseChange(E4,F),EQ5));

IsIsomorphic(E1,E3);
IsIsomorphic(E1,E4);

IsIsomorphic(E2,E3);
IsIsomorphic(E2,E4);

// Rats! We didn't find any new quotients



/*----------------------------X_{H_151,N_{ns}}(48)----------------------------------*/
X151 := eval Read("eq151.txt");
assert (151 eq curgp[3]);
C3 := Scheme(A3 , [Evaluate(jMap45[3][2],[x,y,1]), Evaluate(jMap45[3][3],[x,1,1]) - s^3*Evaluate(jMap45[3][4],[x,1,1])]);
PC3<X,Y,S,Z> := Curve(ProjectiveClosure(C3));
assert (Genus(PC3) eq 4);
boo,_,_ := IsHyperelliptic(PC3);
assert (boo eq false);

E3:=EllipticCurve([0,-1,0,-3,-1]);
assert (Rank(E3) eq 0);
pt0 := E3![0,1,0];
pttors := E3![-1,0,1];
j151 := jMap45[3][3]/jMap45[3][4];
v0 := Evaluate(Denominator(j151),Eltseq(pt0)); 
v1:= Evaluate(j151,Eltseq(pttors));
pt1C3 := C3![-1,0,12];


/*----------------------------X_{H_153,N_{ns}}(48)----------------------------------*/
assert (153 eq curgp[4]);
C4 := Scheme(A3 , [Evaluate(jMap45[4][2],[x,y,1]), Evaluate(jMap45[4][3],[x,1,1]) - s^3*Evaluate(jMap45[4][4],[x,1,1])]);
C4 := Curve(C4);
assert (Genus(C4) eq 4);
Phi4 := CanonicalMap(C4);
PC44<XX,YY,SS> := CanonicalImage(C4,Phi4);
boo,_,_ := IsHyperelliptic(PC44);
assert (boo eq false);

//Finding factors of Jac
aut4 := AutomorphismGroup(PC44);
Quo4 := CurveQuotient(aut4);
pts4 := PointSearch(Quo4,100);
E4 := EllipticCurve(Quo4,pts4[1]);
E42:=EllipticCurve([0,1,0,-3,1]);
IsIsogenous(E4,E42);

// The code below suggest that A is simple over Q (pesky 7!)

for p in [5,7,11,17,19,23] do
"*******************************";
p;  
F := FiniteField(p);
A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC44)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC44)[2],[x1,y1,z1,s1])]);
num := Parent(Numerator(ZetaFunction(CC))) !(Numerator(ZetaFunction(CC)) / Numerator(ZetaFunction( EllipticCurve([F!0,F!0,F!262144,F!0,F!-8589934592])))*Numerator(ZetaFunction( EllipticCurve([F!0,F!1,F!0,F!-3,F!1]))) );
Factorization(num);
end for;

// We try to find this curve

K := RationalsAsNumberField();
O := MaximalOrder(K);
GRcurves:= Eltseq(EllipticCurveWithGoodReductionSearch(2*3*O,500)); 
p := 3; 
Possible := {@@};
while p le 11 do
  p := NextPrime(p); 
"*******************************";
p;  
F := FiniteField(p);
 pvalues := {@@};
A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC44)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC44)[2],[x1,y1,z1,s1])]);
allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
num := Parent(Numerator(ZetaFunction(CC))) !(Numerator(ZetaFunction(CC)) / Numerator(ZetaFunction( EllipticCurve([F!0,F!0,F!262144,F!0,F!-8589934592])))*Numerator(ZetaFunction( EllipticCurve([F!0,F!1,F!0,F!-3,F!1]))) );
exists(c){c : c in allCurves | IsDivisibleBy(num,Numerator(ZetaFunction(c)) ) };
   for i in [1..#GRcurves] do
   g:= ChangeRing(IntegralModel(GRcurves[i]),O);  	
   R,phi:=ResidueClassField(Decomposition(O,p)[1][1]);
   G<X,Y,Z> := BaseChange(g,phi); 
   if ZetaFunction(G) eq ZetaFunction(c) then
    pvalues := pvalues join {i}; 
    end if;
  end for;
  Possible := Possible join {@pvalues@};
end while;

Possible[1] meet Possible[2] meet Possible[3];

// We cannot find this desired curve...

discs := {-1,2,-2,3,-3,6,-6};
for d in discs do
d;
[LegendreSymbol(d,p) : p in [5,7,11,13]];
  F := QuadraticField(d);
  A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
  CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC44)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC44)[2],[x1,y1,z1,s1])]);
[d,#AutomorphismGroup(CC)];
"***********************************";
end for;

// We try to find the extra quotients over a quadratic extension, but we cannot find any

d:=-3;
  F := QuadraticField(d);
  A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
  CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC44)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC44)[2],[x1,y1,z1,s1])]);
aut := AutomorphismGroup(CC);
Quo1 := CurveQuotient(AutomorphismGroup(CC,[aut.1]));
PointSearch(ChangeRing(Quo1,Rationals()),10000);
EQ1 := EllipticCurve(Quo1,Quo1![0,-9216/5,-5/9216,0,0,1]);
Quo2,phi2 := CurveQuotient(AutomorphismGroup(CC,[aut.2]));
PointSearch(ChangeRing(Quo2,Rationals()),100);
EQ2,phiEQ2 := EllipticCurve(Quo2,Quo2![1,0,0]);
Quo3 := CurveQuotient(AutomorphismGroup(CC,[aut.1*aut.2]));
assert (Genus(Quo3) eq 0);
Quo4 := CurveQuotient(AutomorphismGroup(CC,[aut.1*aut.2*aut.2]));
assert (Genus(Quo4) eq 0);
Quo5,phi5 := CurveQuotient(AutomorphismGroup(CC,[aut.2^2]));
PointSearch(ChangeRing(Quo5,Rationals()),100);
EQ5 := EllipticCurve(Quo5,Quo5![1,0,0]);
Quo,phiQ := CurveQuotient(aut);
assert (Genus(Quo) eq 0);

assert (IsIsomorphic(BaseChange(E4,F),EQ1) eq true);
assert (IsIsomorphic(BaseChange(E42,F),EQ2) eq true);

