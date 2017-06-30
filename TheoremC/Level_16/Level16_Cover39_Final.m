load "entanglements.m";

P<x,y,z> := PolynomialRing(Rationals(),3);

curgp := [160,161,165,166];
jMap39 := {@@};
X11 := eval Read("eq11.txt");
X39 := eval Read("eq39.txt");
a39 := X39.1;
b39 := X39.2;
map39to11 := map<X39 -> X11 | [-64*b39^2,a39^2 - 8*b39^2]>;

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
f3 := map<X39 -> X11  | DefiningEquations(map39to11)>;
f4 := map<X -> X39  | DefiningEquations(maptocover)>;
D:=DefiningEquations(f4*f3*f2*f1);
jMap39 := jMap39 join {@[curgp[i],P!DefiningEquation(X),P!D[1],P!D[2]]@};
end for;

A3<x,y,s> := AffineSpace(Rationals(),3);

/*----------------------------X_{H_160,G_4}(48)----------------------------------*/
X160 := eval Read("eq160.txt");
assert (160 eq curgp[1]);
C1 := Scheme(A3 , [Evaluate(jMap39[1][2],[x,y,1]), Evaluate(jMap39[1][3],[x,1,1]) - s^3*Evaluate(jMap39[1][4],[x,1,1])]);
PC1<X,Y,S,Z> := Curve(ProjectiveClosure(C1));
assert (Genus(PC1) eq 4);
boo, _, _ := IsHyperelliptic(PC1); 
assert (boo eq false);

j160 := jMap39[1][3]/jMap39[1][4];
E1:=EllipticCurve([0,-1,0,-13,21]);
assert (Rank(E1) eq 0);
TorsionSubgroup(E1);
pt0 := E1![0,1,0];
pt1 := E1![3,0,1];

// These points pullback to the known points on C1
PointSearch(C1,1000);

// This point is clearly CM with j = 1728


/*----------------------------X_{H_161,G_4}(48)----------------------------------*/
X161 := eval Read("eq161.txt");
assert (161 eq curgp[2]);
C2 := Scheme(A3 , [Evaluate(jMap39[2][2],[x,y,1]), Evaluate(jMap39[2][3],[x,1,1]) - s^3*Evaluate(jMap39[2][4],[x,1,1])]);
PC2<X,Y,S,Z> := Curve(ProjectiveClosure(C2));
assert (Genus(PC2) eq 4);
boo, _, _ := IsHyperelliptic(PC2);
assert (boo eq false);

j161 := jMap39[2][3]/jMap39[2][4];
E2:=EllipticCurve([0,-1,0,-3,-1]);
assert (Rank(E2) eq 0);
pt0 := E2![0,1,0];
pttors := E2![-1,0,1];
j161 := jMap39[2][3]/jMap39[2][4];
v0 := Evaluate(Denominator(j161),Eltseq(pt0)); 
v1:= Evaluate(j161,Eltseq(pttors));
pt1C2 := C2![-1,0,12];

// These are CM points!

/*----------------------------X_{H_165,G_4}(48)----------------------------------*/
X165 := eval Read("eq165.txt");
assert (165 eq curgp[3]);
C3 := Scheme(A3 , [Evaluate(jMap39[3][2],[x,y,1]), Evaluate(jMap39[3][3],[x,1,1]) - s^3*Evaluate(jMap39[3][4],[x,1,1])]);
C3 := Curve(C3);
assert (Genus(C3) eq 4);
boo, _, _ := IsHyperelliptic(C3);
Phi3 := CanonicalMap(C3);
PC33<XX,YY,SS> := CanonicalImage(C3,Phi3);
boo,_,_ := IsHyperelliptic(PC33);
assert (boo eq false);

//We find factors of the Jacobian of PC22

aut3 := AutomorphismGroup(PC33);
Quo,q := CurveQuotient(aut3);
pts := PointSearch(Quo,100);
E2 := WeierstrassModel(EllipticCurve(Quo,pts[2]));

E1 := EllipticCurve([0,71328803586048]);
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
CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC33)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC33)[2],[x1,y1,z1,s1])]);
num := Parent(Numerator(ZetaFunction(CC))) !(Numerator(ZetaFunction(CC)) / Numerator(ZetaFunction( EllipticCurve([F!-0,F!-0,F!0,F!0,F!71328803586048])))*Numerator(ZetaFunction( EllipticCurve([F!0,F!1,F!0,F!-13,F!-21]))) );
Factorization(num);
end for;

K := RationalsAsNumberField();
O := MaximalOrder(K);
GRcurves:= Eltseq(EllipticCurveWithGoodReductionSearch(2*3*O,700)); 
p := 3; 
Possible := {@@};
while p le 7 do
  p := NextPrime(p); 
"*******************************";
p;  
F := FiniteField(p);
 pvalues := {@@};
A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC33)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC33)[2],[x1,y1,z1,s1])]);
allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(CC))) !( Numerator(ZetaFunction(CC))/ (Numerator(ZetaFunction(EllipticCurve([F!0,F!71328803586048])))* Numerator(ZetaFunction(EllipticCurve([F!0,F!1,F!0,F!-13,F!-21])))) );
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

// Such a curve does not exist!

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
P<w> := PolynomialRing(Rationals());
K := NumberField(w^2 + w + 1);
O := MaximalOrder(K);
GRcurves:= Eltseq(EllipticCurveWithGoodReductionSearch(2*3*O,700)); 
p := 5; 
Possible1 := {@@};
while p le 5 do
  p := NextPrime(p); 
"*******************************";
p;  
F := FiniteField(p^2);
 pvalues := {@@};
A1<x1,y1,s1,z1> := ProjectiveSpace(F,3);
CC := Curve(A1 , [Evaluate(DefiningPolynomials(PC33)[1],[x1,y1,z1,s1]), Evaluate(DefiningPolynomials(PC33)[2],[x1,y1,z1,s1])]);
allCurves := [EllipticCurve([a,b]) : a,b in F | not -16*(4*a^3 + 27*b^2) eq 0];
  curves := [];
  for c in allCurves do 
    if not exists{e : e in curves | IsIsogenous(c,e)} then
      curves := curves cat [c];
    end if;
  end for;
num := Parent(Numerator(ZetaFunction(CC))) !( Numerator(ZetaFunction(CC))/ (Numerator(ZetaFunction(EllipticCurve([F!0,F! 71328803586048])))* Numerator(ZetaFunction(EllipticCurve([F!0,F!1,F!0,F!-13,F!-21])))) );
Factorization(num);
exists(c){c : c in curves | IsDivisibleBy(num,Numerator(ZetaFunction(c)) ) };
for i in [1..#Possible] do
g:= ChangeRing(IntegralModel(GRcurves[Possible[1,i]]),O);  	 
R,phi:=ResidueClassField(Decomposition(O,p)[1][1]);
   G<X,Y,Z> := BaseChange(g,phi); 
   if ZetaFunction(G) eq ZetaFunction(c) then
    pvalues := pvalues join {i}; 
    end if;
  end for;
  Possible1 := Possible1 join {@pvalues@};
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


assert (IsIsomorphic(BaseChange(E1,F),EQ1));
assert (IsIsomorphic(BaseChange(E2,F),EQ5));

// Rats! We didn't find any new quotients


/*----------------------------X_{H_166,G_4}(48)----------------------------------*/
assert (166 eq curgp[4]);
C4 := Scheme(A3 , [Evaluate(jMap39[4][2],[x,y,1]), Evaluate(jMap39[4][3],[x,1,1]) - s^3*Evaluate(jMap39[4][4],[x,1,1])]);
PC4<X,Y,S,Z> := Curve(ProjectiveClosure(C4));
assert (Genus(PC4) eq 4);
boo, _, _ := IsHyperelliptic(PC4);
assert (boo eq false);

E4:=EllipticCurve([0,1,0,-3,1]);
assert (Rank(E4) eq 1);
pt0 := E4![0,1,0];
pttors := E4![1,0,1];
ptgen := E4![-1,-2,1];
j166 := jMap39[4][3]/jMap39[4][4];
for i in [-20..20] do
  i;
  if Evaluate(Denominator(j166),Eltseq(i*ptgen)) ne 0 then
  v:= Evaluate(j166,Eltseq(i*ptgen));
  //Factorisation(Numerator(v));
  Factorisation(Denominator(v));
  "***********************";
  end if;
end for;
v0:=Evaluate(Denominator(j166),Eltseq(pt0));
v1:=Evaluate(j166,Eltseq(ptgen));
v2:=Evaluate(j166,Eltseq(pttors));

pt1C4 := C4![1,0,12];
pt2C4 := C4![-1,-2,12];
pt4C4 := C4![-1,2,12];





