////////////////////////////////////////////////////////////////////////////////////
// Computations for the mod 16 and mod 3 simultaneous computations
////////////////////////////////////////////////////////////////////////////////////
/////We only have to consider the case when rho_{E,3} is conjugate to a subgroup of N_{nsp(3), so by abuse of notation, we will denote our modular curves by X_{H_#} for some number/////



SetAutoColumns(false);
SetColumns(100);
SetEchoInput(true);
Attach("routines1.m");

load "entanglements.m";
A2<s,t> := AffineSpace(Rationals(),2);
GG:= GL(2,ResidueClassRing(8));

/*--Level 16, applicable subgroups that do not contain level 8 subgroups of order 128 in kernel of reduction--*/
G:=[i : i in [1..#newsublist] | newsublist[i][2] eq 16 and #{GG!g : g in newsublist[i][3]} eq 128];
Bad := [108,115,116,117,118,119,120,121,122,123,157,158,159,168,169,173,175,176]; 
//These are the subgroups which contain a level 8 subgroup which does not appear as a composite-(8,3) image
G := [i : i in G | not (i in Bad)];


Summary := [];
/*----------------------------X_{H_103,N_{ns}}(48)----------------------------------*/
jmap(103);
C:= Curve(A2, s^3*t^8 - (t^24 + 48*t^16 + 768*t^8 + 4096));
PointSearch(C,100);
PC<S,T,Z> := ProjectiveClosure(C);
assert (Genus(PC) eq 0); 
pts:= Points(PC);
assert (#pts ne 0);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

// X_{H_{103},N_{ns}}(48) is isomorphic to a P^1

/*----------------------------X_{H_104,N_{ns}}(48)----------------------------------*/
jmap(104);
C:= Curve(A2, s^3*t^16 - (256*t^24 + 768*t^16 + 768*t^8 + 256));
PointSearch(C,1000);
PC<S,T,Z> := ProjectiveClosure(C);
assert (Genus(PC) eq 0); 
pts:= Points(PC);
assert (#pts ne 0);
pt := pts[3];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

Summary := Summary cat ["The modular curve X_{H_{104},N_{ns}}(48) is isomorphic to a P^1 .\n"];


/*----------------------------X_{H_109,N_{ns}}(48)----------------------------------*/
jmap(109);
A1<x,s> := AffineSpace(Rationals(),2);
C := Curve(A1,s^3 - 4*(x^4 - 8*x^2 + 8));
assert (Genus(C) eq 3);
PC5<T,y,z> := ProjectiveClosure(C);
//We want to compute a smooth plane model of PC
Phi:= CanonicalMap(PC5);
CQ<X,Y,Z> := CanonicalImage(PC5,Phi);
CQ;
aut := AutomorphismGroup(CQ);
CC,c := CurveQuotient(aut);
PointSearch(CC,1000);
SingularPoints(CC);
E,e := EllipticCurve(CC,PointSearch(CC,1000)[1]);
MordellWeilShaInformation(E);
phi := c*e;
for p in RationalPoints(E : Bound := 100) do
Points(p@@phi);
end for;
PointSearch(CQ,100);
SingularPoints(CQ);

// X_{H_109,N_{ns}}(48) is a genus 3 non-hyperelliptic curve

/*----------------------------X_{H_113,N_{ns}}(48)----------------------------------*/
jmap(113);
C:= Curve(A2, s^3*t^8 - (t^24 - 48*t^16 + 768*t^8 - 4096));

// Factor the RHS
Factorization(PolynomialRing(Integers())!Numerator(jmap(113)));

// Thus, we can rewrite the curve as
CC := Curve(A2, s^3*t^8 - 1);

PointSearch(CC,100);
SingularPoints(CC);
PC<S,T,Z> := ProjectiveClosure(CC);
assert (Genus(PC) eq 0); 
pts:= PointSearch(PC,100);
assert (#pts ne 0);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

// X_{H_{113},N_{ns}}(48) is isomorphic to a P^1 

/*----------------------------X_{H_114,N_{ns}}(48)----------------------------------*/
jmap(114);
C:= Curve(A2, s^3*t^16 - (-256*t^24 + 768*t^16 - 768*t^8 + 256));

// Factor the RHS
Factorization(PolynomialRing(Integers())!Numerator(jmap(114)));

// Thus, we can rewrite the curve as
CC := Curve(A2, s^3*t^16 - 2^2);
PointSearch(CC,100);
SingularPoints(CC);
PC<S,T,Z> := ProjectiveClosure(CC);
assert (Genus(PC) eq 0); 
pts:= PointSearch(PC,100);
assert (#pts ne 0);
pt := pts[2];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

// X_{H_{114},N_{ns}}(48) is isomorphic to a P^1 

/*----------------------------X_{H_105,N_{ns}}(48)----------------------------------*/
jmap(105);
A1<x,s> := AffineSpace(Rationals(),2);
C5:= Curve(A1, s^3*(x^16 - 32*x^14 + 416*x^12 - 2816*x^10 + 10624*x^8 - 22528*x^6 + 26624*x^4 - 16384*x^2 + 4096)- (-x^24 + 48*x^22 - 1008*x^20 + 12160*x^18 - 92352*x^16 + 448512*x^14 - 1304576*x^12 + 1622016*x^10 + 2002944*x^8 - 7929856*x^6 + 589824*x^4 + 14155776*x^2 + 7077888));


// Factor the RHS
Factorization(PolynomialRing(Integers())!Numerator(jmap(105)));
Factorization(PolynomialRing(Integers())!Denominator(jmap(105)));

C5:= Curve(A1, s^3 -(x^4 - 8*x^2 + 8)^2);
PC5<T,y,z> := ProjectiveClosure(C5);
assert (Genus(PC5) eq 3) and (IsHyperelliptic(PC5) eq false);

//We want to compute a smooth plane model of PC
Phi:= CanonicalMap(PC5);
CQ<X,Y,Z> := CanonicalImage(PC5,Phi);
P<X,Y,Z> := PolynomialRing(Rationals(),3);
boo, DQ := IsCoercible(P,DefiningPolynomial(CQ));
q1 := (2*Y^2 - Y*Z);
q2 := (X^2 - 4*Y^2);
q3 := (4*Y^2 + 2*Y*Z + Z^2);
if DQ eq q2^2 - (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;

// X_{105,G}(48) is a non-hyperelliptic genus 3 curve 
// See other files for further info

/*----------------------------X_{H_106,N_{ns}}(48)----------------------------------*/
A1<x,s> := AffineSpace(Rationals(),2);
C6:= Curve(A1, s^3*(x^16 + 32*x^14 + 416*x^12 + 2816*x^10 + 10624*x^8 + 22528*x^6 + 26624*x^4 + 16384*x^2 + 4096)- (-x^24 - 48*x^22 - 1008*x^20 - 12160*x^18 - 92352*x^16 - 448512*x^14 - 1304576*x^12 - 1622016*x^10 + 2002944*x^8 + 7929856*x^6 + 589824*x^4 - 14155776*x^2 + 7077888));
PC6<T,y,z> := ProjectiveClosure(C6);
"The modular curve X_{106,G}(48) is of",Genus(PC6),"and it is",IsHyperelliptic(PC6), "that the curve is hyper elliptic"; 
//We want to compute a smooth plane model of PC
Phi:= CanonicalMap(PC6);
CQ<X,Y,Z> := CanonicalImage(PC6,Phi);
P<X,Y,Z> := PolynomialRing(Rationals(),3);
boo, DQ := IsCoercible(P,DefiningPolynomial(CQ));
q1 := (2*Y^2 - Y*Z);
q2 := (X^2 + 4*Y^2);
q3 := (4*Y^2 + 2*Y*Z + Z^2);
if DQ eq q2^2 - (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;

// X_{106,G}(48) is a non-hyperelliptic genus 3 curve 
// See other files for further info

/*----------------------------X_{H_107,N_{ns}}(48)----------------------------------*/
A1<x,s> := AffineSpace(Rationals(),2);
C7:= Curve(A1, s^3*(x^16 - 4*x^14 + 13/2*x^12 - 11/2*x^10 + 83/32*x^8 - 11/16*x^6 + 13/128*x^4 -1/128*x^2 + 1/4096)- (-4096*x^24 + 24576*x^22 - 64512*x^20 + 97280*x^18 - 92352*x^16 + 56064*x^14 - 20384*x^12 + 3168*x^10 + 489*x^8 - 242*x^6 + 9/4*x^4 + 27/4*x^2 + 27/64));
PC7<T,y,z> := ProjectiveClosure(C7);
"The modular curve X_{107,G}(48) is of",Genus(PC7),"and it is",IsHyperelliptic(PC7), "that the curve is hyper elliptic"; 
//We want to compute a smooth plane model of PC
Phi:= CanonicalMap(PC7);
CQ<X,Y,Z> := CanonicalImage(PC7,Phi);
P<X,Y,Z> := PolynomialRing(Rationals(),3);
boo,DQ:= IsCoercible(P,DefiningPolynomial(CQ));
//The defining polynomial is not in a nice form since only odd powers of 2 appear. 
//We can minimize and reduce this to a nicer model whose determinantal representation we can compute.
boo, MQ := IsCoercible(P,MinimizeReducePlaneQuartic(DQ));
q2 := (Y^2 - 2*Z^2);
q1 := -2*(Z*X - Z^2);
q3 := (X^2 + X*Z + Z^2);
if MQ eq q2^2 - (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;

// X_{107,G}(48) is a non-hyperelliptic genus 3 curve 
// See other files for further info

/*----------------------------X_{H_110,N_{ns}}(48)----------------------------------*/
A1<x,s> := AffineSpace(Rationals(),2);
C10:= Curve(A1, s^3*(x^8 - 2*x^6 + 5/4*x^4 - 1/4*x^2 + 1/64)- (16777216*x^24 - 100663296*x^22 + 264241152*x^20 - 398458880*x^18 + 
    381222912*x^16 - 241434624*x^14 + 102662144*x^12 - 29196288*x^10 + 
    5450496*x^8 - 644608*x^6 + 45504*x^4 - 1728*x^2 + 27));
PC10<T,y,z> := ProjectiveClosure(C10); 
"The modular curve X_{110,G}(48) is of",Genus(PC10),"and it is",IsHyperelliptic(PC10), "that the curve is hyper elliptic"; 
//We want to compute a smooth plane model of PC
Phi:= CanonicalMap(PC10);
CQ<X,Y,Z> := CanonicalImage(PC10,Phi);
P<X,Y,Z> := PolynomialRing(Integers(),3);
boo,DQ:= IsCoercible(P,DefiningPolynomial(CQ));
q2 := 2^10*(4*Y^2 -2*Z^2);
q1 := (Z*X + 128*Z^2);
q3 := (X^2 - 128*X*Z + 16384*Z^2);
if DQ eq -q2^2 + (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;
assert (IsIsomorphic(PC7,PC10) eq true);

/*----------------------------X_{H_111,N_{ns}}(48)----------------------------------*/
A1<x,s> := AffineSpace(Rationals(),2);
C11:= Curve(A1, s^3*(x^8 + 16*x^6 + 80*x^4 + 128*x^2 + 64)- (x^24 + 48*x^22 + 1008*x^20 + 12160*x^18 + 93072*x^16 + 471552*x^14 + 
    1604096*x^12 + 3649536*x^10 + 5450496*x^8 + 5156864*x^6 + 2912256*x^4 + 
    884736*x^2 + 110592));
PC11<T,y,z> := ProjectiveClosure(C11);
"The modular curve X_{111,G}(48) is of",Genus(PC11),"and it is",IsHyperelliptic(PC11), "that the curve is hyper elliptic"; 
//We want to compute a smooth plane model of PC
Phi:= CanonicalMap(PC11);
CQ<X,Y,Z> := CanonicalImage(PC11,Phi);
P<X,Y,Z> := PolynomialRing(Integers(),3);
boo,DQ:= IsCoercible(P,DefiningPolynomial(CQ));
q2 := (Y^2 + 4*Z^2);
q1 := (Z*X + 2*Z^2);
q3 := (X^2 - 2*X*Z + 4*Z^2);
if DQ eq -q2^2 + (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;
assert (IsIsomorphic(PC6,PC11) eq true);

/*----------------------------X_{H_112,N_{ns}}(48)----------------------------------*/
A1<x,s> := AffineSpace(Rationals(),2);
C12:= Curve(A1, s^3*(x^8 - 16*x^6 + 80*x^4 - 128*x^2 + 64)- (x^24 - 48*x^22 + 1008*x^20 - 12160*x^18 + 93072*x^16 - 471552*x^14 + 
    1604096*x^12 - 3649536*x^10 + 5450496*x^8 - 5156864*x^6 + 2912256*x^4 - 
    884736*x^2 + 110592));
PC12<T,y,z> := ProjectiveClosure(C12);
"The modular curve X_{112,G}(48) is of",Genus(PC12),"and it is",IsHyperelliptic(PC12), "that the curve is hyper elliptic"; 
//We want to compute a smooth plane model of PC
Phi:= CanonicalMap(PC12);
CQ<X,Y,Z> := CanonicalImage(PC12,Phi);
P<X,Y,Z> := PolynomialRing(Integers(),3);
boo,DQ:= IsCoercible(P,DefiningPolynomial(CQ));
q2 := (Y^2 - 4*Z^2);
q1 := (Z*X + 2*Z^2);
q3 := (X^2 - 2*X*Z + 4*Z^2);
if DQ eq -q2^2 + (q1*q3) then 
"We have found our determinantal representation given by", [q1,q2,q3];
end if;
assert (IsIsomorphic(PC5,PC12) eq true);








