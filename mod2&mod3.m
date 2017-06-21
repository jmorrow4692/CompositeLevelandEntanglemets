////////////////////////////////////////////////////////////////////////////////////
// Computations for the mod 2 and mod 3 simultaneous computations
////////////////////////////////////////////////////////////////////////////////////


_<t> := FunctionField(Rationals());

//Equations coming from Zywina
J3:=[
	27*(t+1)^3*(t+3)^3*(t^2+3)^3/(t^3*(t^2+3*t+3)^3),
	27*(t+1)^3*(t-3)^3/t^3,
	27*(t+1)*(t+9)^3/t^3,
	t^3
	];
A2<s,t> := AffineSpace(Rationals(),2);
Q<x> := PolynomialRing(Integers());


/*------------------------------ X_{A_3,G_3}(6) ----------------------------------*/
M3 := Q!(Denominator(J3[3])*Numerator(J3[3]) - 1728*Denominator(J3[3])^2);
Factorization(M3);
C3:= Curve(A2, s^2 - (3*t));
PC3<S,T,Z> := ProjectiveClosure(C3);
assert (Genus(PC3) eq 0);
pts:=Points(PC3);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC3,pt,Curve(P1));

// X_{A_3,G_3}(6) is a P^1


/*------------------------------ X_{A_3,G_4}(6) ---------------------------------*/
E:= EllipticCurve([0,-1728]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 2);
pt := E![12,0];
assert (Order(pt) eq 2); 

// X_{A_3,G_4}(6) is a rank zero elliptic curve with a CM point corresponding to j = 1728


/*------------------------------ X_{A_3,G_2}(6) ---------------------------------*/
M2 := Q!(Denominator(J3[2])*Numerator(J3[2]) - 1728*Denominator(J3[2])^2);
Factorization(M2);
C2 := Curve(A2,s^2 - (3*t*(t^2 - 6*t - 3)));
PointSearch(C2,1000);
PC2 := ProjectiveClosure(C2);
assert (Genus(PC2) eq 1);
pts:=Points(PC2);
E,phi := EllipticCurve(PC2,pts[1]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 2);
ptsE:= RationalPoints(E : Bound := 1000);
for P in ptsE do
  Points(P@@phi);
end for;
pts;

// X_{A_3,G_2}(6) is a rank 0 elliptic curve with a CM point


/*------------------------------ X_{A_3,G_1}(6) ---------------------------------*/
//The model of this curve is not needed since X_{A_3,G_2}(6) covers this curve



/*------------------------------ X_{G_2,G_2}(6) ----------------------------------*/
J3[2];
C:= Curve(A2, s*27*(t+1)^3*(t-3)^3 - (t^3*256*(s+1)^3));
ptsC := PointSearch(C,1000); ptsC;
assert (IsSingular(C) eq true);
assert (Genus(C) eq 0);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[2] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD); //3
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(PC) eq 0); 
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[2]),Curve(P1));

// X_{G_2,G_2}(6) is a P^1


/*------------------------------ X_{G_2,G_1}(6) ----------------------------------*/
J3[1];
C := Curve(A2 , t^3*(t^2+3*t+3)^3*256*(s+1)^3 - (s*27*(t+1)^3*(t+3)^3*(t^2+3)^3));
ptsC := PointSearch(C,1000); ptsC;
assert (IsSingular(C) eq true);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] +  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[2];
Degree(DD); //3
phi := DivisorMap(Divisor(DD));
canC := Image(phi); //takes a while ~ 1hr
assert (Genus(PC) eq 0); 
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[1]),Curve(P1));

//X_{G_2,G_1}(6) is a P^1

/*------------------------------ X_{G_2,G_3}(6) --------------------------------------*/
J3[3];
C:= Curve(A2, s*27*(t+1)*(t+9)^3 - (t^3*256*(s+1)^3));
ptsC := PointSearch(C,1000); ptsC;
assert (IsSingular(C) eq true);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] +  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[4];
Degree(DD); //3
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(PC) eq 0); 
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[1]),Curve(P1));

//X_{G_2,G_3}(6) is a P^1


/*------------------------------ X_{G_2,G_4}(6) ----------------------------------*/
J3[4];
C:= Curve(A2, s*t^3 - (256*(s+1)^3));
ptsC := PointSearch(C,1000); ptsC;
assert (IsSingular(C) eq true);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD); //3
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(PC) eq 0); 
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[1]),Curve(P1));

//X_{G_2,G_4}(6) is a P^1

/*------------------------------ X_{G_1,G_3}(6) ----------------------------------*/
C:= Curve(A2, (s^2*(s+1)^2*27*(t+1)*(t+9)^3) - (t^3*256*(s^2+s+1)^3) );
ptsC := PointSearch(C,1000); ptsC;
assert (IsSingular(C) eq true);
Genus(C);
PC := ProjectiveClosure(C);
pts := PointSearch(PC,100);
P2<[X]> := AmbientSpace(PC);
L := Scheme(P2,X[1] -  X[3]);
D := Divisor(PC,L meet PC);
Support(D);
DD := Support(D)[1];
Degree(DD); //4
phi := DivisorMap(Divisor(DD));
canC := Image(phi);
assert (Genus(PC) eq 0); 
P1<u,v> := ProjectiveSpace(Rationals(),1);
Phi := Parametrization(canC,canC!phi(pts[2]),Curve(P1));

//X_{G_1,G_3}(6) is a P^1

/*------------------------------ X_{G_1,G_4}(6) ----------------------------------*/
//Not need since the curve covers X_{A_3,G_4}(6)


/*------------------------------ X_{G_1,G_2}(6) ----------------------------------*/
//Not need since the curve covers X_{A_3,G_2}(6) 


/*------------------------------ X_{G_1,G_1}(6) ----------------------------------*/
//Not need since covers X_{A_3,G_1}(6) which is covers X_{A_3,G_2}







