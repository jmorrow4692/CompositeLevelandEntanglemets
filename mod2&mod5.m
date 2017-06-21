////////////////////////////////////////////////////////////////////////////////////
// Computations for the mod 2 and mod 5 simultaneous computations
////////////////////////////////////////////////////////////////////////////////////

//Equations from Zywina
_<t>:=FunctionField(Rationals());
J5:=[
	(t^20+228*t^15+494*t^10-228*t^5+1)^3/(t^5*(t^10-11*t^5-1)^5),
	(t^2+5*t+5)^3*(t^4+5*t^2+25)^3*(t^4+5*t^3+20*t^2+25*t+25)^3/(t^5*(t^4+5*t^3+15*t^2+25*t+25)^5),
	5^4*t^3*(t^2+5*t+10)^3*(2*t^2+5*t+5)^3*(4*t^4+30*t^3+95*t^2+150*t+100)^3/((t^2+5*t+5)^5*(t^4+5*t^3+15*t^2+25*t+25)^5),
	(t+5)^3*(t^2-5)^3*(t^2+5*t+10)^3/(t^2+5*t+5)^5,
	(t^4+228*t^3+494*t^2-228*t+1)^3/(t*(t^2-11*t-1)^5),
	(t^4-12*t^3+14*t^2+12*t+1)^3/(t^5*(t^2-11*t-1)),
	5^3*(t+1)*(2*t+1)^3*(2*t^2-3*t+3)^3/(t^2+t-1)^5,
	5^2*(t^2+10*t+5)^3/t^5,
	t^3*(t^2+5*t+40)
	];

Q<X> := PolynomialRing(Integers());
A2<s,t> := AffineSpace(Rationals(),2);


/*------------------------------ X_{A_3,G_9}(10) -------------------------------------*/
M9 := Q!(Denominator(J5[9])*Numerator(J5[9]) - 1728*Denominator(J5[9])^2);
Factorization(M9);
C9:= Curve(A2, s^2 - (t-3));
PC9<S,T,Z> := ProjectiveClosure(C9);
assert (Genus(PC9) eq 0);
pts:=Points(PC9);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC9,pt,Curve(P1));

// Thus, X_{A_3,G_9}(10) is a P^1


/*------------------------------ X_{A_3,G_4}(10) -------------------------------------*/
M4 := Q!(Denominator(J5[4])*Numerator(J5[4]) - 1728*Denominator(J5[4])^2);
Factorization(M4);
C4 := Curve(A2, s^2 - ((t+2)*(t^2 -20)*(t^2 + 5*t + 5)));
pts := PointSearch(C4,1000);
assert (Genus(C4) eq 2);
boo, H, phi := IsHyperelliptic(C4);
assert (boo eq true);
J := Jacobian(H);
assert (RankBound(J) eq 0);
ptsH := Chabauty0(J);
for P in ptsH do
  Points(P@@phi);
end for;
pts;
SingularPoints(C4);

// X_{A_3,G_4}(10) is a genus 2 curve with only one CM point

/*------------------------------ X_{A_3,G_2}(10) -------------------------------------*/
//Not needed since it covers X_{A_3,G_4}(10)

/*------------------------------ X_{A_3,G_1}(10) -------------------------------------*/
//Not needed since it covers X_{A_3,G_2}(10) which covers X_{A_3,G_4}(10)




/*------------------------------ X_{A_3,G_7}(10) -------------------------------------*/
M7 := Q!(Denominator(J5[7])*Numerator(J5[7]) - 1728*Denominator(J5[7])^2);
Factorization(M7);
C7 := HyperellipticCurve((X^2 + X - 1)*(8*X^2 - 12*X +7));
assert (IsLocallySoluble(GenusOneModel(C7)) eq false);
assert (IsEmpty(TwoCoverDescent(C7)) eq true);

// X_{A_3,G_7}(10) is a genus one curve without any rational points.


/*------------------------------ X_{A_3,G_3}(10) -------------------------------------*/
//Not necessary to compute since it covers X_{A_3,G_7}(10)



/*------------------------------ X_{A_3,G_8}(10) -------------------------------------*/
M8 := Q!(Denominator(J5[8])*Numerator(J5[8]) - 1728*Denominator(J5[8])^2);
Factorization(M8);
C8 := Curve(A2,s^2 - (t*(25*t^2 + 22*t + 5)));
PointSearch(C8,1000);
PC8 := ProjectiveClosure(C8);
assert (Genus(PC8) eq 1);
pts:=Points(PC8);
E,phi := EllipticCurve(PC8,pts[1]);
assert (Rank(E) eq 0) and (#TorsionSubgroup(E) eq 2);
ptsE:= RationalPoints(E : Bound := 1000);
for P in ptsE do
  Points(P@@phi);
end for;
pts;
SingularPoints(PC8);

// X_{A_3,G_8}(10) is a rank 0 elliptic curve with 2-torsion coming from a CM point.

/*------------------------------ X_{A_3,G_6}(10) -------------------------------------*/
//Not necessary to compute since it covers X_{A_3,G_8}(10)

/*------------------------------ X_{A_3,G_5}(10) -------------------------------------*/
//Not necessary to compute since it covers X_{A_3,G_8}(10)

