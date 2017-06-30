////////////////////////////////////////////////////////////////////////////////////
// Computations for the mod 2 and mod 7 simultaneous computations
////////////////////////////////////////////////////////////////////////////////////


_<t>:=FunctionField(Rationals());

J7:=[
	3^3*5*7^5/2^7,
    	t*(t+1)^3*(t^2-5*t+1)^3*(t^2-5*t+8)^3*(t^4-5*t^3+8*t^2-7*t+7)^3/(t^3-4*t^2+3*t+1)^7,
    	(t^2-t+1)^3*(t^6-11*t^5+30*t^4-15*t^3-10*t^2+5*t+1)^3/((t-1)^7*t^7*(t^3-8*t^2+5*t+1)),
    	(t^2-t+1)^3*(t^6+229*t^5+270*t^4-1695*t^3+1430*t^2-235*t+1)^3/((t-1)*t*(t^3-8*t^2+5*t+1)^7),
    	-(t^2-3*t-3)^3*(t^2-t+1)^3*(3*t^2-9*t+5)^3*(5*t^2-t-1)^3/((t^3-2*t^2-t+1)*(t^3-t^2-2*t+1)^7),
    	64*t^3*(t^2+7)^3*(t^2-7*t+14)^3*(5*t^2-14*t-7)^3/(t^3-7*t^2+7*t+7)^7,
    	(t^2+245*t+2401)^3*(t^2+13*t+49)/t^7
	];
G7:=[
	sub<GL(2,7) | {[2,0,0,4], [0,2,1,0],[-1,0,0,-1]}>,
	sub<GL(2,7) | {[3,0,0,1],[1,0,0,3],[0,-1,1,0]}>,
	sub<GL(2,7) | {[-1,0,0,-1],[1,1,0,1],[1,0,0,3]}>,
	sub<GL(2,7) | {[-1,0,0,-1],[1,1,0,1],[3,0,0,1]}>,
	sub<GL(2,7) | {[1,1,0,1],[3,0,0,3],[1,0,0,-1]}>,
	sub<GL(2,7) | {[1,-4,4,1],[1,0,0,-1]}>,
	sub<GL(2,7) | {[3,0,0,1],[1,0,0,3],[1,1,0,1]}>
	];


Q<x> := PolynomialRing(Rationals());
A2<s,t> := AffineSpace(Rationals(),2);
Summ := [];


/*----------------------------X_{G_3,G_7}(14)----------------------------------*/
M7:= Q!(x*(Numerator(J7[7]) - 1728*Denominator(J7[7])));
C7:= Curve(A2, s^2 - (t^9 - 980*t^8 + 196882*t^7 + 20706224*t^6 + 695893835*t^5 + 10976181104*t^4 + 
    90957030178*t^3 + 387556041628*t^2 + 678223072849*t));
PC7<S,T,Z> := ProjectiveClosure(C7);
assert (Genus(PC7) eq 0);
pts:=Points(PC7);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC7,pt,Curve(P1));


NormalSubgroups(G7[7]);
//Goursat does not sieve anything out

P2<X,jj> := PolynomialRing(Rationals(),2);
j:= ((x^8 - 490*x^6 - 21609*x^4 - 235298*x^2 - 823543)/(x^7))^2 + 1728;
Entangle7 := [];
for i in [1..10] do
 if Evaluate(Denominator(j),i) ne 0 then
 J:= Evaluate(j,i);
 E:= EllipticCurveWithjInvariant(J); 
 ModPoly := P2!AtkinModularPolynomial(7);
 SubPoly := Evaluate(ModPoly,[x,J]);
    [J,Degree(SplittingField(DivisionPolynomial(E,  
       2))),Order(GaloisGroup(SubPoly))];
 D2 := SplittingField(DivisionPolynomial(E,2));
 if Degree(D2) ne 1 then
 S:=SubfieldLattice(SplittingField(SubPoly));
 for k in [2..#S] do
   D7 :=  NumberField(S[k]);
   if Degree(D7) eq 3 then
     if IsIsomorphic(D7,D2) eq true then
       E; k;
       IsAbelian(D7);
     end if;
   end if;
  end for;
 end if;
 end if;
end for;