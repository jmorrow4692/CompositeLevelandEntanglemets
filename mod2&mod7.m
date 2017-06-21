////////////////////////////////////////////////////////////////////////////////////
// Computations for the mod 2 and mod 7 simultaneous computations
////////////////////////////////////////////////////////////////////////////////////


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

// ell=7
G7:=[
	sub<GL(2,7) | {[2,0,0,4], [0,2,1,0],[-1,0,0,-1]}>,
	sub<GL(2,7) | {[3,0,0,1],[1,0,0,3],[0,-1,1,0]}>,
	sub<GL(2,7) | {[-1,0,0,-1],[1,1,0,1],[1,0,0,3]}>,
	sub<GL(2,7) | {[-1,0,0,-1],[1,1,0,1],[3,0,0,1]}>,
	sub<GL(2,7) | {[1,1,0,1],[3,0,0,3],[1,0,0,-1]}>,
	sub<GL(2,7) | {[1,-4,4,1],[1,0,0,-1]}>,
	sub<GL(2,7) | {[3,0,0,1],[1,0,0,3],[1,1,0,1]}>
	];

Q<X> := PolynomialRing(Integers());
A2<s,t> := AffineSpace(Rationals(),2);



/*----------------------------X_{A_3,G_2}(14)----------------------------------*/
M2 := Q!(Denominator(J7[2])*Numerator(J7[2]) - 1728*Denominator(J7[2])^2);
Factorization(M2);
H2 := HyperellipticCurve((X^3 - 4*X^2 + 3*X + 1)*(X^4 - 10*X^3 + 27*X^2 - 10*X - 27));
assert (Genus(H2) eq 3);
ptsH2 := RationalPoints(H2 : Bound := 1000);
SingularPoints(H2);
PointsAtInfinity(H2);
J:= Jacobian(H2);
assert (RankBound(J) eq 0);

// We prove that the point at infinity is the only point on H2 using the MW-sieve
// We need to use local data

torsOrders := {@@};
bad := BadPrimes(H2);
bool := false; p := 2;
while  p le 30 do
  p :=  NextPrime(p);        
  p := p in bad select NextPrime(p) else p;
  pvalues := {@@};
  F := FiniteField(p);
  PF<A> := PolynomialRing(F);
  f := (A^3 - 4*A^2 + 3*A + 1) ;
  g := (A^4 - 10*A^3 + 27*A^2 - 10*A - 27);
  Hp := HyperellipticCurve(f*g);
  numH := Numerator(ZetaFunction(Hp));  
  torsOrders :=   torsOrders join  {@ Evaluate(numH,1) @};
  [p,GCD(torsOrders)];
  Invariants(ClassGroup(Hp));
  "*******************";
end while;

/* This computation shows that the possible torsion orders are 1,2,3,6. */


for p in [1..7] do 
if IsPrime(p) eq true and (p ne 2 ) and (p ne 7) then
F := FiniteField(p);
P<A> := PolynomialRing(F);
  f := (A^3 - 4*A^2 + 3*A + 1) ;
  Factorization(f);
  g := (A^4 - 10*A^3 + 27*A^2 - 10*A - 27);
  Factorization(g);  
  H := HyperellipticCurve(f*g);
J := DivisorGroup(H);
pts := RationalPoints(H);
p;
{order(J!(Divisor(P) - Divisor(Q))) : P,Q in pts};
"**********************";
end if;
end for;

/*
Ok so at 3, we only find 2 torsion and since prime to 2 torsion injects via Katz, we have that there is no 3 torsion. Moreover at 5, we find that the only possible torsion would be 3 torsion. Moreover, since the hyper elliptic polynomials do not factor mod 5, we have no two torsion. Initially, I thought that the data at 5 would tell us that we have no 2 torsion, but it may not inject, so this kind of order is allowable. 

Therefore, we have that the rational points on H2 generate trivial torsion on J, and thus, we have no rational smooth points on C2.
*/

// X_{A_3,G_2}(14) is a genus 3 hyper elliptic curve with rank 0 and only one point at infinity. 


/*----------------------------X_{A_3,G_1}(14)----------------------------------*/
// Not needed since covered by X_{A_3,G_2}(14), but it is clear to see
assert (IsSquare(3^3*5*7^5/2^7 - 1728) eq false);


/*----------------------------X_{A_3,G_7}(14)----------------------------------*/
M7 := Q!(Denominator(J7[7])*Numerator(J7[7]) - 1728*Denominator(J7[7])^2);
Factorization(M7);  
C7:= Curve(A2, s^2 - t);
PC7<S,T,Z> := ProjectiveClosure(C7);
assert (Genus(PC7) eq 0);
pts:=Points(PC7);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC7,pt,Curve(P1));

// X_{A_3,G_7}(14) is a P^1


/*----------------------------X_{A_3,G_5}(14)----------------------------------*/
M5 := Q!(Denominator(J7[5])*Numerator(J7[5]) - 1728*Denominator(J7[5])^2);
Factorization(M5);  
H5 := HyperellipticCurve(-7*(X^3 - X^2 - 2*X + 1)*(X^3 - 2*X^2 - X + 1));
J:= Jacobian(H5);
ptsH5:= RationalPoints(H5 : Bound := 100);
assert (Genus(H5) eq 2) and (RankBound(J) eq 0);
pts := Chabauty0(J); pts;

// X_{A_3,G_5}(14) is a genus 2 curve with no rational points

/*----------------------------X_{A_3,G_4}(14)----------------------------------*/
M4:= Q!(Denominator(J7[4])*Numerator(J7[4]) - 1728*Denominator(J7[4])^2);
Factorization(M4); 
H4 := HyperellipticCurve(X*(X-1)*(X^3 - 8*X^2 + 5*X + 1));
J:= Jacobian(H4);
// assert (RankBound(J) eq 0); perform these computations using the Magma online calculator
ptsH := Chabauty0(J); ptsH;
SingularPoints(H4);
PointsAtInfinity(H4);

// X_{A_3,G_4}(14) is a genus 2 curve two cuspidal points

/*----------------------------X_{A_3,G_3}(14)----------------------------------*/
M3 := Q!(Denominator(J7[3])*Numerator(J7[3]) - 1728*Denominator(J7[3])^2);
SquareFreeFactorization(M3); 
H3 := HyperellipticCurve(X*(X-1)*(X^3 - 8*X^2 + 5*X + 1));
J:= Jacobian(H3);
// assert (RankBound(J) eq 0); perform these computations using the Magma online calculator
ptsH := Chabauty0(J); ptsH;
SingularPoints(H3);
PointsAtInfinity(H3);

// X_{A_3,G_3}(14) is a genus 2 curve two cuspidal points


/*----------------------------X_{G_3,G_6}(14)----------------------------------*/
M6 := Q!(Denominator(J7[6])*Numerator(J7[6]) - 1728*Denominator(J7[6])^2);
Factorization(M6); 

HH := HyperellipticCurve((X-3)*(X^3-7*X^2 + 7*X + 7)*(2*X^4 - 14*X^3 + 21*X^2 + 28*X + 7));
f := HyperellipticPolynomials(H);
F<X> := 8*X^3 + 8*X^2 - 2*X - 1;
G<X> := 64*X^4 - 8*X^3 + 3*X^2 + 10*X + 2;
_,H,phi := HasOddDegreeModel(HH);
ff := HyperellipticPolynomials(H);
assert (-F*G eq ff);
ptsH := RationalPoints(H : Bound:=10000);

/*Our original even degree hyper elliptic curve had a no trivial point corresponding to the known point in C6. We take the odd degree model in order to use all intrinsics of hyper elliptic curves. This mapping moves the known points to the one at infinity. Moreover, we want to show that this is the only point on H */

J := Jacobian(H);
assert (RankBound(J) eq 0);

torsOrders := {@@};
bad := BadPrimes(H);
bool := false; p := 2;
while  p le 30 do
  p :=  NextPrime(p);        
  p := p in bad select NextPrime(p) else p;
  pvalues := {@@};
  F := FiniteField(p);
  PF<A> := PolynomialRing(F);
  f := 8*A^3 + 8*A^2 - 2*A - 1;
  g := 64*A^4 - 8*A^3 + 3*A^2 + 10*A + 2;
  Hp := HyperellipticCurve(-f*g);
  numH := Numerator(ZetaFunction(Hp));  
  torsOrders :=   torsOrders join  {@ Evaluate(numH,1) @};
  [p,GCD(torsOrders)];
  Invariants(ClassGroup(Hp));
  "*******************";
end while;

for p in [1..17] do 
if IsPrime(p) eq true and (p ne 2 ) and (p ne 7) then
F := FiniteField(p);
P<A> := PolynomialRing(F);
  f := 8*A^3 + 8*A^2 - 2*A - 1;
  Factorization(f);
  g := 64*A^4 - 8*A^3 + 3*A^2 + 10*A + 2;
  Factorization(g);
  H := HyperellipticCurve(-f*g);
J := DivisorGroup(H);
pts := RationalPoints(H);
p;
{order(J!(Divisor(P) - Divisor(Q))) : P,Q in pts};
"**********************";
end if;
end for;


/*
Same argument as above.
/*

// X_{G_3,G_6}(14) is a genus 3 hyper elliptic curve with only one point at infinity.