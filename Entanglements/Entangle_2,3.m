////////////////////////////////////////////////////////////////////////////////////
// Entanglement Data for mod 2 and mod 3
////////////////////////////////////////////////////////////////////////////////////



A2<s,t> := AffineSpace(Rationals(),2);
//Subgroups from Zywina
P<x> := PolynomialRing(Rationals());
_<T> := FunctionField(Rationals());
G2:=[
	sub<GL(2,2) | {[1,0,0,1]}>,
	sub<GL(2,2) | {[1,1,0,1]}>,
	sub<GL(2,2) | {[1,1,1,0]}>
	];
J2:=[
	256*(T^2+T+1)^3/(T^2*(T+1)^2),
	256*(T+1)^3/T,
	T^2+1728
	];
G3:=[
	sub<GL(2,3) | {[-1,0,0,-1],[1,0,0,2]}>,
	sub<GL(2,3) | {[1,0,0,2],[2,0,0,1],[0,-1,1,0]}>,
	sub<GL(2,3) | {[1,1,0,1],[2,0,0,1],[1,0,0,2]}>,
	sub<GL(2,3) | {[1,0,0,-1],[-1,0,0,-1],[0,-1,1,0],[1,1,-1,1]}>
	];
H3:=[
	[sub<GL(2,3) | {[1,0,0,2]}>], 
    	[],
    	[sub<GL(2,3) | {[1,0,0,2],[1,1,0,1]}>, sub<GL(2,3) | {[2,0,0,1],[1,1,0,1]}>],
    	[]
	];
J3:=[
	27*(T+1)^3*(T+3)^3*(T^2+3)^3/(T^3*(T^2+3*T+3)^3),
	27*(T+1)^3*(T-3)^3/T^3,
	27*(T+1)*(T+9)^3/T^3,
	T^3
	];

W3:=[ [-3*(T+1)*(T+3)*(T^2+3),-2*(T^2-3)*(T^4+6*T^3+18*T^2+18*T+9)], [], [-3*(T+1)^3*(T+9),-2*(T+1)^4*(T^2-18*T-27)],  [] ];

GG3 := GL(2,3);

/*------------------------------ X_{G_3,G_3}(6) -------------------------------------*/
C:= Curve(A2, (s^2+1728)*t^3 - (27*(t+1)*(t+9)^3));
PC<S,T,Z> := ProjectiveClosure(C);
assert (Genus(PC) eq 0); 
assert (not IsConic(PC)) and (not IsRationalCurve(PC));
pts:=Points(PC);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

NormalSubgroups(G3[3]);

S := Subgroups(G3[3]); //Now we check this for any subgroup of G9
S3 := [];
for i in [1..#S] do
if IsDivisibleBy(Order(S[i]`subgroup),3) then
S3 := S3 cat [S[i]`subgroup];
end if;
end for;

for j in [1..#S3] do
N := NormalSubgroups(S3[j]);
for i in [1..#N] do
if Order(S3[j])/Order(N[i]`subgroup) eq 3 then
S3[j],N[i]`subgroup;
end if;
end for;
"****************************";
end for;

//Sieving using Gorsat, tells us that there cannot be entanglement



/*------------------------------ X_{G_2,G_2}(6) ----------------------------------*/
C:= Curve(A2, s*27*(t+1)^3*(t-3)^3 - (t^3*256*(s+1)^3));
PC<S,T,Z> := ProjectiveClosure(C);
assert (Genus(PC) eq 0); //
assert (not IsConic(PC)) and (not IsRationalCurve(PC));
pts:=Points(PC);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

NormalSubgroups(G3[2]);
//Goursat does not sieve anything out
g := 256*(x+1)^3/x;
f := phi([x,1])[1]/phi([x,1])[3];
j := Evaluate(g,f);
Entangle1 := [];
for i in [-1000..1000] do
 if Evaluate(Denominator(j),i) ne 0 then
 E:= EllipticCurveWithjInvariant(Evaluate(j,i)); 
    [Degree(SplittingField(DivisionPolynomial(E,  
       2))),Degree(SplittingField(DivisionPolynomial(E,3)))];
 D2 := SplittingField(DivisionPolynomial(E,2));
 if Degree(SplittingField(DivisionPolynomial(E,3))) eq 2 then
   if IsIsomorphic(D2,SplittingField(DivisionPolynomial(E,3))) eq true then
    HasComplexMultiplication(E);
    Entangle1 := Entangle1 cat [1,jInvariant(E)];
   end if;
 else
 for k in [2..#SubfieldLattice(SplittingField(DivisionPolynomial(E,3)))] do
   D3 :=  NumberField(SubfieldLattice(SplittingField(DivisionPolynomial(E,3)))[k]);
   if IsIsomorphic(D3,D2) eq true then
    HasComplexMultiplication(E);
    Entangle1 := Entangle1 cat [1,jInvariant(E)];
   end if;
  end for;
 end if;
 end if;
end for;


assert (#Entangle1 ne 0);

C24 := Curve(A2, Evaluate(Denominator(j),t)*Evaluate(JBj,s) -Evaluate(Numerator(j),t)); 

/*------------------------------ X_{G_2,G_1}(6) ----------------------------------*/
C := Curve(A2 , t^3*(t^2+3*t+3)^3*256*(s+1)^3 - (s*27*(t+1)^3*(t+3)^3*(t^2+3)^3));
PC<S,T,Z> := ProjectiveClosure(C);
assert (Genus(PC) eq 0);
assert (not IsConic(PC)) and (not IsRationalCurve(PC));
pts:=Points(PC);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

NormalSubgroups(G3[1]);
//Goursat does not sieve anything out
g := 256*(x+1)^3/x;
f := phi([x,1])[1]/phi([x,1])[3];
j := Evaluate(g,f);
Entangle2 := [];
for i in [-1000..1000] do
 if Evaluate(Denominator(j),i) ne 0 then
 E:= EllipticCurveWithjInvariant(Evaluate(j,i)); 
    [Degree(SplittingField(DivisionPolynomial(E,  
       2))),Degree(SplittingField(DivisionPolynomial(E,3)))];
 D2 := SplittingField(DivisionPolynomial(E,2));
 if Degree(SplittingField(DivisionPolynomial(E,3))) eq 2 then
   if IsIsomorphic(D2,SplittingField(DivisionPolynomial(E,3))) eq true then
    Entangle2 := Entangle2 cat [2,jInvariant(E)];
   end if;
 else
 for k in [2..#SubfieldLattice(SplittingField(DivisionPolynomial(E,3)))] do
   D3 :=  NumberField(SubfieldLattice(SplittingField(DivisionPolynomial(E,3)))[k]);
   if IsIsomorphic(D3,D2) eq true then
    Entangle2 := Entangle2 cat [2,jInvariant(E)];
   end if;
  end for;
 end if;
 end if;
end for;

assert (#Entangle2 eq 0);


/*------------------------------ X_{G_2,G_3}(6) --------------------------------------*/
C:= Curve(A2, s*27*(t+1)*(t+9)^3 - (t^3*256*(s+1)^3));
PC<S,T,Z> := ProjectiveClosure(C);
assert (Genus(PC) eq 0);
assert (not IsConic(PC)) and (not IsRationalCurve(PC));
pts:=Points(PC);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

NormalSubgroups(G3[3]);
//Goursat does not sieve anything out
g := 256*(x+1)^3/x;
f := phi([x,1])[1]/phi([x,1])[3];
j := Evaluate(g,f);
Entangle3 := [];
for i in [-100..100] do
 if Evaluate(Denominator(j),i) ne 0 then
 E:= EllipticCurveWithjInvariant(Evaluate(j,i)); 
    [Degree(SplittingField(DivisionPolynomial(E,  
       2))),Degree(SplittingField(DivisionPolynomial(E,3)))];
 D2 := SplittingField(DivisionPolynomial(E,2));
 if Degree(D2) ne 1 then
 if Degree(SplittingField(DivisionPolynomial(E,3))) eq 2 then
   if IsIsomorphic(D2,SplittingField(DivisionPolynomial(E,3))) eq true then
    Entangle3 := Entangle3 cat [3,jInvariant(E)];
   end if;
 else
 for k in [2..#SubfieldLattice(SplittingField(DivisionPolynomial(E,3)))] do
   D3 :=  NumberField(SubfieldLattice(SplittingField(DivisionPolynomial(E,3)))[k]);
   if IsIsomorphic(D3,D2) eq true then
    Entangle3 := Entangle3 cat [3,jInvariant(E)];
   end if;
  end for;
 end if;
 end if;
 end if;
end for;

assert (#Entangle3 ne 0);


/*------------------------------ X_{G_2,G_4}(6) ----------------------------------*/
C:= Curve(A2, s*t^3 - (256*(s+1)^3));
PC<S,T,Z> := ProjectiveClosure(C);
assert (Genus(PC) eq 0);
assert (not IsConic(PC)) and (not IsRationalCurve(PC));
pts:=Points(PC);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));

NormalSubgroups(G3[4]);
//Goursat does not sieve anything out
g := 256*(x+1)^3/x;
f := phi([x,1])[1]/phi([x,1])[3];
j24 := Evaluate(g,f);
Entangle41 := [];
for i in [-100..100] do
 if Evaluate(Denominator(j24),i) ne 0 then
 E:= EllipticCurveWithjInvariant(Evaluate(j24,i)); 
    [Degree(SplittingField(DivisionPolynomial(E,  
       2))),Degree(SplittingField(DivisionPolynomial(E,3)))];
 D2 := SplittingField(DivisionPolynomial(E,2));
 if Degree(D2) ne 1 then
 if Degree(SplittingField(DivisionPolynomial(E,3))) eq 2 then
   if IsIsomorphic(D2,SplittingField(DivisionPolynomial(E,3))) eq true then
    Entangle41 := Entangle41 cat [4,jInvariant(E)];
   end if;
 else
 for k in [2..#SubfieldLattice(SplittingField(DivisionPolynomial(E,3)))] do
   D3 :=  NumberField(SubfieldLattice(SplittingField(DivisionPolynomial(E,3)))[k]);
   if IsIsomorphic(D3,D2) eq true then
    Entangle41 := Entangle41 cat [4,jInvariant(E)];
   end if;
  end for;
 end if;
 end if;
 end if;
end for;

assert (#Entangle4 ne 0);

Entangle := Entangle1 cat Entangle2 cat Entangle3 cat Entangle4;
Entangle;




/*-----------------------------Brau/Jones_Data------------------------------------*/
NormalSubgroups(GG3);
JB := sub<GL(2,3) | {[0,2,1,0],[1,2,2,2],[2,0,0,2]}>; //index 6 normal subgroup of GL(2,3)
JBj := 2^10*3^3*x^3*(1 - 4*x^3);
for i in [-10..10] do
 if i ne 0 then
 if Evaluate(Denominator(JBj),i) ne 0 then
 E:= EllipticCurveWithjInvariant(Evaluate(JBj,i)); 
 WeierstrassModel(E);
    [Degree(SplittingField(DivisionPolynomial(E,  
       2))),Degree(SplittingField(DivisionPolynomial(E,3)))];
  L := Compositum(CyclotomicField(3),NumberField(x^3 - Discriminant(E))); 
  boo1,_ := IsIsomorphic(SplittingField(DivisionPolynomial(E,2)),L);
  boo2,_ := IsIsomorphic(GaloisGroup(L),SymmetricGroup(3));
  boo3,_:= HasComplexMultiplication(E);
  [boo1,boo2,boo3];
  "*******************";
  end if;
  end if;
end for;

// Check that the only t for which JBj is CM are 0 and 1/2
CMj := [0, 54000, -12288000, 1728, 287496, -3375, 16581375, 8000, -32768, 
-884736, -884736000, -147197952000, -262537412640768000];
for i in [1..#CMj] do
  Roots(JBj - CMj[i]);
end for;

/*-----------------------------Non-abelian entangle--------------------------------*/
NormalSubgroups(G3[3]);
N := sub<GL(2,3) | {[2,0,0,2]}>;
C:= Curve(A2, 2^10*3^3*s^3*(1 - 4*s^3)*t^3 - 27*(t+1)*(t+9)^3); 
assert (Genus(C) eq 0);
PC<S,T,Z> := ProjectiveClosure(C);
pts := Points(PC);
pt := pts[1];
P1<u,v> := ProjectiveSpace(Rationals(),1);
phi := Parametrization(PC,pt,Curve(P1));
f := phi([x,1])[1]/phi([x,1])[3];
J := Evaluate(JBj,f);

E := EllipticCurveWithjInvariant(J);
M<t> := FunctionField(Rationals());
EE:= EllipticCurve([-3*(t+1)^3*(t+9),-2*(t+1)^4*(t^2-18*t-27)]);
assert (IsIsomorphic(E,EE) eq false);
assert (IsIsomorphic(E,QuadraticTwist(EE,-3)) eq false);

D3 := DivisionPolynomial(E,3);
beta := Roots(Factorization(D3)[1,1])[1,1];
A:=aInvariants(E);     
P<t> := PolynomialRing(Rationals());
f<t> := t^3 + A[4]*t + A[5];
alpha := Evaluate(f,beta);
assert (Degree(Numerator(alpha)) eq 324) and (IsIrreducible(Numerator(alpha)) eq true);
assert (Degree(Denominator(alpha)) eq 324) and (IsIrreducible(Denominator(alpha)) eq false);

//alpha is still too difficult to work with because we have some irreducible polynomial of really high degree

//This tells us that curves of the form E will have \rho_{E,3} \iso G_3 and computes some example of the entanglement fields

P<t> := FunctionField(Rationals());
for i in [-50..50] do
 if Evaluate(Denominator(J),i) ne 0 then
 i;
 E:= EllipticCurveWithjInvariant(Evaluate(J,i)); 
    [Degree(SplittingField(DivisionPolynomial(E,  
       2))),Degree(SplittingField(DivisionPolynomial(E,3)))];
  boo1,_:= IsIsomorphic(SplittingField(DivisionPolynomial(E,2)),SplittingField(DivisionPolynomial(E,3)));
   L := Compositum(CyclotomicField(3),NumberField(x^3 - Discriminant(E))); 
 boo2,_ := IsIsomorphic(L,SplittingField(DivisionPolynomial(E,3)));
   boo3,_:= HasComplexMultiplication(E);
  M := NumberField(x^2 - Discriminant(E));
  boo4,_ := IsIsomorphic(M,CyclotomicField(3));
  if 4*AbsoluteValue(Evaluate(-3*(t+1)^3*(t+9),i)^3) - 27*AbsoluteValue(Evaluate(-2*(t+1)^4*(t^2-18*t-27),i)^2) ne 0 then
  EE:= EllipticCurve([Evaluate(-3*(t+1)^3*(t+9),i),Evaluate(-2*(t+1)^4*(t^2-18*t-27),i)]);
  boo5 := IsIsomorphic(E,EE);
  boo6 := IsIsomorphic(E,QuadraticTwist(EE,-3));
  else 
  boo5 := "Empty";
  boo6 := "Empty";
  end if;
  [boo1,boo2,boo3,boo4];
  [boo5,boo6];
  "*******************";
  end if;
end for;

