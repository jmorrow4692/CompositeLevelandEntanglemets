/******************************************************************************
 * routines.m
 *
 * date:   29/06/2004 (amalgamated from earlier work)
 * author: Nils Bruin
 *
 * Various routines to facilitate computation of Prym-varieties of curves of
 * genus 3 and to do Chabauty-type arguments on them.
 *
 * You may use these routines if you refer to the used software in any ensuing
 * publications.
 ******************************************************************************/
 
declare attributes JacHyp:Curve;
declare attributes SrfKum:Scheme;
declare attributes Sch:IsKummer, Twice, BBMatrix;

/******************************************************************************
 * IMPORTED FROM MAGMA PACKAGE TREE
 *
 * NOTE: StrLocalDataRecFormat is statically imported here and might break
 *       if format is changed in future versions.
 ******************************************************************************/

/******************************************************************************
 *
 *
 * localdata.m
 *
 * date:   08/01/2003
 * author: Nils Bruin
 *
 * Stores data in a structure, indexed by prime ideals.
 * Anyone interested can add fields to the recformat StrLocalRecFormat below.
 *
 * In order to not interfere with other clients of this structure, adhere to
 * the following call sequence:
 *
 * r:=GetLocalData(S,p);
 * r`fieldname:=value;
 * StoreLocalData(S,p,r);
 *
 * To use,
 *
 *import "localdata.m":GetLocalData,StoreLocalData;
 ******************************************************************************/
 
declare attributes Str:StrLocalData;

StrLocalDataRecFormat:=recformat<
    
    //for isogenies (2 and mult-by-2) of elliptic curves
    xlist,twotor,twotorimg,
    
    //for mwmaps (maps from abelian group to an elliptic curve)
    reduction,
    
    //for absolute algebras
    TwoSelmerMap,TwoSelmerMapComponents
    >;

function GetLocalData(S,p)
//  {Retrieve information stored on a structure, indexed by a prime ideal}
  if not(assigned(S`StrLocalData)) then
    S`StrLocalData:=[];
  end if;
  if exists(t){u[2]: u in S`StrLocalData | u[1] eq p} then
    return t;
  else
    return rec<StrLocalDataRecFormat|xlist:=[]>;
  end if;
end function;

procedure StoreLocalData(S, p, data) // (S::Str,p::RngOrdIdl,data::Rec)
//  {Store information on a structure, indexed by a prime ideal}
  if not(assigned(S`StrLocalData)) then
    S`StrLocalData:=[];
  end if;
  if exists(j){i:i in [1..#S`StrLocalData] | S`StrLocalData[i][1] eq p} then
    S`StrLocalData[j]:=<p,data>;
  else
    Append(~S`StrLocalData,<p,data>);
  end if;
end procedure;

/******************************************************************************
 * END OF MAGMA PACKAGE IMPORT
 ******************************************************************************/


intrinsic Reduction(C::CrvHyp,p::RngIntElt)->CrvHyp,Map
  {returns a reduction for a hyperelliptic curve}
  require BaseRing(C) eq Rationals():
    "C must be over the rationals";
  if not(assigned GetLocalData(C,p)`reduction) then
    Cr:=BaseChange(C,Coercion(Rationals(),GF(p)));
    w:=Gradings(C)[1][2];
    redmap:=function(a)
      if Valuation(a[3],p) gt Valuation(a[1],p) then
        return Cr![GF(p)!c: c in [1,a[2]/a[1]^w,a[3]/a[1]]];
      else
        return Cr![GF(p)!c: c in [a[1]/a[3],a[2]/a[3]^w,1]];
      end if;
    end function;
    rc:=GetLocalData(C,p);
    rc`reduction:=map<C(Rationals())->Cr(GF(p))| p:->redmap(p)>;
    StoreLocalData(C,p,rc);
  end if;
  rc:=GetLocalData(C,p);
  return Codomain(rc`reduction),rc`reduction;
end intrinsic;

intrinsic Reduction(J::JacHyp,p::RngIntElt)->JacHyp,Map
  {}
  require BaseRing(J) eq Rationals():
     "J must be over the rationals";
  if not(assigned GetLocalData(J,p)`reduction) then
    Cr:=Reduction(Curve(J),p);
    CrIsOdd:=IsOdd(Degree(HyperellipticPolynomials(Cr)));
    Jr:=Jacobian(Cr);
    FF:=BaseRing(Jr);
    PQ:=PolynomialRing(BaseRing(J));
    Pr:=PolynomialRing(FF);
    PQtoPr:=hom<PQ->Pr|
          Coercion(BaseRing(PQ),BaseRing(Pr))*Coercion(BaseRing(Pr),Pr),Pr.1>;
    red:=function(P)
      if P[3] eq 0 then
        return Jr!0;
      end if;
      xpol:=P[1];
      yrel:=P[2];

      x:=Parent(xpol).1;
      cfxpol:=Coefficients(xpol);
      v:=Infinity();
      ixv:=0;
      for i in [1..#cfxpol] do
        if Valuation(cfxpol[i],p) lt v then
          v:=Valuation(cfxpol[i],p);
          ixv:=i;
        end if;
      end for;
      xpol:=xpol/p^v;
      cfxpol:=Coefficients(xpol);
      print "ixv",ixv;
      //now we know that xpol has integral coefficients at p and that
      //x^(ixv-1) is the lowest degree monomial with coefficient that's a unit at p
      while true do
        cfyrel:=Coefficients(yrel);
        iyv:=0;
        v:=Infinity();
        for i in [1..#cfyrel] do
          if Valuation(cfyrel[i],p) lt v then
            v:=Valuation(cfyrel[i],p);
            iyv:=i;
          end if;
        end for;

        if v ge 0 then
          //we have an integral relation for y, so now xpol,yrel can be reduced
          xpolr:=PQtoPr(xpol);
          yrelr:=PQtoPr(yrel);
          if yrelr eq 0 then
            yrelr:=xpolr;
          end if;
          print "Trying to create",<xpolr,yrelr,P[3]>;
          if Degree(xpolr) eq 0 then
            print "Divisor in reduction entirely supported at infinity";
            f,h:=HyperellipticPolynomials(Cr);
            d:=Degree(f);
            if exists{i: i in [d-P[3]+1..d] |
                  Coefficient(yrelr^2+h*yrelr-f,i) ne 0} then
              print "but yrel does not have enough zeros there. Returning 0 divisor";
              return Jr!0;
            else
              print "yrel seems to define a legitimate point here";
            end if;
          end if;
          if CrIsOdd then
            return elt<Jr|xpolr,yrelr,Degree(xpolr)>;
          else
            return elt<Jr|xpolr,yrelr,P[3]>;
          end if;
        elif Valuation(cfxpol[P[3]+1],p) eq 0 then
          //something strange happens: xpol mod p has full degree,
          //so the reduction of the divisor is completely supported at
          //finite points. Yet, the relation for y is awkward.
          //We assume that the divisor in reduction is of the form
          //[(x,y)+(x,-y) - infty^+ - infty^-].
          //The least we can do is check that Discriminant(xpolr)=0
          xpolr:=PQtoPr(xpol);
          assert Discriminant(xpolr) eq 0;
          print "exceptional branch triggered.";
          return Jr!0;
        end if;

        //We have to do something about the coefficient of x^iyv in yrel
        //if iyv<ixy, we cannot reach the offending term.
        error if iyv lt ixv, "Cannot reach term";

        //the offending coefficient:
        c:=cfyrel[iyv];
        //take the unit part ...
        cunit:=c/p^Valuation(c,p);
        M:=(Integers()!(GF(p)!(cunit/cfxpol[ixv])))*p^Valuation(c,p);
        //*p^Valuation(c,p);
        print "M:",M;
        //this should kill one valuation level in the coefficient
        yrel:=yrel-M*xpol*x^(iyv-ixv);
        print "xpol,yrel:=",<xpol,yrel>;
      end while;
    end function;
    rc:=GetLocalData(J,p);
    rc`reduction:=map<J->Jr| P:-> red(P)>;
    StoreLocalData(J,p,rc);
  end if;
  rc:=GetLocalData(J,p);
  return Codomain(rc`reduction),rc`reduction;
end intrinsic;

intrinsic Reduction(MWmap::Map,P::RngIntElt)->Map,Map
  {compute the reduction of a mordell-weil group mod a prime of good reduction}
  require ISA(Type(Domain(MWmap)),GrpAb) and
          ISA(Type(Codomain(MWmap)),JacHyp):
    "The map should be from an abelian group into a hyperelliptic jacobian or its",
    "point set over the base ring";
  if not(assigned GetLocalData(MWmap,P)`reduction) then
    J:=Codomain(MWmap);
    Jr,toJr:=Reduction(J,P);
    JrGrp,JrGrpMap:=AbelianGroup(Jr);
    rc:=GetLocalData(MWmap,P);
    rc`reduction:=<
      hom<Domain(MWmap)->JrGrp|
        [g@MWmap@toJr@@JrGrpMap:g in OrderedGenerators(Domain(MWmap))]>,
      JrGrpMap>;
    StoreLocalData(MWmap,P,rc);
  end if;
  rc:=GetLocalData(MWmap,P);
  return rc`reduction[1],rc`reduction[2];
end intrinsic;
  
intrinsic Divisor(P::JacHypPt)->DivCrvElt
  {Returns a divisor representing the divisor class corresponding to P}
  C:=Curve(Parent(P));
  K:=FunctionField(C);
  f:=Evaluate(P[1],K.1);
  g:=K.2-Evaluate(P[2],K.1);
  Kr:=RationalExtensionRepresentation(K);
  Ofin:=MaximalOrderFinite(Kr);
  Oinf:=MaximalOrderInfinite(Kr);
  D:=Divisor(ideal<Ofin|f,g>);
  if Degree(P[1]) gt 0 and Degree(D) lt Degree(P[1]) then
    assert ((Degree(D)-Degree(P[1])) mod Degree(D)) eq 0;
    D:=((Degree(D)-Degree(P[1])) div Degree(D))*D;
  end if;
  if Degree(P[1]) lt P[3] then
    Z:=Divisor(ideal<Oinf|g> meet Oinf);
    Z:=Support(Z);
    assert #Z eq 1;
    Z:=Z[1];
    assert ((P[3]-Degree(D)) mod Degree(Z)) eq 0;
    D:=D+((P[3]-Degree(D)) div Degree(Z))*Z;
  end if;
  infty:=&+InfinitePlaces(Kr);
  assert (Degree(D) mod Degree(infty)) eq 0;
  return CurveDivisor(DivisorGroup(K)!(D-(Degree(D) div Degree(infty))*infty));
end intrinsic;

intrinsic JacobianPoint(D::DivCrvElt)->JacHypPt
  {Returns the point on the jacobian corresponding to the divisor class of D}
  C:=Curve(D);
  require ISA(Type(C),CrvHyp):
    "Only implemented for hyperelliptic curves";
  require Degree(D) eq 0:
    "Only degree 0 divisors can be mapped to Jacobian";
  g:=Genus(C);
  K:=FunctionField(C);
  Kr:=RationalExtensionRepresentation(K);
  Ofin:=MaximalOrderFinite(Kr);
  Oinf:=MaximalOrderInfinite(Kr);
  infty:=DivisorGroup(K)!(&+InfinitePlaces(Kr));
  require g mod 2 eq 0 or Degree(infty) eq 1:
    "For odd genus curves there must be a unique place of degree 1 at infinity";
  Dred:=Reduction(FunctionFieldDivisor(D)+(g div Degree(infty))*infty,infty);
  gens:=Generators(Ideals(DivisorGroup(Kr)!Dred));
  P:=PolynomialRing(BaseRing(C));

  if #gens eq 1 then
    a:=Evaluate(Numerator(RationalFunction(K!gens[1])),[P.1,0]);
    b:=Parent(a)!0;
  else
    a:=Evaluate(Numerator(RationalFunction(K!gens[1])),[P.1,0]);
    b:=Numerator(RationalFunction(K!gens[2]));
    assert Degree(b,2) eq 1;
    b:=Evaluate(-b+MonomialCoefficient(b,Parent(b).2)*Parent(b).2,[P.1,0]);
  end if;
  
  if Degree(a) eq Degree(Dred) then
    jpnt:=Jacobian(C)![a,b];
    assert FunctionFieldDivisor(Divisor(jpnt)) eq
                              Dred-(Degree(Dred) div Degree(infty))*infty;
    return jpnt;
  end if;
  
  assert #InfinitePlaces(K) eq 2;
  rrs,rrm:=RiemannRochSpace(-Dred+((Degree(Dred) div 2)+1)*infty);
  assert Dimension(rrs) eq 1;
  a:=rrm(rrs.1);
  a:=Evaluate(Numerator(RationalFunction(K!gens[1])),[P.1,0]);
  rrs,rrm:=RiemannRochSpace(-Dred+((Degree(Dred) div 2)+2)*infty);
  assert Dimension(rrs) eq 3;
  bl:=exists(b){b: f in Basis(rrs)| Degree(b,2) eq 1 where
          b:=Numerator(RationalFunction(rrm(f)))};
  require bl: "This should not happen.";
  b:=Evaluate(-b+MonomialCoefficient(b,Parent(b).2)*Parent(b).2,[P.1,0]);
  jpnt:=elt<Jacobian(C)|a,b,Degree(Dred)>;
  assert FunctionFieldDivisor(Divisor(jpnt)) eq
                         Dred-(Degree(Dred) div Degree(infty))*infty;
  return jpnt;
end intrinsic;

function dsc(M)
  K:=Kernel(M);
  assert Dimension(K) eq 1;
  V:=Generic(K);
  bs:=ExtendBasis(K,V)[2..3];
  B:=Matrix(bs);
  return -Determinant(B*M*Transpose(B));
end function;

intrinsic Prym(P2::Prj,Q1::RngMPolElt,Q2::RngMPolElt,Q3::RngMPolElt)->
     MapSch,Map,JacHyp
  {Returns pi:D->C, m, J. Here pi is the obvious unramified double cover of
  C:Q1*Q3=Q2^2, J is the associated Prym-variety represented as a Jacobian of a
  curve of genus 2 and m is a map from C to quadratic polynomials x^2-Tx+1,
  corresponding to an embedding of D into J. P2 must be Proj(Parent(Q1))}
  
  require Dimension(P2) eq 2 and
    Parent(Q1) eq CoordinateRing(P2) and
    Parent(Q2) eq CoordinateRing(P2) and
    Parent(Q3) eq CoordinateRing(P2):
        "Invalid input";
  C:=Curve(P2,Q1*Q3-Q2^2);
  P4:=ProjectiveSpace(BaseRing(P2),4);
  UVW:=[P4.i: i in [1,2,3]];

  M1:=Evaluate(Q1,UVW)-P4.4^2;
  M2:=Evaluate(Q2,UVW)-P4.4*P4.5;
  M3:=Evaluate(Q3,UVW)-P4.5^2;

  m1:=SymmetricMatrix(M1);
  m2:=SymmetricMatrix(M2);
  m3:=SymmetricMatrix(M3);

  D:=Scheme(P4,[M1,M2,M3]);

  q1:=SymmetricMatrix(Q1);
  q2:=SymmetricMatrix(Q2);
  q3:=SymmetricMatrix(Q3);

  x:=PolynomialRing(BaseRing(P2)).1;
  Fpol:=-4*Determinant(q1-2*x*q2+x^2*q3);
  F:=HyperellipticCurve(Fpol);
  J:=Jacobian(F);

  pi:=map<D->C|[P4.1,P4.2,P4.3]>;
  function xpolmap(P0,P1)
    assert Scheme(P0) eq D and Scheme(P1) eq D;
    v:=Vector(Eltseq(P0));
    R:=BaseRing(v);
    x:=PolynomialRing(R).1;
    m1R:=Matrix(5,5,ChangeUniverse(Eltseq(m1),R));
    m2R:=Matrix(5,5,ChangeUniverse(Eltseq(m2),R));
    m3R:=Matrix(5,5,ChangeUniverse(Eltseq(m3),R));
    if P0 eq P1 then
      M:=Matrix([v*m1R,v*m2R,v*m3R]);
      TM:=Transpose(M);
      Ker:=Kernel(TM);
      w:=ExtendBasis([Ker!v],Ker)[2];
      xpol:=    InnerProduct(w*m1R,w)-
            2*x*InnerProduct(w*m2R,w)+
            x^2*InnerProduct(w*m3R,w);
    else
      w:=Vector(Eltseq(P1));
      xpol:=    InnerProduct(v*m1R,w)-
            2*x*InnerProduct(v*m2R,w)+
            x^2*InnerProduct(v*m3R,w);
    end if;
    return xpol;
  end function;
  
  return pi,xpolmap,J;
end intrinsic;

intrinsic KummerSection(KJ::SrfKum,plane::RngMPolElt)->RngMPolElt,RngMPolElt,RngMPolElt
  {Given a plane section of a kummer surface, return Q1, Q2, Q3 such that
  Q1*Q3-Q2^2 describes the plane section.}
  polKJ:=Parent(DefiningPolynomial(KJ));
  require Parent(plane) eq polKJ: "check parent of plane";
  Kmr:=Scheme(KJ);
  PKJ:=Ambient(Kmr);
  require TotalDegree(plane) eq 1 and IsHomogeneous(plane) and
	 Degree(plane,PKJ.4) eq 1: "not the right kind of plane";
  x4rel:=-Coefficient(plane,PKJ.4,0)/MonomialCoefficient(plane,PKJ.4);
  Kmr:=Scheme(KJ);

  P2<k1,k2,k3>:=ProjectiveSpace(BaseRing(PKJ),2);
  PKJtoP2:=map<PKJ->P2|[PKJ.1,PKJ.2,PKJ.3]>;

  CKm:=Kmr meet Scheme(PKJ,plane);
  C:=Curve(PKJtoP2(CKm));
  assert Genus(C) eq 3;

  F:=Curve(Jacobian(KJ));
  kk:=BaseRing(F);
  f,g:=HyperellipticPolynomials(F);
  assert g eq 0;
  cfs:=Degree(f) eq 6 select Coefficients(f) else Coefficients(f) cat [0];
  f0,f1,f2,f3,f4,f5,f6:=Explode(cfs);

  //Take the affine patch k1=1
  A2<Ak2,Ak3>:=AffinePatch(P2,3);

  Pa<a1,a2,a6,a7,a8,a9>:=PolynomialRing(Parent(Ak2),6); //the "odd" functions
  Pl<l0,l1,l2,l3,l4,l5>:=PolynomialRing(Pa,6);

  //we consider the general "square" of an odd function on the jacobian
  Sqr:=(&+[Pl.i*Pa.i: i in [1..6]])^2;
  
  //and split off monomials and their coefficients
  SqrMn:=Monomials(Sqr);
  SqrCf:=Coefficients(Sqr);

//these are the relations of the "odd" functions in terms of the Kummer.
//They are given affinely and x1=1. They are polynomial in
//x2,x3,x4.
Rels:=[a7*a1 = 1/2*x2*x4^2-1/2*f1*x4-1/2*f3*x4*x3+1/2*f5*x3^2*x4+f6*x3^
2*x2*x4-f0*f3-2*f0*f4*x2+f5*f0*x3-2*f5*f0*x2^2+2*f0*f6*x2*x3-2*f0*f6*x2^3-f1*
f4*x3-f1*f5*x2*x3-f1*f6*x3*x2^2, a9*a1 = 1/2*x3*x2*x4^2+2*f0*x2*x4+1/2*f1*x3*
x4+1/2*f1*x4*x2^2+f2*x3*x2*x4+1/2*f3*x3^2*x4-1/2*f5*x3^3*x4+2*f0*f2*x2+f0*f3*
x3+f0*f3*x2^2+2*f0*f4*x3*x2-f0*f5*x3^2+f5*f0*x3*x2^2-1/2*f1^2*x2+1/2*f1*f3*x3*
x2+f1*f4*x3^2+1/2*f1*f5*x2*x3^2, a1^2 = f6*x3^2*x4^2+f2*x4^2+f1^2*f4+f0*f3^2+
x4^3-4*x2^2*f0*f6*x4-2*x3*f0*f3*f5-4*x2*f0*f2*f5-4*f0*f5*x2*x4-f1*f5*x3*x4-4*
x3^2*f0*f4*f6-2*f1*f6*x2*x3*x4-4*f0*f2*f6*x2^2-4*x3*x2*f0*f3*f6+x3^2*f0*f5^2-4
*f0*f4*x4-4*f0*f2*f4+x4*f1*f3+x2*f1^2*f5+f1^2*f6*x2^2, a2*a1 = -4*x3^2*x2*f0*
f4*f6-2*x3^3*f1*f4*f6-x2*x3*f0*f3*f5-f1*f6*x3^2*x4-2*f0*f6*f3*x3*x2^2-2*x3*f0*
f2*f5+x2*x3^2*f0*f5^2-1/2*x4^2*f5*x3^2-4*x2*x3*f0*f2*f6-1/2*x3^2*f1*f3*f5-2*x3
^2*f0*f3*f6-2*f0*f5*x4*x2^2-x2*x3^2*f1*f3*f6-3/2*f1*f5*x3*x2*x4-2*f0*f4*x2*x4-\
2*f0*f6*x2*x4*x3+x2*x3*f1^2*f6+1/2*x4^3*x2-f3*f6*x3^3*x4-2*f0*f6*x2^3*x4-2*f1*
f6*x3*x4*x2^2-2*f2*f6*x3^2*x2*x4-f0*f3*x4+1/2*x3*f1^2*f5-1/2*x4^2*f3*x3+1/2*x3
^3*f1*f5^2-1/2*x4^2*f1-x3^2*x4*f2*f5-x3*x4*f0*f5-x3*x4*f1*f4, a6*a2 = 1/2*x2*
x4^2+2*f6*x3^2*x2*x4+1/2*f5*x3^2*x4+1/2*f5*x3*x4*x2^2+f4*x2*x3*x4+1/2*f3*x4*x3
-1/2*f1*x4+2*f6*f4*x3^3*x2+f6*f3*x3^3+f6*f3*x3^2*x2^2+2*f2*f6*x2*x3^2-f1*f6*x3
^2+f1*f6*x3*x2^2-1/2*f5^2*x3^3*x2+1/2*f3*f5*x2*x3^2+f5*f2*x3^2+1/2*f1*f5*x2*x3
, a9*a7 = -x3^2*x4+1/2*x3*x4*x2^2-1/2*f5*x3^3*x2-f4*x3^3-1/2*f3*x3^2*x2+1/2*f1
*x2*x3-f0*x3+f0*x2^2, a8*a6 = -x3*x4+1/2*x4*x2^2-1/2*f1*x2-f2*x3-1/2*f3*x3*x2+
1/2*f5*x3^2*x2-f6*x3^3+f6*x3^2*x2^2, a6^2 = x4+f2+f3*x2+f4*x2^2-f5*x2*x3+f5*x2
^3+f6*x3^2-2*f6*x3*x2^2+f6*x2^4, a9*a8 = -1/2*f1*x3^2+1/2*f3*x3^3-1/2*x3^4*f5+
1/2*x3^2*x2*x4+f2*x2*x3^2+f1*x3*x2^2-f0*x2*x3+f0*x2^3, a9*a6 = 1/2*f1*x3-1/2*
x2^2*f1-1/2*f3*x3^2-1/2*x2^2*f3*x3+1/2*f5*x3^3-1/2*x2^2*f5*x3^2-3/2*x3*x2*x4+1
/2*x2^3*x4-f2*x3*x2-f4*x3^2*x2, a6*a1 = 2*f2*f6*x2^2*x3+2*f3*f6*x3^2*x2-f1*f6*
x2*x3+2*f2*f5*x2*x3+f6*x3^2*x4+2*f4*f6*x3^3+3/2*f5*x3*x2*x4+f2*x4+1/2*f1*f3-1/
2*f3^2*x3-1/2*f5^2*x3^3+f3*f5*x3^2+2*f2*f4*x3-1/2*f1*f5*x3+f1*f4*x2+2*f4*x3*x4
+x4^2+f1*f6*x2^3+f1*f5*x2^2+f6*x3*x4*x2^2+1/2*f3*x2*x4, a7*a6 = -1/2*f1+1/2*f3
*x3+f4*x2*x3-1/2*f5*x3^2+1/2*x2*x4+f5*x3*x2^2-f6*x3^2*x2+f6*x3*x2^3, a8*a1 = -\
2*f0*f6*x2^4-f6*x3^3*x4-2*f4*f6*x3^4+1/2*f5^2*x3^4+1/2*x4^2*x2^2-2*f3*f6*x3^3*
x2-2*f2*f6*x3^2*x2^2-2*f1*f6*x2^3*x3-f5*x3^2*x2*x4+1/2*f1*f5*x3^2-1/2*f1*f3*x3
-1/2*f1*x2*x4-2*f4*x3^2*x4-2*f5*f0*x2^3-2*f2*f4*x3^2-f2*x3*x4-2*f0*f4*x2^2-f3*
f0*x2-f3*f5*x3^3+1/2*f3^2*x3^2-x3*x4^2-2*f1*f4*x3*x2+2*f0*f6*x3*x2^2-f3*x3*x2*
x4+f5*f0*x2*x3-2*f1*f5*x3*x2^2-2*f2*f5*x3^2*x2+f1*f6*x2*x3^2, a7*a2 = -2*f0*f2
-2*f0*f6*x2^4+1/2*f1^2+1/2*x4^2*x2^2-f3*f6*x3^3*x2-2*f2*f6*x3^2*x2^2-2*f1*f6*
x2^3*x3-1/2*f5*x3^2*x2*x4+1/2*f1*f5*x3^2-f1*f3*x3-f1*x2*x4-f4*x3^2*x4-2*f5*f0*
x2^3-2*f2*f4*x3^2-2*f2*x3*x4-2*f0*f4*x2^2-2*f3*f0*x2-1/2*f3*f5*x3^3+1/2*f3^2*
x3^2-x3*x4^2-f0*x4-2*f1*f4*x3*x2+2*f0*f6*x3*x2^2-f3*x3*x2*x4+f5*f0*x2*x3-2*f1*
f5*x3*x2^2-2*f2*f5*x3^2*x2+f1*f6*x2*x3^2, a2^2 = x3^4*f2*f5^2+x3^4*f3^2*f6+x3^
2*x2^2*f0*f5^2+x3^2*f1^2*f6-4*x3^3*x2*f1*f4*f6-4*x3^3*x4*f2*f6-4*x3^4*f2*f4*f6
+x3*x4^3-4*x3^2*x2^2*f0*f4*f6+x3^3*x4*f3*f5+x3^3*x2*f1*f5^2+f4*x3^2*x4^2-2*f5*
f0*x3*x2*x4-4*f1*f6*x3^2*x2*x4-4*f0*f6*x2^2*x3*x4-4*f0*f3*f6*x3^2*x2-2*x3^3*f1
*f3*f6-f1*f5*x3^2*x4-4*x3^2*f0*f2*f6+f0*x4^2, a8*a7 = 1/2*f1*x3-1/2*f3*x3^2+1/
2*f5*x3^3+1/2*x3*x2*x4+f0*x2+f6*x3^3*x2, a9^2 = x3^3*x4+f4*x3^4+f3*x3^3*x2+f2*
x3^2*x2^2-f1*x3^2*x2+f1*x2^3*x3+f0*x3^2-2*f0*x3*x2^2+f0*x2^4, a8^2 = x3^2*x4+
f0*x2^2+f1*x2*x3+f2*x3^2+f6*x3^4, a8*a2 = 1/2*x3*x2*x4^2-1/2*f5*x3^3*x4-1/2*f3
*x3^2*x4+1/2*f1*x3*x4+f0*x2*x4-f6*f3*x3^4-2*f2*f6*x3^3*x2+x3^3*f1*f6-2*f1*f6*
x3^2*x2^2+2*f0*f6*x3^2*x2-2*f0*f6*x2^3*x3-f2*f5*x3^3-f1*f5*x2*x3^2-f5*f0*x3*x2
^2, a7^2 = x3*x4+f0+f4*x3^2+f5*x3^2*x2+f6*x3^2*x2^2, a9*a2 = f4*x3^3*x4+x3^2*
f1*f3+f0*x3*x4+1/2*f5*f3*x3^4+f5*f0*x2^3*x3+f1*f5*x3^2*x2^2+f0*x4*x2^2+1/2*f3*
x3^2*x2*x4+2*f0*f2*x3+x3^2*x4^2+2*f0*f4*x2^2*x3-1/2*f1*f5*x3^3-f5*f0*x3^2*x2+2
*f4*f2*x3^3+2*f4*f1*x3^2*x2+3/2*f1*x3*x2*x4+2*f3*f0*x2*x3+2*f2*x3^2*x4-1/2*f1^
2*x3-1/2*f3^2*x3^3+f5*f2*x3^3*x2] where
         x1,x2,x3,x4:=Explode([1,Ak2,Ak3,Evaluate(x4rel,[1,Ak2,Ak3,0])]);

  //Since the square Sqr is of even degree in the odd functions, it is actually
  //a function on the Kummer. By matching up the monomials in Rels, we can
  //express Sqr as such.
  SqrKmCf:=[CoordinateRing(A2)|Coefficients(cf)[1]*Coefficients(cfkm)[1] where
     _:=exists(cfkm){RHS(rel): rel in Rels | LHS(rel) eq Monomials(cf)[1]}:
        cf in SqrCf];

  //We want Sqr to be a quadratic polynomial in x2,x3 when restricted to plane.
  //We want to take a linear combination of the quadratic terms such that
  //the higher homogeneous parts vanish.
  HighComp:=[&+[HomogeneousComponent(f,i): i in [3,4]]:f in SqrKmCf];
  //and the corresponding linear combination gives the function we're looking
  //for.
  LowComp:=[&+[HomogeneousComponent(f,i): i in [0,1,2]]:f in SqrKmCf];
  
  //the terms that have to cancel:
  HighMons:=Setseq(&join[Seqset(Monomials(f)):f in HighComp]);
  
  //which means, we want something in the kernel of the matrix:
  MM:=Matrix([[MonomialCoefficient(f,mn):mn in HighMons]:f in HighComp]);

  //however, we looked at the quadratic terms. Substituting back
  //changes our linear equations into quadratic ones (in less variables)
  P5<L0,L1,L2,L3,L4,L5>:=ProjectiveSpace(kk,5);
  //No need to worry about the a's anymore, so we express directly over base
  //ring.
  SqrMnL:=[Evaluate(f,[L0,L1,L2,L3,L4,L5]):f in SqrMn];
  //assemble the quadratic equations by realizing that the variables for which
  //MM describes a linear system of equations are really quadratic in
  //L0...L5
  Leq:=[&+[MM[i][j]*SqrMnL[i]: i in [1..#SqrKmCf]]:j in [1..#HighMons]];
  V:=Scheme(P5,Leq);

  //And the solution is:
  solL:=RationalPoints(V);
  print solL;
  if #solL eq 2 then
    //This allows us to assemble quadrics:
    Q1A:=&+[Evaluate(SqrMnL[i],Eltseq(solL[1]))*LowComp[i]:i in [1..#SqrMnL]];
    print "Q1A:",Q1A;
    vv:=Scheme(A2,Q1A);
    print dsc(SymmetricMatrix(DefiningEquation(ProjectiveClosure(vv))));
    assert &+[Evaluate(SqrMnL[i],Eltseq(solL[1]))*HighComp[i]:i in [1..#SqrMnL]] eq 0;
    Q3A:=&+[Evaluate(SqrMnL[i],Eltseq(solL[2]))*LowComp[i]:i in [1..#SqrMnL]];
    assert &+[Evaluate(SqrMnL[i],Eltseq(solL[2]))*HighComp[i]:i in [1..#SqrMnL]] eq 0;
    Q1N:=Homogenization(Evaluate(Q1A,[k2,k3]),k1);
    Q3N:=Homogenization(Evaluate(Q3A,[k2,k3]),k1);
    print C, Q1N, Q3N;
    //We know that Q1N and Q3N cut out the right zeros on C. Q2 should pass
    //through these zeros:
    itsct:=ReducedSubscheme(Scheme(P2,Q1N*Q3N) meet C);
    Q2N:=DefiningPolynomials(Image(IdentityMap(P2),itsct,2));
    assert #Q2N eq 1 and TotalDegree(Q2N[1]) eq 2;
    //check we're right ... (Q2 should be uniquely determined, up to scalars)
    Q2N:=Q2N[1];

    //Finding how to match this up now is a matter of linear algebra:
    //v[1]*Q1*Q3-v[2]*Q2^2 = C
    
    //basis of the vector space:
    P2mons:=[k1^i*k2^j*k3^(4-i-j): i in [0..4-j], j in [0..4]];
    
    //and the solution:
    v,Ker:=Solution(Matrix([[MonomialCoefficient(Q1N*Q3N,m):m in P2mons],
       [MonomialCoefficient(-Q2N^2,m):m in P2mons]]),
      Matrix([[MonomialCoefficient(DefiningPolynomial(C),m):m in P2mons]]));
    assert Dimension(Ker) eq 0;
    Q1N:=v[1,1]/v[1,2]*Q1N;
    K:=kk;
      print Q1N,Q2N,Q3N;

  else
    kk:=BaseRing(F);
    Qbar:=AlgebraicClosure();
    solL:=RationalPoints(V,Qbar);
    bl:=exists(m){m:a in Eltseq(solL[1])| Degree(m) eq 2 where
                                         m:=MinimalPolynomial(a)};
    assert bl;
    D:=PowerFreePart(Discriminant(m),2);
    x:=PolynomialRing(kk).1;
    K:=ext<kk|x^2-D>;
    solL:=RationalPoints(V,K);
    print solL;
    A2K:=BaseChange(A2,K);
    toA2K:=hom<CoordinateRing(A2)->CoordinateRing(A2K)|
        Coercion(kk,K)*Coercion(K,CoordinateRing(A2K)),[A2K.1,A2K.2]>;
    fromA2K:=hom<CoordinateRing(A2K)->CoordinateRing(A2)|
        Coercion(K,kk)*Coercion(kk,CoordinateRing(A2)),[A2.1,A2.2]>;
    P5K:=BaseChange(P5,K);
    toP5K:=hom<CoordinateRing(P5)->CoordinateRing(P5K)|
        Coercion(kk,K)*Coercion(K,CoordinateRing(P5K)),[P5K.i:i in [1..6]]>;
    LowCompK:=[toA2K(f):f in LowComp];
    HighCompK:=[toA2K(f):f in HighComp];
    SqrMnLK:=[toP5K(f):f in SqrMnL];
    
    Q1K:=&+[Evaluate(SqrMnLK[i],Eltseq(solL[1]))*LowCompK[i]:i in [1..#SqrMnLK]];
    assert
      &+[Evaluate(SqrMnLK[i],Eltseq(solL[1]))*HighCompK[i]:i in [1..#SqrMnLK]] eq 0;
    Q3K:=&+[Evaluate(SqrMnLK[i],Eltseq(solL[2]))*LowCompK[i]:i in [1..#SqrMnLK]];
    assert
      &+[Evaluate(SqrMnLK[i],Eltseq(solL[2]))*HighCompK[i]:i in [1..#SqrMnLK]] eq 0;
    Q13N:=Homogenization(Evaluate(fromA2K(Q1K*Q3K),[k2,k3]),k1);
    itsct:=ReducedSubscheme(Scheme(P2,Q13N) meet C);
    Q2N:=DefiningPolynomials(Image(IdentityMap(P2),itsct,2));
    assert #Q2N eq 1 and TotalDegree(Q2N[1]) eq 2;
    //check we're right ... (Q2 should be uniquely determined, up to scalars)
    Q2N:=Q2N[1];
     
    //Finding how to match this up now is a matter of linear algebra:
    //v[1]Q1*Q3-v[2]*Q2^2=C
    
    //basis of the vector space:
    P2mons:=[k1^i*k2^j*k3^(4-i-j): i in [0..4-j], j in [0..4]];
    
    //and the solution:
    MAT:=Matrix(
       [[MonomialCoefficient(Q13N,m):m in P2mons],
        [MonomialCoefficient(-Q2N^2,m):m in P2mons]]);
    VEC:=Matrix([[MonomialCoefficient(DefiningPolynomial(C),m):m in P2mons]]);
    v,Ker:=Solution(MAT,VEC);
    print MAT,VEC;
    assert Dimension(Ker) eq 0;
    assert v[1,1]/v[1,2]*Q13N-Q2N^2-1/v[1,2]*DefiningEquation(C) eq 0;
    //v[1]/v[2]*Q1*Q3-Q2^2=lambda*C
    //so find a delta such that Norm(delta)=v[1]/v[2].
    Ndelta:=v[1,1]/v[1,2];
    bl,delta:=NormEquation(K,Numerator(Ndelta)*Denominator(Ndelta));
    assert bl;
    print delta;
    delta:=delta[1]/Denominator(Ndelta);
    assert Norm(delta) eq Ndelta;
    Q1K:=delta*Q1K;
    Q3K:=Norm(delta)/delta*Q3K;
    sigmaK:=hom<K->K|[-K.1]>;
    sigmaA2K:=hom<CoordinateRing(A2K)->CoordinateRing(A2K)|
                   sigmaK*Coercion(K,CoordinateRing(A2K)),[A2K.1,A2K.2]>;
    assert sigmaA2K(Q1K) eq Q3K;
    Q13N:=Homogenization(Evaluate(fromA2K(Q1K*Q3K),[k2,k3]),k1);
    mn:=[fromA2K(m): m in Monomials(Q1K)];
    cf0:=[Eltseq(c)[1]: c in Coefficients(Q1K)];
    cf1:=[Eltseq(c)[2]: c in Coefficients(Q1K)];
    Q0:=&+[cf0[i]*mn[i]: i in [1..#mn]];
    QD:=&+[cf1[i]*mn[i]: i in [1..#mn]];
 
    Q0N:=Homogenization(Evaluate(Q0,[k2,k3]),k1);
    QDN:=Homogenization(Evaluate(QD,[k2,k3]),k1);
    //Now Q0N^2-D*QDN^2-Q2N^2 equals Q13N-Q2N^2 (hopefully);
    assert Q0N^2-D*QDN^2 eq Q13N;
    //and we can safely put Q1N=1/D*(Q0N-Q2N), Q2N=(Q0N+Q2N) Q3N:=QDN
    Q1N:=(Q0N-Q2N)/D;
    Q3N:=(Q0N+Q2N);
    Q2N:=QDN;      //so now the old Q2N does not live anymore!!!
  end if;

  q1:=SymmetricMatrix(Q1N);
  q2:=SymmetricMatrix(Q2N);
  q3:=SymmetricMatrix(Q3N);
  x:=PolynomialRing(kk).1;
  MR:=MatrixAlgebra(Parent(x),3);
  Nfpol:=(-Determinant(MR!q1-2*x*MR!q2+x^2*MR!q3));
  fpol:=HyperellipticPolynomials(F);
  bl,T:=IsGL2Equivalent(Nfpol,fpol,6);
  print T;
  if #T gt 1 then
    print "WARNING! hyperelliptic curve has extra automorphisms";
  end if;
  T:=T[1];
  a,b,c,d:=Explode(T);
/******
  t:=DefiningPolynomials(T);
  P:=Universe(t);
  a:=MonomialCoefficient(t[1],P.1);b:=MonomialCoefficient(t[1],P.3);
  c:=MonomialCoefficient(t[3],P.1);d:=MonomialCoefficient(t[3],P.3);
*******/
  Q3:=a^2*Q3N-2*a*c*Q2N+c^2*Q1N;
  Q2:=(a*d+b*c)*Q2N-a*b*Q3N-c*d*Q1N;
  Q1:=b^2*Q3N-2*b*d*Q2N+d^2*Q1N;
  q1:=SymmetricMatrix(Q1);
  q2:=SymmetricMatrix(Q2);
  q3:=SymmetricMatrix(Q3);
  if Type(kk) eq FldRat then
    dn:=LCM([Denominator(cf): cf in &cat[Coefficients(q):q in [Q1,Q2,Q3]]]);
    Q1:=dn*Q1;Q2:=dn*Q2;Q3:=dn*Q3;
    nm:=GCD([Numerator(cf): cf in &cat[Coefficients(q):q in [Q1,Q2,Q3]]]);
    Q1:=Q1/nm;Q2:=Q2/nm;Q3:=Q3/nm;
  end if;
  assert TotalDegree(DefiningEquation(C) div (Q1*Q3-Q2^2)) eq 0;
  return Restriction(PKJtoP2,CKm,C),Q1,Q2,Q3;

end intrinsic;

intrinsic RationalPoints(K::SrfKum,B::RngIntElt)->SetEnum
  {Determine the rational points on a Kummer surface, up to a height bound B}
  L:=jPoints(Jacobian(K),B);
  assert #L mod 4 eq 0;
  return {@ K!L[i..i+3]: i in [1..#L by 4] @};
end intrinsic;

intrinsic LiftClasses(L::Tup,mp::Map,crit::Map)->Tup
  {given a coset list L and Kernel(mp) a subgroup of Kernel(L[1]),
  together with a predicate crit on Codomain(mp), return the cosets mod
  Codomain(mp) that map down to a coset in L and satisfy the criterion crit.}
  
  Gnew:=Codomain(mp);
  Gold:=Codomain(L[1]);
  assert Kernel(mp) subset Kernel(L[1]);
  relker:=Kernel(hom<Gnew->Gold|[L[1](g@@mp):g in OrderedGenerators(Gnew)]>);
  return <mp,{Gnew|u: k in relker, g in L[2] |crit(u) where u:=k+mp(g@@L[1])}>;
end intrinsic;

intrinsic NextStage(L::Tup,mwmap::Map,EQ::RngMPolElt,
                          p::RngIntElt,v::RngIntElt)->Tup
  {Lift }
  J:=Codomain(mwmap);
  KJ:=KummerSurface(J);
  Km:=Scheme(KJ);
  require Parent(EQ) eq Parent(Km.1):
    "Equation must be in coordinate ring of Kummer Scheme";
  Kp:=pAdicField(p:Precision:=40);
  pp:=UniformizingElement(Kp);
  G:=Domain(L[1]);
  require Invariants(G) eq [0,0]:
    "Only implemented for Z x Z MW groups at the moment";
  Kmp:=Km(Kp);
  toKmp:=map<J->Kmp|w:->Kmp!Eltseq(KJ!w)>;
  gs:=[mwmap(g):g in OrderedGenerators(G)];
  g1:=toKmp(gs[1]);
  g2:=toKmp(gs[2]);
  g2mg1:=toKmp(gs[2]-gs[1]);

  function lincomb(a,b)
    ag1:=Multiple(a,g1);
    ag1mg2:=PseudoAddMultiple(g2,g1,g2mg1,-a);   // g2mag1 is the same
    ag1pbg2:=PseudoAddMultiple(ag1,g2,ag1mg2,b);
    return ag1pbg2;
  end function;

  function cutoffseq(P)
    L:=Eltseq(P);
    min:=Minimum([Valuation(c):c in L]);
    L:=[c/pp^min+O(pp^(v)):c in L];
    return L;
  end function;

  mwmapl:=map<G->Kmp|a:->(lincomb(b1,b2) where b1,b2:=Explode(Eltseq(a)))>;
  newquo,mp:=quo<G|[p*g: g in OrderedGenerators(Kernel(L[1]))]>;
  crit:=map<newquo->Booleans()|
    a:->RelativePrecision(Evaluate(EQ,cutoffseq(mwmapl(a@@mp)))) eq 0>;

  print "Assuming information is accurate up to p ^",(v-1),
        "and that new kernel has relative index p^2.";
  return LiftClasses(L,mp,crit);
end intrinsic;



intrinsic Scheme(K::SrfKum)->Sch
  {Returns a scheme corresponding to the kummer}
  if not(assigned K`Scheme) then
    P3:=Proj(Parent(DefiningPolynomial(K)));
    Ks:=Scheme(P3,DefiningPolynomial(K));
    Ks`Twice:=map<Ks->Ks|K`Delta>;
    Ks`IsKummer:=true;
    K`Scheme:=Ks;
    Ks`BBMatrix:=K`BBMatrix;
  end if;
  return K`Scheme;
end intrinsic;

intrinsic IsKumSch(K::Sch)->BoolElt
  {Tests if K has been made by Scheme(SrfKum)}
  return assigned K`IsKummer and K`IsKummer;
end intrinsic;

intrinsic HalfPoints(P::Pt)->SetIndx
  {returns the points on the parent of P that give P when multiplied with 2}
  Kprj:=Scheme(P);
  require IsKumSch(Kprj): "Point must lie on a kummer surface";
  require Codomain(RingMap(Parent(P))) cmpeq BaseRing(Kprj):
    "Halving is only supported for points with values in the base ring of K";
  twice:=Kprj`Twice;
  Pprj:=Kprj!Eltseq(P);
  halfPprj:=RationalPoints(Pprj@@twice);
  return halfPprj;
end intrinsic;

intrinsic Double(P::Pt) -> Pt
  {Returns the double of the point P.}
  K:=Scheme(P);
  require IsKumSch(K): "Point must lie on a kummer surface";
  return K`Twice(P);
end intrinsic;

function SelCoord(cf)
  K:=Universe(cf);
  if ISA(Type(K),FldPad) or ISA(Type(K),RngPad) then
    _,i:=Minimum([Valuation(c):c in cf]);
  else
    exists(i){i:i in [1..4]|cf[i] ne 0};
  end if;
  return i;
end function;

intrinsic PseudoAdd(P1::Pt, P2::Pt, P3::Pt) -> Pt
{Given the images on the Kummer surface of points P, Q, P-Q on the 
Jacobian, returns the image of P+Q.}
    K := Scheme(P1);
    require IsKumSch(K): "Points must lie on a kummer surface";
    require K cmpeq Scheme(P2) and K cmpeq Scheme(P3) and
            Parent(P1) cmpeq Parent(P2) and Parent(P1) cmpeq Parent(P3):
            "Points are on different Kummer surfaces.";
    L1:= Eltseq(P1);
    L2:= Eltseq(P2);
    L3 := Eltseq(P3);
    if ISA(Type(Universe(L1)),FldPad) then
      v:=-Minimum([Valuation(w):w in L1]);
      pp:=UniformizingElement(Universe(L1));
      L1:=[w*pp^v:w in L1];
      v:=-Minimum([Valuation(w):w in L2]);
      L2:=[w*pp^v:w in L2];
      v:=-Minimum([Valuation(w):w in L3]);
      L3:=[w*pp^v:w in L3];
    end if;
    L12 := L1 cat L2;
    i := SelCoord(L3);
    BB := K`BBMatrix;
    c1 := 2*L3[i]; c2 := Evaluate(BB[i,i], L12);
    L := [ c1*Evaluate(BB[i,j], L12) - L3[j]*c2 : j in [1..4] ];
    //print m where m:=Minimum([Valuation(l/2):l in L]);
    return Parent(P1)!L;
    // Check if point really is on K here, since third argument might
    // not be image of P-Q.
end intrinsic;

intrinsic KumZero(KK::SetPt) -> Pt
  {Create the appropriate zero in the point set}
  require IsKumSch(Scheme(KK)): "Must be a kummer scheme";
  return KK![0,0,0,1];
end intrinsic;

intrinsic Multiple(n::RngIntElt, P::Pt) -> Pt
{The n-th multiple of P on the Kummer surface K.}
    K := Parent(P);
    if n eq 0 then return KumZero(Parent(P)); end if;
    m := Abs(n);
    Px := KumZero(Parent(P)); Py := P; Pz := P;
    // invariants: Px = ax*P, Py = ay*P, Pz = az*P with
    //  ax + ay = az  and  ax + m*az = n .
    while true do
      if IsOdd(m) then
        Px := PseudoAdd(Px, Pz, Py); 
      else
        Py := PseudoAdd(Py, Pz, Px);
      end if;
      m div:= 2;
      if m eq 0 then return Px; end if;
      Pz := Double(Pz);
    end while;
end intrinsic;

intrinsic PseudoAddMultiple(P1::Pt, P2::Pt, 
                            P3::Pt, n::RngIntElt) -> Pt
{Given the images on the Kummer surface of points P, Q, P-Q on the 
Jacobian, returns the image of P+n*Q.}
    K := Scheme(P1);
    require IsKumSch(K): "Points must lie on a kummer surface";
    require K cmpeq Scheme(P2) and K cmpeq Scheme(P3) and
            Parent(P1) cmpeq Parent(P2) and Parent(P1) cmpeq Parent(P3):
            "Points are on different Kummer surfaces.";
    if n lt 0 then
      P3 := PseudoAdd(P1, P2, P3); n := -n;
    end if;
    while true do
      // This is a variant of the multiplication algorithm above.
      if IsOdd(n) then
        P1 := PseudoAdd(P1, P2, P3);
      else
        P3 := PseudoAdd(P3, P2, P1);
      end if;
      n div:= 2;
      if n eq 0 then return P1; end if;
      P2 := Double(P2);
    end while;
end intrinsic;

intrinsic BadPrimes(L::[RngMPolElt])->RngIntElt
  {Determine the bad primes of a 0-dimensional separated scheme in P2. Input
  polynomials should be defined over Q. The routine clears denominators as
  required.}
  R:=Universe(L);
  require Rank(R) eq 3 and forall{l:l in L|IsHomogeneous(l)}:
    "polynomials must be homogeneous and ternary";
  require BaseRing(R) eq Rationals():
   "Polynomial must have rational coefficients";
  //Make integral
  L:=[LCM([Denominator(c):c in Coefficients(l)])*l:l in L];
  L2:=[Resultant(l1,l2,R.3):l1,l2 in L| l1 ne l2];
  L2:=[l:l in L2| l ne 0];
  L3:=[Resultant(l1,l2,R.2):l1,l2 in L2| l1 ne l2];
  L3:=[l:l in L3| l ne 0];
  assert forall{l: l in L3|#Coefficients(l) eq 1};
  return GCD([Integers()|Coefficients(l)[1]:l in L3]);
end intrinsic;

intrinsic HasRealPoints(C::Crv:Precision:=50)->BoolElt
  {Test a plane curve for real solvability}
  F:=DefiningEquation(C);
  PF:=Parent(F);
  require BaseRing(C) eq Rationals(): "Not implemented for this base field";
  RR:=RealField(Precision);
  preceps:=RR!10^(5-Precision);
  eps:=RR!10^(-Precision div 2);
  x:=PolynomialRing(Rationals()).1;
  XRR:=PolynomialRing(RR).1;
  sign:=0;
  while sign eq 0 do
    repeat
      v:=[Random([-10..10]):i in [1..3]];
    until v ne [0,0,0];
    w:=Evaluate(F,v);
    if w lt 0 then
      sign:=-1;
    elif w gt 0 then
      sign:=1;
    elif not(IsSingular(C!v)) then
      print "found nonsingular rational point",v;
      return true;
    end if;
  end while;
  F:=sign*F;
  //So after this, the only mission is to decide if F takes negative values.
  print "first looking at what happens on coordinate axes";
  for v in [[x,1,0],[0,x,1],[1,0,x]] do
    f:=Evaluate(F,v);
    if IsOdd(Degree(f)) then
      print
        "equation has odd degree at a line at infinity. We must have points.";
      return true;
    elif LeadingCoefficient(f) lt 0 or TrailingCoefficient(f) lt 0 then
      print "negative leading or trailing coefficient";
      return true;
    else
      df:=Derivative(f);
      V:=RealRoots(df,RR,preceps);
      for t in V do
        w:=Evaluate(f,t);
        if w lt -eps then
          print "Looks like we found a point with negative sign",
                      [Evaluate(i,t): i in v];
          return true;
        elif w lt eps then
          print "extremal value takes undecided value (double point?)";
        end if;
      end for;
    end if;
  end for;
  print "Will now see what happens in extremal points";
  f:=Evaluate(F,[PF.1,PF.2,1]);
  dfx:=Derivative(f,PF.1);
  dfy:=Derivative(f,PF.2);
  rs:=SquarefreePart(Evaluate(Resultant(dfx,dfy,PF.1),[0,x,1]));
  yvals:=RealRoots(rs,RR,preceps);
  for yv in yvals do
    g:=Evaluate(dfx,[XRR,yv,1]);
    xvals:=[Re(x[1]): x in Roots(g)| Abs(Im(x[1])) lt eps];
    for xv in xvals do
      w:=Evaluate(f,[xv,yv,1]);
      if w lt -eps then
        print "found negative value at",[xv,yv,1];
        return true;
      elif w lt eps then
        print "undecided value",[xv,yv,1];
      end if;
    end for;
  end for;
  print "exhausted all possibilities";
  return false;
end intrinsic;

function Pad(L,n)
  if #L lt n then
    return L cat [Universe(L)|0: i in [1..n-#L]];
  else
    return L;
  end if;
end function;

intrinsic KummerImage(pi::Map,xpolmap::UserProgram,J::JacHyp)->Sch
  {Given the retun values of Prym, compute a model of C as a section of the
  Kummer surface of J}
  
  KJ:=KummerSurface(J);
  Km:=Scheme(KJ);
  P3:=Ambient(Km);
  k1:=Km.1;k2:=Km.2;k3:=Km.3;k4:=Km.4;
  D:=Domain(pi);
  C:=Codomain(pi);
  U:=D.1;V:=D.2;W:=D.3;
  
  mons:=[[i,j,k,l]: i in [j..4], j in [k..4], k in [l..4], l in [1..4]];

  M:=[];
  for t in [[1,b,c]:b,c in [-3..3]] do
    rel:=t[1]*U+t[2]*V+t[3]*W;
    print "rel=",rel;
    Qbar:=AlgebraicClosure();
    gn:=MinimalPolynomial(RationalPoints(Scheme(D,[rel]),Qbar)[1][1]);    
    Fld:=quo<Parent(gn)|gn>;
    if Degree(gn) eq 8 then
      P:=D(Fld)!RationalPoints(Scheme(D,[rel]),Fld)[1];
      xpol:=xpolmap(P,P);
      if Degree(xpol) ne 2 or Discriminant(xpol) eq 0 then
	print "!!!";
      else
	Jfld:=BaseChange(J,BaseRing(xpol));
	Jpnt:=RationalPoints(Jfld,xpol,2);
	Kfld:=KummerSurface(Jfld);
	kpnt:=Kfld!Jpnt[1];
	qds:=[ &*[kpnt[i]:i in mn]: mn in mons];
	L:=[[Pad(Eltseq(qds[i]),8)[j]:i in [1..#mons]]:j in [1..8]];
	L:=[l:l in L| l ne [0: i in [1..#mons]]];
	M cat:= L;
	print "#M=",#M;
	if #M gt #mons+4 then
	  print "Gathered enough data for interpolation.";
          break;
	end if;
      end if;
    end if;
  end for;

  bs:=Basis(Kernel(Transpose(Matrix(M))));
  v:=bs[1];
  w:=bs[2];
  topol:=map<Parent(v)->Parent(k1)|
    v:->&+[&*[P3.i: i in mons[j]]*v[j]: j in [1..#mons]]>;
  I:=[
    topol(v)*LCM([Denominator(c):c in Coefficients(topol(v))]),
    topol(w)*LCM([Denominator(c):c in Coefficients(topol(w))])];
  I:=[f/GCD([Numerator(c):c in Coefficients(f)]):f in I];
  Ckm:=Scheme(P3,I);
  return Ckm;
end intrinsic;

intrinsic CosetIntersection(V::Tup,W::Tup:Weak:=false)->Tup
  {Computes the intersection of two collections of cosets of an abelian group.
   If the parameter Weak is supplied, returns cosets of the kernel associated
   with V, otherwise returns cosets of the intersection of the kernels
   associated with V and W}
  require #V eq 2 and #W eq 2 and ISA(Type(V[1]),Map) and ISA(Type(W[1]),Map)
  and ISA(Type(V[2]),SetEnum) and ISA(Type(W[2]),SetEnum) and
  ISA(Type(Domain(V[1])),GrpAb) and Domain(V[1]) eq Domain(W[1]) and
  Universe(V[2]) eq Codomain(V[1]) and Universe(W[2]) eq Codomain(W[1]):
    "V and W must describe coset collections of the same abelian group";
  m1:=V[1];m2:=W[1];
  if Weak then
    G:=Domain(m1);
    gcd,togcd:=quo<G|Generators(Kernel(m1))join Generators(Kernel(m2))>;
    m1togcd:=hom<Codomain(m1)->gcd|
        [togcd(a@@m1):a in OrderedGenerators(Codomain(m1))]>;
    m2togcd:=hom<Codomain(m2)->gcd|
        [togcd(a@@m2):a in OrderedGenerators(Codomain(m2))]>;
    gcdW:={m2togcd(w):w in W[2]};
    return <V[1],{Universe(V[2])|v:v in V[2]| m1togcd(v) in gcdW}>;
  else
    G:=FreeAbelianGroup(Ngens(Domain(V[1])));
    m1:=hom<G->Image(m1)|[m1(g):g in OrderedGenerators(Domain(m1))]>;
    m2:=hom<G->Image(m2)|[m2(g):g in OrderedGenerators(Domain(m2))]>;
    gcd,togcd:=quo<G|Generators(Kernel(m1))join Generators(Kernel(m2))>;
    lcm,tolcm:=quo<G|Kernel(m1) meet Kernel(m2)>;
    lcmto1:=hom<lcm->Codomain(m1)|[m1(a@@tolcm):a in OrderedGenerators(lcm)]>;
    lcmto2:=hom<lcm->Codomain(m2)|[m2(a@@tolcm):a in OrderedGenerators(lcm)]>;
    m1togcd:=hom<Codomain(m1)->gcd|
        [togcd(a@@m1):a in OrderedGenerators(Codomain(m1))]>;
    m2togcd:=hom<Codomain(m2)->gcd|
        [togcd(a@@m2):a in OrderedGenerators(Codomain(m2))]>;
    function CRT(e1,e2)
      if m1togcd(e1) eq m2togcd(e2) then
        v:=Eltseq(e1@@m1-e2@@m2);
        A1:=[Eltseq(G!a):a in OrderedGenerators(Kernel(m1))];
        A2:=[Eltseq(G!a):a in OrderedGenerators(Kernel(m2))];
        w:=Solution(Matrix(A1 cat A2),Vector(v));
        crt:=tolcm(e1@@m1-Kernel(m1)![w[i]:i in [1..Ngens(Kernel(m1))]]);
        return {crt+a:a in Kernel(lcmto1)meet Kernel(lcmto2)};
      else
        return {lcm|};
      end if;
    end function;
    //This creates #V[2] * #W[2] complexity. Especially if
    //#gcd is comparatively large, one can do quite a bit better by first
    //sorting W[2] according to class in gcd and only CRT-ing with
    //elements of V[2] of the same class in gcd.
    return <hom<Domain(V[1])->lcm|[tolcm(g):g in OrderedGenerators(G)]>,
                  &join[CRT(v,w):v in V[2],w in W[2]]>;
  end if;
end intrinsic;
