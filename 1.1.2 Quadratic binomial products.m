(* ::Package:: *)

(* ::Section:: *)
(*1.1.2 Quadratic binomial products integration rules*)


(* ::Subsection::Closed:: *)
(*1.1.2.y (c x)^m Pq(x) (a+b x^2)^p*)


Int[x_^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*SubstFor[x^2,Pq,x]*(a+b*x)^p,x],x,x^2] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x^2] && IntegerQ[(m-1)/2]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
  1/c*Int[(c*x)^(m+1)*PolynomialQuotient[Pq,x,x]*(a+b*x^2)^p,x] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,x,x],0]


Int[(c_.*x_)^m_.*P2_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
  With[{f=Coeff[P2,x,0],g=Coeff[P2,x,1],h=Coeff[P2,x,2]},
  h*(c*x)^(m+1)*(a+b*x^2)^(p+1)/(b*c*(m+2*p+3)) /;
 EqQ[g,0] && EqQ[a*h*(m+1)-b*f*(m+2*p+3),0]] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[P2,x,2] && NeQ[m,-1]


Int[x_^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  Coeff[Pq,x,1-m]*(a+b*x^2)^(p+1)/(2*b*(p+1)) + 
  Int[x^m*ExpandToSum[Pq-Coeff[Pq,x,1-m]*x^(1-m),x]*(a+b*x^2)^p,x] /;
FreeQ[{a,b,m},x] && PolyQ[Pq,x] && IGtQ[p,0] && IGtQ[2-m,0] && NeQ[Coeff[Pq,x,1-m],0]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*Pq*(a+b*x^2)^p,x],x] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && IGtQ[p,-2]


Int[x_^m_*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{A=Coeff[Pq,x,0],Q=PolynomialQuotient[Pq-Coeff[Pq,x,0],x^2,x]},
  A*x^(m+1)*(a+b*x^2)^(p+1)/(a*(m+1)) + 1/(a*(m+1))*Int[x^(m+2)*(a+b*x^2)^p*(a*(m+1)*Q-A*b*(m+2*(p+1)+1)),x]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x^2] && IntegerQ[m/2] && ILtQ[(m+1)/2+p,0] && LtQ[m+Expon[Pq,x]+2*p+1,0]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a+b*x^2,x],
        f=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,1]},
  (c*x)^m*(a+b*x^2)^(p+1)*(a*g-b*f*x)/(2*a*b*(p+1)) + 
  c/(2*a*b*(p+1))*Int[(c*x)^(m-1)*(a+b*x^2)^(p+1)*ExpandToSum[2*a*b*(p+1)*x*Q-a*g*m+b*f*(m+2*p+3)*x,x],x]] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && LtQ[p,-1] && GtQ[m,0]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[(c*x)^m*Pq,a+b*x^2,x],
        f=Coeff[PolynomialRemainder[(c*x)^m*Pq,a+b*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[(c*x)^m*Pq,a+b*x^2,x],x,1]},
  (a*g-b*f*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) + 
  1/(2*a*(p+1))*Int[(c*x)^m*(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*(c*x)^(-m)*Q+f*(2*p+3)*(c*x)^(-m),x],x]] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && LtQ[p,-1] && ILtQ[m,0]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a+b*x^2,x],
        f=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,1]},
  -(c*x)^(m+1)*(f+g*x)*(a+b*x^2)^(p+1)/(2*a*c*(p+1)) + 
  1/(2*a*(p+1))*Int[(c*x)^m*(a+b*x^2)^(p+1)*ExpandToSum[2*a*(p+1)*Q+f*(m+2*p+3)+g*(m+2*p+4)*x,x],x]] /;
FreeQ[{a,b,c,m},x] && PolyQ[Pq,x] && LtQ[p,-1] && Not[GtQ[m,0]]


Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,c*x,x], R=PolynomialRemainder[Pq,c*x,x]},
  R*(c*x)^(m+1)*(a+b*x^2)^(p+1)/(a*c*(m+1)) + 
  1/(a*c*(m+1))*Int[(c*x)^(m+1)*(a+b*x^2)^p*ExpandToSum[a*c*(m+1)*Q-b*R*(m+2*p+3)*x,x],x]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && LtQ[m,-1] && (IntegerQ[2*p] || NeQ[Expon[Pq,x],1])


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Coeff[Pq,x,q]/c^q*Int[(c*x)^(m+q)*(a+b*x^2)^p,x] + 
  1/c^q*Int[(c*x)^m*(a+b*x^2)^p*ExpandToSum[c^q*Pq-Coeff[Pq,x,q]*(c*x)^q,x],x] /;
 EqQ[q,1] || EqQ[m+q+2*p+1,0]] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && Not[IGtQ[m,0] && ILtQ[p+1/2,0]]


Int[(c_.*x_)^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
  f*(c*x)^(m+q-1)*(a+b*x^2)^(p+1)/(b*c^(q-1)*(m+q+2*p+1)) + 
  1/(b*(m+q+2*p+1))*Int[(c*x)^m*(a+b*x^2)^p*ExpandToSum[b*(m+q+2*p+1)*Pq-b*f*(m+q+2*p+1)*x^q-a*f*(m+q-1)*x^(q-2),x],x] /;
 GtQ[q,1] && NeQ[m+q+2*p+1,0]] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && (Not[IGtQ[m,0]] || IGtQ[p+1/2,-1])


Int[x_^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],k},
  Int[x^m*Sum[Coeff[Pq,x,2*k]*x^(2*k),{k,0,q/2}]*(a+b*x^2)^p,x] + 
  Int[x^(m+1)*Sum[Coeff[Pq,x,2*k+1]*x^(2*k),{k,0,(q-1)/2}]*(a+b*x^2)^p,x]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && Not[PolyQ[Pq,x^2]] && IntegerQ[m] && NeQ[p,-1]


Int[(c_.*x_)^m_*Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
  Integral[(c*x)^m*Pq*(a+b*x^2)^p,x] /;
FreeQ[{a,b,c,m,p},x] && PolyQ[Pq,x] && Not[IGtQ[m,0]]


(* ::Subsection::Closed:: *)
(*1.1.2.x Pq(x) (a+b x^2)^p*)


Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  Coeff[Pq,x,1]*(a+b*x^2)^(p+1)/(2*b*(p+1)) + 
  Int[ExpandToSum[Pq-Coeff[Pq,x,1]*x,x]*(a+b*x^2)^p,x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[p,0] && NeQ[Coeff[Pq,x,1],0]


Int[Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^2)^p,x],x] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && IGtQ[p,-2]


Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  Int[x*PolynomialQuotient[Pq,x,x]*(a+b*x^2)^p,x] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,x,x],0] && Not[MatchQ[Pq,x^m_.*u_. /; IntegerQ[m]]]


Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{A=Coeff[Pq,x,0],Q=PolynomialQuotient[Pq-Coeff[Pq,x,0],x^2,x]},
  A*x*(a+b*x^2)^(p+1)/a + 1/a*Int[x^2*(a+b*x^2)^p*(a*Q-A*b*(2*p+3)),x]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x^2] && ILtQ[p+1/2,0] && LtQ[Expon[Pq,x]+2*p+1,0]


Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a+b*x^2,x],
        f=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[Pq,a+b*x^2,x],x,1]},
  (a*g-b*f*x)*(a+b*x^2)^(p+1)/(2*a*b*(p+1)) + 
  1/(2*a*b*(p+1))*Int[(a+b*x^2)^(p+1)*ExpandToSum[2*a*b*(p+1)*Q+b*f*(2*p+3),x],x]] /;
FreeQ[{a,b},x] && PolyQ[Pq,x] && LtQ[p,-1]


Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x],e=Coeff[Pq,x,Expon[Pq,x]]},
  e*x^(q-1)*(a+b*x^2)^(p+1)/(b*(q+2*p+1)) + 
  1/(b*(q+2*p+1))*Int[(a+b*x^2)^p*ExpandToSum[b*(q+2*p+1)*Pq-a*e*(q-1)*x^(q-2)-b*e*(q+2*p+1)*x^q,x],x]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && Not[LeQ[p,-1]]


Int[Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],k},
  Int[Sum[Coeff[Pq,x,2*k]*x^(2*k),{k,0,q/2}]*(a+b*x^2)^p,x] + 
  Int[x*Sum[Coeff[Pq,x,2*k+1]*x^(2*k),{k,0,(q-1)/2}]*(a+b*x^2)^p,x]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && Not[PolyQ[Pq,x^2]] && NeQ[p,-1]


Int[Pq_*(a_+b_.*x_^2)^p_.,x_Symbol] :=
  Integral[Pq*(a+b*x^2)^p,x] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x]
