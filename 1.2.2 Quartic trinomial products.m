(* ::Package:: *)

(* ::Section:: *)
(*1.2.2 Quartic trinomial products integration rules*)


(* ::Subsection::Closed:: *)
(*1.2.2.1 (a+b x^2+c x^4)^p*)


(* Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  1/c^p*Int[(b/2+c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,p},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p] *)


(* Int[1/(a_+b_.*x_^2+c_.*x_^4)^(5/4),x_Symbol] :=
  2*x/(3*a*(a+b*x^2+c*x^4)^(1/4)) + x*(2*a+b*x^2)/(6*a*(a+b*x^2+c*x^4)^(5/4)) /;
FreeQ[{a,b,c},x] && EqQ[b^2-4*a*c,0] *)


Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^p/(b+2*c*x^2)^(2*p)*Int[(b+2*c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,p},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p-1/2]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^2+c*x^4)^FracPart[p]/(1+2*c*x^2/b)^(2*FracPart[p])*Int[(1+2*c*x^2/b)^(2*p),x] /;
FreeQ[{a,b,c,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[2*p]]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  x*(a+b*x^2+c*x^4)^p/(4*p+1) + 
  2*p/(4*p+1)*Int[(2*a+b*x^2)*(a+b*x^2+c*x^4)^(p-1),x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && IntegerQ[2*p]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  -x*(b^2-2*a*c+b*c*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*a*(p+1)*(b^2-4*a*c)) +
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[(b^2-2*a*c+2*(p+1)*(b^2-4*a*c)+b*c*(4*p+7)*x^2)*(a+b*x^2+c*x^4)^(p+1),x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IntegerQ[2*p]


Int[1/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[1/(b/2-q/2+c*x^2),x] - c/q*Int[1/(b/2+q/2+c*x^2),x]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && PosQ[b^2-4*a*c]


Int[1/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[a/c,2]},
  With[{r=Rt[2*q-b/c,2]},
  1/(2*c*q*r)*Int[(r-x)/(q-r*x+x^2),x] + 1/(2*c*q*r)*Int[(r+x)/(q+r*x+x^2),x]]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && NegQ[b^2-4*a*c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*Sqrt[-c]*Int[1/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[c,0]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  (1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(2*q*Sqrt[a+b*x^2+c*x^4])*EllipticF[2*ArcTan[q*x],1/2-b*q^2/(4*c)]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && GtQ[c/a,0] && LtQ[b/a,0]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[-2*a-(b-q)*x^2]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*Sqrt[-a]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)] /;
  IntegerQ[q]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*Sqrt[a+b*x^2+c*x^4]*Sqrt[a/(2*a+(b+q)*x^2)])*
    EllipticF[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*a+(b+q)*x^2)*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]/(2*a*Rt[(b+q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcTan[Rt[(b+q)/(2*a),2]*x],2*q/(b+q)] /;
 PosQ[(b+q)/a] && Not[PosQ[(b-q)/a] && SimplerSqrtQ[(b-q)/(2*a),(b+q)/(2*a)]]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*a+(b-q)*x^2)*Sqrt[(2*a+(b+q)*x^2)/(2*a+(b-q)*x^2)]/(2*a*Rt[(b-q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcTan[Rt[(b-q)/(2*a),2]*x],-2*q/(b-q)] /;
 PosQ[(b-q)/a]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+(b+q)*x^2/(2*a)]*Sqrt[1+(b-q)*x^2/(2*a)]/(Rt[-(b+q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcSin[Rt[-(b+q)/(2*a),2]*x],(b-q)/(b+q)] /;
 NegQ[(b+q)/a] && Not[NegQ[(b-q)/a] && SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+(b-q)*x^2/(2*a)]*Sqrt[1+(b+q)*x^2/(2*a)]/(Rt[-(b-q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcSin[Rt[-(b-q)/(2*a),2]*x],(b+q)/(b-q)] /;
 NegQ[(b-q)/a]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  (1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(2*q*Sqrt[a+b*x^2+c*x^4])*EllipticF[2*ArcTan[q*x],1/2-b*q^2/(4*c)]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[1/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && NegQ[c/a]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  a^IntPart[p]*(a+b*x^2+c*x^4)^FracPart[p]/((1+2*c*x^2/(b+q))^FracPart[p]*(1+2*c*x^2/(b-q))^FracPart[p])*
    Int[(1+2*c*x^2/(b+q))^p*(1+2*c*x^2/(b-q))^p,x]] /;
FreeQ[{a,b,c,p},x] && NeQ[b^2-4*a*c,0]





(* ::Subsection::Closed:: *)
(*1.2.2.2 (d x)^m (a+b x^2+c x^4)^p*)


(* Int[(d_.*x_)^m_.*(b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/d^(2*p)*Int[(d*x)^(m+2*p)*(b+c*x^2)^p,x] /;
FreeQ[{b,c,d,m},x] && IntegerQ[p] *)


(* Int[(d_.*x_)^m_.*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (b*x^2+c*x^4)^p/((d*x)^(2*p)*(b+c*x^2)^p)*Int[(d*x)^(m+2*p)*(b+c*x^2)^p,x] /;
FreeQ[{b,c,d,m,p},x] && Not[IntegerQ[p]] *)


Int[x_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/2*Subst[Int[(a+b*x+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,b,c,p},x]


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c,d,m},x] && IGtQ[p,0] && Not[IntegerQ[(m+1)/2]]


(* Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/c^p*Int[(d*x)^m*(b/2+c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p] *)


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  2*(d*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(d*(m+3)*(2*a+b*x^2)) - 
  (d*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(2*a*d*(m+3)*(p+1)) /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && EqQ[m+4*p+5,0] && LtQ[p,-1]


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(4*a*d*(p+1)*(2*p+1)) - 
  (d*x)^(m+1)*(2*a+b*x^2)*(a+b*x^2+c*x^4)^p/(4*a*d*(2*p+1)) /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && EqQ[m+4*p+5,0] && NeQ[p,-1/2]


Int[x_^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*(a+b*x+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,b,c,p},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p-1/2] && IntegerQ[(m-1)/2] && (GtQ[m,0] || LtQ[0,4*p,-m-1])


(* Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  c*(a+b*x^2+c*x^4)^(p+1)/(b/2+c*x^2)^(2*(p+1))*Int[(d*x)^m*(b/2+c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p-1/2] && IGeQ[m,2*p] *)


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^FracPart[p]/(c^IntPart[p]*(b/2+c*x^2)^(2*FracPart[p]))*Int[(d*x)^m*(b/2+c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p-1/2]


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^2+c*x^4)^FracPart[p]/(1+2*c*x^2/b)^(2*FracPart[p])*Int[(d*x)^m*(1+2*c*x^2/b)^(2*p),x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[2*p]]


Int[x_^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*(a+b*x+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,b,c,p},x] && IntegerQ[(m-1)/2]


Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/d*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(2*k)/d^2+c*x^(4*k)/d^4)^p,x],x,(d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && NeQ[b^2-4*a*c,0] && FractionQ[m] && IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  d*(d*x)^(m-1)*(a+b*x^2+c*x^4)^p*(2*b*p+c*(m+4*p-1)*x^2)/(c*(m+4*p+1)*(m+4*p-1)) - 
  2*p*d^2/(c*(m+4*p+1)*(m+4*p-1))*
    Int[(d*x)^(m-2)*(a+b*x^2+c*x^4)^(p-1)*Simp[a*b*(m-1)-(2*a*c*(m+4*p-1)-b^2*(m+2*p-1))*x^2,x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && GtQ[m,1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^2+c*x^4)^p/(d*(m+1)) - 
  2*p/(d^2*(m+1))*Int[(d*x)^(m+2)*(b+2*c*x^2)*(a+b*x^2+c*x^4)^(p-1),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && LtQ[m,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^2+c*x^4)^p/(d*(m+4*p+1)) + 
  2*p/(m+4*p+1)*Int[(d*x)^m*(2*a+b*x^2)*(a+b*x^2+c*x^4)^(p-1),x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[m+4*p+1,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  d*(d*x)^(m-1)*(b+2*c*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*(p+1)*(b^2-4*a*c)) - 
  d^2/(2*(p+1)*(b^2-4*a*c))*Int[(d*x)^(m-2)*(b*(m-1)+2*c*(m+4*p+5)*x^2)*(a+b*x^2+c*x^4)^(p+1),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,1] && LeQ[m,3] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  -d^3*(d*x)^(m-3)*(2*a+b*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*(p+1)*(b^2-4*a*c)) + 
  d^4/(2*(p+1)*(b^2-4*a*c))*Int[(d*x)^(m-4)*(2*a*(m-3)+b*(m+4*p+3)*x^2)*(a+b*x^2+c*x^4)^(p+1),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,3] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  -(d*x)^(m+1)*(b^2-2*a*c+b*c*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*a*d*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^m*(a+b*x^2+c*x^4)^(p+1)*Simp[b^2*(m+2*p+3)-2*a*c*(m+4*p+5)+b*c*(m+4*p+7)*x^2,x],x] /;
FreeQ[{a,b,c,d,m},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  d^3*(d*x)^(m-3)*(a+b*x^2+c*x^4)^(p+1)/(c*(m+4*p+1)) - 
  d^4/(c*(m+4*p+1))*
    Int[(d*x)^(m-4)*Simp[a*(m-3)+b*(m+2*p-1)*x^2,x]*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,d,p},x] && NeQ[b^2-4*a*c,0] && GtQ[m,3] && NeQ[m+4*p+1,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(d_.*x_)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(a*d*(m+1)) - 
  1/(a*d^2*(m+1))*Int[(d*x)^(m+2)*(b*(m+2*p+3)+c*(m+4*p+5)*x^2)*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,d,p},x] && NeQ[b^2-4*a*c,0] && LtQ[m,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(d_.*x_)^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  (d*x)^(m+1)/(a*d*(m+1)) -
  1/(a*d^2)*Int[(d*x)^(m+2)*(b+c*x^2)/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && LtQ[m,-1]


Int[x_^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  Int[PolynomialDivide[x^m,(a+b*x^2+c*x^4),x],x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && IGtQ[m,5]


Int[(d_.*x_)^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  d^3*(d*x)^(m-3)/(c*(m-3)) - d^4/c*Int[(d*x)^(m-4)*(a+b*x^2)/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && GtQ[m,3]


Int[x_^2/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  With[{q=Rt[a/c,2]},
  1/2*Int[(q+x^2)/(a+b*x^2+c*x^4),x] - 1/2*Int[(q-x^2)/(a+b*x^2+c*x^4),x]] /;
FreeQ[{a,b,c},x] && LtQ[b^2-4*a*c,0] && PosQ[a*c]


Int[x_^m_./(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[a/c,2]},
  With[{r=Rt[2*q-b/c,2]},
  1/(2*c*r)*Int[x^(m-3)*(q+r*x)/(q+r*x+x^2),x] - 
  1/(2*c*r)*Int[x^(m-3)*(q-r*x)/(q-r*x+x^2),x]]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && GeQ[m,3] && LtQ[m,4] && NegQ[b^2-4*a*c]


Int[x_^m_./(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[a/c,2]},
  With[{r=Rt[2*q-b/c,2]},
  1/(2*c*r)*Int[x^(m-1)/(q-r*x+x^2),x] - 1/(2*c*r)*Int[x^(m-1)/(q+r*x+x^2),x]]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && GeQ[m,1] && LtQ[m,3] && NegQ[b^2-4*a*c]


Int[(d_.*x_)^m_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  d^2/2*(b/q+1)*Int[(d*x)^(m-2)/(b/2+q/2+c*x^2),x] - 
  d^2/2*(b/q-1)*Int[(d*x)^(m-2)/(b/2-q/2+c*x^2),x]] /;
FreeQ[{a,b,c,d},x] && NeQ[b^2-4*a*c,0] && GeQ[m,2]


Int[(d_.*x_)^m_./(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[(d*x)^m/(b/2-q/2+c*x^2),x] - c/q*Int[(d*x)^m/(b/2+q/2+c*x^2),x]] /;
FreeQ[{a,b,c,d,m},x] && NeQ[b^2-4*a*c,0]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*Sqrt[-c]*Int[x^2/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[c,0]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  1/q*Int[1/Sqrt[a+b*x^2+c*x^4],x] - 1/q*Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && GtQ[c/a,0] && LtQ[b/a,0]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(b-q)/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  x*(b+q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) - 
  Rt[(b+q)/(2*a),2]*(2*a+(b+q)*x^2)*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]/(2*c*Sqrt[a+b*x^2+c*x^4])*
    EllipticE[ArcTan[Rt[(b+q)/(2*a),2]*x],2*q/(b+q)] /;
 PosQ[(b+q)/a] && Not[PosQ[(b-q)/a] && SimplerSqrtQ[(b-q)/(2*a),(b+q)/(2*a)]]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  x*(b-q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) - 
  Rt[(b-q)/(2*a),2]*(2*a+(b-q)*x^2)*Sqrt[(2*a+(b+q)*x^2)/(2*a+(b-q)*x^2)]/(2*c*Sqrt[a+b*x^2+c*x^4])*
    EllipticE[ArcTan[Rt[(b-q)/(2*a),2]*x],-2*q/(b-q)] /;
 PosQ[(b-q)/a]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(b+q)/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c)*Int[(b+q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NegQ[(b+q)/a] && Not[NegQ[(b-q)/a] && SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(b-q)/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NegQ[(b-q)/a]] /;
FreeQ[{a,b,c},x] && GtQ[b^2-4*a*c,0]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  1/q*Int[1/Sqrt[a+b*x^2+c*x^4],x] - 1/q*Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[x^2/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && NegQ[c/a]


Int[(d_.*x_)^m_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^2+c*x^4)^FracPart[p]/
    ((1+2*c*x^2/(b+Rt[b^2-4*a*c,2]))^FracPart[p]*(1+2*c*x^2/(b-Rt[b^2-4*a*c,2]))^FracPart[p])*
    Int[(d*x)^m*(1+2*c*x^2/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^2/(b-Sqrt[b^2-4*a*c]))^p,x] /;
FreeQ[{a,b,c,d,m,p},x]


Int[u_^m_.*(a_.+b_.*v_^2+c_.*v_^4)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^2+c*x^(2*2))^p,x],x,v] /;
FreeQ[{a,b,c,m,p},x] && LinearPairQ[u,v,x]





(* ::Subsection::Closed:: *)
(*1.2.2.3 (d+e x^2)^q (a+b x^2+c x^4)^p*)


Int[(d_+e_.*x_^2)/(b_.*x_^2+c_.*x_^4)^(3/4),x_Symbol] :=
  -2*(c*d-b*e)*(b*x^2+c*x^4)^(1/4)/(b*c*x) + e/c*Int[(b*x^2+c*x^4)^(1/4)/x^2,x] /;
FreeQ[{b,c,d,e},x]


Int[(d_+e_.*x_^2)*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  e*(b*x^2+c*x^4)^(p+1)/(c*(4*p+3)*x) /;
FreeQ[{b,c,d,e,p},x] && Not[IntegerQ[p]] && NeQ[4*p+3,0] && EqQ[b*e*(2*p+1)-c*d*(4*p+3),0]


Int[(d_+e_.*x_^2)*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  e*(b*x^2+c*x^4)^(p+1)/(c*(4*p+3)*x) - ((b*e*(2*p+1)-c*d*(4*p+3))/(c*(4*p+3)))*Int[(b*x^2+c*x^4)^p,x] /;
FreeQ[{b,c,d,e,p},x] && Not[IntegerQ[p]] && NeQ[4*p+3,0] && NeQ[b*e*(2*p+1)-c*d*(4*p+3),0]


Int[(d_+e_.*x_^2)^q_.*(b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (b*x^2+c*x^4)^FracPart[p]/(x^(2*FracPart[p])*(b+c*x^2)^FracPart[p])*Int[x^(2*p)*(d+e*x^2)^q*(b+c*x^2)^p,x] /;
FreeQ[{b,c,d,e,p,q},x] && Not[IntegerQ[p]]


(* Int[(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/c^p*Int[(d+e*x^2)^q*(b/2+c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p] *)


Int[(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^p/(d+e*x^2)^(2*p)*Int[(d+e*x^2)^(q+2*p),x] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && EqQ[2*c*d-b*e,0]


Int[(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^FracPart[p]/(c^IntPart[p]*(b/2+c*x^2)^(2*FracPart[p]))*Int[(d+e*x^2)^q*(b/2+c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Int[(d+e*x^2)^(p+q)*(a/d+c/e*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p]


Int[(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  Int[(d+e*x^2)^(p+q)*(a/d+c/e*x^2)^p,x] /;
FreeQ[{a,c,d,e,q},x] && EqQ[c*d^2+a*e^2,0] && IntegerQ[p]


Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^FracPart[p]/((d+e*x^2)^FracPart[p]*(a/d+c*x^2/e)^FracPart[p])*Int[(d+e*x^2)^(p+q)*(a/d+c/e*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  (a+c*x^4)^FracPart[p]/((d+e*x^2)^FracPart[p]*(a/d+c*x^2/e)^FracPart[p])*Int[(d+e*x^2)^(p+q)*(a/d+c/e*x^2)^p,x] /;
FreeQ[{a,c,d,e,p,q},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0] && IGtQ[q,0]


Int[(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && IGtQ[q,0]


(* Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  -(c*d^2-b*d*e+a*e^2)*x*(d+e*x^2)^(q+1)/(2*d*e^2*(q+1)) + 
  1/(2*d*e^2*(q+1))*Int[(d+e*x^2)^(q+1)*Simp[c*d^2-b*d*e+a*e^2*(2*q+3)+2*c*d*e*(q+1)*x^2,x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[q,-1] *)


(* Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4),x_Symbol] :=
  -(c*d^2+a*e^2)*x*(d+e*x^2)^(q+1)/(2*d*e^2*(q+1)) + 
  1/(2*d*e^2*(q+1))*Int[(d+e*x^2)^(q+1)*Simp[c*d^2+a*e^2*(2*q+3)+2*c*d*e*(q+1)*x^2,x],x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && LtQ[q,-1] *)


(* Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  c*x^(2+1)*(d+e*x^2)^(q+1)/(e*(2*q+5)) + 
  1/(e*(2*q+5))*Int[(d+e*x^2)^q*(a*e*(2*q+5)-(3*c*d-b*e*(2*q+5))*x^2),x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] *)


(* Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4),x_Symbol] :=
  c*x^(2+1)*(d+e*x^2)^(q+1)/(e*(2*(q+2)+1)) + 
  1/(e*(2*q+5))*Int[(d+e*x^2)^q*(a*e*(2*q+5)-3*c*d*x^2),x] /;
FreeQ[{a,c,d,e,q},x] && NeQ[c*d^2+a*e^2,0] *)


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[2*d/e-b/c,2]},
  e/(2*c)*Int[1/Simp[d/e+q*x+x^2,x],x] + e/(2*c)*Int[1/Simp[d/e-q*x+x^2,x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && (GtQ[2*d/e-b/c,0] || Not[LtQ[2*d/e-b/c,0]] && EqQ[d-e*Rt[a/c,2],0])


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[2*d/e,2]},
  e/(2*c)*Int[1/Simp[d/e+q*x+x^2,x],x] + e/(2*c)*Int[1/Simp[d/e-q*x+x^2,x],x]] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2-a*e^2,0] && PosQ[d*e]


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (e/2+(2*c*d-b*e)/(2*q))*Int[1/(b/2-q/2+c*x^2),x] + (e/2-(2*c*d-b*e)/(2*q))*Int[1/(b/2+q/2+c*x^2),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && GtQ[b^2-4*a*c,0]


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[-2*d/e-b/c,2]},
  e/(2*c*q)*Int[(q-2*x)/Simp[d/e+q*x-x^2,x],x] + e/(2*c*q)*Int[(q+2*x)/Simp[d/e-q*x-x^2,x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && Not[GtQ[b^2-4*a*c,0]]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[-2*d/e,2]},
  e/(2*c*q)*Int[(q-2*x)/Simp[d/e+q*x-x^2,x],x] + e/(2*c*q)*Int[(q+2*x)/Simp[d/e-q*x-x^2,x],x]] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2-a*e^2,0] && NegQ[d*e]


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (e/2+(2*c*d-b*e)/(2*q))*Int[1/(b/2-q/2+c*x^2),x] + (e/2-(2*c*d-b*e)/(2*q))*Int[1/(b/2+q/2+c*x^2),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-a*e^2,0] && PosQ[b^2-4*a*c]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (e/2+c*d/(2*q))*Int[1/(-q+c*x^2),x] + (e/2-c*d/(2*q))*Int[1/(q+c*x^2),x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2-a*e^2,0] && PosQ[-a*c]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  (d*q+a*e)/(2*a*c)*Int[(q+c*x^2)/(a+c*x^4),x] + (d*q-a*e)/(2*a*c)*Int[(q-c*x^2)/(a+c*x^4),x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && NeQ[c*d^2-a*e^2,0] && NegQ[-a*c]


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[a/c,2]},
  With[{r=Rt[2*q-b/c,2]},
  1/(2*c*q*r)*Int[(d*r-(d-e*q)*x)/(q-r*x+x^2),x] + 1/(2*c*q*r)*Int[(d*r+(d-e*q)*x)/(q+r*x+x^2),x]]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NegQ[b^2-4*a*c]


Int[(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q/(a+b*x^2+c*x^4),x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[q]


Int[(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q/(a+c*x^4),x],x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IntegerQ[q]


Int[(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  e^2/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x^2)^q,x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x^2)^(q+1)*(c*d-b*e-c*e*x^2)/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[q]] && LtQ[q,-1]


Int[(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  e^2/(c*d^2+a*e^2)*Int[(d+e*x^2)^q,x] + 
  c/(c*d^2+a*e^2)*Int[(d+e*x^2)^(q+1)*(d-e*x^2)/(a+c*x^4),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[q]] && LtQ[q,-1]


Int[(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  2*c/r*Int[(d+e*x^2)^q/(b-r+2*c*x^2),x] - 2*c/r*Int[(d+e*x^2)^q/(b+r+2*c*x^2),x]] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[q]]


Int[(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  With[{r=Rt[-a*c,2]},
  -c/(2*r)*Int[(d+e*x^2)^q/(r-c*x^2),x] - c/(2*r)*Int[(d+e*x^2)^q/(r+c*x^2),x]] /;
FreeQ[{a,c,d,e,q},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[q]]


Int[(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  x*(2*b*e*p+c*d*(4*p+3)+c*e*(4*p+1)*x^2)*(a+b*x^2+c*x^4)^p/(c*(4*p+1)*(4*p+3)) + 
  2*p/(c*(4*p+1)*(4*p+3))*Int[Simp[2*a*c*d*(4*p+3)-a*b*e+(2*a*c*e*(4*p+1)+b*c*d*(4*p+3)-b^2*e*(2*p+1))*x^2,x]*
    (a+b*x^2+c*x^4)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && GtQ[p,0] && FractionQ[p] && IntegerQ[2*p]


Int[(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
  x*(d*(4*p+3)+e*(4*p+1)*x^2)*(a+c*x^4)^p/((4*p+1)*(4*p+3)) + 
  2*p/((4*p+1)*(4*p+3))*Int[Simp[2*a*d*(4*p+3)+(2*a*e*(4*p+1))*x^2,x]*(a+c*x^4)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && GtQ[p,0] && FractionQ[p] && IntegerQ[2*p]


Int[(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  -x*(d*b^2-a*b*e-2*a*c*d+(b*d-2*a*e)*c*x^2)*(a+b*x^2+c*x^4)^(p+1)/(2*a*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[Simp[(2*p+3)*d*b^2-a*b*e-2*a*c*d*(4*p+5)+(4*p+7)*(d*b-2*a*e)*c*x^2,x]*
    (a+b*x^2+c*x^4)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && IntegerQ[2*p]


Int[(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
  -x*(d+e*x^2)*(a+c*x^4)^(p+1)/(4*a*(p+1)) + 
  1/(4*a*(p+1))*Int[Simp[d*(4*p+5)+e*(4*p+7)*x^2,x]*(a+c*x^4)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && IntegerQ[2*p]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*Sqrt[-c]*Int[(d+e*x^2)/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && LtQ[c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  Sqrt[-c]*Int[(d+e*x^2)/(Sqrt[q+c*x^2]*Sqrt[q-c*x^2]),x]] /;
FreeQ[{a,c,d,e},x] && GtQ[a,0] && LtQ[c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  -d*x*Sqrt[a+b*x^2+c*x^4]/(a*(1+q^2*x^2)) + 
  d*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+b*x^2+c*x^4])*EllipticE[2*ArcTan[q*x],1/2-b*q^2/(4*c)] /;
 EqQ[e+d*q^2,0]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && GtQ[c/a,0] && LtQ[b/a,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  (e+d*q)/q*Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/q*Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NeQ[e+d*q,0]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && GtQ[c/a,0] && LtQ[b/a,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  e*x*(b+q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) - 
  e*q*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*c*Sqrt[a+b*x^2+c*x^4]*Sqrt[a/(2*a+(b+q)*x^2)])*
    EllipticE[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)] /;
 EqQ[2*c*d-e*(b-q),0]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  e*x*(q+c*x^2)/(c*Sqrt[a+c*x^4]) - 
  Sqrt[2]*e*q*Sqrt[-a+q*x^2]*Sqrt[(a+q*x^2)/q]/(Sqrt[-a]*c*Sqrt[a+c*x^4])*
    EllipticE[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2] /;
 EqQ[c*d+e*q,0] && IntegerQ[q]] /;
FreeQ[{a,c,d,e},x] && LtQ[a,0] && GtQ[c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  e*x*(q+c*x^2)/(c*Sqrt[a+c*x^4]) - 
  Sqrt[2]*e*q*Sqrt[(a-q*x^2)/(a+q*x^2)]*Sqrt[(a+q*x^2)/q]/(c*Sqrt[a+c*x^4]*Sqrt[a/(a+q*x^2)])*
    EllipticE[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2] /;
 EqQ[c*d+e*q,0]] /;
FreeQ[{a,c,d,e},x] && LtQ[a,0] && GtQ[c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-e*(b-q))/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NeQ[2*c*d-e*(b-q),0]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && LtQ[a,0] && GtQ[c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (c*d+e*q)/c*Int[1/Sqrt[a+c*x^4],x] - e/c*Int[(q-c*x^2)/Sqrt[a+c*x^4],x] /;
 NeQ[c*d+e*q,0]] /;
FreeQ[{a,c,d,e},x] && LtQ[a,0] && GtQ[c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  d*Int[1/Sqrt[a+b*x^2+c*x^4],x] + e*Int[x^2/Sqrt[a+b*x^2+c*x^4],x] /;
 PosQ[(b+q)/a] || PosQ[(b-q)/a]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  d*Int[1/Sqrt[a+c*x^4],x] + e*Int[x^2/Sqrt[a+c*x^4],x] /;
FreeQ[{a,c,d,e},x] && GtQ[-a*c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -a*e*Rt[-(b+q)/(2*a),2]*Sqrt[1+(b+q)*x^2/(2*a)]*Sqrt[1+(b-q)*x^2/(2*a)]/(c*Sqrt[a+b*x^2+c*x^4])*
    EllipticE[ArcSin[Rt[-(b+q)/(2*a),2]*x],(b-q)/(b+q)] /;
 NegQ[(b+q)/a] && EqQ[2*c*d-e*(b+q),0] && Not[SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-e*(b+q))/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c)*Int[(b+q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NegQ[(b+q)/a] && NeQ[2*c*d-e*(b+q),0] && Not[SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -a*e*Rt[-(b-q)/(2*a),2]*Sqrt[1+(b-q)*x^2/(2*a)]*Sqrt[1+(b+q)*x^2/(2*a)]/(c*Sqrt[a+b*x^2+c*x^4])*
    EllipticE[ArcSin[Rt[-(b-q)/(2*a),2]*x],(b+q)/(b-q)] /;
 NegQ[(b-q)/a] && EqQ[2*c*d-e*(b-q),0]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-e*(b-q))/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NegQ[(b-q)/a] && NeQ[2*c*d-e*(b-q),0]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  -d*x*Sqrt[a+b*x^2+c*x^4]/(a*(1+q^2*x^2)) + 
  d*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+b*x^2+c*x^4])*EllipticE[2*ArcTan[q*x],1/2-b*q^2/(4*c)] /;
 EqQ[e+d*q^2,0]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  -d*x*Sqrt[a+c*x^4]/(a*(1+q^2*x^2)) + 
  d*(1+q^2*x^2)*Sqrt[(a+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+c*x^4])*EllipticE[2*ArcTan[q*x],1/2] /;
 EqQ[e+d*q^2,0]] /;
FreeQ[{a,c,d,e},x] && PosQ[c/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  (e+d*q)/q*Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/q*Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NeQ[e+d*q,0]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  (e+d*q)/q*Int[1/Sqrt[a+c*x^4],x] - e/q*Int[(1-q*x^2)/Sqrt[a+c*x^4],x] /;
 NeQ[e+d*q,0]] /;
FreeQ[{a,c,d,e},x] && PosQ[c/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  d/Sqrt[a]*Int[Sqrt[1+e*x^2/d]/Sqrt[1-e*x^2/d],x] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && EqQ[c*d^2+a*e^2,0] && GtQ[a,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  Sqrt[1+c*x^4/a]/Sqrt[a+c*x^4]*Int[(d+e*x^2)/Sqrt[1+c*x^4/a],x] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && EqQ[c*d^2+a*e^2,0] && Not[GtQ[a,0]]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-c/a,2]},
  (d*q-e)/q*Int[1/Sqrt[a+c*x^4],x] + e/q*Int[(1+q*x^2)/Sqrt[a+c*x^4],x]] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && NeQ[c*d^2+a*e^2,0]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[(d+e*x^2)/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NegQ[c/a]


Int[(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)*(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)*(a+c*x^4)^p,x],x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


(* Int[(d_+e_.*x_^2)^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  e^2*x*Sqrt[a+b*x^2+c*x^4]/(3*c) + 
  2*(3*c*d-b*e)/(3*c)*Int[(d+e*x^2)/Sqrt[a+b*x^2+c*x^4],x] - 
  (3*c*d^2-2*b*d*e+a*e^2)/(3*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] *)


(* Int[(d_+e_.*x_^2)^2/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  e^2*x*Sqrt[a+c*x^4]/(3*c) + 
  2*d*Int[(d+e*x^2)/Sqrt[a+c*x^4],x] - 
  (3*c*d^2+a*e^2)/(3*c)*Int[1/Sqrt[a+c*x^4],x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] *)


(* Int[(d_+e_.*x_^2)^q_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  e^2*x*(d+e*x^2)^(q-2)*Sqrt[a+b*x^2+c*x^4]/(c*(2*q-1)) + 
  2*(q-1)*(3*c*d-b*e)/(c*(2*q-1))*Int[(d+e*x^2)^(q-1)/Sqrt[a+b*x^2+c*x^4],x] - 
  (2*q-3)*(3*c*d^2-2*b*d*e+a*e^2)/(c*(2*q-1))*Int[(d+e*x^2)^(q-2)/Sqrt[a+b*x^2+c*x^4],x] + 
  2*d*(q-2)*(c*d^2-b*d*e+a*e^2)/(c*(2*q-1))*Int[(d+e*x^2)^(q-3)/Sqrt[a+b*x^2+c*x^4],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[q,2] *)


(* Int[(d_+e_.*x_^2)^q_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  e^2*x*(d+e*x^2)^(q-2)*Sqrt[a+c*x^4]/(c*(2*q-1)) + 
  6*d*(q-1)/(2*q-1)*Int[(d+e*x^2)^(q-1)/Sqrt[a+c*x^4],x] - 
  (2*q-3)*(3*c*d^2+a*e^2)/(c*(2*q-1))*Int[(d+e*x^2)^(q-2)/Sqrt[a+c*x^4],x] + 
  2*d*(q-2)*(c*d^2+a*e^2)/(c*(2*q-1))*Int[(d+e*x^2)^(q-3)/Sqrt[a+c*x^4],x] /;
FreeQ[{a,c,d,e},x] && IGtQ[q,2] *)


Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{f=Coeff[PolynomialRemainder[(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,0],
        g=Coeff[PolynomialRemainder[(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,2]},
  x*(a+b*x^2+c*x^4)^(p+1)*(a*b*g-f*(b^2-2*a*c)-c*(b*f-2*a*g)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[(a+b*x^2+c*x^4)^(p+1)*
    ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*PolynomialQuotient[(d+e*x^2)^q,a+b*x^2+c*x^4,x]+
      b^2*f*(2*p+3)-2*a*c*f*(4*p+5)-a*b*g+c*(4*p+7)*(b*f-2*a*g)*x^2,x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[q,1] && LtQ[p,-1]


Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  e^q*x^(2*q-3)*(a+b*x^2+c*x^4)^(p+1)/(c*(4*p+2*q+1)) + 
  1/(c*(4*p+2*q+1))*Int[(a+b*x^2+c*x^4)^p*
    ExpandToSum[c*(4*p+2*q+1)*(d+e*x^2)^q-a*(2*q-3)*e^q*x^(2*q-4)-b*(2*p+2*q-1)*e^q*x^(2*q-2)-c*(4*p+2*q+1)*e^q*x^(2*q),x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[q,1]


Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  e^q*x^(2*q-3)*(a+c*x^4)^(p+1)/(c*(4*p+2*q+1)) + 
  1/(c*(4*p+2*q+1))*Int[(a+c*x^4)^p*
    ExpandToSum[c*(4*p+2*q+1)*(d+e*x^2)^q-a*(2*q-3)*e^q*x^(2*q-4)-c*(4*p+2*q+1)*e^q*x^(2*q),x],x] /;
FreeQ[{a,c,d,e,p},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[q,1]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
  -1/e^2*Int[(c*d-b*e-c*e*x^2)*(a+b*x^2+c*x^4)^(p-1),x] + 
  (c*d^2-b*d*e+a*e^2)/e^2*Int[(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p+1/2,0]


Int[(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
  -1/e^2*Int[(c*d-c*e*x^2)*(a+c*x^4)^(p-1),x] + 
  (c*d^2+a*e^2)/e^2*Int[(a+c*x^4)^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p+1/2,0]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*Sqrt[-c]*Int[1/((d+e*x^2)*Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && LtQ[c,0]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  Sqrt[-c]*Int[1/((d+e*x^2)*Sqrt[q+c*x^2]*Sqrt[q-c*x^2]),x]] /;
FreeQ[{a,c,d,e},x] && GtQ[a,0] && LtQ[c,0]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/(2*c*d-e*(b-q))*Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/(2*c*d-e*(b-q))*Int[(b-q+2*c*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
FreeQ[{a,b,c,d,e},x] && GtQ[b^2-4*a*c,0] && Not[LtQ[c,0]]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  c/(c*d+e*q)*Int[1/Sqrt[a+c*x^4],x] + e/(c*d+e*q)*Int[(q-c*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
FreeQ[{a,c,d,e},x] && GtQ[-a*c,0] && Not[LtQ[c,0]]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[c/a,4]},
  ArcTan[Sqrt[(c*d^2-b*d*e+a*e^2)/(d*e)]*x/Sqrt[a+b*x^2+c*x^4]]/(2*d*Sqrt[(c*d^2-b*d*e+a*e^2)/(d*e)]) + 
  (e+d*q^2)*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*d*q*(e-d*q^2)*Sqrt[a+b*x^2+c*x^4])*
    EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2-b*q^2/(4*c)] - 
  q^2/(e-d*q^2)*Int[1/Sqrt[a+b*x^2+c*x^4],x] /;
 NeQ[e-d*q^2,0]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && PosQ[c/a]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[c/a,4]},
  ArcTan[Sqrt[(c*d^2+a*e^2)/(d*e)]*x/Sqrt[a+c*x^4]]/(2*d*Sqrt[(c*d^2+a*e^2)/(d*e)]) + 
  (e+d*q^2)*(1+q^2*x^2)*Sqrt[(a+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*d*q*(e-d*q^2)*Sqrt[a+c*x^4])*
    EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2] - 
  q^2/(e-d*q^2)*Int[1/Sqrt[a+c*x^4],x] /;
 NeQ[e-d*q^2,0]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && PosQ[c/a]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[-c/a,4]},
  1/(d*Sqrt[a]*q)*EllipticPi[-e/(d*q^2),ArcSin[q*x],-1]] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && GtQ[a,0]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  Sqrt[1+c*x^4/a]/Sqrt[a+c*x^4]*Int[1/((d+e*x^2)*Sqrt[1+c*x^4/a]),x] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && Not[GtQ[a,0]]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[1/((d+e*x^2)*Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NegQ[c/a]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
  1/(c*d^2-b*d*e+a*e^2)*Int[(c*d-b*e-c*e*x^2)*(a+b*x^2+c*x^4)^p,x] + 
  e^2/(c*d^2-b*d*e+a*e^2)*Int[(a+b*x^2+c*x^4)^(p+1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[p+1/2,0]


Int[(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
  1/(c*d^2+a*e^2)*Int[(c*d-c*e*x^2)*(a+c*x^4)^p,x] + 
  e^2/(c*d^2+a*e^2)*Int[(a+c*x^4)^(p+1)/(d+e*x^2),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[p+1/2,0]


Int[1/((d_+e_.*x_^2)^2*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  e^2*x*Sqrt[a+b*x^2+c*x^4]/(2*d*(c*d^2-b*d*e+a*e^2)*(d+e*x^2)) - 
  c/(2*d*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x^2)/Sqrt[a+b*x^2+c*x^4],x] + 
  (3*c*d^2-2*b*d*e+a*e^2)/(2*d*(c*d^2-b*d*e+a*e^2))*Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[1/((d_+e_.*x_^2)^2*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  e^2*x*Sqrt[a+c*x^4]/(2*d*(c*d^2+a*e^2)*(d+e*x^2)) - 
  c/(2*d*(c*d^2+a*e^2))*Int[(d+e*x^2)/Sqrt[a+c*x^4],x] + 
  (3*c*d^2+a*e^2)/(2*d*(c*d^2+a*e^2))*Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


Int[(d_+e_.*x_^2)^q_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  -e^2*x*(d+e*x^2)^(q+1)*Sqrt[a+b*x^2+c*x^4]/(2*d*(q+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/(2*d*(q+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x^2)^(q+1)/Sqrt[a+b*x^2+c*x^4]*
    Simp[a*e^2*(2*q+3)+2*d*(c*d-b*e)*(q+1)-2*e*(c*d*(q+1)-b*e*(q+2))*x^2+c*e^2*(2*q+5)*x^4,x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && ILtQ[q,-1]


Int[(d_+e_.*x_^2)^q_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  -e^2*x*(d+e*x^2)^(q+1)*Sqrt[a+c*x^4]/(2*d*(q+1)*(c*d^2+a*e^2)) + 
  1/(2*d*(q+1)*(c*d^2+a*e^2))*Int[(d+e*x^2)^(q+1)/Sqrt[a+c*x^4]*
    Simp[a*e^2*(2*q+3)+2*c*d^2*(q+1)-2*e*c*d*(q+1)*x^2+c*e^2*(2*q+5)*x^4,x],x] /;
FreeQ[{a,c,d,e},x] && ILtQ[q,-1]


Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*Sqrt[a+b*x^2+c*x^4]/(2*d*(d+e*x^2)) + 
  c/(2*d*e^2)*Int[(d-e*x^2)/Sqrt[a+b*x^2+c*x^4],x] - 
  (c*d^2-a*e^2)/(2*d*e^2)*Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[Sqrt[a_+c_.*x_^4]/(d_+e_.*x_^2)^2,x_Symbol] :=
  x*Sqrt[a+c*x^4]/(2*d*(d+e*x^2)) + 
  c/(2*d*e^2)*Int[(d-e*x^2)/Sqrt[a+c*x^4],x] - 
  (c*d^2-a*e^2)/(2*d*e^2)*Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  Module[{aa,bb,cc},
  Int[ReplaceAll[ExpandIntegrand[1/Sqrt[aa+bb*x^2+cc*x^4],(d+e*x^2)^q*(aa+bb*x^2+cc*x^4)^(p+1/2),x],{aa->a,bb->b,cc->c}],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[q,0] && IntegerQ[p+1/2]


Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  Module[{aa,cc},
  Int[ReplaceAll[ExpandIntegrand[1/Sqrt[aa+cc*x^4],(d+e*x^2)^q*(aa+cc*x^4)^(p+1/2),x],{aa->a,cc->c}],x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[q,0] && IntegerQ[p+1/2]


Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  1/(2*Sqrt[a]*Sqrt[d]*Rt[-e/d,2])*EllipticF[2*ArcSin[Rt[-e/d,2]*x],b*d/(4*a*e)] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c*d-b*e,0] && GtQ[a,0] && GtQ[d,0]


Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  Sqrt[(d+e*x^2)/d]*Sqrt[(a+b*x^2+c*x^4)/a]/(Sqrt[d+e*x^2]*Sqrt[a+b*x^2+c*x^4])*
    Int[1/(Sqrt[1+e/d*x^2]*Sqrt[1+b/a*x^2+c/a*x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c*d-b*e,0] && Not[GtQ[a,0] && GtQ[d,0]]


Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  x^3*Sqrt[e+d/x^2]*Sqrt[c+b/x^2+a/x^4]/(Sqrt[d+e*x^2]*Sqrt[a+b*x^2+c*x^4])*
    Int[1/(x^3*Sqrt[e+d/x^2]*Sqrt[c+b/x^2+a/x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  x^3*Sqrt[e+d/x^2]*Sqrt[c+a/x^4]/(Sqrt[d+e*x^2]*Sqrt[a+c*x^4])*
    Int[1/(x^3*Sqrt[e+d/x^2]*Sqrt[c+a/x^4]),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[a]/(2*Sqrt[d]*Rt[-e/d,2])*EllipticE[2*ArcSin[Rt[-e/d,2]*x],b*d/(4*a*e)] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c*d-b*e,0] && GtQ[a,0] && GtQ[d,0]


Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2+c*x^4]*Sqrt[(d+e*x^2)/d]/(Sqrt[d+e*x^2]*Sqrt[(a+b*x^2+c*x^4)/a])*
    Int[Sqrt[1+b/a*x^2+c/a*x^4]/Sqrt[1+e/d*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && EqQ[c*d-b*e,0] && Not[GtQ[a,0] && GtQ[d,0]]


Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[e+d/x^2]*Sqrt[a+b*x^2+c*x^4]/(x*Sqrt[d+e*x^2]*Sqrt[c+b/x^2+a/x^4])*
    Int[(x*Sqrt[c+b/x^2+a/x^4])/Sqrt[e+d/x^2],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[Sqrt[a_+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[e+d/x^2]*Sqrt[a+c*x^4]/(x*Sqrt[d+e*x^2]*Sqrt[c+a/x^4])*
    Int[(x*Sqrt[c+a/x^4])/Sqrt[e+d/x^2],x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  c^p*x^(4*p-1)*(d+e*x^2)^(q+1)/(e*(4*p+2*q+1)) + 
  Int[(d+e*x^2)^q*ExpandToSum[(a+b*x^2+c*x^4)^p-c^p*x^(4*p)-d*c^p*(4*p-1)*x^(4*p-2)/(e*(4*p+2*q+1)),x],x] /;
FreeQ[{a,b,c,d,e,q},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && NeQ[4*p+2*q+1,0] && Not[IGtQ[q,0]]


Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  c^p*x^(4*p-1)*(d+e*x^2)^(q+1)/(e*(4*p+2*q+1)) + 
  Int[(d+e*x^2)^q*ExpandToSum[(a+c*x^4)^p-c^p*x^(4*p)-d*c^p*(4*p-1)*x^(4*p-2)/(e*(4*p+2*q+1)),x],x] /;
FreeQ[{a,c,d,e,q},x] && IGtQ[p,0] && NeQ[4*p+2*q+1,0] && Not[IGtQ[q,0]]


Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c,d,e,p,q},x] && NeQ[b^2-4*a*c,0] && (IntegerQ[p] && IntegerQ[q] || IGtQ[p,0] || IGtQ[q,0])


Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
FreeQ[{a,c,d,e,p,q},x] && (IntegerQ[p] && IntegerQ[q] || IGtQ[p,0])


Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^4)^p,(d/(d^2-e^2*x^4)-e*x^2/(d^2-e^2*x^4))^(-q),x],x] /;
FreeQ[{a,c,d,e,p},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[q,0] && Not[IntegerQ[2*p]]


Int[(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Unintegrable[(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,d,e,p,q},x]


Int[(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  Unintegrable[(d+e*x^2)^q*(a+c*x^4)^p,x] /;
FreeQ[{a,c,d,e,p,q},x]





(* ::Subsection::Closed:: *)
(*1.2.2.4 (f x)^m (d+e x^2)^q (a+b x^2+c x^4)^p*)


(* Int[(f_.*x_)^m_.*(e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  e^q/f^(2*q)*Int[(f*x)^(m+2*q)*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,e,f,m,p},x] && IntegerQ[q] *)


(* Int[(f_.*x_)^m_.*(e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  e^q/f^(2*q)*Int[(f*x)^(m+2*q)*(a+c*x^4)^p,x] /;
FreeQ[{a,c,e,f,m,p},x] && IntegerQ[q] *)


Int[x_^m_.*(e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/(2*e^((m-1)/2))*Subst[Int[(e*x)^(q+(m-1)/2)*(a+b*x+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,b,c,e,p,q},x] && Not[IntegerQ[q]] && IntegerQ[(m-1)/2]


Int[x_^m_.*(e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  1/(2*e^((m-1)/2))*Subst[Int[(e*x)^(q+(m-1)/2)*(a+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,c,e,p,q},x] && Not[IntegerQ[q]] && IntegerQ[(m-1)/2]


Int[(f_.*x_)^m_.*(e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  e^IntPart[q]*(e*x^2)^FracPart[q]/(f^(2*IntPart[q])*(f*x)^(2*FracPart[q]))*Int[(f*x)^(m+2*q)*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,e,f,m,p,q},x] && Not[IntegerQ[q]]


Int[(f_.*x_)^m_.*(e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  e^IntPart[q]*(e*x^2)^FracPart[q]/(f^(2*IntPart[q])*(f*x)^(2*FracPart[q]))*Int[(f*x)^(m+2*q)*(a+c*x^4)^p,x] /;
FreeQ[{a,c,e,f,m,p,q},x] && Not[IntegerQ[q]]


Int[x_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/2*Subst[Int[(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,b,c,d,e,p,q},x]


Int[x_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  1/2*Subst[Int[(d+e*x)^q*(a+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,c,d,e,p,q},x]


(* Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/c^p*Int[(f*x)^m*(d+e*x^2)^q*(b/2+c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p] *)


Int[x_^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,b,c,d,e,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && IGtQ[(m+1)/2,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^FracPart[p]/(c^IntPart[p]*(b/2+c*x^2)^(2*FracPart[p]))*
    Int[(f*x)^m*(d+e*x^2)^q*(b/2+c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,b,c,d,e,p,q},x] && IntegerQ[(m-1)/2]


Int[x_^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*(d+e*x)^q*(a+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,c,d,e,p,q},x] && IntegerQ[(m+1)/2]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Int[(f*x)^m*(d+e*x^2)^(q+p)*(a/d+c/e*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  Int[(f*x)^m*(d+e*x^2)^(q+p)*(a/d+c/e*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,q,m,q},x] && EqQ[c*d^2+a*e^2,0] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^FracPart[p]/((d+e*x^2)^FracPart[p]*(a/d+(c*x^2)/e)^FracPart[p])*
    Int[(f*x)^m*(d+e*x^2)^(q+p)*(a/d+c/e*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  (a+c*x^4)^FracPart[p]/((d+e*x^2)^FracPart[p]*(a/d+(c*x^2)/e)^FracPart[p])*Int[(f*x)^m*(d+e*x^2)^(q+p)*(a/d+c/e*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  (-d)^(m/2-1)*(c*d^2-b*d*e+a*e^2)^p*x*(d+e*x^2)^(q+1)/(2*e^(2*p+m/2)*(q+1)) + 
  1/(2*e^(2*p+m/2)*(q+1))*Int[(d+e*x^2)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^2)*(2*e^(2*p+m/2)*(q+1)*x^m*(a+b*x^2+c*x^4)^p-
      (-d)^(m/2-1)*(c*d^2-b*d*e+a*e^2)^p*(d+e*(2*q+3)*x^2))],x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && ILtQ[q,-1] && IGtQ[m/2,0]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  (-d)^(m/2-1)*(c*d^2+a*e^2)^p*x*(d+e*x^2)^(q+1)/(2*e^(2*p+m/2)*(q+1)) + 
  1/(2*e^(2*p+m/2)*(q+1))*Int[(d+e*x^2)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^2)*(2*e^(2*p+m/2)*(q+1)*x^m*(a+c*x^4)^p-
      (-d)^(m/2-1)*(c*d^2+a*e^2)^p*(d+e*(2*q+3)*x^2))],x],x] /;
FreeQ[{a,c,d,e},x] && IGtQ[p,0] && ILtQ[q,-1] && IGtQ[m/2,0]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  (-d)^(m/2-1)*(c*d^2-b*d*e+a*e^2)^p*x*(d+e*x^2)^(q+1)/(2*e^(2*p+m/2)*(q+1)) + 
  (-d)^(m/2-1)/(2*e^(2*p)*(q+1))*Int[x^m*(d+e*x^2)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^2)*(2*(-d)^(-m/2+1)*e^(2*p)*(q+1)*(a+b*x^2+c*x^4)^p - 
      (e^(-m/2)*(c*d^2-b*d*e+a*e^2)^p*x^(-m))*(d+e*(2*q+3)*x^2))],x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && ILtQ[q,-1] && ILtQ[m/2,0]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  (-d)^(m/2-1)*(c*d^2+a*e^2)^p*x*(d+e*x^2)^(q+1)/(2*e^(2*p+m/2)*(q+1)) + 
  (-d)^(m/2-1)/(2*e^(2*p)*(q+1))*Int[x^m*(d+e*x^2)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^2)*(2*(-d)^(-m/2+1)*e^(2*p)*(q+1)*(a+c*x^4)^p - 
      (e^(-m/2)*(c*d^2+a*e^2)^p*x^(-m))*(d+e*(2*q+3)*x^2))],x],x] /;
FreeQ[{a,c,d,e},x] && IGtQ[p,0] && ILtQ[q,-1] && ILtQ[m/2,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  c^p*(f*x)^(m+4*p-1)*(d+e*x^2)^(q+1)/(e*f^(4*p-1)*(m+4*p+2*q+1)) + 
  1/(e*(m+4*p+2*q+1))*Int[(f*x)^m*(d+e*x^2)^q*
    ExpandToSum[e*(m+4*p+2*q+1)*((a+b*x^2+c*x^4)^p-c^p*x^(4*p))-d*c^p*(m+4*p-1)*x^(4*p-2),x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && Not[IntegerQ[q]] && NeQ[m+4*p+2*q+1,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  c^p*(f*x)^(m+4*p-1)*(d+e*x^2)^(q+1)/(e*f^(4*p-1)*(m+4*p+2*q+1)) + 
  1/(e*(m+4*p+2*q+1))*Int[(f*x)^m*(d+e*x^2)^q*
    ExpandToSum[e*(m+4*p+2*q+1)*((a+c*x^4)^p-c^p*x^(4*p))-d*c^p*(m+4*p-1)*x^(4*p-2),x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && IGtQ[p,0] && Not[IntegerQ[q]] && NeQ[m+4*p+2*q+1,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && IGtQ[p,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && IGtQ[p,0]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/f*Subst[Int[x^(k*(m+1)-1)*(d+e*x^(2*k)/f^2)^q*(a+b*x^(2*k)/f^k+c*x^(4*k)/f^4)^p,x],x,(f*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NeQ[b^2-4*a*c,0] && FractionQ[m] && IntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/f*Subst[Int[x^(k*(m+1)-1)*(d+e*x^(2*k)/f)^q*(a+c*x^(4*k)/f)^p,x],x,(f*x)^(1/k)]] /;
FreeQ[{a,c,d,e,f,p,q},x] && FractionQ[m] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+b*x^2+c*x^4)^p*(d*(m+4*p+3)+e*(m+1)*x^2)/(f*(m+1)*(m+4*p+3)) + 
  2*p/(f^2*(m+1)*(m+4*p+3))*Int[(f*x)^(m+2)*(a+b*x^2+c*x^4)^(p-1)*
    Simp[2*a*e*(m+1)-b*d*(m+4*p+3)+(b*e*(m+1)-2*c*d*(m+4*p+3))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && LtQ[m,-1] && m+4*p+3!=0 && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+c*x^4)^p*(d*(m+4*p+3)+e*(m+1)*x^2)/(f*(m+1)*(m+4*p+3)) + 
  4*p/(f^2*(m+1)*(m+4*p+3))*Int[(f*x)^(m+2)*(a+c*x^4)^(p-1)*(a*e*(m+1)-c*d*(m+4*p+3)*x^2),x] /;
FreeQ[{a,c,d,e,f},x] && GtQ[p,0] && LtQ[m,-1] && m+4*p+3!=0 && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+b*x^2+c*x^4)^p*(b*e*2*p+c*d*(m+4*p+3)+c*e*(4*p+m+1)*x^2)/
    (c*f*(4*p+m+1)*(m+4*p+3)) + 
  2*p/(c*(4*p+m+1)*(m+4*p+3))*Int[(f*x)^m*(a+b*x^2+c*x^4)^(p-1)*
    Simp[2*a*c*d*(m+4*p+3)-a*b*e*(m+1)+(2*a*c*e*(4*p+m+1)+b*c*d*(m+4*p+3)-b^2*e*(m+2*p+1))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[4*p+m+1,0] && NeQ[m+4*p+3,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+c*x^4)^p*(c*d*(m+4*p+3)+c*e*(4*p+m+1)*x^2)/(c*f*(4*p+m+1)*(m+4*p+3)) + 
  4*a*p/((4*p+m+1)*(m+4*p+3))*Int[(f*x)^m*(a+c*x^4)^(p-1)*Simp[d*(m+4*p+3)+e*(4*p+m+1)*x^2,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && GtQ[p,0] && NeQ[4*p+m+1,0] && NeQ[m+4*p+3,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  f*(f*x)^(m-1)*(a+b*x^2+c*x^4)^(p+1)*(b*d-2*a*e-(b*e-2*c*d)*x^2)/(2*(p+1)*(b^2-4*a*c)) - 
  f^2/(2*(p+1)*(b^2-4*a*c))*Int[(f*x)^(m-2)*(a+b*x^2+c*x^4)^(p+1)*
    Simp[(m-1)*(b*d-2*a*e)-(4*p+4+m+1)*(b*e-2*c*d)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  f*(f*x)^(m-1)*(a+c*x^4)^(p+1)*(a*e-c*d*x^2)/(4*a*c*(p+1)) - 
  f^2/(4*a*c*(p+1))*Int[(f*x)^(m-2)*(a+c*x^4)^(p+1)*(a*e*(m-1)-c*d*(4*p+4+m+1)*x^2),x] /;
FreeQ[{a,c,d,e,f},x] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)*(d*(b^2-2*a*c)-a*b*e+(b*d-2*a*e)*c*x^2)/(2*a*f*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[(f*x)^m*(a+b*x^2+c*x^4)^(p+1)*
    Simp[d*(b^2*(m+2*(p+1)+1)-2*a*c*(m+4*(p+1)+1))-a*b*e*(m+1)+c*(m+2*(2*p+3)+1)*(b*d-2*a*e)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+c*x^4)^(p+1)*(d+e*x^2)/(4*a*f*(p+1)) + 
  1/(4*a*(p+1))*Int[(f*x)^m*(a+c*x^4)^(p+1)*Simp[d*(m+4*(p+1)+1)+e*(m+2*(2*p+3)+1)*x^2,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && LtQ[p,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  e*f*(f*x)^(m-1)*(a+b*x^2+c*x^4)^(p+1)/(c*(m+4*p+3)) - 
  f^2/(c*(m+4*p+3))*Int[(f*x)^(m-2)*(a+b*x^2+c*x^4)^p*Simp[a*e*(m-1)+(b*e*(m+2*p+1)-c*d*(m+4*p+3))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && NeQ[b^2-4*a*c,0] && GtQ[m,1] && NeQ[m+4*p+3,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
  e*f*(f*x)^(m-1)*(a+c*x^4)^(p+1)/(c*(m+4*p+3)) - 
  f^2/(c*(m+4*p+3))*Int[(f*x)^(m-2)*(a+c*x^4)^p*(a*e*(m-1)-c*d*(m+4*p+3)*x^2),x] /;
FreeQ[{a,c,d,e,f,p},x] && GtQ[m,1] && NeQ[m+4*p+3,0] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  d*(f*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(a*f*(m+1)) + 
  1/(a*f^2*(m+1))*Int[(f*x)^(m+2)*(a+b*x^2+c*x^4)^p*Simp[a*e*(m+1)-b*d*(m+2*p+3)-c*d*(m+4*p+5)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && NeQ[b^2-4*a*c,0] && LtQ[m,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)*(a_+c_.*x_^4)^p_,x_Symbol] :=
  d*(f*x)^(m+1)*(a+c*x^4)^(p+1)/(a*f*(m+1)) + 
  1/(a*f^2*(m+1))*Int[(f*x)^(m+2)*(a+c*x^4)^p*(a*e*(m+1)-c*d*(m+4*p+5)*x^2),x] /;
FreeQ[{a,c,d,e,f,p},x] && LtQ[m,-1] && IntegerQ[2*p] && (IntegerQ[p] || IntegerQ[m])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  With[{r=Rt[c/e*(2*c*d-b*e),2]},
  e/2*Int[(f*x)^m/(c*d/e-r*x+c*x^2),x] + 
  e/2*Int[(f*x)^m/(c*d/e+r*x+c*x^2),x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-a*e^2,0] && GtQ[d/e,0] && PosQ[c/e*(2*c*d-b*e)]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
  With[{r=Rt[2*c^2*d/e,2]},
  e/2*Int[(f*x)^m/(c*d/e-r*x+c*x^2),x] + 
  e/2*Int[(f*x)^m/(c*d/e+r*x+c*x^2),x]] /;
FreeQ[{a,c,d,e,f,m},x] && EqQ[c*d^2-a*e^2,0] && GtQ[d/e,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (e/2+(2*c*d-b*e)/(2*q))*Int[(f*x)^m/(b/2-q/2+c*x^2),x] + (e/2-(2*c*d-b*e)/(2*q))*Int[(f*x)^m/(b/2+q/2+c*x^2),x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  -(e/2+c*d/(2*q))*Int[(f*x)^m/(q-c*x^2),x] + (e/2-c*d/(2*q))*Int[(f*x)^m/(q+c*x^2),x]] /;
FreeQ[{a,c,d,e,f,m},x]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_./(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q/(a+b*x^2+c*x^4),x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && IntegerQ[q] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_./(a_+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q/(a+c*x^4),x],x] /;
FreeQ[{a,c,d,e,f,m},x] && IntegerQ[q] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_./(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m,(d+e*x^2)^q/(a+b*x^2+c*x^4),x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && IntegerQ[q] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_./(a_+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m,(d+e*x^2)^q/(a+c*x^4),x],x] /;
FreeQ[{a,c,d,e,f,m},x] && IntegerQ[q] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  f^4/c^2*Int[(f*x)^(m-4)*(c*d-b*e+c*e*x^2)*(d+e*x^2)^(q-1),x] - 
  f^4/c^2*Int[(f*x)^(m-4)*(d+e*x^2)^(q-1)*Simp[a*(c*d-b*e)+(b*c*d-b^2*e+a*c*e)*x^2,x]/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,3]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  f^4/c*Int[(f*x)^(m-4)*(d+e*x^2)^q,x] - 
  a*f^4/c*Int[(f*x)^(m-4)*(d+e*x^2)^q/(a+c*x^4),x] /;
FreeQ[{a,c,d,e,f,q},x] && Not[IntegerQ[q]] && GtQ[m,3]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  e*f^2/c*Int[(f*x)^(m-2)*(d+e*x^2)^(q-1),x] - 
  f^2/c*Int[(f*x)^(m-2)*(d+e*x^2)^(q-1)*Simp[a*e-(c*d-b*e)*x^2,x]/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,1] && LeQ[m,3]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  e*f^2/c*Int[(f*x)^(m-2)*(d+e*x^2)^(q-1),x] - 
  f^2/c*Int[(f*x)^(m-2)*(d+e*x^2)^(q-1)*Simp[a*e-c*d*x^2,x]/(a+c*x^4),x] /;
FreeQ[{a,c,d,e,f},x] && Not[IntegerQ[q]] && GtQ[q,0] && GtQ[m,1] && LeQ[m,3]


Int[(f_.*x_)^m_*(d_.+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  d/a*Int[(f*x)^m*(d+e*x^2)^(q-1),x] - 
  1/(a*f^2)*Int[(f*x)^(m+2)*(d+e*x^2)^(q-1)*Simp[b*d-a*e+c*d*x^2,x]/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && GtQ[q,0] && LtQ[m,0]


Int[(f_.*x_)^m_*(d_.+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  d/a*Int[(f*x)^m*(d+e*x^2)^(q-1),x] + 
  1/(a*f^2)*Int[(f*x)^(m+2)*(d+e*x^2)^(q-1)*Simp[a*e-c*d*x^2,x]/(a+c*x^4),x] /;
FreeQ[{a,c,d,e,f},x] && Not[IntegerQ[q]] && GtQ[q,0] && LtQ[m,0]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  d^2*f^4/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-4)*(d+e*x^2)^q,x] - 
  f^4/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-4)*(d+e*x^2)^(q+1)*Simp[a*d+(b*d-a*e)*x^2,x]/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,3]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  d^2*f^4/(c*d^2+a*e^2)*Int[(f*x)^(m-4)*(d+e*x^2)^q,x] - 
  a*f^4/(c*d^2+a*e^2)*Int[(f*x)^(m-4)*(d+e*x^2)^(q+1)*(d-e*x^2)/(a+c*x^4),x] /;
FreeQ[{a,c,d,e,f},x] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,3]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  -d*e*f^2/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2)*(d+e*x^2)^q,x] + 
  f^2/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*Simp[a*e+c*d*x^2,x]/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,1] && LeQ[m,3]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  -d*e*f^2/(c*d^2+a*e^2)*Int[(f*x)^(m-2)*(d+e*x^2)^q,x] + 
  f^2/(c*d^2+a*e^2)*Int[(f*x)^(m-2)*(d+e*x^2)^(q+1)*Simp[a*e+c*d*x^2,x]/(a+c*x^4),x] /;
FreeQ[{a,c,d,e,f},x] && Not[IntegerQ[q]] && LtQ[q,-1] && GtQ[m,1] && LeQ[m,3]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  e^2/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^m*(d+e*x^2)^q,x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^m*(d+e*x^2)^(q+1)*Simp[c*d-b*e-c*e*x^2,x]/(a+b*x^2+c*x^4),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && LtQ[q,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  e^2/(c*d^2+a*e^2)*Int[(f*x)^m*(d+e*x^2)^q,x] + 
  c/(c*d^2+a*e^2)*Int[(f*x)^m*(d+e*x^2)^(q+1)*(d-e*x^2)/(a+c*x^4),x] /;
FreeQ[{a,c,d,e,f,m},x] && Not[IntegerQ[q]] && LtQ[q,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q,(f*x)^m/(a+b*x^2+c*x^4),x],x] /;
FreeQ[{a,b,c,d,e,f,q},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^2)^q,(f*x)^m/(a+c*x^4),x],x] /;
FreeQ[{a,c,d,e,f,q},x] && Not[IntegerQ[q]] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q,1/(a+b*x^2+c*x^4),x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[q]] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q,1/(a+c*x^4),x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && Not[IntegerQ[q]] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  2*c/r*Int[(f*x)^m*(d+e*x^2)^q/(b-r+2*c*x^2),x] - 2*c/r*Int[(f*x)^m*(d+e*x^2)^q/(b+r+2*c*x^2),x]] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && NeQ[b^2-4*a*c,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_/(a_+c_.*x_^4),x_Symbol] :=
  With[{r=Rt[-a*c,2]},
  -c/(2*r)*Int[(f*x)^m*(d+e*x^2)^q/(r-c*x^2),x] - c/(2*r)*Int[(f*x)^m*(d+e*x^2)^q/(r+c*x^2),x]] /;
FreeQ[{a,c,d,e,f,m,q},x]


Int[(f_.*x_)^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_./(d_.+e_.*x_^2),x_Symbol] :=
  1/d^2*Int[(f*x)^m*(a*d+(b*d-a*e)*x^2)*(a+b*x^2+c*x^4)^(p-1),x] + 
  (c*d^2-b*d*e+a*e^2)/(d^2*f^4)*Int[(f*x)^(m+4)*(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && LtQ[m,-2]


Int[(f_.*x_)^m_*(a_+c_.*x_^4)^p_./(d_.+e_.*x_^2),x_Symbol] :=
  a/d^2*Int[(f*x)^m*(d-e*x^2)*(a+c*x^4)^(p-1),x] + 
  (c*d^2+a*e^2)/(d^2*f^4)*Int[(f*x)^(m+4)*(a+c*x^4)^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,c,d,e,f},x] && GtQ[p,0] && LtQ[m,-2]


Int[(f_.*x_)^m_*(a_.+b_.*x_^2+c_.*x_^4)^p_./(d_.+e_.*x_^2),x_Symbol] :=
  1/(d*e)*Int[(f*x)^m*(a*e+c*d*x^2)*(a+b*x^2+c*x^4)^(p-1),x] - 
  (c*d^2-b*d*e+a*e^2)/(d*e*f^2)*Int[(f*x)^(m+2)*(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && LtQ[m,0]


Int[(f_.*x_)^m_*(a_+c_.*x_^4)^p_./(d_.+e_.*x_^2),x_Symbol] :=
  1/(d*e)*Int[(f*x)^m*(a*e+c*d*x^2)*(a+c*x^4)^(p-1),x] - 
  (c*d^2+a*e^2)/(d*e*f^2)*Int[(f*x)^(m+2)*(a+c*x^4)^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,c,d,e,f},x] && GtQ[p,0] && LtQ[m,0]


Int[(f_.*x_)^m_.*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_.+e_.*x_^2),x_Symbol] :=
  -f^4/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-4)*(a*d+(b*d-a*e)*x^2)*(a+b*x^2+c*x^4)^p,x] + 
  d^2*f^4/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-4)*(a+b*x^2+c*x^4)^(p+1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,2]


Int[(f_.*x_)^m_.*(a_+c_.*x_^4)^p_/(d_.+e_.*x_^2),x_Symbol] :=
  -a*f^4/(c*d^2+a*e^2)*Int[(f*x)^(m-4)*(d-e*x^2)*(a+c*x^4)^p,x] + 
  d^2*f^4/(c*d^2+a*e^2)*Int[(f*x)^(m-4)*(a+c*x^4)^(p+1)/(d+e*x^2),x] /;
FreeQ[{a,c,d,e,f},x] && LtQ[p,-1] && GtQ[m,2]


Int[(f_.*x_)^m_.*(a_.+b_.*x_^2+c_.*x_^4)^p_/(d_.+e_.*x_^2),x_Symbol] :=
  f^2/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2)*(a*e+c*d*x^2)*(a+b*x^2+c*x^4)^p,x] - 
  d*e*f^2/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2)*(a+b*x^2+c*x^4)^(p+1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[m,0]


Int[(f_.*x_)^m_.*(a_+c_.*x_^4)^p_/(d_.+e_.*x_^2),x_Symbol] :=
  f^2/(c*d^2+a*e^2)*Int[(f*x)^(m-2)*(a*e+c*d*x^2)*(a+c*x^4)^p,x] - 
  d*e*f^2/(c*d^2+a*e^2)*Int[(f*x)^(m-2)*(a+c*x^4)^(p+1)/(d+e*x^2),x] /;
FreeQ[{a,c,d,e,f},x] && LtQ[p,-1] && GtQ[m,0]


Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[c/a,4]},
  1/(e-d*q^2)*Int[1/Sqrt[a+b*x^2+c*x^4],x] - 
  ArcTan[Sqrt[(c*d^2-b*d*e+a*e^2)/(d*e)]*x/Sqrt[a+b*x^2+c*x^4]]/(2*e*Sqrt[(c*d^2-b*d*e+a*e^2)/(d*e)]) - 
  (e+d*q^2)*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*e*q*(e-d*q^2)*Sqrt[a+b*x^2+c*x^4])*
     EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2-b*q^2/(4*c)] /;
 NeQ[e-d*q^2,0]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && PosQ[c/a]


Int[x_^2/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[c/a,4]},
  1/(e-d*q^2)*Int[1/Sqrt[a+c*x^4],x] - 
  ArcTan[Sqrt[(c*d^2+a*e^2)/(d*e)]*x/Sqrt[a+c*x^4]]/(2*e*Sqrt[(c*d^2+a*e^2)/(d*e)]) - 
  (e+d*q^2)*(1+q^2*x^2)*Sqrt[(a+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*e*q*(e-d*q^2)*Sqrt[a+c*x^4])*
     EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2] /;
 NeQ[e-d*q^2,0]] /;
FreeQ[{a,c,d,e},x] && PosQ[c/a]


Int[x_^m_/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  Int[PolynomialQuotient[x^m,d+e*x^2,x]/Sqrt[a+b*x^2+c*x^4],x] + 
  Int[PolynomialRemainder[x^m,d+e*x^2,x]/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IGtQ[m/2,1] && PosQ[c/a]


Int[x_^m_/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  Int[PolynomialQuotient[x^m,d+e*x^2,x]/Sqrt[a+c*x^4],x] + 
  Int[PolynomialRemainder[x^m,d+e*x^2,x]/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
FreeQ[{a,c,d,e},x] && IGtQ[m/2,1] && PosQ[c/a]


Int[x_^m_/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  x^3*Sqrt[e+d/x^2]*Sqrt[c+b/x^2+a/x^4]/(Sqrt[d+e*x^2]*Sqrt[a+b*x^2+c*x^4])*
    Int[x^(m-3)/(Sqrt[e+d/x^2]*Sqrt[c+b/x^2+a/x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && IntegerQ[m/2]


Int[x_^m_/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  x^3*Sqrt[e+d/x^2]*Sqrt[c+a/x^4]/(Sqrt[d+e*x^2]*Sqrt[a+c*x^4])*
    Int[x^(m-3)/(Sqrt[e+d/x^2]*Sqrt[c+a/x^4]),x] /;
FreeQ[{a,c,d,e},x] && IntegerQ[m/2]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{f=Coeff[PolynomialRemainder[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,0],
        g=Coeff[PolynomialRemainder[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,2]},
  x*(a+b*x^2+c*x^4)^(p+1)*(a*b*g-f*(b^2-2*a*c)-c*(b*f-2*a*g)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[(a+b*x^2+c*x^4)^(p+1)*
    Simp[ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*PolynomialQuotient[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x]+
      b^2*f*(2*p+3)-2*a*c*f*(4*p+5)-a*b*g+c*(4*p+7)*(b*f-2*a*g)*x^2,x],x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IGtQ[q,1] && IGtQ[m/2,0]


Int[x_^m_*(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{f=Coeff[PolynomialRemainder[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,0],
        g=Coeff[PolynomialRemainder[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x],x,2]},
  x*(a+b*x^2+c*x^4)^(p+1)*(a*b*g-f*(b^2-2*a*c)-c*(b*f-2*a*g)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[x^m*(a+b*x^2+c*x^4)^(p+1)*
    Simp[ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*x^(-m)*PolynomialQuotient[x^m*(d+e*x^2)^q,a+b*x^2+c*x^4,x]+
      (b^2*f*(2*p+3)-2*a*c*f*(4*p+5)-a*b*g)*x^(-m)+c*(4*p+7)*(b*f-2*a*g)*x^(2-m),x],x],x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IGtQ[q,1] && ILtQ[m/2,0]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && NeQ[b^2-4*a*c,0] && (IGtQ[p,0] || IGtQ[q,0] || IntegersQ[m,q])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^2)^q*(a+c*x^4)^p,x],x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && (IGtQ[p,0] || IGtQ[q,0] || IntegersQ[m,q])


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  f^m*Int[ExpandIntegrand[x^m*(a+c*x^4)^p,(d/(d^2-e^2*x^4)-e*x^2/(d^2-e^2*x^4))^(-q),x],x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && ILtQ[q,0] && (IntegerQ[m] || GtQ[f,0])


Int[(f_.*x_)^m_*(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  (f*x)^m/x^m*Int[x^m*(d+e*x^2)^q*(a+c*x^4)^p,x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && ILtQ[q,0] && Not[IntegerQ[m] || GtQ[f,0]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x^2)^q*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_+c_.*x_^4)^p_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x^2)^q*(a+c*x^4)^p,x] /;
FreeQ[{a,c,d,e,f,m,p,q},x]





(* ::Subsection::Closed:: *)
(*1.2.2.6 (d x)^m Pq(x) (a+b x^2+c x^4)^p*)


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],k},
  Int[(d*x)^m*Sum[Coeff[Pq,x,2*k]*x^(2*k),{k,0,q/2+1}]*(a+b*x^2+c*x^4)^p,x] + 
  1/d*Int[(d*x)^(m+1)*Sum[Coeff[Pq,x,2*k+1]*x^(2*k),{k,0,(q-1)/2+1}]*(a+b*x^2+c*x^4)^p,x]] /;
FreeQ[{a,b,c,d,m,p},x] && PolyQ[Pq,x] && Not[PolyQ[Pq,x^2]]


Int[x_^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  1/2*Subst[Int[x^((m-1)/2)*SubstFor[x^2,Pq,x]*(a+b*x+c*x^2)^p,x],x,x^2] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x^2] && IntegerQ[(m-1)/2]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*Pq*(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c,d,m},x] && PolyQ[Pq,x^2] && IGtQ[p,-2]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  1/d^2*Int[(d*x)^(m+2)*ExpandToSum[Pq/x^2,x]*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,d,m,p},x] && PolyQ[Pq,x^2] && EqQ[Coeff[Pq,x,0],0]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  With[{e=Coeff[Pq,x,0],f=Coeff[Pq,x,2],g=Coeff[Pq,x,4]},
  e*(d*x)^(m+1)*(a+b*x^2+c*x^4)^(p+1)/(a*d*(m+1)) /;
 EqQ[a*f*(m+1)-b*e*(m+2*p+3),0] && EqQ[a*g*(m+1)-c*e*(m+4*p+5),0] && NeQ[m,-1]] /;
FreeQ[{a,b,c,d,m,p},x] && PolyQ[Pq,x^2] && EqQ[Expon[Pq,x],4]


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^2)^(2*FracPart[p]))*Int[(d*x)^m*Pq*(b+2*c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,d,m,p},x] && PolyQ[Pq,x^2] && GtQ[Expon[Pq,x^2],1] && EqQ[b^2-4*a*c,0]


Int[x_^m_*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{d=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,0],
        e=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,2]},
  x*(a+b*x^2+c*x^4)^(p+1)*(a*b*e-d*(b^2-2*a*c)-c*(b*d-2*a*e)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[(a+b*x^2+c*x^4)^(p+1)*
    ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*PolynomialQuotient[x^m*Pq,a+b*x^2+c*x^4,x]+
      b^2*d*(2*p+3)-2*a*c*d*(4*p+5)-a*b*e+c*(4*p+7)*(b*d-2*a*e)*x^2,x],x]] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x^2] && GtQ[Expon[Pq,x^2],1] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IGtQ[m/2,0]


Int[x_^m_*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{d=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,0],
        e=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,2]},
  x*(a+b*x^2+c*x^4)^(p+1)*(a*b*e-d*(b^2-2*a*c)-c*(b*d-2*a*e)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[x^m*(a+b*x^2+c*x^4)^(p+1)*
    ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*x^(-m)*PolynomialQuotient[x^m*Pq,a+b*x^2+c*x^4,x]+
      (b^2*d*(2*p+3)-2*a*c*d*(4*p+5)-a*b*e)*x^(-m)+c*(4*p+7)*(b*d-2*a*e)*x^(2-m),x],x]] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x^2] && GtQ[Expon[Pq,x^2],1] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && ILtQ[m/2,0]


(* Int[x_^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{d=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,1],
        e=Coeff[PolynomialRemainder[x^m*Pq,a+b*x^2+c*x^4,x],x,3]},
  x^2*(a+b*x^2+c*x^4)^(p+1)*(a*b*e-d*(b^2-2*a*c)-c*(b*d-2*a*e)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) + 
  1/(a*(p+1)*(b^2-4*a*c))*Int[x^m*(a+b*x^2+c*x^4)^(p+1)*
    ExpandToSum[a*(p+1)*(b^2-4*a*c)*x^(-m)*PolynomialQuotient[x^m*Pq,a+b*x^2+c*x^4,x]+
      (b^2*d*(p+2)-2*a*c*d*(2*p+3)-a*b*e)*x^(1-m)+2*c*(p+2)*(b*d-2*a*e)*x^(3-m),x],x]] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x^2] && GtQ[Expon[Pq,x^2],1] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && IntegerQ[(m-1)/2] *)


Int[(d_.*x_)^m_.*Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Unintegrable[(d*x)^m*Pq*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,d,m,p},x] && PolyQ[Pq,x]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_.*P4_/(d_+e_.*x_^2),x_Symbol] :=
  With[{A=Coeff[P4,x,0],B=Coeff[P4,x,2],C=Coeff[P4,x,4]},
  -1/e^2*Int[(a+b*x^2+c*x^4)^p*(C*d-B*e-C*e*x^2),x] + 
  (C*d^2-B*d*e+A*e^2)/e^2*Int[(a+b*x^2+c*x^4)^p/(d+e*x^2),x]] /;
FreeQ[{a,b,c,d,e,p},x] && PolyQ[P4,x^2] && EqQ[Expon[P4,x],4] && NeQ[b^2-4*a*c,0]


Int[(a_+c_.*x_^4)^p_.*P4_/(d_+e_.*x_^2),x_Symbol] :=
  With[{A=Coeff[P4,x,0],B=Coeff[P4,x,2],C=Coeff[P4,x,4]},
  -1/e^2*Int[(a+c*x^4)^p*(C*d-B*e-C*e*x^2),x] + 
  (C*d^2-B*d*e+A*e^2)/e^2*Int[(a+c*x^4)^p/(d+e*x^2),x]] /;
FreeQ[{a,c,d,e,p},x] && PolyQ[P4,x^2] && EqQ[Expon[P4,x],4]


Int[(d_+e_.*x_^2)^q_*P4_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{A=Coeff[P4,x,0],B=Coeff[P4,x,2],C=Coeff[P4,x,4]},
  C*x*(d+e*x^2)^q*Sqrt[a+b*x^2+c*x^4]/(c*(2*q+3)) + 
  1/(c*(2*q+3))*Int[(d+e*x^2)^(q-1)/Sqrt[a+b*x^2+c*x^4]*
    Simp[A*c*d*(2*q+3)-a*C*d+(c*(B*d+A*e)*(2*q+3)-C*(2*b*d+a*e+2*a*e*q))*x^2+(B*c*e*(2*q+3)-2*C*(b*e-c*d*q+b*e*q))*x^4,x],x]] /;
FreeQ[{a,b,c,d,e},x] && PolyQ[P4,x^2] && LeQ[Expon[P4,x],4] && NeQ[b^2-4*a*c,0] && IGtQ[q,0]


Int[(d_+e_.*x_^2)^q_*P4_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{A=Coeff[P4,x,0],B=Coeff[P4,x,2],C=Coeff[P4,x,4]},
  C*x*(d+e*x^2)^q*Sqrt[a+c*x^4]/(c*(2*q+3)) + 
  1/(c*(2*q+3))*Int[(d+e*x^2)^(q-1)/Sqrt[a+c*x^4]*
    Simp[A*c*d*(2*q+3)-a*C*d+(c*(B*d+A*e)*(2*q+3)-a*C*e*(2*q+1))*x^2+(B*c*e*(2*q+3)+2*c*C*d*q)*x^4,x],x]] /;
FreeQ[{a,c,d,e},x] && PolyQ[P4,x^2] && LeQ[Expon[P4,x],4] && IGtQ[q,0]


Int[(d_+e_.*x_^2)^q_*P4_/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{A=Coeff[P4,x,0],B=Coeff[P4,x,2],C=Coeff[P4,x,4]},
  -(C*d^2-B*d*e+A*e^2)*x*(d+e*x^2)^(q+1)*Sqrt[a+b*x^2+c*x^4]/(2*d*(q+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/(2*d*(q+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x^2)^(q+1)/Sqrt[a+b*x^2+c*x^4]*
    Simp[a*d*(C*d-B*e)+A*(a*e^2*(2*q+3)+2*d*(c*d-b*e)*(q+1))-
      2*((B*d-A*e)*(b*e*(q+2)-c*d*(q+1))-C*d*(b*d+a*e*(q+1)))*x^2+
      c*(C*d^2-B*d*e+A*e^2)*(2*q+5)*x^4,x],x]] /;
FreeQ[{a,b,c,d,e},x] && PolyQ[P4,x^2] && LeQ[Expon[P4,x],4] && NeQ[b^2-4*a*c,0] && ILtQ[q,-1]


Int[(d_+e_.*x_^2)^q_*P4_/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{A=Coeff[P4,x,0],B=Coeff[P4,x,2],C=Coeff[P4,x,4]},
  -(C*d^2-B*d*e+A*e^2)*x*(d+e*x^2)^(q+1)*Sqrt[a+c*x^4]/(2*d*(q+1)*(c*d^2+a*e^2)) + 
  1/(2*d*(q+1)*(c*d^2+a*e^2))*Int[(d+e*x^2)^(q+1)/Sqrt[a+c*x^4]*
    Simp[a*d*(C*d-B*e)+A*(a*e^2*(2*q+3)+2*c*d^2*(q+1))+2*d*(B*c*d-A*c*e+a*C*e)*(q+1)*x^2+c*(C*d^2-B*d*e+A*e^2)*(2*q+5)*x^4,x],x]] /;
FreeQ[{a,c,d,e},x] && PolyQ[P4,x^2] && LeQ[Expon[P4,x],4] && ILtQ[q,-1]





(* ::Subsection::Closed:: *)
(*1.2.2.5 Pq(x) (a+b x^2+c x^4)^p*)


Int[Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x^2+c*x^4)^p,x],x] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && IGtQ[p,0]


Int[Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  Int[x*PolynomialQuotient[Pq,x,x]*(a+b*x^2+c*x^4)^p,x] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,x,x],0] && Not[MatchQ[Pq,x^m_.*u_. /; IntegerQ[m]]]


Int[Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],k},
  Int[Sum[Coeff[Pq,x,2*k]*x^(2*k),{k,0,q/2}]*(a+b*x^2+c*x^4)^p,x] + 
  Int[x*Sum[Coeff[Pq,x,2*k+1]*x^(2*k),{k,0,(q-1)/2}]*(a+b*x^2+c*x^4)^p,x]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && Not[PolyQ[Pq,x^2]]


Int[Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  With[{d=Coeff[Pq,x,0],e=Coeff[Pq,x,2],f=Coeff[Pq,x,4]},
  d*x*(a+b*x^2+c*x^4)^(p+1)/a /;
 EqQ[a*e-b*d*(2*p+3),0] && EqQ[a*f-c*d*(4*p+5),0]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x^2] && EqQ[Expon[Pq,x],4]


Int[Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_.,x_Symbol] :=
  With[{d=Coeff[Pq,x,0],e=Coeff[Pq,x,2],f=Coeff[Pq,x,4],g=Coeff[Pq,x,6]},
  x*(3*a*d+(a*e-b*d*(2*p+3))*x^2)*(a+b*x^2+c*x^4)^(p+1)/(3*a^2) /;
 EqQ[3*a^2*g-c*(4*p+7)*(a*e-b*d*(2*p+3)),0] && EqQ[3*a^2*f-3*a*c*d*(4*p+5)-b*(2*p+5)*(a*e-b*d*(2*p+3)),0]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x^2] && EqQ[Expon[Pq,x],6]


Int[Pq_/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  Int[ExpandIntegrand[Pq/(a+b*x^2+c*x^4),x],x] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x^2] && Expon[Pq,x^2]>1


Int[Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  (a+b*x^2+c*x^4)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^2)^(2*FracPart[p]))*Int[Pq*(b+2*c*x^2)^(2*p),x] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x^2] && Expon[Pq,x^2]>1 && EqQ[b^2-4*a*c,0]


Int[Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{d=Coeff[PolynomialRemainder[Pq,a+b*x^2+c*x^4,x],x,0],
        e=Coeff[PolynomialRemainder[Pq,a+b*x^2+c*x^4,x],x,2]},
  x*(a+b*x^2+c*x^4)^(p+1)*(a*b*e-d*(b^2-2*a*c)-c*(b*d-2*a*e)*x^2)/(2*a*(p+1)*(b^2-4*a*c)) + 
  1/(2*a*(p+1)*(b^2-4*a*c))*Int[(a+b*x^2+c*x^4)^(p+1)*
    ExpandToSum[2*a*(p+1)*(b^2-4*a*c)*PolynomialQuotient[Pq,a+b*x^2+c*x^4,x]+
      b^2*d*(2*p+3)-2*a*c*d*(4*p+5)-a*b*e+c*(4*p+7)*(b*d-2*a*e)*x^2,x],x]] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x^2] && Expon[Pq,x^2]>1 && NeQ[b^2-4*a*c,0] && LtQ[p,-1]


Int[Pq_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x^2],e=Coeff[Pq,x^2,Expon[Pq,x^2]]},
  e*x^(2*q-3)*(a+b*x^2+c*x^4)^(p+1)/(c*(2*q+4*p+1)) + 
  1/(c*(2*q+4*p+1))*Int[(a+b*x^2+c*x^4)^p*
    ExpandToSum[c*(2*q+4*p+1)*Pq-a*e*(2*q-3)*x^(2*q-4)-b*e*(2*q+2*p-1)*x^(2*q-2)-c*e*(2*q+4*p+1)*x^(2*q),x],x]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x^2] && Expon[Pq,x^2]>1 && NeQ[b^2-4*a*c,0] && Not[LtQ[p,-1]]
