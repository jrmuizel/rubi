(* ::Package:: *)

(* ::Section:: *)
(*3 Logarithms integration rules*)


(* ::Subsection::Closed:: *)
(*3.1 u (a+b log(c x^n))^p*)


Int[(A_.+B_.*Log[c_.*(d_.+e_.*x_)^n_.])/Sqrt[a_+b_.*Log[c_.*(d_.+e_.*x_)^n_.]],x_Symbol] :=
  B*(d+e*x)*Sqrt[a+b*Log[c*(d+e*x)^n]]/(b*e) + 
  (2*A*b-B*(2*a+b*n))/(2*b)*Int[1/Sqrt[a+b*Log[c*(d+e*x)^n]],x] /;
FreeQ[{a,b,c,d,e,A,B,n},x]


Int[Log[c_.*x_^n_.],x_Symbol] :=
  x*Log[c*x^n] - n*x /;
FreeQ[{c,n},x]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  x*(a+b*Log[c*x^n])^p - b*n*p*Int[(a+b*Log[c*x^n])^(p-1),x] /;
FreeQ[{a,b,c,n},x] && GtQ[p,0] && IntegerQ[2*p]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
  x*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) - 1/(b*n*(p+1))*Int[(a+b*Log[c*x^n])^(p+1),x] /;
FreeQ[{a,b,c,n},x] && LtQ[p,-1] && IntegerQ[2*p]


Int[1/Log[c_.*x_],x_Symbol] :=
  LogIntegral[c*x]/c /;
FreeQ[c,x]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
  1/(n*c^(1/n))*Subst[Int[E^(x/n)*(a+b*x)^p,x],x,Log[c*x^n]] /;
FreeQ[{a,b,c,p},x] && IntegerQ[1/n]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
  x/(n*(c*x^n)^(1/n))*Subst[Int[E^(x/n)*(a+b*x)^p,x],x,Log[c*x^n]] /;
FreeQ[{a,b,c,n,p},x]


Int[(a_.+b_.*Log[c_.*x_^n_.])/x_,x_Symbol] :=
  (a+b*Log[c*x^n])^2/(2*b*n) /;
FreeQ[{a,b,c,n},x]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
  1/(b*n)*Subst[Int[x^p,x],x,a+b*Log[c*x^n]] /;
FreeQ[{a,b,c,n,p},x]


Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  b*(d*x)^(m+1)*Log[c*x^n]/(d*(m+1)) /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1] && EqQ[a*(m+1)-b*n,0]


Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  (d*x)^(m+1)*(a+b*Log[c*x^n])/(d*(m+1)) - b*n*(d*x)^(m+1)/(d*(m+1)^2) /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1]


Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  (d*x)^(m+1)*(a+b*Log[c*x^n])^p/(d*(m+1)) - b*n*p/(m+1)*Int[(d*x)^m*(a+b*Log[c*x^n])^(p-1),x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1] && GtQ[p,0]


Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*Log[c*x^n])^(p+1)/(b*d*n*(p+1)) - (m+1)/(b*n*(p+1))*Int[(d*x)^m*(a+b*Log[c*x^n])^(p+1),x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[m,-1] && LtQ[p,-1]


Int[x_^m_./Log[c_.*x_^n_],x_Symbol] :=
  1/n*Subst[Int[1/Log[c*x],x],x,x^n] /;
FreeQ[{c,m,n},x] && EqQ[m,n-1]


Int[(d_*x_)^m_./Log[c_.*x_^n_],x_Symbol] :=
  (d*x)^m/x^m*Int[x^m/Log[c*x^n],x] /;
FreeQ[{c,d,m,n},x] && EqQ[m,n-1]


Int[x_^m_.*(a_.+b_.*Log[c_.*x_])^p_,x_Symbol] :=
  1/c^(m+1)*Subst[Int[E^((m+1)*x)*(a+b*x)^p,x],x,Log[c*x]] /;
FreeQ[{a,b,c,p},x] && IntegerQ[m]


Int[(d_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
  (d*x)^(m+1)/(d*n*(c*x^n)^((m+1)/n))*Subst[Int[E^((m+1)/n*x)*(a+b*x)^p,x],x,Log[c*x^n]] /;
FreeQ[{a,b,c,d,m,n,p},x]


Int[(d_.*x_^q_)^m_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  (d*x^q)^m/x^(m*q)*Int[x^(m*q)*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,m,n,p,q},x]


Int[(d1_.*x_^q1_)^m1_*(d2_.*x_^q2_)^m2_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  (d1*x^q1)^m1*(d2*x^q2)^m2/x^(m1*q1+m2*q2)*Int[x^(m1*q1+m2*q2)*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d1,d2,m1,m2,n,p,q1,q2},x]


Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^r)^q,x]},
  u*(a+b*Log[c*x^n]) - b*n*Int[SimplifyIntegrand[u/x,x],x]] /;
FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[q,0]


Int[(d_+e_.*x_^r_.)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  x*(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])/d - b*n/d*Int[(d+e*x^r)^(q+1),x] /;
FreeQ[{a,b,c,d,e,n,q,r},x] && EqQ[r*(q+1)+1,0]


Int[Log[c_.*x_]/(d_+e_.*x_),x_Symbol] :=
  -1/e*PolyLog[2,1-c*x] /;
FreeQ[{c,d,e},x] && EqQ[e+c*d,0]


Int[(a_.+b_.*Log[c_.*x_])/(d_+e_.*x_),x_Symbol] :=
  (a+b*Log[-c*d/e])*Log[d+e*x]/e + b*Int[Log[-e*x/d]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e},x] && GtQ[-c*d/e,0]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(d_+e_.*x_),x_Symbol] :=
  Log[1+e*x/d]*(a+b*Log[c*x^n])^p/e - b*n*p/e*Int[Log[1+e*x/d]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(d_+e_.*x_)^2,x_Symbol] :=
  x*(a+b*Log[c*x^n])^p/(d*(d+e*x)) - b*n*p/d*Int[(a+b*Log[c*x^n])^(p-1)/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && GtQ[p,0]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  (d+e*x)^(q+1)*(a+b*Log[c*x^n])^p/(e*(q+1)) - b*n*p/(e*(q+1))*Int[((d+e*x)^(q+1)*(a+b*Log[c*x^n])^(p-1))/x,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && GtQ[p,0] && NeQ[q,-1] && (EqQ[p,1] || IntegersQ[2*p,2*q] && Not[IGtQ[q,0]] || EqQ[p,2] && NeQ[q,1])


Int[(d_+e_.*x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
  x*(d+e*x)^q*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) + 
  d*q/(b*n*(p+1))*Int[(d+e*x)^(q-1)*(a+b*Log[c*x^n])^(p+1),x] - 
  (q+1)/(b*n*(p+1))*Int[(d+e*x)^q*(a+b*Log[c*x^n])^(p+1),x] /;
FreeQ[{a,b,c,d,e,n},x] && LtQ[p,-1] && GtQ[q,0]


Int[(d_+e_.*x_^2)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  x*(d+e*x^2)^q*(a+b*Log[c*x^n])/(2*q+1) - 
  b*n/(2*q+1)*Int[(d+e*x^2)^q,x] + 
  2*d*q/(2*q+1)*Int[(d+e*x^2)^(q-1)*(a+b*Log[c*x^n]),x] /;
FreeQ[{a,b,c,d,e,n},x] && GtQ[q,0]


Int[(a_.+b_.*Log[c_.*x_^n_.])/(d_+e_.*x_^2)^(3/2),x_Symbol] :=
  x*(a+b*Log[c*x^n])/(d*Sqrt[d+e*x^2]) - b*n/d*Int[1/Sqrt[d+e*x^2],x] /;
FreeQ[{a,b,c,d,e,n},x]


Int[(d_+e_.*x_^2)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  -x*(d+e*x^2)^(q+1)*(a+b*Log[c*x^n])/(2*d*(q+1)) + 
  b*n/(2*d*(q+1))*Int[(d+e*x^2)^(q+1),x] + 
  (2*q+3)/(2*d*(q+1))*Int[(d+e*x^2)^(q+1)*(a+b*Log[c*x^n]),x] /;
FreeQ[{a,b,c,d,e,n},x] && LtQ[q,-1]


Int[(a_.+b_.*Log[c_.*x_^n_.])/(d_+e_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(d+e*x^2),x]},  
  u*(a+b*Log[c*x^n]) - b*n*Int[u/x,x]] /;
FreeQ[{a,b,c,d,e,n},x]


Int[(a_.+b_.*Log[c_.*x_^n_.])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  ArcSinh[Rt[e,2]*x/Sqrt[d]]*(a+b*Log[c*x^n])/Rt[e,2] - b*n/Rt[e,2]*Int[ArcSinh[Rt[e,2]*x/Sqrt[d]]/x,x] /;
FreeQ[{a,b,c,d,e,n},x] && GtQ[d,0] && PosQ[e]


Int[(a_.+b_.*Log[c_.*x_^n_.])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  ArcSin[Rt[-e,2]*x/Sqrt[d]]*(a+b*Log[c*x^n])/Rt[-e,2] - b*n/Rt[-e,2]*Int[ArcSin[Rt[-e,2]*x/Sqrt[d]]/x,x] /;
FreeQ[{a,b,c,d,e,n},x] && GtQ[d,0] && NegQ[e]


Int[(a_.+b_.*Log[c_.*x_^n_.])/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[1+e/d*x^2]/Sqrt[d+e*x^2]*Int[(a+b*Log[c*x^n])/Sqrt[1+e/d*x^2],x] /;
FreeQ[{a,b,c,d,e,n},x] && Not[GtQ[d,0]]


Int[(a_.+b_.*Log[c_.*x_^n_.])/(Sqrt[d1_+e1_.*x_]*Sqrt[d2_+e2_.*x_]),x_Symbol] :=
  Sqrt[1+e1*e2/(d1*d2)*x^2]/(Sqrt[d1+e1*x]*Sqrt[d2+e2*x])*Int[(a+b*Log[c*x^n])/Sqrt[1+e1*e2/(d1*d2)*x^2],x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[d2*e1+d1*e2,0]


Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[(d+e*x^r)^q,x]},  
  Dist[(a+b*Log[c*x^n]),u,x] - b*n*Int[SimplifyIntegrand[u/x,x],x] /;
 EqQ[r,1] && IntegerQ[q-1/2] || EqQ[r,2] && EqQ[q,-1] || InverseFunctionFreeQ[u,x]] /;
FreeQ[{a,b,c,d,e,n,q,r},x] && IntegerQ[2*q] && IntegerQ[r]


Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*x^n])^p,(d+e*x^r)^q,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n,p,q,r},x] && IntegerQ[q] && (GtQ[q,0] || IGtQ[p,0] && IntegerQ[r])


Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(d+e*x^r)^q*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q,r},x]


Int[u_^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^q*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,n,p,q},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*(d_+e_./x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[(e+d*x)^q*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[m,q] && IntegerQ[q]


Int[x_^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[x^m*(d+e*x^r)^q,x]},
  u*(a+b*Log[c*x^n]) - b*n*Int[SimplifyIntegrand[u/x,x],x]] /;
FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[q,0] && IntegerQ[m] && Not[EqQ[q,1] && EqQ[m,-1]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  (f*x)^(m+1)*(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])/(d*f*(m+1)) - 
  b*n/(d*(m+1))*Int[(f*x)^m*(d+e*x^r)^(q+1),x] /;
FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && EqQ[m+r*(q+1)+1,0] && NeQ[m,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*x_^n_])^p_.,x_Symbol] :=
  f^m/n*Subst[Int[(d+e*x)^q*(a+b*Log[c*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && EqQ[m,r-1] && IGtQ[p,0] && (IntegerQ[m] || GtQ[f,0]) && EqQ[r,n]


Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_./(d_+e_.*x_^r_),x_Symbol] :=
  f^m*Log[1+e*x^r/d]*(a+b*Log[c*x^n])^p/(e*r) - 
  b*f^m*n*p/(e*r)*Int[Log[1+e*x^r/d]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
FreeQ[{a,b,c,d,e,f,m,n,r},x] && EqQ[m,r-1] && IGtQ[p,0] && (IntegerQ[m] || GtQ[f,0]) && NeQ[r,n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  f^m*(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])^p/(e*r*(q+1)) - 
  b*f^m*n*p/(e*r*(q+1))*Int[(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])^(p-1)/x,x] /;
FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && EqQ[m,r-1] && IGtQ[p,0] && (IntegerQ[m] || GtQ[f,0]) && NeQ[r,n] && NeQ[q,-1]


Int[(f_*x_)^m_.*(d_+e_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  (f*x)^m/x^m*Int[x^m*(d+e*x^r)^q*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && EqQ[m,r-1] && IGtQ[p,0] && Not[(IntegerQ[m] || GtQ[f,0])]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  -(f*x)^(m+1)*(d+e*x^2)^(q+1)*(a+b*Log[c*x^n])/(2*d*f*(q+1)) + 
  1/(2*d*(q+1))*Int[(f*x)^m*(d+e*x^2)^(q+1)*(a*(m+2*q+3)+b*n+b*(m+2*q+3)*Log[c*x^n]),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ILtQ[q,-1] && ILtQ[m,0]


Int[x_^m_.*(d_+e_.*x_^2)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  d^IntPart[q]*(d+e*x^2)^FracPart[q]/(1+e/d*x^2)^FracPart[q]*Int[x^m*(1+e/d*x^2)^q*(a+b*Log[c*x^n]),x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[m/2] && IntegerQ[q-1/2] && Not[LtQ[m+2*q,-2] || GtQ[d,0]]


Int[x_^m_.*(d1_+e1_.*x_)^q_*(d2_+e2_.*x_)^q_*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  (d1+e1*x)^q*(d2+e2*x)^q/(1+e1*e2/(d1*d2)*x^2)^q*Int[x^m*(1+e1*e2/(d1*d2)*x^2)^q*(a+b*Log[c*x^n]),x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n},x] && EqQ[d2*e1+d1*e2,0] && IntegerQ[m] && IntegerQ[q-1/2]


Int[(a_.+b_.*Log[c_.*x_^n_])/(x_*(d_+e_.*x_^r_.)),x_Symbol] :=
  1/n*Subst[Int[(a+b*Log[c*x])/(x*(d+e*x^(r/n))),x],x,x^n] /;
FreeQ[{a,b,c,d,e,n,r},x] && IntegerQ[r/n]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(x_*(d_+e_.*x_)),x_Symbol] :=
  1/d*Int[(a+b*Log[c*x^n])^p/x,x] - e/d*Int[(a+b*Log[c*x^n])^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0]


(* Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(x_*(d_+e_.*x_^r_.)),x_Symbol] :=
  (r*Log[x]-Log[1+(e*x^r)/d])*(a+b*Log[c*x^n])^p/(d*r) - 
  b*n*p/d*Int[Log[x]*(a+b*Log[c*x^n])^(p-1)/x,x] + 
  b*n*p/(d*r)*Int[Log[1+(e*x^r)/d]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[p,0] *)


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_./(x_*(d_+e_.*x_^r_.)),x_Symbol] :=
  -Log[1+d/(e*x^r)]*(a+b*Log[c*x^n])^p/(d*r) + 
  b*n*p/(d*r)*Int[Log[1+d/(e*x^r)]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[p,0]


Int[(d_+e_.*x_)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
  d*Int[(d+e*x)^(q-1)*(a+b*Log[c*x^n])^p/x,x] + 
  e*Int[(d+e*x)^(q-1)*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0] && GtQ[q,0] && IntegerQ[2*q]


Int[(d_+e_.*x_)^q_*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
  1/d*Int[(d+e*x)^(q+1)*(a+b*Log[c*x^n])^p/x,x] - 
  e/d*Int[(d+e*x)^q*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,n},x] && IGtQ[p,0] && LtQ[q,-1] && IntegerQ[2*q]


Int[(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])/x_,x_Symbol] :=
  With[{u=IntHide[(d+e*x^r)^q/x,x]},  
  u*(a+b*Log[c*x^n]) - b*n*Int[Dist[1/x,u,x],x]] /;
FreeQ[{a,b,c,d,e,n,r},x] && IntegerQ[q-1/2]


Int[(d_+e_.*x_^r_.)^q_*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
  1/d*Int[(d+e*x^r)^(q+1)*(a+b*Log[c*x^n])^p/x,x] - 
  e/d*Int[x^(r-1)*(d+e*x^r)^q*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,n,r},x] && IGtQ[p,0] && ILtQ[q,-1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[(f*x)^m*(d+e*x^r)^q,x]},  
  Dist[(a+b*Log[c*x^n]),u,x] - b*n*Int[SimplifyIntegrand[u/x,x],x] /;
 (EqQ[r,1] || EqQ[r,2]) && IntegerQ[m] && IntegerQ[q-1/2] || InverseFunctionFreeQ[u,x]] /;
FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && IntegerQ[2*q] && (IntegerQ[m] && IntegerQ[r] || IGtQ[q,0])


Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*x^n]),(f*x)^m*(d+e*x^r)^q,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,m,n,q,r},x] && IntegerQ[q] && (GtQ[q,0] || IntegerQ[m] && IntegerQ[r])


Int[x_^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_])^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x^(r/n))^q*(a+b*Log[c*x])^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,m,n,p,q,r},x] && IntegerQ[q] && IntegerQ[r/n] && IntegerQ[Simplify[(m+1)/n]] && (GtQ[(m+1)/n,0] || IGtQ[p,0])


Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*x^n])^p,(f*x)^m*(d+e*x^r)^q,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && IntegerQ[q] && (GtQ[q,0] || IGtQ[p,0] && IntegerQ[m] && IntegerQ[r])


Int[(f_.*x_)^m_.*(d_+e_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(d+e*x^r)^q*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x]


Int[(f_.*x_)^m_.*u_^q_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[(f*x)^m*ExpandToSum[u,x]^q*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,f,m,n,p,q},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[Polyx_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Polyx*(a+b*Log[c*x^n])^p,x],x] /;
FreeQ[{a,b,c,n,p},x] && PolynomialQ[Polyx,x]


Int[RFx_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*x^n])^p,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,n},x] && RationalFunctionQ[RFx,x] && IGtQ[p,0]


Int[RFx_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[RFx*(a+b*Log[c*x^n])^p,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,n},x] && RationalFunctionQ[RFx,x] && IGtQ[p,0]


Int[AFx_*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[AFx*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,n,p},x] && AlgebraicFunctionQ[AFx,x,True]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_+e_.*Log[c_.*x_^n_.])^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*Log[c*x^n])^p*(d+e*Log[c*x^n])^q,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && IntegerQ[p] && IntegerQ[q]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.]),x_Symbol] :=
  With[{u=IntHide[(a+b*Log[c*x^n])^p,x]},
  Dist[d+e*Log[f*x^r],u,x] - e*r*Int[SimplifyIntegrand[u/x,x],x]] /;
FreeQ[{a,b,c,d,e,f,n,p,r},x]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.])^q_.,x_Symbol] :=
  x*(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^q - 
  e*q*r*Int[(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^(q-1),x] - 
  b*n*p*Int[(a+b*Log[c*x^n])^(p-1)*(d+e*Log[f*x^r])^q,x] /;
FreeQ[{a,b,c,d,e,f,n,r},x] && IGtQ[p,0] && IGtQ[q,0]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.])^q_.,x_Symbol] :=
  Unintegrable[(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^q,x] /;
FreeQ[{a,b,c,d,e,f,n,p,q,r},x]


Int[(a_.+b_.*Log[v_])^p_.*(c_.+d_.*Log[v_])^q_.,x_Symbol] :=
  1/Coeff[v,x,1]*Subst[Int[(a+b*Log[x])^p*(c+d*Log[x])^q,x],x,v] /;
FreeQ[{a,b,c,d,p,q},x] && LinearQ[v,x] && NeQ[Coeff[v,x,0],0]


Int[(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[c_.*x_^n_.])^q_./x_,x_Symbol] :=
  1/n*Subst[Int[(a+b*x)^p*(d+e*x)^q,x],x,Log[c*x^n]] /;
FreeQ[{a,b,c,d,e,n,p,q},x]


Int[(g_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.]),x_Symbol] :=
  With[{u=IntHide[(g*x)^m*(a+b*Log[c*x^n])^p,x]},
  Dist[(d+e*Log[f*x^r]),u,x] - e*r*Int[SimplifyIntegrand[u/x,x],x]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,r},x] && Not[EqQ[p,1] && EqQ[a,0] && NeQ[d,0]]


Int[(g_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.])^q_.,x_Symbol] :=
  (g*x)^(m+1)*(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^q/(g*(m+1)) - 
  e*q*r/(m+1)*Int[(g*x)^m*(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^(q-1),x] - 
  b*n*p/(m+1)*Int[(g*x)^m*(a+b*Log[c*x^n])^(p-1)*(d+e*Log[f*x^r])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,r},x] && IGtQ[p,0] && IGtQ[q,0] && NeQ[m,-1]


Int[(g_.*x_)^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_.*(d_.+e_.*Log[f_.*x_^r_.])^q_.,x_Symbol] :=
  Unintegrable[(g*x)^m*(a+b*Log[c*x^n])^p*(d+e*Log[f*x^r])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x]


Int[u_^m_.*(a_.+b_.*Log[v_])^p_.*(c_.+d_.*Log[v_])^q_.,x_Symbol] :=
  With[{e=Coeff[u,x,0],f=Coeff[u,x,1],g=Coeff[v,x,0],h=Coeff[v,x,1]},
  1/h*Subst[Int[(f*x/h)^m*(a+b*Log[x])^p*(c+d*Log[x])^q,x],x,v] /;
 EqQ[f*g-e*h,0] && NeQ[g,0]] /;
FreeQ[{a,b,c,d,m,p,q},x] && LinearQ[{u,v},x]


Int[Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  With[{u=IntHide[Log[d*(e+f*x^m)^r],x]},
  Dist[(a+b*Log[c*x^n])^p,u,x] - b*n*p*Int[Dist[(a+b*Log[c*x^n])^(p-1)/x,u,x],x]] /;
FreeQ[{a,b,c,d,e,f,r,m,n},x] && IGtQ[p,0] && RationalQ[m] && (EqQ[p,1] || FractionQ[m] && IntegerQ[1/m] || EqQ[r,1] && EqQ[m,1] && EqQ[d*e,1])


Int[Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  With[{u=IntHide[(a+b*Log[c*x^n])^p,x]},
  Dist[Log[d*(e+f*x^m)^r],u,x] - f*m*r*Int[Dist[x^(m-1)/(e+f*x^m),u,x],x]] /;
FreeQ[{a,b,c,d,e,f,r,m,n},x] && IGtQ[p,0] && IntegerQ[m]


Int[Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[Log[d*(e+f*x^m)^r]*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,r,m,n,p},x]


Int[Log[d_.*u_^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[Log[d*ExpandToSum[u,x]^r]*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,r,n,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[Log[d_.*(e_+f_.*x_^m_.)]*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
  -PolyLog[2,-d*f*x^m]*(a+b*Log[c*x^n])^p/m + 
  b*n*p/m*Int[PolyLog[2,-d*f*x^m]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0] && EqQ[d*e,1]


Int[Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
  Log[d*(e+f*x^m)^r]*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) - 
  f*m*r/(b*n*(p+1))*Int[x^(m-1)*(a+b*Log[c*x^n])^(p+1)/(e+f*x^m),x] /;
FreeQ[{a,b,c,d,e,f,r,m,n},x] && IGtQ[p,0] && NeQ[d*e,1]


Int[(g_.*x_)^q_.*Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[(g*x)^q*Log[d*(e+f*x^m)^r],x]},
  Dist[(a+b*Log[c*x^n]),u,x] - b*n*Int[Dist[1/x,u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g,r,m,n,q},x] && (IntegerQ[(q+1)/m] || RationalQ[m] && RationalQ[q]) && NeQ[q,-1]


Int[(g_.*x_)^q_.*Log[d_.*(e_+f_.*x_^m_.)]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  With[{u=IntHide[(g*x)^q*Log[d*(e+f*x^m)],x]},
  Dist[(a+b*Log[c*x^n])^p,u,x] - b*n*p*Int[Dist[(a+b*Log[c*x^n])^(p-1)/x,u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && IGtQ[p,0] && RationalQ[m] && RationalQ[q] && NeQ[q,-1] && 
  (EqQ[p,1] || FractionQ[m] && IntegerQ[(q+1)/m] || IGtQ[q,0] && IntegerQ[(q+1)/m] && EqQ[d*e,1])


Int[(g_.*x_)^q_.*Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  With[{u=IntHide[(g*x)^q*(a+b*Log[c*x^n])^p,x]},
  Dist[Log[d*(e+f*x^m)^r],u,x] - f*m*r*Int[Dist[x^(m-1)/(e+f*x^m),u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g,r,m,n,q},x] && IGtQ[p,0] && RationalQ[m] && RationalQ[q]


Int[(g_.*x_)^q_.*Log[d_.*(e_+f_.*x_^m_.)^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(g*x)^q*Log[d*(e+f*x^m)^r]*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,r,m,n,p,q},x]


Int[(g_.*x_)^q_.*Log[d_.*u_^r_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Int[(g*x)^q*Log[d*ExpandToSum[u,x]^r]*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,g,r,n,p,q},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  -b*n*x*PolyLog[k,e*x^q] + x*PolyLog[k,e*x^q]*(a+b*Log[c*x^n]) + 
  b*n*q*Int[PolyLog[k-1,e*x^q],x] - q*Int[PolyLog[k-1,e*x^q]*(a+b*Log[c*x^n]),x] /;
FreeQ[{a,b,c,e,n,q},x] && IGtQ[k,0]


Int[PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[PolyLog[k,e*x^q]*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,e,n,p,q},x]


Int[PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
  PolyLog[k+1,e*x^q]*(a+b*Log[c*x^n])^p/q - b*n*p/q*Int[PolyLog[k+1,e*x^q]*(a+b*Log[c*x^n])^(p-1)/x,x] /;
FreeQ[{a,b,c,e,k,n,q},x] && GtQ[p,0]


Int[PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_./x_,x_Symbol] :=
  PolyLog[k,e*x^q]*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) - q/(b*n*(p+1))*Int[PolyLog[k-1,e*x^q]*(a+b*Log[c*x^n])^(p+1)/x,x] /;
FreeQ[{a,b,c,e,k,n,q},x] && LtQ[p,-1]


Int[(d_.*x_)^m_.*PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  -b*n*(d*x)^(m+1)*PolyLog[k,e*x^q]/(d*(m+1)^2) + 
  (d*x)^(m+1)*PolyLog[k,e*x^q]*(a+b*Log[c*x^n])/(d*(m+1)) + 
  b*n*q/(m+1)^2*Int[(d*x)^m*PolyLog[k-1,e*x^q],x] - 
  q/(m+1)*Int[(d*x)^m*PolyLog[k-1,e*x^q]*(a+b*Log[c*x^n]),x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && IGtQ[k,0]


Int[(d_.*x_)^m_.*PolyLog[k_,e_.*x_^q_.]*(a_.+b_.*Log[c_.*x_^n_.])^p_.,x_Symbol] :=
  Unintegrable[(d*x)^m*PolyLog[k,e*x^q]*(a+b*Log[c*x^n])^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x]


Int[Px_.*F_[d_.*(e_.+f_.*x_)]^m_.*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[Px*F[d*(e+f*x)]^m,x]},
  Dist[(a+b*Log[c*x^n]),u,x] - b*n*Int[Dist[1/x,u,x],x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && PolynomialQ[Px,x] && IGtQ[m,0] && MemberQ[{ArcSin, ArcCos, ArcSinh, ArcCosh},F]


Int[Px_.*F_[d_.*(e_.+f_.*x_)]*(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
  With[{u=IntHide[Px*F[d*(e+f*x)],x]},
  Dist[(a+b*Log[c*x^n]),u,x] - b*n*Int[Dist[1/x,u,x],x]] /;
FreeQ[{a,b,c,d,e,f,n},x] && PolynomialQ[Px,x] && MemberQ[{ArcTan, ArcCot, ArcTanh, ArcCoth},F]





(* ::Subsection::Closed:: *)
(*3.2 u (a+b log(c (d+e x)^n))^p*)


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  1/e*Subst[Int[(a+b*Log[c*x^n])^p,x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,n,p},x]


Int[(f_+g_. x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  1/e*Subst[Int[(f*x/d)^q*(a+b*Log[c*x^n])^p,x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q},x] && EqQ[e*f-d*g,0]


Int[Log[c_.*(d_+e_.*x_^n_.)]/x_,x_Symbol] :=
  -PolyLog[2,-c*e*x^n]/n /;
FreeQ[{c,d,e,n},x] && EqQ[c*d,1]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)])/x_,x_Symbol] :=
  (a+b*Log[c*d])*Log[x] + b*Int[Log[1+e*x/d]/x,x] /;
FreeQ[{a,b,c,d,e},x] && GtQ[c*d,0]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)])/(f_.+g_. x_),x_Symbol] :=
  1/g*Subst[Int[(a+b*Log[1+c*e*x/g])/x,x],x,f+g*x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[g+c*(e*f-d*g),0]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/(f_.+g_. x_),x_Symbol] :=
  Log[e*(f+g*x)/(e*f-d*g)]*(a+b*Log[c*(d+e*x)^n])/g - b*e*n/g*Int[Log[(e*(f+g*x))/(e*f-d*g)]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0]


Int[(f_.+g_.*x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
  (f+g*x)^(q+1)*(a+b*Log[c*(d+e*x)^n])/(g*(q+1)) - 
  b*e*n/(g*(q+1))*Int[(f+g*x)^(q+1)/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,n,q},x] && NeQ[e*f-d*g,0] && NeQ[q,-1]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_/(f_.+g_. x_),x_Symbol] :=
  Log[e*(f+g*x)/(e*f-d*g)]*(a+b*Log[c*(d+e*x)^n])^p/g - 
  b*e*n*p/g*Int[Log[(e*(f+g*x))/(e*f-d*g)]*(a+b*Log[c*(d+e*x)^n])^(p-1)/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && IGtQ[p,1]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_/(f_.+g_.*x_)^2,x_Symbol] :=
  (d+e*x)*(a+b*Log[c*(d+e*x)^n])^p/((e*f-d*g)*(f+g*x)) - 
  b*e*n*p/(e*f-d*g)*Int[(a+b*Log[c*(d+e*x)^n])^(p-1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && GtQ[p,0]


Int[(f_.+g_.*x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
  (f+g*x)^(q+1)*(a+b*Log[c*(d+e*x)^n])^p/(g*(q+1)) - 
  b*e*n*p/(g*(q+1))*Int[(f+g*x)^(q+1)*(a+b*Log[c*(d+e*x)^n])^(p-1)/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,n,q},x] && NeQ[e*f-d*g,0] && GtQ[p,0] && NeQ[q,-1] && IntegersQ[2*p,2*q] && 
  (Not[IGtQ[q,0]] || EqQ[p,2] && NeQ[q,1])


Int[(f_.+g_.*x_)^q_./(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
  Int[ExpandIntegrand[(f+g*x)^q/(a+b*Log[c*(d+e*x)^n]),x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && IGtQ[q,0]


Int[(f_.+g_.*x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
  (d+e*x)*(f+g*x)^q*(a+b*Log[c*(d+e*x)^n])^(p+1)/(b*e*n*(p+1)) + 
  q*(e*f-d*g)/(b*e*n*(p+1))*Int[(f+g*x)^(q-1)*(a+b*Log[c*(d+e*x)^n])^(p+1),x] - 
  (q+1)/(b*n*(p+1))*Int[(f+g*x)^q*(a+b*Log[c*(d+e*x)^n])^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && LtQ[p,-1] && GtQ[q,0]


Int[(f_.+g_.*x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
  Int[ExpandIntegrand[(f+g*x)^q*(a+b*Log[c*(d+e*x)^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && IGtQ[q,0]


Int[Log[c_./(d_+e_.*x_)]/(f_+g_.*x_^2),x_Symbol] :=
  -e/g*Subst[Int[Log[2*d*x]/(1-2*d*x),x],x,1/(d+e*x)] /;
FreeQ[{c,d,e,f,g},x] && EqQ[c,2*d] && EqQ[e^2*f+d^2*g,0]


Int[(a_.+b_.*Log[c_./(d_+e_.*x_)])/(f_+g_.*x_^2),x_Symbol] :=
  (a+b*Log[c/(2*d)])*Int[1/(f+g*x^2),x] + b*Int[Log[2*d/(d+e*x)]/(f+g*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[e^2*f+d^2*g,0] && GtQ[c/(2*d),0]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/Sqrt[f_+g_.*x_^2],x_Symbol] :=
  With[{u=IntHide[1/Sqrt[f+g*x^2],x]},  
  u*(a+b*Log[c*(d+e*x)^n]) - b*e*n*Int[SimplifyIntegrand[u/(d+e*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && GtQ[f,0]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/(Sqrt[f1_+g1_.*x_]*Sqrt[f2_+g2_.*x_]),x_Symbol] :=
  With[{u=IntHide[1/Sqrt[f1*f2+g1*g2*x^2],x]},  
  u*(a+b*Log[c*(d+e*x)^n]) - b*e*n*Int[SimplifyIntegrand[u/(d+e*x),x],x]] /;
FreeQ[{a,b,c,d,e,f1,g1,f2,g2,n},x] && EqQ[f2*g1+f1*g2,0] && GtQ[f1,0] && GtQ[f2,0]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/Sqrt[f_+g_.*x_^2],x_Symbol] :=
  Sqrt[1+g/f*x^2]/Sqrt[f+g*x^2]*Int[(a+b*Log[c*(d+e*x)^n])/Sqrt[1+g/f*x^2],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && Not[GtQ[f,0]]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/(Sqrt[f1_+g1_.*x_]*Sqrt[f2_+g2_.*x_]),x_Symbol] :=
  Sqrt[1+g1*g2/(f1*f2)*x^2]/(Sqrt[f1+g1*x]*Sqrt[f2+g2*x])*Int[(a+b*Log[c*(d+e*x)^n])/Sqrt[1+g1*g2/(f1*f2)*x^2],x] /;
FreeQ[{a,b,c,d,e,f1,g1,f2,g2,n},x] && EqQ[f2*g1+f1*g2,0]


Int[(f_.+g_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  With[{k=Denominator[r]},
  k*Subst[Int[x^(k-1)*(f+g*x^(k*r))^q*(a+b*Log[c*(d+e*x^k)^n])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q},x] && FractionQ[r] && IGtQ[p,0]


Int[(f_+g_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*Log[c*(d+e*x)^n])^p,(f+g*x^r)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,r},x] && IGtQ[p,0] && IntegerQ[q] && (GtQ[q,0] || IntegerQ[r] && NeQ[r,1])


Int[x_^m_.*Log[c_.*(d_+e_.*x_)]/(f_+g_. x_),x_Symbol] :=
  Int[ExpandIntegrand[Log[c*(d+e*x)],x^m/(f+g*x),x],x] /;
FreeQ[{c,d,e,f,g},x] && EqQ[e*f-d*g,0] && EqQ[c*d,1] && IntegerQ[m]


Int[(f_.+g_. x_)^q_.*(h_.+i_. x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  1/e*Subst[Int[(g*x/e)^q*((e*h-d*i)/e+i*x/e)^r*(a+b*Log[c*x^n])^p,x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,n,p,q,r},x] && EqQ[e*f-d*g,0] && (IGtQ[p,0] || IGtQ[r,0]) && IntegerQ[2*r]


Int[x_^m_.*(f_+g_./x_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  Int[(g+f*x)^q*(a+b*Log[c*(d+e*x)^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q},x] && EqQ[m,q] && IntegerQ[q]


Int[x_^m_.*(f_.+g_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  (f+g*x^r)^(q+1)*(a+b*Log[c*(d+e*x)^n])^p/(g*r*(q+1)) - 
  b*e*n*p/(g*r*(q+1))*Int[(f+g*x^r)^(q+1)*(a+b*Log[c*(d+e*x)^n])^(p-1)/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,q,r},x] && EqQ[m,r-1] && NeQ[q,-1] && IGtQ[p,0]


Int[x_^m_.*(f_+g_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
  With[{u=IntHide[x^m*(f+g*x^r)^q,x]},  
  Dist[(a+b*Log[c*(d+e*x)^n]),u,x] - b*e*n*Int[SimplifyIntegrand[u/(d+e*x),x],x] /;
 InverseFunctionFreeQ[u,x]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,q,r},x] && IntegerQ[m] && IntegerQ[q] && IntegerQ[r]


Int[x_^m_.*(f_.+g_.*x_^r_)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  With[{k=Denominator[r]},
  k*Subst[Int[x^(k*(m+1)-1)*(f+g*x^(k*r))^q*(a+b*Log[c*(d+e*x^k)^n])^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q},x] && FractionQ[r] && IGtQ[p,0] && IntegerQ[m]


Int[(h_.*x_)^m_.*(f_+g_.*x_^r_.)^q_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*Log[c*(d+e*x)^n])^p,(h*x)^m*(f+g*x^r)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q,r},x] && IntegerQ[m] && IntegerQ[q]


Int[Polyx_*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Polyx*(a+b*Log[c*(d+e*x)^n])^p,x],x] /;
FreeQ[{a,b,c,d,e,n,p},x] && PolynomialQ[Polyx,x]


Int[RFx_*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*(d+e*x)^n])^p,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n},x] && RationalFunctionQ[RFx,x] && IntegerQ[p]


Int[RFx_*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  With[{u=ExpandIntegrand[RFx*(a+b*Log[c*(d+e*x)^n])^p,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,n},x] && RationalFunctionQ[RFx,x] && IntegerQ[p]


Int[AFx_*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  Unintegrable[AFx*(a+b*Log[c*(d+e*x)^n])^p,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && AlgebraicFunctionQ[AFx,x,True]


Int[u_^q_.*(a_.+b_.*Log[c_.*v_^n_.])^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^q*(a+b*Log[c*ExpandToSum[v,x]^n])^p,x] /;
FreeQ[{a,b,c,n,p,q},x] && BinomialQ[u,x] && LinearQ[v,x] && Not[BinomialMatchQ[u,x] && LinearMatchQ[v,x]]


Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
  -x*(m-Log[f*x^m])*(a+b*Log[c*(d+e*x)^n]) + b*e*m*n*Int[x/(d+e*x),x] - b*e*n*Int[(x*Log[f*x^m])/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
  With[{u=IntHide[(a+b*Log[c*(d+e*x)^n])^p,x]},
  Dist[Log[f*x^m],u,x] - m*Int[Dist[1/x,u,x],x]] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,1]


Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  Unintegrable[Log[f*x^m]*(a+b*Log[c*(d+e*x)^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x]


Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])/x_,x_Symbol] :=
  Log[f*x^m]^2*(a+b*Log[c*(d+e*x)^n])/(2*m) - b*e*n/(2*m)*Int[Log[f*x^m]^2/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x]


Int[(g_.*x_)^q_.*Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
  -1/(g*(q+1))*(m*(g*x)^(q+1)/(q+1)-(g*x)^(q+1)*Log[f*x^m])*(a+b*Log[c*(d+e*x)^n]) + 
  b*e*m*n/(g*(q+1)^2)*Int[(g*x)^(q+1)/(d+e*x),x] - 
  b*e*n/(g*(q+1))*Int[(g*x)^(q+1)*Log[f*x^m]/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && NeQ[q,-1]


Int[Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_./x_,x_Symbol] :=
  Log[f*x^m]^2*(a+b*Log[c*(d+e*x)^n])^p/(2*m) - b*e*n*p/(2*m)*Int[Log[f*x^m]^2*(a+b*Log[c*(d+e*x)^n])^(p-1)/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[p,0]


Int[(g_.*x_)^q_.*Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
  With[{u=IntHide[(g*x)^q*(a+b*Log[c*(d+e*x)^n])^p,x]},
  Dist[Log[f*x^m],u,x] - m*Int[Dist[1/x,u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && IGtQ[p,1] && IGtQ[q,0]


(* Int[(g_.*x_)^q_.*Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_,x_Symbol] :=
  With[{u=IntHide[(a+b*Log[c*(d+e*x)^n])^p,x]},
  Dist[(g*x)^q*Log[f*x^m],u,x] - g*m*Int[Dist[(g*x)^(q-1),u,x],x] - g*q*Int[Dist[(g*x)^(q-1)*Log[f*x^m],u,x],x]] /;
FreeQ[{a,b,c,d,e,f,g,m,n,q},x] && IGtQ[p,1] *)


Int[(g_.*x_)^q_.*Log[f_.*x_^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  Unintegrable[(g*x)^q*Log[f*x^m]*(a+b*Log[c*(d+e*x)^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q},x]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.]),x_Symbol] :=
  x*(a+b*Log[c*(d+e*x)^n])^p*(f+g*Log[h*(i+j*x)^m]) - 
  g*j*m*Int[x*(a+b*Log[c*(d+e*x)^n])^p/(i+j*x),x] - 
  b*e*n*p*Int[x*(a+b*Log[c*(d+e*x)^n])^(p-1)*(f+g*Log[h*(i+j*x)^m])/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && IGtQ[p,0]


Int[Log[f_.*(g_.+h_.*x_)^m_.]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.,x_Symbol] :=
  1/e*Subst[Int[Log[f*(g*x/d)^m]*(a+b*Log[c*x^n])^p,x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && EqQ[e*f-d*g,0]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.])^q_.,x_Symbol] :=
  Unintegrable[(a+b*Log[c*(d+e*x)^n])^p*(f+g*Log[h*(i+j*x)^m])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n,p},x]


Int[(k_.+l_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.]),x_Symbol] :=
  1/e*Subst[Int[(k*x/d)^r*(a+b*Log[c*x^n])^p*(f+g*Log[h*((e*i-d*j)/e+j*x/e)^m]),x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,l,n,p,r},x] && EqQ[e*k-d*l,0]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.])/x_,x_Symbol] :=
  Log[x]*(a+b*Log[c*(d+e*x)^n])*(f+g*Log[h*(i+j*x)^m]) - 
  e*g*m*Int[Log[x]*(a+b*Log[c*(d+e*x)^n])/(d+e*x),x] - 
  b*j*n*Int[Log[x]*(f+g*Log[h*(i+j*x)^m])/(i+j*x),x]/;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && EqQ[e*i-d*j,0]


Int[Log[a_+b_.*x_]*Log[c_+d_.*x_]/x_,x_Symbol] :=
  Log[-b*x/a]*Log[a+b*x]*Log[c+d*x] - 
  1/2*(Log[-b*x/a]-Log[-d*x/c])*(Log[a+b*x]+Log[a*(c+d*x)/(c*(a+b*x))])^2 + 
  1/2*(Log[-b*x/a]-Log[-(b*c-a*d)*x/(a*(c+d*x))]+Log[(b*c-a*d)/(b*(c+d*x))])*Log[a*(c+d*x)/(c*(a+b*x))]^2 + 
  (Log[c+d*x]-Log[a*(c+d*x)/(c*(a+b*x))])*PolyLog[2,1+b*x/a] + 
  (Log[a+b*x]+Log[a*(c+d*x)/(c*(a+b*x))])*PolyLog[2,1+d*x/c] - 
  Log[a*(c+d*x)/(c*(a+b*x))]*PolyLog[2,d*(a+b*x)/(b*(c+d*x))] + 
  Log[a*(c+d*x)/(c*(a+b*x))]*PolyLog[2,c*(a+b*x)/(a*(c+d*x))] - 
  PolyLog[3,1+b*x/a] - PolyLog[3,1+d*x/c] - PolyLog[3,d*(a+b*x)/(b*(c+d*x))] + PolyLog[3,c*(a+b*x)/(a*(c+d*x))]/;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[Log[v_]*Log[w_]/x_,x_Symbol] :=
  Int[Log[ExpandToSum[v,x]]*Log[ExpandToSum[w,x]]/x,x] /;
LinearQ[{v,w},x] && Not[LinearMatchQ[{v,w},x]]


Int[Log[c_.*(d_+e_.*x_)^n_.]*Log[h_.*(i_.+j_.*x_)^m_.]/x_,x_Symbol] :=
  m*Int[Log[i+j*x]*Log[c*(d+e*x)^n]/x,x] - (m*Log[i+j*x]-Log[h*(i+j*x)^m])*Int[Log[c*(d+e*x)^n]/x,x]/;
FreeQ[{c,d,e,h,i,j,m,n},x] && NeQ[e*i-d*j,0] && NeQ[i+j*x,h*(i+j*x)^m]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_+g_.*Log[h_.*(i_.+j_.*x_)^m_.])/x_,x_Symbol] :=
  f*Int[(a+b*Log[c*(d+e*x)^n])/x,x] + g*Int[Log[h*(i+j*x)^m]*(a+b*Log[c*(d+e*x)^n])/x,x]/;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && NeQ[e*i-d*j,0]


Int[x_^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.]),x_Symbol] :=
  x^(r+1)*(a+b*Log[c*(d+e*x)^n])^p*(f+g*Log[h*(i+j*x)^m])/(r+1) - 
  g*j*m/(r+1)*Int[x^(r+1)*(a+b*Log[c*(d+e*x)^n])^p/(i+j*x),x] - 
  b*e*n*p/(r+1)*Int[x^(r+1)*(a+b*Log[c*(d+e*x)^n])^(p-1)*(f+g*Log[h*(i+j*x)^m])/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,m,n},x] && IGtQ[p,0] && IntegerQ[r] && (EqQ[p,1] || GtQ[r,0]) && NeQ[r,-1]


Int[(k_+l_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.]),x_Symbol] :=
  1/l*Subst[Int[x^r*(a+b*Log[c*(-(e*k-d*l)/l+e*x/l)^n])*(f+g*Log[h*(-(j*k-i*l)/l+j*x/l)^m]),x],x,k+l*x]/;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,l,m,n},x] && IntegerQ[r]


Int[(k_.+l_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_.*(f_.+g_.*Log[h_.*(i_.+j_.*x_)^m_.])^q_.,x_Symbol] :=
  Unintegrable[(k+l*x)^r*(a+b*Log[c*(d+e*x)^n])^p*(f+g*Log[h*(i+j*x)^m])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,k,l,m,n,p,q,r},x]


Int[PolyLog[k_,h_+i_.*x_]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.])^p_./(f_+g_.*x_),x_Symbol] :=
  1/g*Subst[Int[PolyLog[k,h*x/d]*(a+b*Log[c*x^n])^p/x,x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,k,n},x] && EqQ[e*f-d*g,0] && EqQ[g*h-f*i,0] && IGtQ[p,0]


Int[Px_.*F_[f_.*(g_.+h_.*x_)]*(a_.+b_.*Log[c_.*(d_+e_.*x_)^n_.]),x_Symbol] :=
  With[{u=IntHide[Px*F[f*(g+h*x)],x]},
  Dist[(a+b*Log[c*(d+e*x)^n]),u,x] - b*e*n*Int[SimplifyIntegrand[u/(d+e*x),x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h,n},x] && PolynomialQ[Px,x] && 
  MemberQ[{ArcSin, ArcCos, ArcTan, ArcCot, ArcSinh, ArcCosh, ArcTanh, ArcCoth},F]


Int[u_.*(a_.+b_.*Log[c_.*v_^n_.])^p_.,x_Symbol] :=
  Int[u*(a+b*Log[c*ExpandToSum[v,x]^n])^p,x] /;
FreeQ[{a,b,c,n,p},x] && LinearQ[v,x] && Not[LinearMatchQ[v,x]] && Not[EqQ[n,1] && MatchQ[c*v,e_.*(f_+g_.*x) /; FreeQ[{e,f,g},x]]]


Int[u_.*(a_.+b_.*Log[c_.*(d_.*(e_.+f_. x_)^m_.)^n_])^p_.,x_Symbol] :=
  Subst[Int[u*(a+b*Log[c*d^n*(e+f*x)^(m*n)])^p,x],c*d^n*(e+f*x)^(m*n),c*(d*(e+f*x)^m)^n] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[n]] && Not[EqQ[d,1] && EqQ[m,1]] && 
  IntegralFreeQ[IntHide[u*(a+b*Log[c*d^n*(e+f*x)^(m*n)])^p,x]]


Int[AFx_*(a_.+b_.*Log[c_.*(d_.*(e_.+f_. x_)^m_.)^n_])^p_.,x_Symbol] :=
  Unintegrable[AFx*(a+b*Log[c*(d*(e+f*x)^m)^n])^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && AlgebraicFunctionQ[AFx,x,True]





(* ::Subsection::Closed:: *)
(*3.3 u (a+b log(c (d+e x^m)^n))^p*)


Int[Pq_^m_.*Log[u_],x_Symbol] :=
  With[{C=FullSimplify[Pq^m*(1-u)/D[u,x]]},
  C*PolyLog[2,1-u] /;
 FreeQ[C,x]] /; 
IntegerQ[m] && PolyQ[Pq,x] && RationalFunctionQ[u,x] && LeQ[RationalFunctionExponents[u,x][[2]],Expon[Pq,x]]


Int[Log[c_.*(d_+e_.*x_^n_)^p_.],x_Symbol] :=
  x*Log[c*(d+e*x^n)^p] - e*n*p*Int[x^n/(d+e*x^n),x] /;
FreeQ[{c,d,e,n,p},x]


Int[(a_.+b_.*Log[c_.*(d_+e_./x_)^p_.])^q_,x_Symbol] :=
  (e+d*x)*(a+b*Log[c*(d+e/x)^p])^q/d + b*e*p*q/d*Int[(a+b*Log[c*(d+e/x)^p])^(q-1)/x,x] /;
FreeQ[{a,b,c,d,e,p},x] && IGtQ[q,0]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
  x*(a+b*Log[c*(d+e*x^n)^p])^q - b*e*n*p*q*Int[x^n*(a+b*Log[c*(d+e*x^n)^p])^(q-1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && IGtQ[q,0] && (EqQ[q,1] || IntegerQ[n])


(* Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*Log[c*(d+e*x^(k*n))^p])^q,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,e,p,q},x] && LtQ[-1,n,1] && (GtQ[n,0] || IGtQ[q,0]) *)


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*Log[c*(d+e*x^(k*n))^p])^q,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,e,p,q},x] && FractionQ[n]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
  Unintegrable[(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x]


Int[(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
  Int[(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
FreeQ[{a,b,c,p,q},x] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*Log[c*(d+e*x)^p])^q,x],x,x^n] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && IntegerQ[Simplify[(m+1)/n]] && (GtQ[(m+1)/n,0] || IGtQ[q,0]) && Not[EqQ[q,1] && ILtQ[n,0] && IGtQ[m,0]]


Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.]),x_Symbol] :=
  (f*x)^(m+1)*(a+b*Log[c*(d+e*x^n)^p])/(f*(m+1)) - 
  b*e*n*p/(f*(m+1))*Int[x^(n-1)*(f*x)^(m+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && NeQ[m,-1]


Int[(f_*x_)^m_*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  (f*x)^m/x^m*Int[x^m*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && IntegerQ[Simplify[(m+1)/n]] && (GtQ[(m+1)/n,0] || IGtQ[q,0])


Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
  (f*x)^(m+1)*(a+b*Log[c*(d+e*x^n)^p])^q/(f*(m+1)) - 
  b*e*n*p*q/(f^n*(m+1))*Int[(f*x)^(m+n)*(a+b*Log[c*(d+e*x^n)^p])^(q-1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && IGtQ[q,1] && IntegerQ[n] && NeQ[m,-1]


Int[x_^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*Log[c*(d+e*x^(k*n))^p])^q,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,d,e,m,p,q},x] && FractionQ[n]


Int[(f_*x_)^m_*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  (f*x)^m/x^m*Int[x^m*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && FractionQ[n]


Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  Unintegrable[(f*x)^m*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x]


Int[(f_.*x_)^m_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
  Int[(f*x)^m*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
FreeQ[{a,b,c,f,m,p,q},x] && BinomialQ[v,x] && Not[BinomialMatchQ[v,x]]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])/(f_.+g_.*x_),x_Symbol] :=
  Log[f+g*x]*(a+b*Log[c*(d+e*x^n)^p])/g - 
  b*e*n*p/g*Int[x^(n-1)*Log[f+g*x]/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && RationalQ[n]


Int[(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.]),x_Symbol] :=
  (f+g*x)^(r+1)*(a+b*Log[c*(d+e*x^n)^p])/(g*(r+1)) - 
  b*e*n*p/(g*(r+1))*Int[x^(n-1)*(f+g*x)^(r+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,r},x] && (IGtQ[r,0] || RationalQ[n]) && NeQ[r,-1]


Int[(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  Unintegrable[(f+g*x)^r*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r},x]


Int[u_^r_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^r*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
FreeQ[{a,b,c,p,q,r},x] && LinearQ[u,x] && BinomialQ[v,x] && Not[LinearMatchQ[u,x] && BinomialMatchQ[v,x]]


Int[x_^m_.*(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*Log[c*(d+e*x^n)^p])^q,x^m*(f+g*x)^r,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q},x] && IntegerQ[m] && IntegerQ[r]


Int[(h_.*x_)^m_*(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_.)^p_.])^q_.,x_Symbol] :=
  With[{k=Denominator[m]},
  k/h*Subst[Int[x^(k*(m+1)-1)*(f+g*x^k/h)^r*(a+b*Log[c*(d+e*x^(k*n)/h^n)^p])^q,x],x,(h*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,r},x] && FractionQ[m] && IntegerQ[n] && IntegerQ[r]


Int[(h_.*x_)^m_.*(f_.+g_.*x_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  Unintegrable[(h*x)^m*(f+g*x)^r*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q,r},x]


Int[(h_.*x_)^m_.*u_^r_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
  Int[(h*x)^m*ExpandToSum[u,x]^r*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
FreeQ[{a,b,c,h,m,p,q,r},x] && LinearQ[u,x] && BinomialQ[v,x] && Not[LinearMatchQ[u,x] && BinomialMatchQ[v,x]]


Int[(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])/(f_+g_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(f+g*x^2),x]},  
  u*(a+b*Log[c*(d+e*x^n)^p]) - b*e*n*p*Int[u*x^(n-1)/(d+e*x^n),x]] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && IntegerQ[n]


Int[(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  With[{t=ExpandIntegrand[(a+b*Log[c*(d+e*x^n)^p])^q,(f+g*x^s)^r,x]},
  Int[t,x] /;
 SumQ[t]] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r,s},x] && IntegerQ[n] && IGtQ[q,0] && IntegerQ[r] && IntegerQ[s] && 
  (EqQ[q,1] || GtQ[r,0] && GtQ[s,1] || LtQ[s,0] && LtQ[r,0])


Int[(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(f+g*x^(k*s))^r*(a+b*Log[c*(d+e*x^(k*n))^p])^q,x],x,x^(1/k)] /;
 IntegerQ[k*s]] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r,s},x] && FractionQ[n]


Int[(f_+g_.*x_^s_)^r_.(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  Unintegrable[(f+g*x^s)^r*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r,s},x]


Int[u_^r_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^r*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
FreeQ[{a,b,c,p,q,r},x] && BinomialQ[{u,v},x] && Not[BinomialMatchQ[{u,v},x]]


Int[x_^m_.*(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(f+g*x^(s/n))^r*(a+b*Log[c*(d+e*x)^p])^q,x],x,x^n] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r,s},x] && IntegerQ[r] && IntegerQ[s/n] && IntegerQ[Simplify[(m+1)/n]] && (GtQ[(m+1)/n,0] || IGtQ[q,0])


Int[x_^m_.*(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*Log[c*(d+e*x^n)^p])^q,x^m*(f+g*x^s)^r,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r,s},x] && IGtQ[q,0] && IntegerQ[m] && IntegerQ[r] && IntegerQ[s]


Int[(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(f+g*x^(k*s))^r*(a+b*Log[c*(d+e*x^(k*n))^p])^q,x],x,x^(1/k)] /;
 IntegerQ[k*s]] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r,s},x] && FractionQ[n]


Int[x_^m_.*(f_+g_.*x_^s_)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  1/n*Subst[Int[x^(m+1/n-1)*(f+g*x^(s/n))^r*(a+b*Log[c*(d+e*x)^p])^q,x],x,x^n] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r,s},x] && FractionQ[n] && IntegerQ[1/n] && IntegerQ[s/n]


Int[(h_.*x_)^m_*(f_.+g_.*x_^s_.)^r_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_.)^p_.])^q_.,x_Symbol] :=
  With[{k=Denominator[m]},
  k/h*Subst[Int[x^(k*(m+1)-1)*(f+g*x^(k*s)/h^s)^r*(a+b*Log[c*(d+e*x^(k*n)/h^n)^p])^q,x],x,(h*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,r},x] && FractionQ[m] && IntegerQ[n] && IntegerQ[s]


Int[(h_.*x_)^m_.*(f_+g_.*x_^s_)^r_.(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])^q_.,x_Symbol] :=
  Unintegrable[(h*x)^m*(f+g*x^s)^r*(a+b*Log[c*(d+e*x^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q,r,s},x]


Int[(h_.*x_)^m_.*u_^r_.*(a_.+b_.*Log[c_.*v_^p_.])^q_.,x_Symbol] :=
  Int[(h*x)^m*ExpandToSum[u,x]^r*(a+b*Log[c*ExpandToSum[v,x]^p])^q,x] /;
FreeQ[{a,b,c,h,m,p,q,r},x] && BinomialQ[{u,v},x] && Not[BinomialMatchQ[{u,v},x]]


Int[Log[f_.*x_^q_.]^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.])/x_,x_Symbol] :=
  Log[f*x^q]^(m+1)*(a+b*Log[c*(d+e*x^n)^p])/(q*(m+1)) - 
  b*e*n*p/(q*(m+1))*Int[x^(n-1)*Log[f*x^q]^(m+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && NeQ[m,-1]


Int[F_[f_.*x_]^m_.*(a_.+b_.*Log[c_.*(d_+e_.*x_^n_)^p_.]),x_Symbol] :=
  With[{u=IntHide[F[f*x]^m,x]},  
  Dist[a+b*Log[c*(d+e*x^n)^p],u,x] - b*e*n*p*Int[SimplifyIntegrand[u*x^(n-1)/(d+e*x^n),x],x]] /;
FreeQ[{a,b,c,d,e,f,p},x] && MemberQ[{ArcSin,ArcCos,ArcSinh,ArcCosh},F] && IGtQ[m,0] && IGtQ[n,1]


Int[(a_.+b_.*Log[c_.*(d_+e_.*(f_.+g_.*x_)^n_)^p_.])^q_.,x_Symbol] :=
  1/g*Subst[Int[(a+b*Log[c*(d+e*x^n)^p])^q,x],x,f+g*x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && IGtQ[q,0] && (EqQ[q,1] || IntegerQ[n])


Int[(a_.+b_.*Log[c_.*(d_+e_.*(f_.+g_.*x_)^n_)^p_.])^q_.,x_Symbol] :=
  Unintegrable[(a+b*Log[c*(d+e*(f+g*x)^n)^p])^q,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q},x]





(* ::Subsection::Closed:: *)
(*3.4 u log(e (f (a+b x)^p (c+d x)^q)^r)^s*)


Int[u_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  Int[u*Log[e*(b^p*f/d^p*(c+d*x)^(p+q))^r]^s,x] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && EqQ[b*c-a*d,0] && IntegerQ[p]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  (a+b*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/b - 
  r*s/b*Int[(b*c*p+a*d*q+b*d*(p+q)*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_./(g_.+h_.*x_),x_Symbol] :=
  -Log[-(b*c-a*d)/(d*(a+b*x))]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/h + 
  p*r*s (b*c-a*d)/h*Int[Log[-(b*c-a*d)/(d*(a+b*x))]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[b*g-a*h,0] && EqQ[p+q,0]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]/(g_.+h_.*x_),x_Symbol] :=
  Log[g+h*x]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/h - 
  b*p*r/h*Int[Log[g+h*x]/(a+b*x),x] - 
  d*q*r/h*Int[Log[g+h*x]/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r},x] && NeQ[b*c-a*d,0]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_/(g_.+h_.*x_),x_Symbol] :=
  d/h*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(c+d*x),x] - 
  (d*g-c*h)/h*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/((c+d*x)*(g+h*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,1]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_./(g_.+h_.*x_)^2,x_Symbol] :=
  (a+b*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/((b*g-a*h)*(g+h*x)) - 
  p*r*s*(b*c-a*d)/(b*g-a*h)*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((c+d*x)*(g+h*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0] && NeQ[b*g-a*h,0]


Int[Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_/(g_.+h_.*x_)^3,x_Symbol] :=
  d/(d*g-c*h)*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(g+h*x)^2,x] - 
  h/(d*g-c*h)*Int[(c+d*x)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(g+h*x)^3,x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0] && EqQ[b*g-a*h,0] && NeQ[d*g-c*h,0]


Int[(g_.+h_.*x_)^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  (g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(h*(m+1)) - 
  p*r*s*(b*c-a*d)/(h*(m+1))*Int[(g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && NeQ[m,-1] && EqQ[p+q,0]


Int[(g_.+h_.*x_)^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  (g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(h*(m+1)) - 
  b*p*r*s/(h*(m+1))*Int[(g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(a+b*x),x] - 
  d*q*r*s/(h*(m+1))*Int[(g+h*x)^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && NeQ[m,-1] && NeQ[p+q,0]


Int[1/((g_.+h_.*x_)^2*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]),x_Symbol] :=
  b*(c+d*x)*(e*(f*(a+b*x)^p*(c+d*x)^q)^r)^(1/(p*r))/(h*p*r*(b*c-a*d)*(g+h*x))*
    ExpIntegralEi[-1/(p*r)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q,r},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && EqQ[b*g-a*h,0]


Int[Log[i_.*(j_.*(h_.*x_)^t_.)^u_.]^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]/x_,x_Symbol] :=
  Log[i*(j*(h*x)^t)^u]^(m+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]/(t*u*(m+1)) - 
  b*p*r/(t*u*(m+1))*Int[Log[i*(j*(h*x)^t)^u]^(m+1)/(a+b*x),x] - 
  d*q*r/(t*u*(m+1))*Int[Log[i*(j*(h*x)^t)^u]^(m+1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,h,i,j,m,p,q,r,t,u},x] && NeQ[b*c-a*d,0] && IGtQ[m,0]


Int[Log[i_.*(j_.*(h_.*x_)^t_.)^u_.]^m_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_./x_,x_Symbol] :=
  Unintegrable[Log[i*(j*(h*x)^t)^u]^m*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/x,x] /;
FreeQ[{a,b,c,d,e,f,h,i,j,m,p,q,r,s,t,u},x] && NeQ[b*c-a*d,0]


Int[u_*Log[e_.*(c_.+d_.*x_)/(a_.+b_.*x_)],x_Symbol] :=
  With[{g=Coeff[Simplify[1/(u*(a+b*x))],x,0],h=Coeff[Simplify[1/(u*(a+b*x))],x,1]},
  -(b-d*e)/(h*(b*c-a*d))*Subst[Int[Log[e*x]/(1-e*x),x],x,(c+d*x)/(a+b*x)] /;
 EqQ[g*(b-d*e)-h*(a-c*e),0]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b*c-a*d,0] && LinearQ[Simplify[1/(u*(a+b*x))],x]


Int[u_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{g=Coeff[Simplify[1/(u*(a+b*x))],x,0],h=Coeff[Simplify[1/(u*(a+b*x))],x,1]},
  -Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(b*g-a*h)*Log[-(b*c-a*d)*(g+h*x)/((d*g-c*h)*(a+b*x))] + 
  p*r*s*(b*c-a*d)/(b*g-a*h)*
    Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x))*Log[-(b*c-a*d)*(g+h*x)/((d*g-c*h)*(a+b*x))],x] /;
 NeQ[b*g-a*h,0] && NeQ[d*g-c*h,0]] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0] && LinearQ[Simplify[1/(u*(a+b*x))],x]


Int[u_/Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
  With[{h=Simplify[u*(a+b*x)*(c+d*x)]},
  h*Log[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]]/(p*r*(b*c-a*d)) /;
 FreeQ[h,x]] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0]


Int[u_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{h=Simplify[u*(a+b*x)*(c+d*x)]},
  h*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s+1)/(p*r*(s+1)*(b*c-a*d)) /;
 FreeQ[h,x]] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && NeQ[s,-1]


Int[u_*Log[v_]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{g=Simplify[(v-1)*(c+d*x)/(a+b*x)],h=Simplify[u*(a+b*x)*(c+d*x)]},
  -h*PolyLog[2,1-v]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(b*c-a*d) + 
  h*p*r*s*Int[PolyLog[2,1-v]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
 FreeQ[{g,h},x]] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0]


Int[v_*Log[i_.*(j_.*(g_.+h_.*x_)^t_.)^u_.]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{k=Simplify[v*(a+b*x)*(c+d*x)]},
  k*Log[i*(j*(g+h*x)^t)^u]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s+1)/(p*r*(s+1)*(b*c-a*d)) - 
  k*h*t*u/(p*r*(s+1)*(b*c-a*d))*Int[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s+1)/(g+h*x),x] /;
 FreeQ[k,x]] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q,r,s,t,u},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && NeQ[s,-1]


Int[u_*PolyLog[n_,v_]*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{g=Simplify[v*(c+d*x)/(a+b*x)],h=Simplify[u*(a+b*x)*(c+d*x)]},
  h*PolyLog[n+1,v]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/(b*c-a*d) - 
  h*p*r*s*Int[PolyLog[n+1,v]*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1)/((a+b*x)*(c+d*x)),x] /;
 FreeQ[{g,h},x]] /;
FreeQ[{a,b,c,d,e,f,n,p,q,r,s},x] && NeQ[b*c-a*d,0] && IGtQ[s,0] && EqQ[p+q,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s/((m+1)*(b*c-a*d)) - 
  p*r*s*(b*c-a*d)/((m+1)*(b*c-a*d))*Int[(a+b*x)^m*(c+d*x)^n*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^(s-1),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r,s},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && EqQ[m+n+2,0] && NeQ[m,-1] && IGtQ[s,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_./Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/(p*r*(b*c-a*d)*(e*(f*(a+b*x)^p*(c+d*x)^q)^r)^((m+1)/(p*r)))*
    ExpIntegralEi[(m+1)/(p*r)*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && NeQ[b*c-a*d,0] && EqQ[p+q,0] && EqQ[m+n+2,0] && NeQ[m,-1]


Int[(a_.+b_.*Log[c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]])^n_./(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  2*e*g/(C*(e*f-d*g))*Subst[Int[(a+b*Log[c*x])^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
FreeQ[{a,b,c,d,e,f,g,A,B,C,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[B*e*g-C*(e*f+d*g),0]


Int[(a_.+b_.*Log[c_.*Sqrt[d_.+e_.*x_]/Sqrt[f_.+g_.*x_]])^n_./(A_.+C_.*x_^2),x_Symbol] :=
  g/(C*f)*Subst[Int[(a+b*Log[c*x])^n/x,x],x,Sqrt[d+e*x]/Sqrt[f+g*x]] /;
FreeQ[{a,b,c,d,e,f,g,A,C,n},x] && EqQ[C*d*f-A*e*g,0] && EqQ[e*f+d*g,0]


Int[RFx_.*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
  p*r*Int[RFx*Log[a+b*x],x] + 
  q*r*Int[RFx*Log[c+d*x],x] - 
  (p*r*Log[a+b*x]+q*r*Log[c+d*x] - Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r])*Int[RFx,x] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && RationalFunctionQ[RFx,x] && NeQ[b*c-a*d,0] && 
  Not[MatchQ[RFx,u_.*(a+b*x)^m_.*(c+d*x)^n_. /; IntegersQ[m,n]]]


(* Int[RFx_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.],x_Symbol] :=
  With[{u=IntHide[RFx,x]},  
  u*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r] - b*p*r*Int[u/(a+b*x),x] - d*q*r*Int[u/(c+d*x),x] /;
 NonsumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q,r},x] && RationalFunctionQ[RFx,x] && NeQ[b*c-a*d,0] *)


Int[RFx_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  With[{u=ExpandIntegrand[Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s,RFx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && RationalFunctionQ[RFx,x] && IGtQ[s,0]


Int[RFx_*Log[e_.*(f_.*(a_.+b_.*x_)^p_.*(c_.+d_.*x_)^q_.)^r_.]^s_.,x_Symbol] :=
  Unintegrable[RFx*Log[e*(f*(a+b*x)^p*(c+d*x)^q)^r]^s,x] /;
FreeQ[{a,b,c,d,e,f,p,q,r,s},x] && RationalFunctionQ[RFx,x]


Int[u_.*Log[e_.*(f_.*v_^p_.*w_^q_.)^r_.]^s_.,x_Symbol] :=
  Int[u*Log[e*(f*ExpandToSum[v,x]^p*ExpandToSum[w,x]^q)^r]^s,x] /;
FreeQ[{e,f,p,q,r,s},x] && LinearQ[{v,w},x] && Not[LinearMatchQ[{v,w},x]] && AlgebraicFunctionQ[u,x]


Int[u_.*Log[e_.*(f_.*(g_+v_./w_))^r_.]^s_.,x_Symbol] :=
  Int[u*Log[e*(f*ExpandToSum[v+g*w,x]/ExpandToSum[w,x])^r]^s,x] /;
FreeQ[{e,f,g,r,s},x] && LinearQ[w,x] && (FreeQ[v,x] || LinearQ[v,x]) && AlgebraicFunctionQ[u,x]


(* Int[Log[g_.*(h_.*(a_.+b_.*x_)^p_.)^q_.]*Log[i_.*(j_.*(c_.+d_.*x_)^r_.)^s_.]/(e_+f_.*x_),x_Symbol] :=
  1/f*Subst[Int[Log[g*(h*Simp[-(b*e-a*f)/f+b*x/f,x]^p)^q]*Log[i*(j*Simp[-(d*e-c*f)/f+d*x/f,x]^r)^s]/x,x],x,e+f*x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,j,p,q,r,s},x] *)





(* ::Subsection::Closed:: *)
(*3.5 Miscellaneous logarithms*)


Int[u_*Log[v_],x_Symbol] :=
  With[{w=DerivativeDivides[v,u*(1-v),x]},
  w*PolyLog[2,1-v] /;
 Not[FalseQ[w]]]


Int[(a_.+b_.*Log[u_])*Log[v_]*w_,x_Symbol] :=
  With[{z=DerivativeDivides[v,w*(1-v),x]},
  z*(a+b*Log[u])*PolyLog[2,1-v] - 
  b*Int[SimplifyIntegrand[z*PolyLog[2,1-v]*D[u,x]/u,x],x] /;
 Not[FalseQ[z]]] /;
FreeQ[{a,b},x] && InverseFunctionFreeQ[u,x]


Int[Log[c_.*Log[d_.*x_^n_.]^p_.],x_Symbol] :=
  x*Log[c*Log[d*x^n]^p] - n*p*Int[1/Log[d*x^n],x] /;
FreeQ[{c,d,n,p},x]


Int[(a_.+b_.*Log[c_.*Log[d_.*x_^n_.]^p_.])/x_,x_Symbol] :=
  Log[d*x^n]*(a+b*Log[c*Log[d*x^n]^p])/n - b*p*Log[x] /;
FreeQ[{a,b,c,d,n,p},x]


Int[(e_.*x_)^m_.*(a_.+b_.*Log[c_.*Log[d_.*x_^n_.]^p_.]),x_Symbol] :=
  (e*x)^(m+1)*(a+b*Log[c*Log[d*x^n]^p])/(e*(m+1)) - b*n*p/(m+1)*Int[(e*x)^m/Log[d*x^n],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NeQ[m,-1]


Int[(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  x*(a+b*Log[c*RFx^p])^n - 
  b*n*p*Int[SimplifyIntegrand[x*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x],x] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[(a_.+b_.*Log[c_.*RFx_^p_.])^n_./(d_.+e_.*x_),x_Symbol] :=
  Log[d+e*x]*(a+b*Log[c*RFx^p])^n/e - 
  b*n*p/e*Int[Log[d+e*x]*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x] /;
FreeQ[{a,b,c,d,e,p},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*Log[c*RFx^p])^n/(e*(m+1)) - 
  b*n*p/(e*(m+1))*Int[SimplifyIntegrand[(d+e*x)^(m+1)*(a+b*Log[c*RFx^p])^(n-1)*D[RFx,x]/RFx,x],x] /;
FreeQ[{a,b,c,d,e,m,p},x] && RationalFunctionQ[RFx,x] && IGtQ[n,0] && (EqQ[n,1] || IntegerQ[m]) && NeQ[m,-1]


Int[Log[c_.*RFx_^n_.]/(d_+e_.*x_^2),x_Symbol] :=
  With[{u=IntHide[1/(d+e*x^2),x]},  
  u*Log[c*RFx^n] - n*Int[SimplifyIntegrand[u*D[RFx,x]/RFx,x],x]] /;
FreeQ[{c,d,e,n},x] && RationalFunctionQ[RFx,x] && Not[PolynomialQ[RFx,x]]


Int[Log[c_.*Px_^n_.]/Qx_,x_Symbol] :=
  With[{u=IntHide[1/Qx,x]},  
  u*Log[c*Px^n] - n*Int[SimplifyIntegrand[u*D[Px,x]/Px,x],x]] /;
FreeQ[{c,n},x] && QuadraticQ[{Qx,Px},x] && EqQ[D[Px/Qx,x],0]


Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[(a+b*Log[c*RFx^p])^n,RGx,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && IGtQ[n,0]


Int[RGx_*(a_.+b_.*Log[c_.*RFx_^p_.])^n_.,x_Symbol] :=
  With[{u=ExpandIntegrand[RGx*(a+b*Log[c*RFx^p])^n,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,p},x] && RationalFunctionQ[RFx,x] && RationalFunctionQ[RGx,x] && IGtQ[n,0]


Int[RFx_*(a_.+b_.*Log[u_]),x_Symbol] :=
  With[{lst=SubstForFractionalPowerOfLinear[RFx*(a+b*Log[u]),x]},
  lst[[2]]*lst[[4]]*Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])] /;
 Not[FalseQ[lst]]] /;
FreeQ[{a,b},x] && RationalFunctionQ[RFx,x]


Int[(f_.+g_.*x_)^m_.*Log[1+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  -(f+g*x)^m*PolyLog[2,-e*(F^(c*(a+b*x)))^n]/(b*c*n*Log[F]) + 
  g*m/(b*c*n*Log[F])*Int[(f+g*x)^(m-1)*PolyLog[2,-e*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,e,f,g,n},x] && GtQ[m,0]


Int[(f_.+g_.*x_)^m_.*Log[d_+e_.*(F_^(c_.*(a_.+b_.*x_)))^n_.],x_Symbol] :=
  (f+g*x)^(m+1)*Log[d+e*(F^(c*(a+b*x)))^n]/(g*(m+1)) - 
  (f+g*x)^(m+1)*Log[1+e/d*(F^(c*(a+b*x)))^n]/(g*(m+1)) + 
  Int[(f+g*x)^m*Log[1+e/d*(F^(c*(a+b*x)))^n],x] /;
FreeQ[{F,a,b,c,d,e,f,g,n},x] && GtQ[m,0] && NeQ[d,1]


Int[Log[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  x*Log[d+e*x+f*Sqrt[a+b*x+c*x^2]] + 
  f^2*(b^2-4*a*c)/2*Int[x/((2*d*e-b*f^2)*(a+b*x+c*x^2)-f*(b*d-2*a*e+(2*c*d-b*e)*x)*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[e^2-c*f^2,0]


Int[Log[d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]],x_Symbol] :=
  x*Log[d+e*x+f*Sqrt[a+c*x^2]] - 
  a*c*f^2*Int[x/(d*e*(a+c*x^2)+f*(a*e-c*d*x)*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f},x] && EqQ[e^2-c*f^2,0]


Int[(g_.*x_)^m_.*Log[d_.+e_.*x_+f_.*Sqrt[a_.+b_.*x_+c_.*x_^2]],x_Symbol] :=
  (g*x)^(m+1)*Log[d+e*x+f*Sqrt[a+b*x+c*x^2]]/(g*(m+1)) + 
  f^2*(b^2-4*a*c)/(2*g*(m+1))*Int[(g*x)^(m+1)/((2*d*e-b*f^2)*(a+b*x+c*x^2)-f*(b*d-2*a*e+(2*c*d-b*e)*x)*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && EqQ[e^2-c*f^2,0] && NeQ[m,-1] && IntegerQ[2*m]


Int[(g_.*x_)^m_.*Log[d_.+e_.*x_+f_.*Sqrt[a_.+c_.*x_^2]],x_Symbol] :=
  (g*x)^(m+1)*Log[d+e*x+f*Sqrt[a+c*x^2]]/(g*(m+1)) - 
  a*c*f^2/(g*(m+1))*Int[(g*x)^(m+1)/(d*e*(a+c*x^2)+f*(a*e-c*d*x)*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f,g,m},x] && EqQ[e^2-c*f^2,0] && NeQ[m,-1] && IntegerQ[2*m]


Int[v_.*Log[d_.+e_.*x_+f_.*Sqrt[u_]],x_Symbol] :=
  Int[v*Log[d+e*x+f*Sqrt[ExpandToSum[u,x]]],x] /;
FreeQ[{d,e,f},x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]] && (EqQ[v,1] || MatchQ[v,(g_.*x)^m_. /; FreeQ[{g,m},x]])


Int[Log[u_],x_Symbol] :=
  x*Log[u] - Int[SimplifyIntegrand[x*D[u,x]/u,x],x] /;
InverseFunctionFreeQ[u,x]


Int[Log[u_],x_Symbol] :=
  x*Log[u] - Int[SimplifyIntegrand[x*Simplify[D[u,x]/u],x],x] /;
ProductQ[u]


Int[Log[u_]/(a_.+b_.*x_),x_Symbol] :=
  Log[a+b*x]*Log[u]/b -
  1/b*Int[SimplifyIntegrand[Log[a+b*x]*D[u,x]/u,x],x] /;
FreeQ[{a,b},x] && RationalFunctionQ[D[u,x]/u,x] && (NeQ[a,0] || Not[BinomialQ[u,x] && EqQ[BinomialDegree[u,x]^2,1]])


Int[(a_.+b_.*x_)^m_.*Log[u_],x_Symbol] :=
  (a+b*x)^(m+1)*Log[u]/(b*(m+1)) - 
  1/(b*(m+1))*Int[SimplifyIntegrand[(a+b*x)^(m+1)*D[u,x]/u,x],x] /;
FreeQ[{a,b,m},x] && InverseFunctionFreeQ[u,x] && NeQ[m,-1] (* && Not[FunctionOfQ[x^(m+1),u,x]] && FalseQ[PowerVariableExpn[u,m+1,x]] *)


Int[Log[u_]/Qx_,x_Symbol] :=
  With[{v=IntHide[1/Qx,x]},  
  v*Log[u] - Int[SimplifyIntegrand[v*D[u,x]/u,x],x]] /;
QuadraticQ[Qx,x] && InverseFunctionFreeQ[u,x]


Int[u_^(a_.*x_)*Log[u_],x_Symbol] :=
  u^(a*x)/a - Int[SimplifyIntegrand[x*u^(a*x-1)*D[u,x],x],x] /;
FreeQ[a,x] && InverseFunctionFreeQ[u,x]


Int[v_*Log[u_],x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[Log[u],w,x] - Int[SimplifyIntegrand[w*D[u,x]/u,x],x] /;
 InverseFunctionFreeQ[w,x]] /;
InverseFunctionFreeQ[u,x]


Int[v_*Log[u_],x_Symbol] :=
  With[{w=IntHide[v,x]},  
  Dist[Log[u],w,x] - Int[SimplifyIntegrand[w*Simplify[D[u,x]/u],x],x] /;
 InverseFunctionFreeQ[w,x]] /;
ProductQ[u]


Int[Log[v_]*Log[w_],x_Symbol] :=
  x*Log[v]*Log[w] - 
  Int[SimplifyIntegrand[x*Log[w]*D[v,x]/v,x],x] - 
  Int[SimplifyIntegrand[x*Log[v]*D[w,x]/w,x],x] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[u_*Log[v_]*Log[w_],x_Symbol] :=
  With[{z=IntHide[u,x]},  
  Dist[Log[v]*Log[w],z,x] - 
  Int[SimplifyIntegrand[z*Log[w]*D[v,x]/v,x],x] - 
  Int[SimplifyIntegrand[z*Log[v]*D[w,x]/w,x],x] /;
 InverseFunctionFreeQ[z,x]] /;
InverseFunctionFreeQ[v,x] && InverseFunctionFreeQ[w,x]


Int[f_^(a_.*Log[u_]),x_Symbol] :=
  Int[u^(a*Log[f]),x] /;
FreeQ[{a,f},x]


(* If[$LoadShowSteps,

Int[u_/x_,x_Symbol] :=
  With[{lst=FunctionOfLog[u,x]},
  ShowStep["","Int[F[Log[a*x^n]]/x,x]","Subst[Int[F[x],x],x,Log[a*x^n]]/n",Hold[
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]] /;
 Not[FalseQ[lst]]] /;
SimplifyFlag && NonsumQ[u],

Int[u_/x_,x_Symbol] :=
  With[{lst=FunctionOfLog[u,x]},
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
 Not[FalseQ[lst]]] /;
NonsumQ[u]] *)


If[$LoadShowSteps,

Int[u_,x_Symbol] :=
  With[{lst=FunctionOfLog[Cancel[x*u],x]},
  ShowStep["","Int[F[Log[a*x^n]]/x,x]","Subst[Int[F[x],x],x,Log[a*x^n]]/n",Hold[
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]] /;
 Not[FalseQ[lst]]] /;
SimplifyFlag && NonsumQ[u],

Int[u_,x_Symbol] :=
  With[{lst=FunctionOfLog[Cancel[x*u],x]},
  1/lst[[3]]*Subst[Int[lst[[1]],x],x,Log[lst[[2]]]] /;
 Not[FalseQ[lst]]] /;
NonsumQ[u]]


Int[u_.*Log[Gamma[v_]],x_Symbol] :=
  (Log[Gamma[v]]-LogGamma[v])*Int[u,x] + Int[u*LogGamma[v],x]


Int[u_.*(a_. w_+b_. w_*Log[v_]^n_.)^p_.,x_Symbol] :=
  Int[u*w^p*(a+b*Log[v]^n)^p,x] /;
FreeQ[{a,b,n},x] && IntegerQ[p]



