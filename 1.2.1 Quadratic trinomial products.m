(* ::Package:: *)

(* ::Section:: *)
(*1.2.1 Quadratic trinomial products integration rules*)


(* ::Subsection::Closed:: *)
(*1.2.1.1 (a+b x+c x^2)^p*)


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  2*(a+b*x+c*x^2)^(p+1)/((2*p+1)*(b+2*c*x)) /;
FreeQ[{a,b,c,p},x] && EqQ[b^2-4*a*c,0] && LtQ[p,-1]


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  (b/2+c*x)/Sqrt[a+b*x+c*x^2]*Int[1/(b/2+c*x),x] /;
FreeQ[{a,b,c},x] && EqQ[b^2-4*a*c,0]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) /;
FreeQ[{a,b,c,p},x] && EqQ[b^2-4*a*c,0] && NeQ[p,-1/2]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  1/c^p*Int[Simp[b/2-q/2+c*x,x]^p*Simp[b/2+q/2+c*x,x]^p,x]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && PerfectSquareQ[b^2-4*a*c]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && IGtQ[p,0] && Not[PerfectSquareQ[b^2-4*a*c]]


Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) -
  p*(b^2-4*a*c)/(2*c*(2*p+1))*Int[(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && IntegerQ[4*p]


Int[1/(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
  -2*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2]) /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) -
  2*c*(2*p+3)/((p+1)*(b^2-4*a*c))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && NeQ[p,-3/2] && IntegerQ[4*p]


Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[1/Simp[b/2-q/2+c*x,x],x] - c/q*Int[1/Simp[b/2+q/2+c*x,x],x]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && PosQ[b^2-4*a*c] && PerfectSquareQ[b^2-4*a*c]


Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=1-4*Simplify[a*c/b^2]},
  -2/b*Subst[Int[1/(q-x^2),x],x,1+2*c*x/b] /;
 RationalQ[q] && (EqQ[q^2,1] || Not[RationalQ[b^2-4*a*c]])] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]


Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  -2*Subst[Int[1/Simp[b^2-4*a*c-x^2,x],x],x,b+2*c*x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  1/(2*c*(-4*c/(b^2-4*a*c))^p)*Subst[Int[Simp[1-x^2/(b^2-4*a*c),x]^p,x],x,b+2*c*x] /;
FreeQ[{a,b,c,p},x] && GtQ[4*a-b^2/c,0]


Int[1/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
  2*Subst[Int[1/(1-c*x^2),x],x,x/Sqrt[b*x+c*x^2]] /;
FreeQ[{b,c},x]


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*Subst[Int[1/(4*c-x^2),x],x,(b+2*c*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0]


Int[(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b*x+c*x^2)^p/(-c*(b*x+c*x^2)/(b^2))^p*Int[(-c*x/b-c^2*x^2/b^2)^p,x] /;
FreeQ[{b,c},x] && RationalQ[p] && 3<=Denominator[p]<=4


(* Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^p/(-c*(a+b*x+c*x^2)/(b^2-4*a*c))^p*Int[(-a*c/(b^2-4*a*c)-b*c*x/(b^2-4*a*c)-c^2*x^2/(b^2-4*a*c))^p,x] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && RationalQ[p] && 3<=Denominator[p]<=4 *)


Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{d=Denominator[p]},
  d*Sqrt[(b+2*c*x)^2]/(b+2*c*x)*Subst[Int[x^(d*(p+1)-1)/Sqrt[b^2-4*a*c+4*c*x^d],x],x,(a+b*x+c*x^2)^(1/d)] /;
 3<=d<=4] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && RationalQ[p]


Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(a+b*x+c*x^2)^(p+1)/(q*(p+1)*((q-b-2*c*x)/(2*q))^(p+1))*Hypergeometric2F1[-p,p+1,p+2,(b+q+2*c*x)/(2*q)]] /;
FreeQ[{a,b,c,p},x] && NeQ[b^2-4*a*c,0] && Not[IntegerQ[4*p]]


Int[(a_.+b_.*u_+c_.*u_^2)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,p},x] && LinearQ[u,x] && NeQ[u,x]





(* ::Subsection::Closed:: *)
(*1.2.1.2 (d+e x)^m (a+b x+c x^2)^p*)


(* Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  1/c^p*Int[(d+e*x)^m*(b/2+c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m},x] && EqQ[b^2-4*a*c,0] && IntegerQ[p] *)


(* Int[(d_+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  d/b*Subst[Int[x^p,x],x,a+b*x+c*x^2] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[2*c*d-b*e,0] *)


Int[(d_+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(p+1)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0] && IGtQ[p,0] && EqQ[c*d^2-b*d*e+a*e^2,0]


Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0] && IGtQ[p,0]


Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (c*d-e*(b/2-q/2))/q*Int[1/(b/2-q/2+c*x),x] - (c*d-e*(b/2+q/2))/q*Int[1/(b/2+q/2+c*x),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0] && NeQ[b^2-4*a*c,0] && NiceSqrtQ[b^2-4*a*c]


Int[(d_+e_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (e/2+c*d/(2*q))*Int[1/(-q+c*x),x] + (e/2-c*d/(2*q))*Int[1/(q+c*x),x]] /;
FreeQ[{a,c,d,e},x] && NiceSqrtQ[-a*c]


Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(* (d-b*e/(2*c))*Int[1/(a+b*x+c*x^2),x] + *)
  (2*c*d-b*e)/(2*c)*Int[1/(a+b*x+c*x^2),x] + e/(2*c)*Int[(b+2*c*x)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0] && NeQ[b^2-4*a*c,0] && Not[NiceSqrtQ[b^2-4*a*c]]


Int[(d_+e_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  d*Int[1/(a+c*x^2),x] + e*Int[x/(a+c*x^2),x] /;
FreeQ[{a,c,d,e},x] && Not[NiceSqrtQ[-a*c]]


Int[(d_.+e_.*x_)/(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
  -2*(b*d-2*a*e+(2*c*d-b*e)*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2]) /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0] && NeQ[b^2-4*a*c,0]


Int[(d_+e_.*x_)/(a_+c_.*x_^2)^(3/2),x_Symbol] :=
  (-a*e+c*d*x)/(a*c*Sqrt[a+c*x^2]) /;
FreeQ[{a,c,d,e},x]


Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b*d-2*a*e+(2*c*d-b*e)*x)/((p+1)*(b^2-4*a*c))*(a+b*x+c*x^2)^(p+1) - 
  (2*p+3)*(2*c*d-b*e)/((p+1)*(b^2-4*a*c))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && NeQ[p,-3/2]


Int[(d_+e_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a*e-c*d*x)/(2*a*c*(p+1))*(a+c*x^2)^(p+1) + 
  d*(2*p+3)/(2*a*(p+1))*Int[(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && LtQ[p,-1] && NeQ[p,-3/2]


Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) + (2*c*d-b*e)/(2*c)*Int[(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[2*c*d-b*e,0] && NeQ[p,-1]


Int[(d_+e_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(a+c*x^2)^(p+1)/(2*c*(p+1)) + d*Int[(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && NeQ[p,-1]


Int[(d_+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^m/c^(m/2)*Int[(a+b*x+c*x^2)^(p+m/2),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && EqQ[2*c*d-b*e,0] && IntegerQ[m/2]


Int[(d_+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^(m-1)/c^((m-1)/2)*Int[(d+e*x)*(a+b*x+c*x^2)^(p+(m-1)/2),x] /;
FreeQ[{a,b,c,d,e,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && EqQ[2*c*d-b*e,0] && IntegerQ[(m-1)/2]


Int[(d_+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^p/(d+e*x)^(2*p)*Int[(d+e*x)^(m+2*p),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && EqQ[2*c*d-b*e,0] && Not[IntegerQ[m]]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p]))*
    Int[ExpandLinearProduct[(b/2+c*x)^(2*p),(d+e*x)^m,b/2,c,x],x] /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && NeQ[2*c*d-b*e,0] && IGtQ[m,0] && EqQ[m-2*p+1,0]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p]))*Int[(d+e*x)^m*(b/2+c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]] && NeQ[2*c*d-b*e,0]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && EqQ[c*d^2+a*e^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[d,0] && IntegerQ[m+p])


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+p,0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(p+1)) /;
FreeQ[{a,c,d,e,m,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+p,0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*c*d-b*e)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+2*p+2,0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) /;
FreeQ[{a,c,d,e,m,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+2*p+2,0]


Int[(d_.+e_.*x_)^2*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) - e^2*(p+2)/(c*(p+1))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && LtQ[p,-1]


Int[(d_+e_.*x_)^2*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)*(a+c*x^2)^(p+1)/(c*(p+1)) - e^2*(p+2)/(c*(p+1))*Int[(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && LtQ[p,-1]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(a+b*x+c*x^2)^(m+p)/(a/d+c*x/e)^m,x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && IntegerQ[m] && 
  RationalQ[p] && (LtQ[0,-m,p] || LtQ[p,-m,0]) && NeQ[m,2] && NeQ[m,-1]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  d^(2*m)/a^m*Int[(a+c*x^2)^(m+p)/(d-e*x)^m,x] /;
FreeQ[{a,c,d,e,m,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && IntegerQ[m] && 
  RationalQ[p] && (LtQ[0,-m,p] || LtQ[p,-m,0]) && NeQ[m,2] && NeQ[m,-1]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  Simplify[m+p]*(2*c*d-b*e)/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && IGtQ[Simplify[m+p],0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  2*c*d*Simplify[m+p]/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && IGtQ[Simplify[m+p],0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((m+p+1)*(2*c*d-b*e)) + 
  c*Simplify[m+2*p+2]/((m+p+1)*(2*c*d-b*e))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[Simplify[m+2*p+2],0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) + 
  Simplify[m+2*p+2]/(2*d*(m+p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[Simplify[m+2*p+2],0]


Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  2*e*Subst[Int[1/(2*c*d-b*e+e^2*x^2),x],x,Sqrt[a+b*x+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0]


Int[1/(Sqrt[d_+e_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  2*e*Subst[Int[1/(2*c*d+e^2*x^2),x],x,Sqrt[a+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+p+1)) - 
  c*p/(e^2*(m+p+1))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && GtQ[p,0] && (LtQ[m,-2] || EqQ[m+2*p+1,0]) && NeQ[m+p+1,0] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+p+1)) - 
  c*p/(e^2*(m+p+1))*Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && GtQ[p,0] && (LtQ[m,-2] || EqQ[m+2*p+1,0]) && NeQ[m+p+1,0] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  p*(2*c*d-b*e)/(e^2*(m+2*p+1))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && GtQ[p,0] && (LeQ[-2,m,0] || EqQ[m+p+1,0]) && NeQ[m+2*p+1,0] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+2*p+1)) - 
  2*c*d*p/(e^2*(m+2*p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && GtQ[p,0] && (LeQ[-2,m,0] || EqQ[m+p+1,0]) && NeQ[m+2*p+1,0] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (2*c*d-b*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) - 
  (2*c*d-b*e)*(m+2*p+2)/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && LtQ[0,m,1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -d*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*e*(p+1)) + 
  d*(m+2*p+2)/(2*a*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && LtQ[p,-1] && LtQ[0,m,1] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) - 
  e^2*(m+p)/(c*(p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(p+1)) - 
  e^2*(m+p)/(c*(p+1))*Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2+a*e^2,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  (m+p)*(2*c*d-b*e)/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  2*c*d*(m+p)/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && EqQ[c*d^2+a*e^2,0] && GtQ[m,1] && NeQ[m+2*p+1,0] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((m+p+1)*(2*c*d-b*e)) + 
  c*(m+2*p+2)/((m+p+1)*(2*c*d-b*e))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[m,0] && NeQ[m+p+1,0] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) + 
  (m+2*p+2)/(2*d*(m+p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && EqQ[c*d^2+a*e^2,0] && LtQ[m,0] && NeQ[m+p+1,0] && IntegerQ[2*p]


Int[(e_.*x_)^m_*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (e*x)^m*(b*x+c*x^2)^p/(x^(m+p)*(b+c*x)^p)*Int[x^(m+p)*(b+c*x)^p,x] /;
FreeQ[{b,c,e,m},x] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && GtQ[a,0] && GtQ[d,0] && Not[IGtQ[m,0]]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  a^(p+1)*d^(m-1)*((d-e*x)/d)^(p+1)/(a/d+c*x/e)^(p+1)*Int[(1+e*x/d)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && (IntegerQ[m] || GtQ[d,0]) && GtQ[a,0] && 
  Not[IGtQ[m,0] && (IntegerQ[3*p] || IntegerQ[4*p])]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  d^m*(a+b*x+c*x^2)^FracPart[p]/((1+e*x/d)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(1+e*x/d)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && (IntegerQ[m] || GtQ[d,0]) && 
  Not[IGtQ[m,0] && (IntegerQ[3*p] || IntegerQ[4*p])]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  d^(m-1)*(a+c*x^2)^(p+1)/((1+e*x/d)^(p+1)*(a/d+(c*x)/e)^(p+1))*Int[(1+e*x/d)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && (IntegerQ[m] || GtQ[d,0]) && Not[IGtQ[m,0] && (IntegerQ[3*p] || IntegerQ[4*p])]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  d^IntPart[m]*(d+e*x)^FracPart[m]/(1+e*x/d)^FracPart[m]*Int[(1+e*x/d)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && Not[IntegerQ[m] || GtQ[d,0]]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  d^IntPart[m]*(d+e*x)^FracPart[m]/(1+e*x/d)^FracPart[m]*Int[(1+e*x/d)^m*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && Not[IntegerQ[m] || GtQ[d,0]]


Int[1/((d_+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  -4*b*c/(d*(b^2-4*a*c))*Int[1/(b+2*c*x),x] + 
  b^2/(d^2*(b^2-4*a*c))*Int[(d+e*x)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*c*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && EqQ[m+2*p+3,0] && NeQ[p,-1]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && IGtQ[p,0] && Not[EqQ[m,3] && NeQ[p,1]]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  b*p/(d*e*(m+1))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && GtQ[p,0] && LtQ[m,-1] && 
  Not[IntegerQ[m/2] && LtQ[m+2*p+3,0]] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  d*p*(b^2-4*a*c)/(b*e*(m+2*p+1))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && GtQ[p,0] && 
  Not[LtQ[m,-1]] && Not[IGtQ[(m-1)/2,0] && (Not[IntegerQ[p]] || LtQ[m,2*p])] && RationalQ[m] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  d*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)) - 
  d*e*(m-1)/(b*(p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && LtQ[p,-1] && GtQ[m,1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*c*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) - 
  2*c*e*(m+2*p+3)/(e*(p+1)*(b^2-4*a*c))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && LtQ[p,-1] && Not[GtQ[m,1]] && RationalQ[m] && IntegerQ[2*p]


Int[1/((d_+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  4*c*Subst[Int[1/(b^2*e-4*a*c*e+4*c*e*x^2),x],x,Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0]


Int[1/(Sqrt[d_+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  4/e*Sqrt[-c/(b^2-4*a*c)]*Subst[Int[1/Sqrt[Simp[1-b^2*x^4/(d^2*(b^2-4*a*c)),x]],x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && LtQ[c/(b^2-4*a*c),0]


Int[Sqrt[d_+e_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  4/e*Sqrt[-c/(b^2-4*a*c)]*Subst[Int[x^2/Sqrt[Simp[1-b^2*x^4/(d^2*(b^2-4*a*c)),x]],x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && LtQ[c/(b^2-4*a*c),0]


Int[(d_+e_.*x_)^m_/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  Sqrt[-c*(a+b*x+c*x^2)/(b^2-4*a*c)]/Sqrt[a+b*x+c*x^2]*
    Int[(d+e*x)^m/Sqrt[-a*c/(b^2-4*a*c)-b*c*x/(b^2-4*a*c)-c^2*x^2/(b^2-4*a*c)],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && EqQ[m^2,1/4]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*d*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(b*(m+2*p+1)) + 
  d^2*(m-1)*(b^2-4*a*c)/(b^2*(m+2*p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && GtQ[m,1] && 
  NeQ[m+2*p+1,0] && (IntegerQ[2*p] || IntegerQ[m] && RationalQ[p] || OddQ[m])


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -2*b*d*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(d^2*(m+1)*(b^2-4*a*c)) + 
  b^2*(m+2*p+3)/(d^2*(m+1)*(b^2-4*a*c))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0] && NeQ[m+2*p+3,0] && LtQ[m,-1] && 
  (IntegerQ[2*p] || IntegerQ[m] && RationalQ[p] || IntegerQ[(m+2*p+3)/2])


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  1/e*Subst[Int[x^m*(a-b^2/(4*c)+(c*x^2)/e^2)^p,x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[2*c*d-b*e,0]


Int[1/((d_+e_.*x_)*(a_.+c_.*x_^2)^(1/4)),x_Symbol] :=
  1/(2*(-a)^(1/4)*e)*ArcTan[(-1-c*x^2/a)^(1/4)/(1-c*d*x/(2*a*e)-Sqrt[-1-c*x^2/a])] + 
  1/(4*(-a)^(1/4)*e)*Log[(1-c*d*x/(2*a*e)+Sqrt[-1-c*x^2/a]-(-1-c*x^2/a)^(1/4))/
    (1-c*d*x/(2*a*e)+Sqrt[-1-c*x^2/a]+(-1-c*x^2/a)^(1/4))] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2+2*a*e^2,0] && LtQ[a,0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && IGtQ[p,0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,m},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && Not[EqQ[m,1] && GtQ[p,1]] 


(* Int[Sqrt[d_.+e_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[(c*d^2-b*d*e+a*e^2)/c,2]},
  1/2*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x] + 
  1/2*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && LtQ[b^2-4*a*c,0] *)


(* Int[Sqrt[d_+e_.*x_]/(a_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[(c*d^2+a*e^2)/c,2]},
  1/2*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x] + 
  1/2*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && LtQ[-a*c,0] *)


(* Int[Sqrt[d_.+e_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-b*e+e*q)/q*Int[1/(Sqrt[d+e*x]*(b-q+2*c*x)),x] - 
  (2*c*d-b*e-e*q)/q*Int[1/(Sqrt[d+e*x]*(b+q+2*c*x)),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] (* && Not[LtQ[b^2-4*a*c,0]] *) *)


(* Int[Sqrt[d_+e_.*x_]/(a_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (c*d+e*q)/(2*q)*Int[1/(Sqrt[d+e*x]*(-q+c*x)),x] - 
  (c*d-e*q)/(2*q)*Int[1/(Sqrt[d+e*x]*(+q+c*x)),x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] (* && Not[LtQ[-a*c,0]] *) *)


Int[Sqrt[d_.+e_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  2*e*Subst[Int[x^2/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0]


Int[Sqrt[d_+e_.*x_]/(a_+c_.*x_^2),x_Symbol] :=
  2*e*Subst[Int[x^2/(c*d^2+a*e^2-2*c*d*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[PolynomialDivide[(d+e*x)^m,a+b*x+c*x^2,x],x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && IGtQ[m,1] && (NeQ[d,0] || GtQ[m,2])


Int[(d_+e_.*x_)^m_/(a_+c_.*x_^2),x_Symbol] :=
  Int[PolynomialDivide[(d+e*x)^m,a+c*x^2,x],x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[m,1] && (NeQ[d,0] || GtQ[m,2])


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m-1)/(c*(m-1)) + 
  1/c*Int[(d+e*x)^(m-2)*Simp[c*d^2-a*e^2+e*(2*c*d-b*e)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && GtQ[m,1]


Int[(d_+e_.*x_)^m_/(a_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m-1)/(c*(m-1)) + 
  1/c*Int[(d+e*x)^(m-2)*Simp[c*d^2-a*e^2+2*c*d*e*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && GtQ[m,1]


Int[1/((d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  e^2/(c*d^2-b*d*e+a*e^2)*Int[1/(d+e*x),x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(c*d-b*e-c*e*x)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0]


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)),x_Symbol] :=
  e^2/(c*d^2+a*e^2)*Int[1/(d+e*x),x] + 
  1/(c*d^2+a*e^2)*Int[(c*d-c*e*x)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


(* Int[1/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  With[{q=Rt[(c*d^2-b*d*e+a*e^2)/c,2]},
  1/(2*q)*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x] - 
  1/(2*q)*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && LtQ[b^2-4*a*c,0] *)


(* Int[1/(Sqrt[d_+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  With[{q=Rt[(c*d^2+a*e^2)/c,2]},
  1/(2*q)*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x] - 
  1/(2*q)*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && LtQ[-a*c,0] *)


(* Int[1/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(Sqrt[d+e*x]*(b-q+2*c*x)),x] - 
  2*c/q*Int[1/(Sqrt[d+e*x]*(b+q+2*c*x)),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] (* && Not[LtQ[b^2-4*a*c,0]] *) *)


(* Int[1/(Sqrt[d_+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  c/(2*q)*Int[1/(Sqrt[d+e*x]*(-q+c*x)),x] - 
  c/(2*q)*Int[1/(Sqrt[d+e*x]*(q+c*x)),x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] (* && Not[LtQ[-a*c,0]] *) *)


Int[1/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  2*e*Subst[Int[1/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0]


Int[1/(Sqrt[d_+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  2*e*Subst[Int[1/(c*d^2+a*e^2-2*c*d*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x)^(m+1)*Simp[c*d-b*e-c*e*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && LtQ[m,-1]


Int[(d_+e_.*x_)^m_/(a_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m+1)/((m+1)*(c*d^2+a*e^2)) + 
  c/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*(d-e*x)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,m},x] && NeQ[c*d^2+a*e^2,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,1/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && Not[IntegerQ[m]]


Int[(d_+e_.*x_)^m_/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,1/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,m},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[m]]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^FracPart[p]*(a+b*x+c*x^2)^FracPart[p]/(a*d+c*e*x^3)^FracPart[p]*Int[(d+e*x)^(m-p)*(a*d+c*e*x^3)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b*d+a*e,0] && EqQ[c*d+b*e,0] && IGtQ[m-p+1,0] && Not[IntegerQ[p]]


Int[(d_.+e_.*x_)^m_/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
  Int[(d+e*x)^m/(Sqrt[b*x]*Sqrt[1+c/b*x]),x] /;
FreeQ[{b,c,d,e},x] && NeQ[c*d-b*e,0] && NeQ[2*c*d-b*e,0] && EqQ[m^2,1/4] && LtQ[c,0] && RationalQ[b]


Int[(d_.+e_.*x_)^m_/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
  Sqrt[x]*Sqrt[b+c*x]/Sqrt[b*x+c*x^2]*Int[(d+e*x)^m/(Sqrt[x]*Sqrt[b+c*x]),x] /;
FreeQ[{b,c,d,e},x] && NeQ[c*d-b*e,0] && NeQ[2*c*d-b*e,0] && EqQ[m^2,1/4]


Int[x_^m_/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*Subst[Int[x^(2*m+1)/Sqrt[a+b*x^2+c*x^4],x],x,Sqrt[x]] /;
FreeQ[{a,b,c},x] && NeQ[b^2-4*a*c,0] && EqQ[m^2,1/4]


Int[(e_*x_)^m_/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  (e*x)^m/x^m*Int[x^m/Sqrt[a+b*x+c*x^2], x] /;
FreeQ[{a,b,c,e},x] && NeQ[b^2-4*a*c,0] && EqQ[m^2,1/4]


Int[(d_.+e_.*x_)^m_/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*Rt[b^2-4*a*c,2]*(d+e*x)^m*Sqrt[-c*(a+b*x+c*x^2)/(b^2-4*a*c)]/
    (c*Sqrt[a+b*x+c*x^2]*(2*c*(d+e*x)/(2*c*d-b*e-e*Rt[b^2-4*a*c,2]))^m)*
    Subst[Int[(1+2*e*Rt[b^2-4*a*c,2]*x^2/(2*c*d-b*e-e*Rt[b^2-4*a*c,2]))^m/Sqrt[1-x^2],x],x,
      Sqrt[(b+Rt[b^2-4*a*c,2]+2*c*x)/(2*Rt[b^2-4*a*c,2])]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && EqQ[m^2,1/4]


Int[(d_+e_.*x_)^m_/Sqrt[a_+c_.*x_^2],x_Symbol] :=
  2*a*Rt[-c/a,2]*(d+e*x)^m*Sqrt[1+c*x^2/a]/(c*Sqrt[a+c*x^2]*(c*(d+e*x)/(c*d-a*e*Rt[-c/a,2]))^m)*
    Subst[Int[(1+2*a*e*Rt[-c/a,2]*x^2/(c*d-a*e*Rt[-c/a,2]))^m/Sqrt[1-x^2],x],x,Sqrt[(1-Rt[-c/a,2]*x)/2]] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && EqQ[m^2,1/4]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^p/(2*(m+1)*(c*d^2-b*d*e+a*e^2)) + 
  p*(b^2-4*a*c)/(2*(m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && EqQ[m+2*p+2,0] && GtQ[p,0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(-2*a*e+(2*c*d)*x)*(a+c*x^2)^p/(2*(m+1)*(c*d^2+a*e^2)) - 
  4*a*c*p/(2*(m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && EqQ[m+2*p+2,0] && GtQ[p,0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) - 
  2*(2*p+3)*(c*d^2-b*d*e+a*e^2)/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && EqQ[m+2*p+2,0] && LtQ[p,-1]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(a*e-c*d*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) + 
  (2*p+3)*(c*d^2+a*e^2)/(2*a*c*(p+1))*Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && EqQ[m+2*p+2,0] && LtQ[p,-1]


Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -2*Subst[Int[1/(4*c*d^2-4*b*d*e+4*a*e^2-x^2),x],x,(2*a*e-b*d-(2*c*d-b*e)*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[2*c*d-b*e,0]


Int[1/((d_+e_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  -Subst[Int[1/(c*d^2+a*e^2-x^2),x],x,(a*e-c*d*x)/Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e},x]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(b-Rt[b^2-4*a*c,2]+2*c*x)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/
    ((m+1)*(2*c*d-b*e+e*Rt[b^2-4*a*c,2])*
      ((2*c*d-b*e+e*Rt[b^2-4*a*c,2])*(b+Rt[b^2-4*a*c,2]+2*c*x)/((2*c*d-b*e-e*Rt[b^2-4*a*c,2])*(b-Rt[b^2-4*a*c,2]+2*c*x)))^p)*
    Hypergeometric2F1[m+1,-p,m+2,-4*c*Rt[b^2-4*a*c,2]*(d+e*x)/((2*c*d-b*e-e*Rt[b^2-4*a*c,2])*(b-Rt[b^2-4*a*c,2]+2*c*x))] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && Not[IntegerQ[p]] && EqQ[m+2*p+2,0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (Rt[-a*c,2]-c*x)*(d+e*x)^(m+1)*(a+c*x^2)^p/
    ((m+1)*(c*d+e*Rt[-a*c,2])*((c*d+e*Rt[-a*c,2])*(Rt[-a*c,2]+c*x)/((c*d-e*Rt[-a*c,2])*(-Rt[-a*c,2]+c*x)))^p)*
    Hypergeometric2F1[m+1,-p,m+2,2*c*Rt[-a*c,2]*(d+e*x)/((c*d-e*Rt[-a*c,2])*(Rt[-a*c,2]-c*x))] /;
FreeQ[{a,c,d,e,m,p},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+2*p+2,0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  m*(2*c*d-b*e)/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && EqQ[m+2*p+3,0] && LtQ[p,-1]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^m*(2*c*x)*(a+c*x^2)^(p+1)/(4*a*c*(p+1)) - 
  m*(2*c*d)/(4*a*c*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,m,p},x] && NeQ[c*d^2+a*e^2,0] && EqQ[m+2*p+3,0] && LtQ[p,-1]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  (2*c*d-b*e)/(2*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && EqQ[m+2*p+3,0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  c*d/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NeQ[c*d^2+a*e^2,0] && EqQ[m+2*p+3,0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  p/(e*(m+1))*Int[(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && GtQ[p,0] && 
  (IntegerQ[p] || LtQ[m,-1]) && NeQ[m,-1] && Not[ILtQ[m+2*p+1,0]] && IntQuadraticQ[a,b,c,d,e,m,p,x]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+1)) - 
  2*c*p/(e*(m+1))*Int[x*(d+e*x)^(m+1)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,m},x] && NeQ[c*d^2+a*e^2,0] && GtQ[p,0] && 
  (IntegerQ[p] || LtQ[m,-1]) && NeQ[m,-1] && Not[ILtQ[m+2*p+1,0]] && IntQuadraticQ[a,0,c,d,e,m,p,x]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  p/(e*(m+2*p+1))*Int[(d+e*x)^m*Simp[b*d-2*a*e+(2*c*d-b*e)*x,x]*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && GtQ[p,0] && 
  NeQ[m+2*p+1,0] && (Not[RationalQ[m]] || LtQ[m,1]) && Not[ILtQ[m+2*p,0]] && IntQuadraticQ[a,b,c,d,e,m,p,x]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+2*p+1)) + 
  2*p/(e*(m+2*p+1))*Int[(d+e*x)^m*Simp[a*e-c*d*x,x]*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,m},x] && NeQ[c*d^2+a*e^2,0] && GtQ[p,0] && 
  NeQ[m+2*p+1,0] && (Not[RationalQ[m]] || LtQ[m,1]) && Not[ILtQ[m+2*p,0]] && IntQuadraticQ[a,0,c,d,e,m,p,x]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) - 
  1/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(b*e*m+2*c*d*(2*p+3)+2*c*e*(m+2*p+3)*x)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && 
  LtQ[p,-1] && GtQ[m,0] && (LtQ[m,1] || ILtQ[m+2*p+3,0] && NeQ[m,2]) && IntQuadraticQ[a,b,c,d,e,m,p,x]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -x*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*(p+1)) + 
  1/(2*a*(p+1))*Int[(d+e*x)^(m-1)*(d*(2*p+3)+e*(m+2*p+3)*x)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && 
  LtQ[p,-1] && GtQ[m,0] && (LtQ[m,1] || ILtQ[m+2*p+3,0] && NeQ[m,2]) && IntQuadraticQ[a,0,c,d,e,m,p,x]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*
    Int[(d+e*x)^(m-2)*
      Simp[e*(2*a*e*(m-1)+b*d*(2*p-m+4))-2*c*d^2*(2*p+3)+e*(b*e-2*d*c)*(m+2*p+2)*x,x]*
      (a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && LtQ[p,-1] && GtQ[m,1] && IntQuadraticQ[a,b,c,d,e,m,p,x]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(a*e-c*d*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) + 
  1/((p+1)*(-2*a*c))*
    Int[(d+e*x)^(m-2)*Simp[a*e^2*(m-1)-c*d^2*(2*p+3)-d*c*e*(m+2*p+2)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && GtQ[m,1] && IntQuadraticQ[a,0,c,d,e,m,p,x]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(b*c*d-b^2*e+2*a*c*e+c*(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) + 
  1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^m*
      Simp[b*c*d*e*(2*p-m+2)+b^2*e^2*(m+p+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3)-c*e*(2*c*d-b*e)*(m+2*p+4)*x,x]*
      (a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && LtQ[p,-1] && IntQuadraticQ[a,b,c,d,e,m,p,x]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(a*e+c*d*x)*(a+c*x^2)^(p+1)/(2*a*(p+1)*(c*d^2+a*e^2)) + 
  1/(2*a*(p+1)*(c*d^2+a*e^2))*
    Int[(d+e*x)^m*Simp[c*d^2*(2*p+3)+a*e^2*(m+2*p+3)+c*e*d*(m+2*p+4)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,m},x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && IntQuadraticQ[a,0,c,d,e,m,p,x]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  1/(c*(m+2*p+1))*
    Int[(d+e*x)^(m-2)*
      Simp[c*d^2*(m+2*p+1)-e*(a*e*(m-1)+b*d*(p+1))+e*(2*c*d-b*e)*(m+p)*x,x]*
      (a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && 
  If[RationalQ[m], GtQ[m,1], SumSimplerQ[m,-2]] && NeQ[m+2*p+1,0] && IntQuadraticQ[a,b,c,d,e,m,p,x]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  1/(c*(m+2*p+1))*
    Int[(d+e*x)^(m-2)*Simp[c*d^2*(m+2*p+1)-a*e^2*(m-1)+2*c*d*e*(m+p)*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NeQ[c*d^2+a*e^2,0] && 
  If[RationalQ[m], GtQ[m,1], SumSimplerQ[m,-2]] && NeQ[m+2*p+1,0] && IntQuadraticQ[a,0,c,d,e,m,p,x]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^(m+1)*Simp[c*d*(m+1)-b*e*(m+p+2)-c*e*(m+2*p+3)*x,x]*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && NeQ[m,-1] && 
  (LtQ[m,-1] && IntQuadraticQ[a,b,c,d,e,m,p,x] || SumSimplerQ[m,1] && IntegerQ[p] || ILtQ[Simplify[m+2*p+3],0])


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  c/((m+1)*(c*d^2+a*e^2))*
    Int[(d+e*x)^(m+1)*Simp[d*(m+1)-e*(m+2*p+3)*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NeQ[c*d^2+a*e^2,0] && NeQ[m,-1] && 
  (LtQ[m,-1] && IntQuadraticQ[a,0,c,d,e,m,p,x] || SumSimplerQ[m,1] && IntegerQ[p] || ILtQ[Simplify[m+2*p+3],0])


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(1/4)),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*(a+c*x^2)^(1/4)),x] - e*Int[x/((d^2-e^2*x^2)*(a+c*x^2)^(1/4)),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(3/4)),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*(a+c*x^2)^(3/4)),x] - e*Int[x/((d^2-e^2*x^2)*(a+c*x^2)^(3/4)),x] /;
FreeQ[{a,c,d,e},x] && NeQ[c*d^2+a*e^2,0]


Int[(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  1/(-4*c/(b^2-4*a*c))^p*Subst[Int[Simp[1-x^2/(b^2-4*a*c),x]^p/Simp[2*c*d-b*e+e*x,x],x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,p},x] && GtQ[4*a-b^2/c,0] && IntegerQ[4*p]


Int[(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  (a+b*x+c*x^2)^p/(-c*(a+b*x+c*x^2)/(b^2-4*a*c))^p*
    Int[(-a*c/(b^2-4*a*c)-b*c*x/(b^2-4*a*c)-c^2*x^2/(b^2-4*a*c))^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,p},x] && Not[GtQ[4*a-b^2/c,0]] && IntegerQ[4*p]


Int[1/((d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^(1/3)),x_Symbol] :=
  With[{q=Rt[3*c*e^2*(2*c*d-b*e),3]},
  -Sqrt[3]*c*e*ArcTan[1/Sqrt[3]+2*(c*d-b*e-c*e*x)/(Sqrt[3]*q*(a+b*x+c*x^2)^(1/3))]/q^2 - 
  3*c*e*Log[d+e*x]/(2*q^2) + 
  3*c*e*Log[c*d-b*e-c*e*x-q*(a+b*x+c*x^2)^(1/3)]/(2*q^2)] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0] && EqQ[c^2*d^2-b*c*d*e+b^2*e^2-3*a*c*e^2,0] && PosQ[c*e^2*(2*c*d-b*e)]


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(1/3)),x_Symbol] :=
  With[{q=Rt[6*c^2*e^2/d^2,3]},
  -Sqrt[3]*c*e*ArcTan[1/Sqrt[3]+2*c*(d-e*x)/(Sqrt[3]*d*q*(a+c*x^2)^(1/3))]/(d^2*q^2) - 
  3*c*e*Log[d+e*x]/(2*d^2*q^2) + 
  3*c*e*Log[c*d-c*e*x-d*q*(a+c*x^2)^(1/3)]/(2*d^2*q^2)] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2-3*a*e^2,0]


Int[1/((d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^(1/3)),x_Symbol] :=
  With[{q=Rt[-3*c*e^2*(2*c*d-b*e),3]},
  -Sqrt[3]*c*e*ArcTan[1/Sqrt[3]-2*(c*d-b*e-c*e*x)/(Sqrt[3]*q*(a+b*x+c*x^2)^(1/3))]/q^2 - 
  3*c*e*Log[d+e*x]/(2*q^2) + 
  3*c*e*Log[c*d-b*e-c*e*x+q*(a+b*x+c*x^2)^(1/3)]/(2*q^2)] /;
FreeQ[{a,b,c,d,e},x] && NeQ[2*c*d-b*e,0] && EqQ[c^2*d^2-b*c*d*e+b^2*e^2-3*a*c*e^2,0] && NegQ[c*e^2*(2*c*d-b*e)]


(* Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(1/3)),x_Symbol] :=
  With[{q=Rt[-6*c^2*d*e^2,3]},
  -Sqrt[3]*c*e*ArcTan[1/Sqrt[3]-2*(c*d-c*e*x)/(Sqrt[3]*q*(a+c*x^2)^(1/3))]/q^2 - 
  3*c*e*Log[d+e*x]/(2*q^2) + 
  3*c*e*Log[c*d-c*e*x+q*(a+c*x^2)^(1/3)]/(2*q^2)] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2-3*a*e^2,0] && NegQ[c^2*d*e^2] *)


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(1/3)),x_Symbol] :=
  a^(1/3)*Int[1/((d+e*x)*(1-3*e*x/d)^(1/3)*(1+3*e*x/d)^(1/3)),x] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2+9*a*e^2,0] && GtQ[a,0]


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(1/3)),x_Symbol] :=
  (1+c*x^2/a)^(1/3)/(a+c*x^2)^(1/3)*Int[1/((d+e*x)*(1+c*x^2/a)^(1/3)),x] /;
FreeQ[{a,c,d,e},x] && EqQ[c*d^2+9*a*e^2,0] && Not[GtQ[a,0]]


Int[1/((d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^(1/3)),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (b+q+2*c*x)^(1/3)*(b-q+2*c*x)^(1/3)/(a+b*x+c*x^2)^(1/3)*Int[1/((d+e*x)*(b+q+2*c*x)^(1/3)*(b-q+2*c*x)^(1/3)),x]] /;
FreeQ[{a,b,c,d,e},x] && NeQ[b^2-4*a*c,0] && EqQ[c^2*d^2-b*c*d*e-2*b^2*e^2+9*a*c*e^2,0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(d+e*x)^m*(Rt[a,2]+Rt[-c,2]*x)^p*(Rt[a,2]-Rt[-c,2]*x)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && GtQ[a,0] && LtQ[c,0]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^2)^p,(d/(d^2-e^2*x^2)-e*x/(d^2-e^2*x^2))^(-m),x],x] /;
FreeQ[{a,c,d,e,p},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[m,0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(1/(d+e*x))^(2*p)*(a+b*x+c*x^2)^p/(e*(e*(b-q+2*c*x)/(2*c*(d+e*x)))^p*(e*(b+q+2*c*x)/(2*c*(d+e*x)))^p)*
    Subst[Int[x^(-m-2*(p+1))*Simp[1-(d-e*(b-q)/(2*c))*x,x]^p*Simp[1-(d-e*(b+q)/(2*c))*x,x]^p,x],x,1/(d+e*x)]] /;
FreeQ[{a,b,c,d,e,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && Not[IntegerQ[p]] && ILtQ[m,0]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (a+b*x+c*x^2)^p/(e*(1-(d+e*x)/(d-e*(b-q)/(2*c)))^p*(1-(d+e*x)/(d-e*(b+q)/(2*c)))^p)*
    Subst[Int[x^m*Simp[1-x/(d-e*(b-q)/(2*c)),x]^p*Simp[1-x/(d-e*(b+q)/(2*c)),x]^p,x],x,d+e*x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && NeQ[2*c*d-b*e,0] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (a+c*x^2)^p/(e*(1-(d+e*x)/(d+e*q/c))^p*(1-(d+e*x)/(d-e*q/c))^p)*
    Subst[Int[x^m*Simp[1-x/(d+e*q/c),x]^p*Simp[1-x/(d-e*q/c),x]^p,x],x,d+e*x]] /;
FreeQ[{a,c,d,e,m,p},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]]


Int[(d_.+e_.*u_)^m_.*(a_+b_.*u_+c_.*u_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,m,p},x] && LinearQ[u,x] && NeQ[u,x]


Int[(d_.+e_.*u_)^m_.*(a_+c_.*u_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(a+c*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,e,m,p},x] && LinearQ[u,x] && NeQ[u,x]


(* IntQuadraticQ[a,b,c,d,e,m,p,x] returns True iff (d+e*x)^m*(a+b*x+c*x^2)^p is integrable wrt x in terms of non-Appell functions. *)
IntQuadraticQ[a_,b_,c_,d_,e_,m_,p_,x_] :=
  IntegerQ[p] || IGtQ[m,0] || IntegersQ[2*m,2*p] || IntegersQ[m,4*p] || 
  IntegersQ[m,p+1/3] && (EqQ[c^2*d^2-b*c*d*e+b^2*e^2-3*a*c*e^2,0] || EqQ[c^2*d^2-b*c*d*e-2*b^2*e^2+9*a*c*e^2,0])


(* ::Subsection::Closed:: *)
(*1.2.1.3 (d+e x)^m (f+g x) (a+b x+c x^2)^p*)


Int[x_^m_.*(f_+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  f*Int[x^m*(a+c*x^2)^p,x] + g*Int[x^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,f,g,p},x] && IntegerQ[m] && Not[IntegerQ[2*p]]


Int[(e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(f+g*x)*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,e,f,g,m},x] && IGtQ[p,0]


Int[(e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(f+g*x)*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,e,f,g,m},x] && IGtQ[p,0]


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -f*g*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)*(e*f-d*g)) /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b^2-4*a*c,0] && EqQ[m+2*p+3,0] && EqQ[2*c*f-b*g,0]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) - 
  e*g*m/(2*c*(p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[2*c*f-b*g,0] && LtQ[p,-1] && GtQ[m,0]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -2*c*(e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*c*d-b*e)^2) + 
  (2*c*f-b*g)/(2*c*d-b*e)*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[b^2-4*a*c,0] && EqQ[m+2*p+3,0] && NeQ[2*c*f-b*g,0] && NeQ[2*c*d-b*e,0]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p]))*Int[(d+e*x)^m*(f+g*x)*(b/2+c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && EqQ[b^2-4*a*c,0]


Int[(d_.+e_.*x_)*(f_+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*g*x/c + 1/c*Int[(c*d*f-a*e*g+(c*e*f+c*d*g-b*e*g)*x)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0]


Int[(d_.+e_.*x_)*(f_+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  e*g*x/c + 1/c*Int[(c*d*f-a*e*g+c*(e*f+d*g)*x)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(b*e*g*(p+2)-c*(e*f+d*g)*(2*p+3)-2*c*e*g*(p+1)*x)*(a+b*x+c*x^2)^(p+1)/(2*c^2*(p+1)*(2*p+3)) /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b^2-4*a*c,0] && EqQ[b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3),0] && NeQ[p,-1]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  ((e*f+d*g)*(2*p+3)+2*e*g*(p+1)*x)*(a+c*x^2)^(p+1)/(2*c*(p+1)*(2*p+3)) /;
FreeQ[{a,c,d,e,f,g,p},x] && EqQ[a*e*g-c*d*f*(2*p+3),0] && NeQ[p,-1]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(2*a*c*(e*f+d*g)-b*(c*d*f+a*e*g)-(b^2*e*g-b*c*(e*f+d*g)+2*c*(c*d*f-a*e*g))*x)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(b^2-4*a*c)) - 
  (b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3))/(c*(p+1)*(b^2-4*a*c))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a*(e*f+d*g)-(c*d*f-a*e*g)*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) - 
  (a*e*g-c*d*f*(2*p+3))/(2*a*c*(p+1))*Int[(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g},x] && LtQ[p,-1]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(b*e*g*(p+2)-c*(e*f+d*g)*(2*p+3)-2*c*e*g*(p+1)*x)*(a+b*x+c*x^2)^(p+1)/(2*c^2*(p+1)*(2*p+3)) + 
  (b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3))/(2*c^2*(2*p+3))*Int[(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b^2-4*a*c,0] && Not[LeQ[p,-1]]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  ((e*f+d*g)*(2*p+3)+2*e*g*(p+1)*x)*(a+c*x^2)^(p+1)/(2*c*(p+1)*(2*p+3)) - 
  (a*e*g-c*d*f*(2*p+3))/(c*(2*p+3))*Int[(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,p},x] && Not[LeQ[p,-1]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m},x] && EqQ[c*d^2+a*e^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[d,0] && EqQ[m+p,0])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  d^m*e^m*Int[(f+g*x)*(a+b*x+c*x^2)^(m+p)/(a*e+c*d*x)^m,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[2*p]] && ILtQ[m,0]


Int[x_*(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  d^m*e^m*Int[x*(a+c*x^2)^(m+p)/(a*e+c*d*x)^m,x] /;
FreeQ[{a,c,d,e,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[m,0]          && EqQ[m,-1] && Not[ILtQ[p-1/2,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g),0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) /;
FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && EqQ[m*(d*g+e*f)+2*e*f*(p+1),0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (g*(c*d-b*e)+c*e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(2*c*d-b*e)) - 
  e*(m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*(p+1)*(2*c*d-b*e))*
    Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && GtQ[m,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d*g+e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) - 
  e*(m*(d*g+e*f)+2*e*f*(p+1))/(2*c*d*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g},x] && EqQ[c*d^2+a*e^2,0] && LtQ[p,-1] && GtQ[m,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (g*(c*d-b*e)+c*e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(2*c*d-b*e)) - 
  e*(m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*(p+1)*(2*c*d-b*e))*
    Int[(d+e*x)^Simplify[m-1]*(a+b*x+c*x^2)^Simplify[p+1],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && SumSimplerQ[p,1] && SumSimplerQ[m,-1] && NeQ[p,-1]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d*g+e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) - 
  e*(m*(d*g+e*f)+2*e*f*(p+1))/(2*c*d*(p+1))*Int[(d+e*x)^Simplify[m-1]*(a+c*x^2)^Simplify[p+1],x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && SumSimplerQ[p,1] && SumSimplerQ[m,-1] && NeQ[p,-1] && Not[IGtQ[m,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d*g-e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((2*c*d-b*e)*(m+p+1)) + 
  (m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(e*(2*c*d-b*e)*(m+p+1))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  (LtQ[m,-1] && Not[IGtQ[m+p+1,0]] || LtQ[m,0] && LtQ[p,-1] || EqQ[m+2*p+2,0]) && NeQ[m+p+1,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d*g-e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) + 
  (m*(g*c*d+c*e*f)+2*e*c*f*(p+1))/(e*(2*c*d)*(m+p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && 
  (LtQ[m,-1] && Not[IGtQ[m+p+1,0]] || LtQ[m,0] && LtQ[p,-1] || EqQ[m+2*p+2,0]) && NeQ[m+p+1,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  (m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*e*(m+2*p+2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && NeQ[m+2*p+2,0] && (NeQ[m,2] || EqQ[d,0])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  (m*(d*g+e*f)+2*e*f*(p+1))/(e*(m+2*p+2))*Int[(d+e*x)^m*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && EqQ[c*d^2+a*e^2,0] && NeQ[m+2*p+2,0] && NeQ[m,2]


Int[x_^2*(f_+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  x^2*(a*g-c*f*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) - 
  1/(2*a*c*(p+1))*Int[x*Simp[2*a*g-c*f*(2*p+5)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,f,g},x] && EqQ[a*g^2+f^2*c,0] && LtQ[p,-2]


Int[x_^2*(f_+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  1/c*Int[(f+g*x)*(a+c*x^2)^(p+1),x] - a/c*Int[(f+g*x)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,f,g,p},x] && EqQ[a*g^2+f^2*c,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[m]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && IntegerQ[m]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(2*(p+1)*(c*d^2-b*d*e+a*e^2)) /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && EqQ[Simplify[m+2*p+3],0] && EqQ[b*(e*f+d*g)-2*(c*d*f+a*e*g),0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(2*(p+1)*(c*d^2+a*e^2)) /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NeQ[c*d^2+a*e^2,0] && EqQ[Simplify[m+2*p+3],0] && EqQ[c*d*f+a*e*g,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(b*f-2*a*g+(2*c*f-b*g)*x)/((p+1)*(b^2-4*a*c)) - 
  m*(b*(e*f+d*g)-2*(c*d*f+a*e*g))/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && EqQ[Simplify[m+2*p+3],0] && LtQ[p,-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a+c*x^2)^(p+1)*(a*g-c*f*x)/(2*a*c*(p+1)) - 
  m*(c*d*f+a*e*g)/(2*a*c*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && EqQ[Simplify[m+2*p+3],0] && LtQ[p,-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(2*(p+1)*(c*d^2-b*d*e+a*e^2)) - 
  (b*(e*f+d*g)-2*(c*d*f+a*e*g))/(2*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && EqQ[Simplify[m+2*p+3],0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(2*(p+1)*(c*d^2+a*e^2)) + 
  (c*d*f+a*e*g)/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NeQ[c*d^2+a*e^2,0] && EqQ[Simplify[m+2*p+3],0]


Int[(e_.*x_)^m_*(f_+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  f*Int[(e*x)^m*(a+c*x^2)^p,x] + g/e*Int[(e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,e,f,g,p},x] && Not[RationalQ[m]] && Not[IGtQ[p,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^FracPart[p]*(a+b*x+c*x^2)^FracPart[p]/(a*d+c*e*x^3)^FracPart[p]*Int[(f+g*x)*(a*d+c*e*x^3)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && EqQ[m,p] && EqQ[b*d+a*e,0] && EqQ[c*d+b*e,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e^2*(m+1)*(m+2)*(c*d^2-b*d*e+a*e^2))*
    ((d*g-e*f*(m+2))*(c*d^2-b*d*e+a*e^2)-d*p*(2*c*d-b*e)*(e*f-d*g)-e*(g*(m+1)*(c*d^2-b*d*e+a*e^2)+p*(2*c*d-b*e)*(e*f-d*g))*x) - 
  p/(e^2*(m+1)*(m+2)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1)*
    Simp[2*a*c*e*(e*f-d*g)*(m+2)+b^2*e*(d*g*(p+1)-e*f*(m+p+2))+b*(a*e^2*g*(m+1)-c*d*(d*g*(2*p+1)-e*f*(m+2*p+2)))-
      c*(2*c*d*(d*g*(2*p+1)-e*f*(m+2*p+2))-e*(2*a*e*g*(m+1)-b*(d*g*(m-2*p)+e*f*(m+2*p+2))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && 
  GtQ[p,0] && LtQ[m,-2] && LtQ[m+2*p,0] && Not[ILtQ[m+2*p+3,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  -(d+e*x)^(m+1)*(a+c*x^2)^p/(e^2*(m+1)*(m+2)*(c*d^2+a*e^2))*
    ((d*g-e*f*(m+2))*(c*d^2+a*e^2)-2*c*d^2*p*(e*f-d*g)-e*(g*(m+1)*(c*d^2+a*e^2)+2*c*d*p*(e*f-d*g))*x) - 
  p/(e^2*(m+1)*(m+2)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1)*
    Simp[2*a*c*e*(e*f-d*g)*(m+2)-c*(2*c*d*(d*g*(2*p+1)-e*f*(m+2*p+2))-2*a*e^2*g*(m+1))*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && 
  GtQ[p,0] && LtQ[m,-2] && LtQ[m+2*p,0] && Not[ILtQ[m+2*p+3,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(e*f*(m+2*p+2)-d*g*(2*p+1)+e*g*(m+1)*x)*(a+b*x+c*x^2)^p/(e^2*(m+1)*(m+2*p+2)) + 
  p/(e^2*(m+1)*(m+2*p+2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1)*
    Simp[g*(b*d+2*a*e+2*a*e*m+2*b*d*p)-f*b*e*(m+2*p+2)+(g*(2*c*d+b*e+b*e*m+4*c*d*p)-2*c*e*f*(m+2*p+2))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && RationalQ[p] && p>0 && 
  (LtQ[m,-1] || EqQ[p,1] || IntegerQ[p] && Not[RationalQ[m]]) && NeQ[m,-1] && Not[ILtQ[m+2*p+1,0]] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(e*f*(m+2*p+2)-d*g*(2*p+1)+e*g*(m+1)*x)*(a+c*x^2)^p/(e^2*(m+1)*(m+2*p+2)) + 
  p/(e^2*(m+1)*(m+2*p+2))*Int[(d+e*x)^(m+1)*(a+c*x^2)^(p-1)*
    Simp[g*(2*a*e+2*a*e*m)+(g*(2*c*d+4*c*d*p)-2*c*e*f*(m+2*p+2))*x,x],x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NeQ[c*d^2+a*e^2,0] && RationalQ[p] && p>0 && 
  (LtQ[m,-1] || EqQ[p,1] || IntegerQ[p] && Not[RationalQ[m]]) && NeQ[m,-1] && Not[ILtQ[m+2*p+1,0]] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(c*e*f*(m+2*p+2)-g*(c*d+2*c*d*p-b*e*p)+g*c*e*(m+2*p+1)*x)*(a+b*x+c*x^2)^p/
    (c*e^2*(m+2*p+1)*(m+2*p+2)) - 
  p/(c*e^2*(m+2*p+1)*(m+2*p+2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1)*
    Simp[c*e*f*(b*d-2*a*e)*(m+2*p+2)+g*(a*e*(b*e-2*c*d*m+b*e*m)+b*d*(b*e*p-c*d-2*c*d*p))+
      (c*e*f*(2*c*d-b*e)*(m+2*p+2)+g*(b^2*e^2*(p+m+1)-2*c^2*d^2*(1+2*p)-c*e*(b*d*(m-2*p)+2*a*e*(m+2*p+1))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && 
  GtQ[p,0] && (IntegerQ[p] || Not[RationalQ[m]] || GeQ[m,-1] && LtQ[m,0]) && Not[ILtQ[m+2*p,0]] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(c*e*f*(m+2*p+2)-g*c*d*(2*p+1)+g*c*e*(m+2*p+1)*x)*(a+c*x^2)^p/
    (c*e^2*(m+2*p+1)*(m+2*p+2)) + 
  2*p/(c*e^2*(m+2*p+1)*(m+2*p+2))*Int[(d+e*x)^m*(a+c*x^2)^(p-1)*
    Simp[f*a*c*e^2*(m+2*p+2)+a*c*d*e*g*m-(c^2*f*d*e*(m+2*p+2)-g*(c^2*d^2*(2*p+1)+a*c*e^2*(m+2*p+1)))*x,x],x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NeQ[c*d^2+a*e^2,0] && 
  GtQ[p,0] && (IntegerQ[p] || Not[RationalQ[m]] || GeQ[m,-1] && LtQ[m,0]) && Not[ILtQ[m+2*p,0]] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(a+b*x+c*x^2)^p*ExpandIntegrand[(d+e*x)^m*(f+g*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[p,-1] && IGtQ[m,0] && RationalQ[a,b,c,d,e,f,g]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(a+c*x^2)^p*ExpandIntegrand[(d+e*x)^m*(f+g*x),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[p,-1] && IGtQ[m,0] && RationalQ[a,c,d,e,f,g]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*(2*a*c*(e*f+d*g)-b*(c*d*f+a*e*g)-(2*c^2*d*f+b^2*e*g-c*(b*e*f+b*d*g+2*a*e*g))*x)/
    (c*(p+1)*(b^2-4*a*c)) - 
  1/(c*(p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1)*
    Simp[2*c^2*d^2*f*(2*p+3)+b*e*g*(a*e*(m-1)+b*d*(p+2))-c*(2*a*e*(e*f*(m-1)+d*g*m)+b*d*(d*g*(2*p+3)-e*f*(m-2*p-4))) + 
      e*(b^2*e*g*(m+p+1)+2*c^2*d*f*(m+2*p+2)-c*(2*a*e*g*m+b*(e*f+d*g)*(m+2*p+2)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && GtQ[m,1] && 
  (EqQ[m,2] && EqQ[p,-3] && RationalQ[a,b,c,d,e,f,g] || Not[ILtQ[m+2*p+3,0]])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m-1)*(a+c*x^2)^(p+1)*(a*(e*f+d*g)-(c*d*f-a*e*g)*x)/(2*a*c*(p+1)) - 
  1/(2*a*c*(p+1))*Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1)*
    Simp[a*e*(e*f*(m-1)+d*g*m)-c*d^2*f*(2*p+3)+e*(a*e*g*m-c*d*f*(m+2*p+2))*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && GtQ[m,1] && 
  (EqQ[d,0] || EqQ[m,2] && EqQ[p,-3] && RationalQ[a,c,d,e,f,g] || Not[ILtQ[m+2*p+3,0]])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(f*b-2*a*g+(2*c*f-b*g)*x)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
    Simp[g*(2*a*e*m+b*d*(2*p+3))-f*(b*e*m+2*c*d*(2*p+3))-e*(2*c*f-b*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && GtQ[m,0] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a+c*x^2)^(p+1)*(a*g-c*f*x)/(2*a*c*(p+1)) - 
  1/(2*a*c*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1)*Simp[a*e*g*m-c*d*f*(2*p+3)-c*e*f*(m+2*p+3)*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && GtQ[m,0] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(f*(b*c*d-b^2*e+2*a*c*e)-a*g*(2*c*d-b*e)+c*(f*(2*c*d-b*e)-g*(b*d-2*a*e))*x)*(a+b*x+c*x^2)^(p+1)/
    ((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) + 
  1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
    Simp[f*(b*c*d*e*(2*p-m+2)+b^2*e^2*(p+m+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3))-
      g*(a*e*(b*e-2*c*d*m+b*e*m)-b*d*(3*c*d-b*e+2*c*d*p-b*e*p))+
      c*e*(g*(b*d-2*a*e)-f*(2*c*d-b*e))*(m+2*p+4)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(f*a*c*e-a*g*c*d+c*(c*d*f+a*e*g)*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)*(c*d^2+a*e^2)) + 
  1/(2*a*c*(p+1)*(c*d^2+a*e^2))*Int[(d+e*x)^m*(a+c*x^2)^(p+1)*
    Simp[f*(c^2*d^2*(2*p+3)+a*c*e^2*(m+2*p+3))-a*c*d*e*g*m+c*e*(c*d*f+a*e*g)*(m+2*p+4)*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  g*(d+e*x)^m/(c*m) + 
  1/c*Int[(d+e*x)^(m-1)*Simp[c*d*f-a*e*g+(g*c*d-b*e*g+c*e*f)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && FractionQ[m] && GtQ[m,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  g*(d+e*x)^m/(c*m) + 
  1/c*Int[(d+e*x)^(m-1)*Simp[c*d*f-a*e*g+(g*c*d+c*e*f)*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && FractionQ[m] && GtQ[m,0]


Int[(f_.+g_.*x_)/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  2*Subst[Int[(e*f-d*g+g*x^2)/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[(f_.+g_.*x_)/(Sqrt[d_.+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  2*Subst[Int[(e*f-d*g+g*x^2)/(c*d^2+a*e^2-2*c*d*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x)^(m+1)*Simp[c*d*f-f*b*e+a*e*g-c*(e*f-d*g)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && FractionQ[m] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)/((m+1)*(c*d^2+a*e^2)) + 
  1/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*Simp[c*d*f+a*e*g-c*(e*f-d*g)*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NeQ[c*d^2+a*e^2,0] && FractionQ[m] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,(f+g*x)/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[RationalQ[m]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,(f+g*x)/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && Not[RationalQ[m]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  1/(c*(m+2*p+2))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p*
    Simp[m*(c*d*f-a*e*g)+d*(2*c*f-b*g)*(p+1)+(m*(c*e*f+c*d*g-b*e*g)+e*(p+1)*(2*c*f-b*g))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && GtQ[m,0] && NeQ[m+2*p+2,0] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p]) && Not[IGtQ[m,0] && EqQ[f,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  1/(c*(m+2*p+2))*Int[(d+e*x)^(m-1)*(a+c*x^2)^p*
    Simp[c*d*f*(m+2*p+2)-a*e*g*m+c*(e*f*(m+2*p+2)+d*g*m)*x,x],x] /;
FreeQ[{a,c,d,e,f,g,p},x] && NeQ[c*d^2+a*e^2,0] && GtQ[m,0] && NeQ[m+2*p+2,0] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p]) && Not[IGtQ[m,0] && EqQ[f,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
    Simp[(c*d*f-f*b*e+a*e*g)*(m+1)+b*(d*g-e*f)*(p+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[m,-1] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  1/((m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p*Simp[(c*d*f+a*e*g)*(m+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,c,d,e,f,g,p},x] && NeQ[c*d^2+a*e^2,0] && LtQ[m,-1] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
    Simp[(c*d*f-f*b*e+a*e*g)*(m+1)+b*(d*g-e*f)*(p+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[Simplify[m+2*p+3],0] && NeQ[m,-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  1/((m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p*Simp[(c*d*f+a*e*g)*(m+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[Simplify[m+2*p+3],0] && NeQ[m,-1]


Int[(f_+g_.*x_)/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  4*f*(a-d)/(b*d-a*e)*Subst[Int[1/(4*(a-d)-x^2),x],x,(2*(a-d)+(b-e)*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g},x] && EqQ[4*c*(a-d)-(b-e)^2,0] && EqQ[e*f*(b-e)-2*g*(b*d-a*e),0] && NeQ[b*d-a*e,0]


Int[(f_+g_.*x_)/(Sqrt[x_]*Sqrt[a_+b_.*x_+c_.*x_^2]),x_Symbol] :=
  2*Subst[Int[(f+g*x^2)/Sqrt[a+b*x^2+c*x^4],x],x,Sqrt[x]] /;
FreeQ[{a,b,c,f,g},x] && NeQ[b^2-4*a*c,0]


Int[(f_+g_.*x_)/(Sqrt[x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  2*Subst[Int[(f+g*x^2)/Sqrt[a+c*x^4],x],x,Sqrt[x]] /;
FreeQ[{a,c,f,g},x]


Int[(f_+g_.*x_)/(Sqrt[e_*x_]*Sqrt[a_+b_.*x_+c_.*x_^2]),x_Symbol] :=
  Sqrt[x]/Sqrt[e*x]*Int[(f+g*x)/(Sqrt[x]*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,e,f,g},x] && NeQ[b^2-4*a*c,0]


Int[(f_+g_.*x_)/(Sqrt[e_*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  Sqrt[x]/Sqrt[e*x]*Int[(f+g*x)/(Sqrt[x]*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,e,f,g},x]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  g/e*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] + (e*f-d*g)/e*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IGtQ[m,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  g/e*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] + (e*f-d*g)/e*Int[(d+e*x)^m*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NeQ[c*d^2+a*e^2,0] && Not[IGtQ[m,0]]


(* ::Subsection::Closed:: *)
(*1.2.1.4 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p*)


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p]))*Int[(d+e*x)^m*(f+g*x)^n*(b/2+c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NeQ[e*f-d*g,0] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p] && Not[IGtQ[n,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && (IntegerQ[p] || GtQ[a,0] && GtQ[d,0] && EqQ[m+p,0])


Int[x_^n_.*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  Int[x^n*(a/d+c*x/e)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,n,p},x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && 
  (Not[IntegerQ[n]] || Not[IntegerQ[2*p]] || IGtQ[n,2] || GtQ[p,0] && NeQ[n,2])


Int[x_^n_.*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  Int[x^n*(a/d+c*x/e)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,n,p},x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && 
  (Not[IntegerQ[n]] || Not[IntegerQ[2*p]] || IGtQ[n,2] || GtQ[p,0] && NeQ[n,2])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(a/d+c*x/e)^(-m)*(f+g*x)^n*(a+b*x+c*x^2)^(m+p),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[m,0] && IntegerQ[n] && 
  (LtQ[n,0] || GtQ[p,0])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  d^(2*m)/a^m*Int[(f+g*x)^n*(a+c*x^2)^(m+p)/(d-e*x)^m,x] /;
FreeQ[{a,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && EqQ[f,0] && ILtQ[m,-1] && 
  Not[IGtQ[n,0] && ILtQ[m+n,0] && Not[GtQ[p,1]]]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  d^(2*m)/a^m*Int[(f+g*x)^n*(a+c*x^2)^(m+p)/(d-e*x)^m,x] /;
FreeQ[{a,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[m,0] && IntegerQ[n]


Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  -(2*c*d-b*e)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(e*p*(b^2-4*a*c)*(d+e*x)) - 
  1/(d*e*p*(b^2-4*a*c))*Int[(f+g*x)^(n-1)*(a+b*x+c*x^2)^p*
    Simp[b*(a*e*g*n-c*d*f*(2*p+1))-2*a*c*(d*g*n-e*f*(2*p+1))-c*g*(b*d-2*a*e)*(n+2*p+1)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && IGtQ[n,0] && ILtQ[n+2*p,0]


Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  d*(f+g*x)^n*(a+c*x^2)^(p+1)/(2*a*e*p*(d+e*x)) - 
  1/(2*d*e*p)*Int[(f+g*x)^(n-1)*(a+c*x^2)^p*Simp[d*g*n-e*f*(2*p+1)-e*g*(n+2*p+1)*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && IGtQ[n,0] && ILtQ[n+2*p,0]


Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  (f+g*x)^(n+1)*(a+b*x+c*x^2)^p*(c*d-b*e-c*e*x)/(p*(2*c*d-b*e)*(e*f-d*g)) + 
  1/(p*(2*c*d-b*e)*(e*f-d*g))*Int[(f+g*x)^n*(a+b*x+c*x^2)^p*(b*e*g*(n+p+1)+c*e*f*(2*p+1)-c*d*g*(n+2*p+1)+c*e*g*(n+2*p+2)*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && 
  ILtQ[n,0] && ILtQ[n+2*p,0] && Not[IGtQ[n,0]]


Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  d*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(2*a*p*(e*f-d*g)*(d+e*x)) + 
  1/(p*(2*c*d)*(e*f-d*g))*Int[(f+g*x)^n*(a+c*x^2)^p*(c*e*f*(2*p+1)-c*d*g*(n+2*p+1)+c*e*g*(n+2*p+2)*x),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && 
  ILtQ[n,0] && ILtQ[n+2*p,0] && Not[IGtQ[n,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(m-n-1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && EqQ[c*e*f+c*d*g-b*e*g,0] && NeQ[m-n-1,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(m-n-1)) /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && EqQ[e*f+d*g,0] && NeQ[m-n-1,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g-b*e*g)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+p,0] && EqQ[m-n-2,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*(n+1)*(e*f+d*g)) /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+p,0] && EqQ[m-n-2,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p/(g*(n+1)) + 
  c*m/(e*g*(n+1))*Int[(d+e*x)^(m+1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && GtQ[p,0] && LtQ[n,-1] && Not[IntegerQ[n+p] && LeQ[n+p+2,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p/(g*(n+1)) + 
  c*m/(e*g*(n+1))*Int[(d+e*x)^(m+1)*(f+g*x)^(n+1)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && GtQ[p,0] && LtQ[n,-1] && Not[IntegerQ[n+p] && LeQ[n+p+2,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p/(g*(m-n-1)) - 
  m*(c*e*f+c*d*g-b*e*g)/(e^2*g*(m-n-1))*Int[(d+e*x)^(m+1)*(f+g*x)^n*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && GtQ[p,0] && NeQ[m-n-1,0] && Not[IGtQ[n,0]] && Not[IntegerQ[n+p] && LtQ[n+p+2,0]] && RationalQ[n]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p/(g*(m-n-1)) - 
  c*m*(e*f+d*g)/(e^2*g*(m-n-1))*Int[(d+e*x)^(m+1)*(f+g*x)^n*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && GtQ[p,0] && NeQ[m-n-1,0] && Not[IGtQ[n,0]] && Not[IntegerQ[n+p] && LtQ[n+p+2,0]] && RationalQ[n]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) - 
  e*g*n/(c*(p+1))*Int[(d+e*x)^(m-1)*(f+g*x)^(n-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && LtQ[p,-1] && GtQ[n,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(p+1)) - 
  e*g*n/(c*(p+1))*Int[(d+e*x)^(m-1)*(f+g*x)^(n-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && LtQ[p,-1] && GtQ[n,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((p+1)*(c*e*f+c*d*g-b*e*g)) + 
  e^2*g*(m-n-2)/((p+1)*(c*e*f+c*d*g-b*e*g))*Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+p,0] && 
  LtQ[p,-1] && RationalQ[n]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*(p+1)*(e*f+d*g)) + 
  e^2*g*(m-n-2)/(c*(p+1)*(e*f+d*g))*Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g,n},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+p,0] && LtQ[p,-1] && RationalQ[n]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(m-n-1)) - 
  n*(c*e*f+c*d*g-b*e*g)/(c*e*(m-n-1))*Int[(d+e*x)^m*(f+g*x)^(n-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && GtQ[n,0] && NeQ[m-n-1,0] && (IntegerQ[2*p] || IntegerQ[n])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(m-n-1)) - 
  n*(e*f+d*g)/(e*(m-n-1))*Int[(d+e*x)^m*(f+g*x)^(n-1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && GtQ[n,0] && NeQ[m-n-1,0] && (IntegerQ[2*p] || IntegerQ[n])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g-b*e*g)) - 
  c*e*(m-n-2)/((n+1)*(c*e*f+c*d*g-b*e*g))*Int[(d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && LtQ[n,-1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g)) - 
  e*(m-n-2)/((n+1)*(e*f+d*g))*Int[(d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p,0] && LtQ[n,-1] && IntegerQ[2*p]


Int[Sqrt[d_+e_.*x_]/((f_.+g_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  2*e^2*Subst[Int[1/(c*(e*f+d*g)-b*e*g+e^2*g*x^2),x],x,Sqrt[a+b*x+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0]


Int[Sqrt[d_+e_.*x_]/((f_.+g_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  2*e^2*Subst[Int[1/(c*(e*f+d*g)+e^2*g*x^2),x],x,Sqrt[a+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(c*g*(n+p+2)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p-1,0] && EqQ[b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3),0] && NeQ[n+p+2,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+p+2)) /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p-1,0] && EqQ[e*f*(p+1)-d*g*(2*n+p+3),0] && NeQ[n+p+2,0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(e*f-d*g)*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(g*(n+1)*(c*e*f+c*d*g-b*e*g)) - 
  e*(b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3))/(g*(n+1)*(c*e*f+c*d*g-b*e*g))*
    Int[(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p-1,0] && LtQ[n,-1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(e*f-d*g)*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+1)*(e*f+d*g)) - 
  e*(e*f*(p+1)-d*g*(2*n+p+3))/(g*(n+1)*(e*f+d*g))*Int[(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p-1,0] && LtQ[n,-1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(c*g*(n+p+2)) - 
  (b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3))/(c*g*(n+p+2))*Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p-1,0] && Not[LtQ[n,-1]] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+p+2)) - 
  (e*f*(p+1)-d*g*(2*n+p+3))/(g*(n+p+2))*Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[p]] && EqQ[m+p-1,0] && Not[LtQ[n,-1]] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[p]] && ILtQ[m,0] && (ILtQ[n,0] || IGtQ[n,0] && ILtQ[p+1/2,0]) && Not[IGtQ[n,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[1/Sqrt[a+c*x^2],(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^(p+1/2),x],x] /;
FreeQ[{a,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && IntegerQ[p-1/2] && ILtQ[m,0] && ILtQ[n,0] && Not[IGtQ[n,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g,n,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && ILtQ[m,0] && (ILtQ[n,0] || IGtQ[n,0] && ILtQ[p+1/2,0]) && Not[IGtQ[n,0]]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[(f+g*x)^n,a*e+c*d*x,x], h=PolynomialRemainder[(f+g*x)^n,a*e+c*d*x,x]},
  h*(2*c*d-b*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
    ExpandToSum[d*e*(p+1)*(b^2-4*a*c)*Q-h*(2*c*d-b*e)*(m+2*p+2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[p+1/2,0] && IGtQ[m,0] && IGtQ[n,0] && Not[IGtQ[n,0]]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[(f+g*x)^n,a*e+c*d*x,x], h=PolynomialRemainder[(f+g*x)^n,a*e+c*d*x,x]},
  -d*h*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*e*(p+1)) + 
  d/(2*a*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1)*ExpandToSum[2*a*e*(p+1)*Q+h*(m+2*p+2),x],x]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && ILtQ[p+1/2,0] && IGtQ[m,0] && IGtQ[n,0] && Not[IGtQ[n,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)^p,(d+e*x)^m*(f+g*x)^n,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && 
  EqQ[m+n+2*p+1,0] && ILtQ[m,0] && ILtQ[n,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^2)^p,(d+e*x)^m*(f+g*x)^n,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && EqQ[m+n+2*p+1,0] && ILtQ[m,0] && ILtQ[n,0]


(* Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g^n*(d+e*x)^(m+n-1)*(a+b*x+c*x^2)^(p+1)/(c*e^(n-1)*(m+n+2*p+1)) + 
  1/(c*e^n*(m+n+2*p+1))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p*
    ExpandToSum[c*e^n*(m+n+2*p+1)*(f+g*x)^n-c*g^n*(m+n+2*p+1)*(d+e*x)^n+e*g^n*(m+p+n)*(d+e*x)^(n-2)*(b*d-2*a*e+(2*c*d-b*e)*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && 
  NeQ[m+n+2*p+1,0] && IGtQ[n,0] *)


(* Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  g^n*(d+e*x)^(m+n-1)*(a+c*x^2)^(p+1)/(c*e^(n-1)*(m+n+2*p+1)) + 
  1/(c*e^n*(m+n+2*p+1))*Int[(d+e*x)^m*(a+c*x^2)^p*
    ExpandToSum[c*e^n*(m+n+2*p+1)*(f+g*x)^n-c*g^n*(m+n+2*p+1)*(d+e*x)^n-2*e*g^n*(m+p+n)*(d+e*x)^(n-2)*(a*e-c*d*x),x],x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && NeQ[m+n+2*p+1,0] && IGtQ[n,0] *)


Int[(e_.*x_)^m_*(f_.+g_.*x_)^n_*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (e*x)^m*(b*x+c*x^2)^p/(x^(m+p)*(b+c*x)^p)*Int[x^(m+p)*(f+g*x)^n*(b+c*x)^p,x] /;
FreeQ[{b,c,e,f,g,m,n},x] && Not[IntegerQ[p]] && Not[IGtQ[n,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && GtQ[a,0] && GtQ[d,0] && Not[IGtQ[m,0]] && Not[IGtQ[n,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
(*(a+b*x+c*x^2)^p/((d+e*x)^p*(a*e+c*d*x)^p)*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a*e+c*d*x)^p,x] /; *)
  (a+b*x+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && Not[IGtQ[m,0]] && Not[IGtQ[n,0]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NeQ[e*f-d*g,0] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && Not[IGtQ[m,0]] && Not[IGtQ[n,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p] && 
  (EqQ[p,1] && IntegersQ[m,n] || ILtQ[m,0] && ILtQ[n,0])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[p] && 
  (EqQ[p,1] && IntegersQ[m,n] || ILtQ[m,0] && ILtQ[n,0])


Int[(a_.+b_.*x_+c_.*x_^2)^p_/((d_.+e_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  (c*d^2-b*d*e+a*e^2)/(e*(e*f-d*g))*Int[(a+b*x+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[Simp[c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x,x]*(a+b*x+c*x^2)^(p-1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && FractionQ[p] && GtQ[p,0]


Int[(a_+c_.*x_^2)^p_/((d_.+e_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  (c*d^2+a*e^2)/(e*(e*f-d*g))*Int[(a+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[Simp[c*d*f+a*e*g-c*(e*f-d*g)*x,x]*(a+c*x^2)^(p-1)/(f+g*x),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && FractionQ[p] && GtQ[p,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{q=Denominator[m]},
  q/e*Subst[Int[x^(q*(m+1)-1)*((e*f-d*g)/e+g*x^q/e)^n*
    ((c*d^2-b*d*e+a*e^2)/e^2-(2*c*d-b*e)*x^q/e^2+c*x^(2*q)/e^2)^p,x],x,(d+e*x)^(1/q)]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegersQ[n,p] && FractionQ[m]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{q=Denominator[m]},
  q/e*Subst[Int[x^(q*(m+1)-1)*((e*f-d*g)/e+g*x^q/e)^n*((c*d^2+a*e^2)/e^2-2*c*d*x^q/e^2+c*x^(2*q)/e^2)^p,x],x,(d+e*x)^(1/q)]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegersQ[n,p] && FractionQ[m]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d*f+e*g*x^2)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[m-n,0] && EqQ[e*f+d*g,0] && (IntegerQ[m] || GtQ[d,0] && GtQ[f,0])


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^n_*(a_.+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d*f+e*g*x^2)^m*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && EqQ[m-n,0] && EqQ[e*f+d*g,0] && (IntegerQ[m] || GtQ[d,0] && GtQ[f,0])


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^FracPart[m]*(f+g*x)^FracPart[m]/(d*f+e*g*x^2)^FracPart[m]*Int[(d*f+e*g*x^2)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && EqQ[m-n,0] && EqQ[e*f+d*g,0]


Int[(d_+e_.*x_)^m_*(f_+g_.*x_)^n_*(a_.+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^FracPart[m]*(f+g*x)^FracPart[m]/(d*f+e*g*x^2)^FracPart[m]*Int[(d*f+e*g*x^2)^m*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && EqQ[m-n,0] && EqQ[e*f+d*g,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  g/c^2*Int[Simp[2*c*e*f+c*d*g-b*e*g+c*e*g*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2),x] + 
  1/c^2*Int[Simp[c^2*d*f^2-2*a*c*e*f*g-a*c*d*g^2+a*b*e*g^2+(c^2*e*f^2+2*c^2*d*f*g-2*b*c*e*f*g-b*c*d*g^2+b^2*e*g^2-a*c*e*g^2)*x,x]*
    (d+e*x)^(m-1)*(f+g*x)^(n-2)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && GtQ[n,1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
  g/c*Int[Simp[2*e*f+d*g+e*g*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2),x] + 
  1/c*Int[Simp[c*d*f^2-2*a*e*f*g-a*d*g^2+(c*e*f^2+2*c*d*f*g-a*e*g^2)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && GtQ[n,1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*g/c*Int[(d+e*x)^(m-1)*(f+g*x)^(n-1),x] + 
  1/c*Int[Simp[c*d*f-a*e*g+(c*e*f+c*d*g-b*e*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-1)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && GtQ[n,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
  e*g/c*Int[(d+e*x)^(m-1)*(f+g*x)^(n-1),x] + 
  1/c*Int[Simp[c*d*f-a*e*g+(c*e*f+c*d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-1)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && GtQ[n,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  -g*(e*f-d*g)/(c*f^2-b*f*g+a*g^2)*Int[(d+e*x)^(m-1)*(f+g*x)^n,x] + 
  1/(c*f^2-b*f*g+a*g^2)*
    Int[Simp[c*d*f-b*d*g+a*e*g+c*(e*f-d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n+1)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && LtQ[n,-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
  -g*(e*f-d*g)/(c*f^2+a*g^2)*Int[(d+e*x)^(m-1)*(f+g*x)^n,x] + 
  1/(c*f^2+a*g^2)*
    Int[Simp[c*d*f+a*e*g+c*(e*f-d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n+1)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[m,0] && LtQ[n,-1]


Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  Int[ExpandIntegrand[1/(Sqrt[d+e*x]*Sqrt[f+g*x]),(d+e*x)^(m+1/2)/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[m+1/2,0]


Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*(a_.+c_.*x_^2)),x_Symbol] :=
  Int[ExpandIntegrand[1/(Sqrt[d+e*x]*Sqrt[f+g*x]),(d+e*x)^(m+1/2)/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[c*d^2+a*e^2,0] && IGtQ[m+1/2,0]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n,1/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n,1/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]]


Int[x_^2*(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(c*e*(m+2*p+3)) /;
FreeQ[{a,b,c,d,e,m,p},x] && EqQ[b*e*(m+p+2)+2*c*d*(p+1),0] && EqQ[b*d*(p+1)+a*e*(m+1),0] && NeQ[m+2*p+3,0]


Int[x_^2*(d_.+e_.*x_)^m_.*(a_.+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(c*e*(m+2*p+3)) /;
FreeQ[{a,c,d,e,m,p},x] && EqQ[d*(p+1),0] && EqQ[a*(m+1),0] && NeQ[m+2*p+3,0]


Int[(g_.*x_)^n_*(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^FracPart[p]*(a+b*x+c*x^2)^FracPart[p]/(a*d+c*e*x^3)^FracPart[p]*Int[(g*x)^n*(a*d+c*e*x^3)^p,x] /;
FreeQ[{a,b,c,d,e,g,m,n,p},x] && EqQ[m-p,0] && EqQ[b*d+a*e,0] && EqQ[c*d+b*e,0]


Int[(d_.+e_.*x_)^m_.*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(e*(m+1)) - 
  1/(2*e*(m+1))*Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*Simp[b*f+a*g+2*(c*f+b*g)*x+3*c*g*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[2*m] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_.*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(e*(m+1)) - 
  1/(2*e*(m+1))*Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*Simp[a*g+2*c*f*x+3*c*g*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[2*m] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_.*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(e*(2*m+5)) - 
  1/(e*(2*m+5))*Int[(d+e*x)^m/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
    Simp[b*d*f-3*a*e*f+a*d*g+2*(c*d*f-b*e*f+b*d*g-a*e*g)*x-(c*e*f-3*c*d*g+b*e*g)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[2*m] && Not[LtQ[m,-1]]


Int[(d_.+e_.*x_)^m_.*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2],x_Symbol] :=
  2*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(e*(2*m+5)) + 
  1/(e*(2*m+5))*Int[(d+e*x)^m/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
    Simp[3*a*e*f-a*d*g-2*(c*d*f-a*e*g)*x+(c*e*f-3*c*d*g)*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[2*m] && Not[LtQ[m,-1]]


Int[(d_.+e_.*x_)^m_.*Sqrt[a_.+b_.*x_+c_.*x_^2]/Sqrt[f_.+g_.*x_],x_Symbol] :=
  2*(d+e*x)^m*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(g*(2*m+3)) - 
  1/(g*(2*m+3))*Int[(d+e*x)^(m-1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
    Simp[b*d*f+2*a*(e*f*m-d*g*(m+1))+(2*c*d*f-2*a*e*g+b*(e*f-d*g)*(2*m+1))*x-(b*e*g+2*c*(d*g*m-e*f*(m+1)))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[2*m] && GtQ[m,0]


Int[(d_.+e_.*x_)^m_.*Sqrt[a_+c_.*x_^2]/Sqrt[f_.+g_.*x_],x_Symbol] :=
  2*(d+e*x)^m*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(g*(2*m+3)) - 
  1/(g*(2*m+3))*Int[(d+e*x)^(m-1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
    Simp[2*a*(e*f*m-d*g*(m+1))+(2*c*d*f-2*a*e*g)*x-(2*c*(d*g*m-e*f*(m+1)))*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[2*m] && GtQ[m,0]


Int[Sqrt[a_.+b_.*x_+c_.*x_^2]/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]),x_Symbol] :=
  (c*d^2-b*d*e+a*e^2)/e^2*Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] - 
  1/e^2*Int[(c*d-b*e-c*e*x)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[Sqrt[a_+c_.*x_^2]/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]),x_Symbol] :=
  (c*d^2+a*e^2)/e^2*Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] - 
  1/e^2*Int[(c*d-c*e*x)/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^m_.*Sqrt[a_.+b_.*x_+c_.*x_^2]/Sqrt[f_.+g_.*x_],x_Symbol] :=
  (d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/((m+1)*(e*f-d*g)) - 
  1/(2*(m+1)*(e*f-d*g))*Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
    Simp[b*f+a*g*(2*m+3)+2*(c*f+b*g*(m+2))*x+c*g*(2*m+5)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[2*m] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_.*Sqrt[a_+c_.*x_^2]/Sqrt[f_.+g_.*x_],x_Symbol] :=
  (d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/((m+1)*(e*f-d*g)) - 
  1/(2*(m+1)*(e*f-d*g))*Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
    Simp[a*g*(2*m+3)+2*(c*f)*x+c*g*(2*m+5)*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[2*m] && LtQ[m,-1]


Int[Sqrt[d_.+e_.*x_]/(Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[2]*Sqrt[2*c*f-g*(b+q)]*Sqrt[b-q+2*c*x]*(d+e*x)*
    Sqrt[(e*f-d*g)*(b+q+2*c*x)/((2*c*f-g*(b+q))*(d+e*x))]*
    Sqrt[(e*f-d*g)*(2*a+(b+q)*x)/((b*f+q*f-2*a*g)*(d+e*x))]/
   (g*Sqrt[2*c*d-e*(b+q)]*Sqrt[2*a*c/(b+q)+c*x]*Sqrt[a+b*x+c*x^2])*
    EllipticPi[e*(2*c*f-g*(b+q))/(g*(2*c*d-e*(b+q))),
      ArcSin[Sqrt[2*c*d-e*(b+q)]*Sqrt[f+g*x]/(Sqrt[2*c*f-g*(b+q)]*Sqrt[d+e*x])],
      (b*d+q*d-2*a*e)*(2*c*f-g*(b+q))/((b*f+q*f-2*a*g)*(2*c*d-e*(b+q)))]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[Sqrt[d_.+e_.*x_]/(Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[-4*a*c,2]},
  Sqrt[2]*Sqrt[2*c*f-g*q]*Sqrt[-q+2*c*x]*(d+e*x)*
    Sqrt[(e*f-d*g)*(q+2*c*x)/((2*c*f-g*q)*(d+e*x))]*
    Sqrt[(e*f-d*g)*(2*a+q*x)/((q*f-2*a*g)*(d+e*x))]/
   (g*Sqrt[2*c*d-e*q]*Sqrt[2*a*c/q+c*x]*Sqrt[a+c*x^2])*
    EllipticPi[e*(2*c*f-g*q)/(g*(2*c*d-e*q)),
      ArcSin[Sqrt[2*c*d-e*q]*Sqrt[f+g*x]/(Sqrt[2*c*f-g*q]*Sqrt[d+e*x])],
      (q*d-2*a*e)*(2*c*f-g*q)/((q*f-2*a*g)*(2*c*d-e*q))]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^(3/2)/(Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  e/g*Int[Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[a+b*x+c*x^2],x] - 
  (e*f-d*g)/g*Int[Sqrt[d+e*x]/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[(d_.+e_.*x_)^(3/2)/(Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  e/g*Int[Sqrt[d+e*x]*Sqrt[f+g*x]/Sqrt[a+c*x^2],x] - 
  (e*f-d*g)/g*Int[Sqrt[d+e*x]/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  2*e^2*(d+e*x)^(m-2)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(c*g*(2*m-1)) - 
  1/(c*g*(2*m-1))*Int[(d+e*x)^(m-3)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
    Simp[b*d*e^2*f+a*e^2*(d*g+2*e*f*(m-2))-c*d^3*g*(2*m-1)+
      e*(e*(2*b*d*g+e*(b*f+a*g)*(2*m-3))+c*d*(2*e*f-3*d*g*(2*m-1)))*x+
      2*e^2*(c*e*f-3*c*d*g+b*e*g)*(m-1)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[2*m] && GeQ[m,2]


Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  2*e^2*(d+e*x)^(m-2)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(c*g*(2*m-1)) - 
  1/(c*g*(2*m-1))*Int[(d+e*x)^(m-3)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
    Simp[a*e^2*(d*g+2*e*f*(m-2))-c*d^3*g*(2*m-1)+e*(e*(a*e*g*(2*m-3))+c*d*(2*e*f-3*d*g*(2*m-1)))*x+2*e^2*(c*e*f-3*c*d*g)*(m-1)*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[2*m] && GeQ[m,2]


Int[1/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[-c/a,2]},
  1/Sqrt[a]*Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[1-q*x]*Sqrt[1+q*x]),x]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && GtQ[a,0]


Int[1/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[-c/a,2]},
  Sqrt[1+c*x^2/a]/Sqrt[a+c*x^2]*Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[1-q*x]*Sqrt[1+q*x]),x]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && Not[GtQ[a,0]]


Int[1/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[b-q+2*c*x]*Sqrt[b+q+2*c*x]/Sqrt[a+b*x+c*x^2]*Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[b-q+2*c*x]*Sqrt[b+q+2*c*x]),x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -2*(d+e*x)*Sqrt[(e*f-d*g)^2*(a+b*x+c*x^2)/((c*f^2-b*f*g+a*g^2)*(d+e*x)^2)]/((e*f-d*g)*Sqrt[a+b*x+c*x^2])*
  Subst[
    Int[1/Sqrt[1-(2*c*d*f-b*e*f-b*d*g+2*a*e*g)*x^2/(c*f^2-b*f*g+a*g^2)+(c*d^2-b*d*e+a*e^2)*x^4/(c*f^2-b*f*g+a*g^2)],x],
    x,
    Sqrt[f+g*x]/Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  -2*(d+e*x)*Sqrt[(e*f-d*g)^2*(a+c*x^2)/((c*f^2+a*g^2)*(d+e*x)^2)]/((e*f-d*g)*Sqrt[a+c*x^2])*
  Subst[
    Int[1/Sqrt[1-(2*c*d*f+2*a*e*g)*x^2/(c*f^2+a*g^2)+(c*d^2+a*e^2)*x^4/(c*f^2+a*g^2)],x],x,Sqrt[f+g*x]/Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0]


Int[1/((d_.+e_.*x_)^(3/2)*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -g/(e*f-d*g)*Int[1/(Sqrt[d+e*x]*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] + 
  e/(e*f-d*g)*Int[Sqrt[f+g*x]/((d+e*x)^(3/2)*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[1/((d_.+e_.*x_)^(3/2)*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  -g/(e*f-d*g)*Int[1/(Sqrt[d+e*x]*Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] + 
  e/(e*f-d*g)*Int[Sqrt[f+g*x]/((d+e*x)^(3/2)*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  e^2*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/((m+1)*(e*f-d*g)*(c*d^2-b*d*e+a*e^2)) + 
  1/(2*(m+1)*(e*f-d*g)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
    Simp[2*d*(c*e*f-c*d*g+b*e*g)*(m+1)-e^2*(b*f+a*g)*(2*m+3)+2*e*(c*d*g*(m+1)-e*(c*f+b*g)*(m+2))*x-c*e^2*g*(2*m+5)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[2*m] && LeQ[m,-2]


Int[(d_.+e_.*x_)^m_/(Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  e^2*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/((m+1)*(e*f-d*g)*(c*d^2+a*e^2)) + 
  1/(2*(m+1)*(e*f-d*g)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
    Simp[2*d*(c*e*f-c*d*g)*(m+1)-a*e^2*g*(2*m+3)+2*e*(c*d*g*(m+1)-c*e*f*(m+2))*x-c*e^2*g*(2*m+5)*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[2*m] && LeQ[m,-2]


(* Int[Sqrt[d_.+e_.*x_]*Sqrt[f_.+g_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  0 /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] *)


Int[(d_.+e_.*x_)^m_*Sqrt[f_.+g_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*e*(d+e*x)^(m-1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/(c*(2*m+1)) - 
  1/(c*(2*m+1))*Int[(d+e*x)^(m-2)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
    Simp[e*(b*d*f+a*(d*g+2*e*f*(m-1)))-c*d^2*f*(2*m+1)+
      (a*e^2*g*(2*m-1)-c*d*(4*e*f*m+d*g*(2*m+1))+b*e*(2*d*g+e*f*(2*m-1)))*x+
      e*(2*b*e*g*m-c*(e*f+d*g*(4*m-1)))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[2*m] && GtQ[m,1]


Int[(d_.+e_.*x_)^m_*Sqrt[f_.+g_.*x_]/Sqrt[a_+c_.*x_^2],x_Symbol] :=
  2*e*(d+e*x)^(m-1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/(c*(2*m+1)) - 
  1/(c*(2*m+1))*Int[(d+e*x)^(m-2)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
    Simp[a*e*(d*g+2*e*f*(m-1))-c*d^2*f*(2*m+1)+(a*e^2*g*(2*m-1)-c*d*(4*e*f*m+d*g*(2*m+1)))*x-c*e*(e*f+d*g*(4*m-1))*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[2*m] && GtQ[m,1]


Int[Sqrt[f_.+g_.*x_]/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  g/e*Int[1/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] + 
  (e*f-d*g)/e*Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0]


Int[Sqrt[f_.+g_.*x_]/((d_.+e_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  g/e*Int[1/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] + 
  (e*f-d*g)/e*Int[1/((d+e*x)*Sqrt[f+g*x]*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0]


Int[(d_.+e_.*x_)^m_*Sqrt[f_.+g_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/(2*(m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2])*
    Simp[2*c*d*f*(m+1)-e*(a*g+b*f*(2*m+3))-2*(b*e*g*(2+m)-c*(d*g*(m+1)-e*f*(m+2)))*x-c*e*g*(2*m+5)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[2*m] && LeQ[m,-2]


Int[(d_.+e_.*x_)^m_*Sqrt[f_.+g_.*x_]/Sqrt[a_+c_.*x_^2],x_Symbol] :=
  e*(d+e*x)^(m+1)*Sqrt[f+g*x]*Sqrt[a+c*x^2]/((m+1)*(c*d^2+a*e^2)) + 
  1/(2*(m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+1)/(Sqrt[f+g*x]*Sqrt[a+c*x^2])*
    Simp[2*c*d*f*(m+1)-e*(a*g)+2*c*(d*g*(m+1)-e*f*(m+2))*x-c*e*g*(2*m+5)*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[2*m] && LeQ[m,-2]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0] && 
  (IGtQ[m,0] || EqQ[m,-2] && EqQ[p,1] && EqQ[2*c*d-b*e,0])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && 
  (IGtQ[m,0] || EqQ[m,-2] && EqQ[p,1] && EqQ[d,0])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{Qx=PolynomialQuotient[(a+b*x+c*x^2)^p,d+e*x,x],R=PolynomialRemainder[(a+b*x+c*x^2)^p,d+e*x,x]},
  R*(d+e*x)^(m+1)*(f+g*x)^(n+1)/((m+1)*(e*f-d*g)) + 
  1/((m+1)*(e*f-d*g))*Int[(d+e*x)^(m+1)*(f+g*x)^n*ExpandToSum[(m+1)*(e*f-d*g)*Qx-g*R*(m+n+2),x],x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{Qx=PolynomialQuotient[(a+c*x^2)^p,d+e*x,x],R=PolynomialRemainder[(a+c*x^2)^p,d+e*x,x]},
  R*(d+e*x)^(m+1)*(f+g*x)^(n+1)/((m+1)*(e*f-d*g)) + 
  1/((m+1)*(e*f-d*g))*Int[(d+e*x)^(m+1)*(f+g*x)^n*ExpandToSum[(m+1)*(e*f-d*g)*Qx-g*R*(m+n+2),x],x]] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && LtQ[m,-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  c^p*(d+e*x)^(m+2*p)*(f+g*x)^(n+1)/(g*e^(2*p)*(m+n+2*p+1)) + 
  1/(g*e^(2*p)*(m+n+2*p+1))*Int[(d+e*x)^m*(f+g*x)^n*
    ExpandToSum[g*(m+n+2*p+1)*(e^(2*p)*(a+b*x+c*x^2)^p-c^p*(d+e*x)^(2*p))-c^p*(e*f-d*g)*(m+2*p)*(d+e*x)^(2*p-1),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IGtQ[p,0] && NeQ[m+n+2*p+1,0] && 
  (IntegerQ[n] || Not[IntegerQ[m]])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  c^p*(d+e*x)^(m+2*p)*(f+g*x)^(n+1)/(g*e^(2*p)*(m+n+2*p+1)) + 
  1/(g*e^(2*p)*(m+n+2*p+1))*Int[(d+e*x)^m*(f+g*x)^n*
    ExpandToSum[g*(m+n+2*p+1)*(e^(2*p)*(a+c*x^2)^p-c^p*(d+e*x)^(2*p))-c^p*(e*f-d*g)*(m+2*p)*(d+e*x)^(2*p-1),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IGtQ[p,0] && NeQ[m+n+2*p+1,0] && 
  (IntegerQ[n] || Not[IntegerQ[m]])


Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  (c*d^2-b*d*e+a*e^2)/(e*(e*f-d*g))*Int[(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[(f+g*x)^n*(c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[n]] && Not[IntegerQ[p]] && GtQ[p,0] && LtQ[n,-1]


Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  (c*d^2+a*e^2)/(e*(e*f-d*g))*Int[(f+g*x)^(n+1)*(a+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[(f+g*x)^n*(c*d*f+a*e*g-c*(e*f-d*g)*x)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[n]] && Not[IntegerQ[p]] && GtQ[p,0] && LtQ[n,-1]


Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  e*(e*f-d*g)/(c*d^2-b*d*e+a*e^2)*Int[(f+g*x)^(n-1)*(a+b*x+c*x^2)^(p+1)/(d+e*x),x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(f+g*x)^(n-1)*(c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IntegerQ[n]] && Not[IntegerQ[p]] && LtQ[p,-1] && GtQ[n,0]


Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  e*(e*f-d*g)/(c*d^2+a*e^2)*Int[(f+g*x)^(n-1)*(a+c*x^2)^(p+1)/(d+e*x),x] + 
  1/(c*d^2+a*e^2)*Int[(f+g*x)^(n-1)*(c*d*f+a*e*g-c*(e*f-d*g)*x)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && 
  Not[IntegerQ[n]] && Not[IntegerQ[p]] && LtQ[p,-1] && GtQ[n,0]


Int[(f_.+g_.*x_)^n_/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  Int[ExpandIntegrand[1/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),(f+g*x)^(n+1/2)/(d+e*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[n+1/2]


Int[(f_.+g_.*x_)^n_/((d_.+e_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  Int[ExpandIntegrand[1/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),(f+g*x)^(n+1/2)/(d+e*x),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && IntegerQ[n+1/2]


Int[(g_.*x_)^n_.*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  d*(g*x)^n/x^n*Int[(x^n*(a+c*x^2)^p)/(d^2-e^2*x^2),x] - 
  e*(g*x)^n/x^n*Int[(x^(n+1)*(a+c*x^2)^p)/(d^2-e^2*x^2),x] /;
FreeQ[{a,c,d,e,g,n,p},x] && NeQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && Not[IntegersQ[n,2*p]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && (IntegerQ[p] || ILtQ[m,0] && ILtQ[n,0]) && 
  Not[IGtQ[m,0] || IGtQ[n,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NeQ[e*f-d*g,0] && NeQ[c*d^2+a*e^2,0] && (IntegerQ[p] || ILtQ[m,0] && ILtQ[n,0]) && 
  Not[IGtQ[m,0] || IGtQ[n,0]]


Int[(g_.*x_)^n_.*(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (g*x)^n/x^n*Int[ExpandIntegrand[x^n*(a+c*x^2)^p,(d/(d^2-e^2*x^2)-e*x/(d^2-e^2*x^2))^(-m),x],x] /;
FreeQ[{a,c,d,e,g,n,p},x] && NeQ[c*d^2+a*e^2,0] && ILtQ[m,0] && Not[IntegerQ[p]] && Not[IntegerQ[n]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Unintegrable[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && Not[IGtQ[m,0] || IGtQ[n,0]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Unintegrable[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && Not[IGtQ[m,0] || IGtQ[n,0]]


Int[(d_.+e_.*u_)^m_.*(f_.+g_.*u_)^n_.*(a_+b_.*u_+c_.*u_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && LinearQ[u,x] && NeQ[u,x]


Int[(d_.+e_.*u_)^m_.*(f_.+g_.*u_)^n_.*(a_+c_.*u_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && LinearQ[u,x] && NeQ[u,x]





(* ::Subsection::Closed:: *)
(*1.2.1.5 (a+b x+c x^2)^p (d+e x+f x^2)^q*)


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  (c/f)^p*Int[(d+e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && (IntegerQ[p] || GtQ[c/f,0]) && 
  (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p])*Int[(d+e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[GtQ[c/f,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(b+2*c*x)^(2*p)*(d+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,f,p,q},x] && EqQ[b^2-4*a*c,0] && Not[IntegerQ[p]]


(* Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  1/(2^(2*p+2*q+1)*c*(-c/(b^2-4*a*c))^p*(-f/(e^2-4*d*f))^q)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^p*(1+e*x^2/(b*(4*c*d-b*e)))^q,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0] && 
  (IntegerQ[p] || GtQ[-c/(b^2-4*a*c),0]) && (IntegerQ[q] || GtQ[-f/(e^2-4*d*f),0]) *)


(* Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (d+e*x+f*x^2)^q/(2^(2*p+2*q+1)*c*(-c/(b^2-4*a*c))^p*(-f*(d+e*x+f*x^2)/(e^2-4*d*f))^q)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^p*(1+e*x^2/(b*(4*c*d-b*e)))^q,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0] && 
  (IntegerQ[p] || GtQ[-c/(b^2-4*a*c),0]) && Not[IntegerQ[q] || GtQ[-f/(e^2-4*d*f),0]] *)


(* Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q/(2^(2*p+2*q+1)*c*(-c*(a+b*x+c*x^2)/(b^2-4*a*c))^p*(-f*(d+e*x+f*x^2)/(e^2-4*d*f))^q)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^p*(1+e*x^2/(b*(4*c*d-b*e)))^q,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0] *)


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/((b^2-4*a*c)*(p+1)) - 
  (1/((b^2-4*a*c)*(p+1)))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
      Simp[2*c*d*(2*p+3)+b*e*q+(2*b*f*q+2*c*e*(2*p+q+3))*x+2*c*f*(2*p+2*q+3)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q/((b^2-4*a*c)*(p+1)) - 
  (1/((b^2-4*a*c)*(p+1)))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1)*
      Simp[2*c*d*(2*p+3)+(2*b*f*q)*x+2*c*f*(2*p+2*q+3)*x^2,x],x] /;
FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (2*c*x)*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/((-4*a*c)*(p+1)) - 
  (1/((-4*a*c)*(p+1)))*
    Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
      Simp[2*c*d*(2*p+3)+(2*c*e*(2*p+q+3))*x+2*c*f*(2*p+2*q+3)*x^2,x],x] /;
FreeQ[{a,c,d,e,f},x] && NeQ[e^2-4*d*f] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (2*a*c^2*e-b^2*c*e+b^3*f+b*c*(c*d-3*a*f)+c*(2*c^2*d+b^2*f-c*(b*e+2*a*f))*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/
    ((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)) - 
  (1/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
      Simp[2*c*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)-
        (2*c^2*d+b^2*f-c*(b*e+2*a*f))*(a*f*(p+1)-c*d*(p+2))-
        e*(b^2*c*e-2*a*c^2*e-b^3*f-b*c*(c*d-3*a*f))*(p+q+2)+
       (2*f*(2*a*c^2*e-b^2*c*e+b^3*f+b*c*(c*d-3*a*f))*(p+q+2)-(2*c^2*d+b^2*f-c*(b*e+2*a*f))*(b*f*(p+1)-c*e*(2*p+q+4)))*x+
       c*f*(2*c^2*d+b^2*f-c*(b*e+2*a*f))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,b,c,d,e,f,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && 
  NeQ[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
  (b^3*f+b*c*(c*d-3*a*f)+c*(2*c^2*d+b^2*f-c*(2*a*f))*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q+1)/
    ((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1)) - 
  (1/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1)))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q*
      Simp[2*c*(b^2*d*f+(c*d-a*f)^2)*(p+1)-
        (2*c^2*d+b^2*f-c*(2*a*f))*(a*f*(p+1)-c*d*(p+2))+
       (2*f*(b^3*f+b*c*(c*d-3*a*f))*(p+q+2)-(2*c^2*d+b^2*f-c*(2*a*f))*(b*f*(p+1)))*x+
       c*f*(2*c^2*d+b^2*f-c*(2*a*f))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,b,c,d,f,q},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && NeQ[b^2*d*f+(c*d-a*f)^2,0] && 
  Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (2*a*c^2*e+c*(2*c^2*d-c*(2*a*f))*x)*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/
    ((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1)) - 
  (1/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1)))*
    Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
      Simp[2*c*((c*d-a*f)^2-(-a*e)*(c*e))*(p+1)-(2*c^2*d-c*(2*a*f))*(a*f*(p+1)-c*d*(p+2))-e*(-2*a*c^2*e)*(p+q+2)+
       (2*f*(2*a*c^2*e)*(p+q+2)-(2*c^2*d-c*(2*a*f))*(-c*e*(2*p+q+4)))*x+
       c*f*(2*c^2*d-c*(2*a*f))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,c,d,e,f,q},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && NeQ[a*c*e^2+(c*d-a*f)^2,0] && 
  Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (b*f*(3*p+2*q)-c*e*(2*p+q)+2*c*f*(p+q)*x)*(a+b*x+c*x^2)^(p-1)*(d+e*x+f*x^2)^(q+1)/(2*f^2*(p+q)*(2*p+2*q+1)) - 
  1/(2*f^2*(p+q)*(2*p+2*q+1))*
    Int[(a+b*x+c*x^2)^(p-2)*(d+e*x+f*x^2)^q*
      Simp[(b*d-a*e)*(c*e-b*f)*(1-p)*(2*p+q)-
        (p+q)*(b^2*d*f*(1-p)-a*(f*(b*e-2*a*f)*(2*p+2*q+1)+c*(2*d*f-e^2*(2*p+q))))+
        (2*(c*d-a*f)*(c*e-b*f)*(1-p)*(2*p+q)-
          (p+q)*((b^2-4*a*c)*e*f*(1-p)+b*(c*(e^2-4*d*f)*(2*p+q)+f*(2*c*d-b*e+2*a*f)*(2*p+2*q+1))))*x+
        ((c*e-b*f)^2*(1-p)*p+c*(p+q)*(f*(b*e-2*a*f)*(4*p+2*q-1)-c*(2*d*f*(1-2*p)+e^2*(3*p+q-1))))*x^2,x],x]/;
FreeQ[{a,b,c,d,e,f,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && GtQ[p,1] && 
  NeQ[p+q,0] && NeQ[2*p+2*q+1,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
  (b*(3*p+2*q)+2*c*(p+q)*x)*(a+b*x+c*x^2)^(p-1)*(d+f*x^2)^(q+1)/(2*f*(p+q)*(2*p+2*q+1)) - 
  1/(2*f*(p+q)*(2*p+2*q+1))*
    Int[(a+b*x+c*x^2)^(p-2)*(d+f*x^2)^q*
      Simp[b^2*d*(p-1)*(2*p+q)-(p+q)*(b^2*d*(1-p)-2*a*(c*d-a*f*(2*p+2*q+1)))-
        (2*b*(c*d-a*f)*(1-p)*(2*p+q)-2*(p+q)*b*(2*c*d*(2*p+q)-(c*d+a*f)*(2*p+2*q+1)))*x+
        (b^2*f*p*(1-p)+2*c*(p+q)*(c*d*(2*p-1)-a*f*(4*p+2*q-1)))*x^2,x],x]/;
FreeQ[{a,b,c,d,f,q},x] && NeQ[b^2-4*a*c,0] && GtQ[p,1] && NeQ[p+q,0] && NeQ[2*p+2*q+1,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  -c*(e*(2*p+q)-2*f*(p+q)*x)*(a+c*x^2)^(p-1)*(d+e*x+f*x^2)^(q+1)/(2*f^2*(p+q)*(2*p+2*q+1)) - 
  1/(2*f^2*(p+q)*(2*p+2*q+1))*
    Int[(a+c*x^2)^(p-2)*(d+e*x+f*x^2)^q*
      Simp[-a*c*e^2*(1-p)*(2*p+q)+a*(p+q)*(-2*a*f^2*(2*p+2*q+1)+c*(2*d*f-e^2*(2*p+q)))+
        (2*(c*d-a*f)*(c*e)*(1-p)*(2*p+q)+4*a*c*e*f*(1-p)*(p+q))*x+
        (p*c^2*e^2*(1-p)-c*(p+q)*(2*a*f^2*(4*p+2*q-1)+c*(2*d*f*(1-2*p)+e^2*(3*p+q-1))))*x^2,x],x]/;
FreeQ[{a,c,d,e,f,q},x] && NeQ[e^2-4*d*f,0] && GtQ[p,1] && NeQ[p+q,0] && NeQ[2*p+2*q+1,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[1/((a_+b_.*x_+c_.*x_^2)*(d_+e_.*x_+f_.*x_^2)),x_Symbol] :=
  With[{q=c^2*d^2-b*c*d*e+a*c*e^2+b^2*d*f-2*a*c*d*f-a*b*e*f+a^2*f^2},
  1/q*Int[(c^2*d-b*c*e+b^2*f-a*c*f-(c^2*e-b*c*f)*x)/(a+b*x+c*x^2),x] + 
  1/q*Int[(c*e^2-c*d*f-b*e*f+a*f^2+(c*e*f-b*f^2)*x)/(d+e*x+f*x^2),x] /;
 NeQ[q,0]] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[1/((a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)),x_Symbol] :=
  With[{q=c^2*d^2+b^2*d*f-2*a*c*d*f+a^2*f^2},
  1/q*Int[(c^2*d+b^2*f-a*c*f+b*c*f*x)/(a+b*x+c*x^2),x] - 
  1/q*Int[(c*d*f-a*f^2+b*f^2*x)/(d+f*x^2),x] /;
 NeQ[q,0]] /;
FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0]


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*e*Subst[Int[1/(e*(b*e-4*a*f)-(b*d-a*e)*x^2),x],x,(e+2*f*x)/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0]


(* Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{k=Rt[(a/c-d/f)^2+(b/c-e/f)*(b*d/(c*f)-a*e/(c*f)),2]},
  -2*(c*d-a*f+c*f*k+(c*e-b*f)*x)*Sqrt[(d+e*x+f*x^2)*((c*f*k)/(c*d-a*f+c*f*k+(c*e-b*f)*x))^2]/(c*Sqrt[d+e*x+f*x^2])*
    Subst[Int[(1-x)/(
      (b*d-a*e-b*f*k-(c*d-a*f-c*f*k)^2/(c*e-b*f)+(b*d-a*e+b*f*k-(a*f-c*d-c*f*k)^2/(c*e-b*f))*x^2)*
      Sqrt[-f*((b*d-a*e-c*e*k)/(c*e-b*f)-(c*d-a*f-c*f*k)^2/(c*e-b*f)^2)-f*((b*d-a*e+c*e*k)/(c*e-b*f)-(a*f-c*d-c*f*k)^2/(c*e-b*f)^2)*x^2]),x],x,
        (c*d-a*f-c*f*k+(c*e-b*f)*x)/(c*d-a*f+c*f*k+(c*e-b*f)*x)]] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[a,b,c,d,e,f] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[c*e-b*f,0] && LtQ[b^2-4*a*c,0] *)


(* Int[1/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{k=Rt[(a/c-d/f)^2+a*e^2/(c*f^2),2]},
  -2*(c*d-a*f+c*f*k+c*e*x)*Sqrt[(d+e*x+f*x^2)*((c*f*k)/(c*d-a*f+c*f*k+c*e*x))^2]/(c*Sqrt[d+e*x+f*x^2])*
    Subst[Int[(1-x)/(
      (-a*e-(c*d-a*f-c*f*k)^2/(c*e)+(-a*e-(a*f-c*d-c*f*k)^2/(c*e))*x^2)*
      Sqrt[-f*((-a*e-c*e*k)/(c*e)-(c*d-a*f-c*f*k)^2/(c*e)^2)-f*((-a*e+c*e*k)/(c*e)-(a*f-c*d-c*f*k)^2/(c*e)^2)*x^2]),x],x,
        (c*d-a*f-c*f*k+(c*e)*x)/(c*d-a*f+c*f*k+(c*e)*x)]] /;
FreeQ[{a,c,d,e,f},x] && RationalQ[a,c,d,e,f] && NeQ[e^2-4*d*f,0] && LtQ[-a*c,0] *)


(* Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  With[{k=Rt[(a/c-d/f)^2+b^2*d/(c^2*f),2]},
  -2*(c*d-a*f+c*f*k-b*f*x)*Sqrt[(d+f*x^2)*((c*f*k)/(c*d-a*f+c*f*k-b*f*x))^2]/(c*Sqrt[d+f*x^2])*
    Subst[Int[(1-x)/(
      (b*d-b*f*k+(c*d-a*f-c*f*k)^2/(b*f)+(b*d+b*f*k+(a*f-c*d-c*f*k)^2/(b*f))*x^2)*
      Sqrt[-f*(-d/f-(c*d-a*f-c*f*k)^2/(b*f)^2)-f*(-d/f-(a*f-c*d-c*f*k)^2/(b*f)^2)*x^2]),x],x,
        (c*d-a*f-c*f*k+(-b*f)*x)/(c*d-a*f+c*f*k+(-b*f)*x)]] /;
FreeQ[{a,b,c,d,f},x] && RationalQ[a,b,c,d,f] && NeQ[b^2-4*a*c,0] && LtQ[b^2-4*a*c,0] *)


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/((b-q+2*c*x)*Sqrt[d+e*x+f*x^2]),x] -
  2*c/q*Int[1/((b+q+2*c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[c*e-b*f,0] && PosQ[b^2-4*a*c]


Int[1/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  1/2*Int[1/((a-Rt[-a*c,2]*x)*Sqrt[d+e*x+f*x^2]),x] +
  1/2*Int[1/((a+Rt[-a*c,2]*x)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,c,d,e,f},x] && NeQ[e^2-4*d*f,0] && PosQ[-a*c]


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/((b-q+2*c*x)*Sqrt[d+f*x^2]),x] -
  2*c/q*Int[1/((b+q+2*c*x)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0] && PosQ[b^2-4*a*c]


Int[1/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),2]},
  1/(2*q)*Int[(c*d-a*f+q+(c*e-b*f)*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] - 
  1/(2*q)*Int[(c*d-a*f-q+(c*e-b*f)*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[c*e-b*f,0] && NegQ[b^2-4*a*c]


Int[1/((a_.+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2+a*c*e^2,2]},
  1/(2*q)*Int[(c*d-a*f+q+c*e*x)/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x] - 
  1/(2*q)*Int[(c*d-a*f-q+c*e*x)/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,c,d,e,f},x] && NeQ[e^2-4*d*f,0] && NegQ[-a*c]


Int[1/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2+b^2*d*f,2]},
  1/(2*q)*Int[(c*d-a*f+q+(-b*f)*x)/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x] - 
  1/(2*q)*Int[(c*d-a*f-q+(-b*f)*x)/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0] && NegQ[b^2-4*a*c]


Int[Sqrt[a_+b_.*x_+c_.*x_^2]/(d_+e_.*x_+f_.*x_^2),x_Symbol] :=
  c/f*Int[1/Sqrt[a+b*x+c*x^2],x] - 
  1/f*Int[(c*d-a*f+(c*e-b*f)*x)/(Sqrt[a+b*x+c*x^2]*(d+e*x+f*x^2)),x] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[Sqrt[a_+b_.*x_+c_.*x_^2]/(d_+f_.*x_^2),x_Symbol] :=
  c/f*Int[1/Sqrt[a+b*x+c*x^2],x] - 
  1/f*Int[(c*d-a*f-b*f*x)/(Sqrt[a+b*x+c*x^2]*(d+f*x^2)),x] /;
FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0]


Int[Sqrt[a_+c_.*x_^2]/(d_+e_.*x_+f_.*x_^2),x_Symbol] :=
  c/f*Int[1/Sqrt[a+c*x^2],x] - 
  1/f*Int[(c*d-a*f+c*e*x)/(Sqrt[a+c*x^2]*(d+e*x+f*x^2)),x] /;
FreeQ[{a,c,d,e,f},x] && NeQ[e^2-4*d*f,0]


Int[1/(Sqrt[a_+b_.*x_+c_.*x_^2]*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  Sqrt[b+r+2*c*x]*Sqrt[2*a+(b+r)*x]/Sqrt[a+b*x+c*x^2]*Int[1/(Sqrt[b+r+2*c*x]*Sqrt[2*a+(b+r)*x]*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[1/(Sqrt[a_+b_.*x_+c_.*x_^2]*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  Sqrt[b+r+2*c*x]*Sqrt[2*a+(b+r)*x]/Sqrt[a+b*x+c*x^2]*Int[1/(Sqrt[b+r+2*c*x]*Sqrt[2*a+(b+r)*x]*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f},x] && NeQ[b^2-4*a*c,0]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Unintegrable[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Unintegrable[(a+c*x^2)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,c,d,e,f,p,q},x] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
FreeQ[{a,c,d,e,f,p,q},x] && LinearQ[u,x] && NeQ[u,x]





(* ::Subsection::Closed:: *)
(*1.2.1.6 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q*)


Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (c/f)^p*Int[(g+h*x)^m*(d+e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && (IntegerQ[p] || GtQ[c/f,0]) && 
  (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])


Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p])*Int[(g+h*x)^m*(d+e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[GtQ[c/f,0]]


Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(g+h*x)^m*(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && EqQ[b^2-4*a*c,0]


Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(g+h*x)^m*(b+2*c*x)^(2*p)*(d+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,f,g,h,m,p,q},x] && EqQ[b^2-4*a*c,0]


Int[(g_+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^m_.,x_Symbol] :=
  Int[(d*g/a+f*h*x/c)^m*(a+b*x+c*x^2)^(m+p),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p},x] && EqQ[c*g^2-b*g*h+a*h^2,0] && EqQ[c^2*d*g^2-a*c*e*g*h+a^2*f*h^2,0] && IntegerQ[m]


Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^m_.,x_Symbol] :=
  Int[(d*g/a+f*h*x/c)^m*(a+c*x^2)^(m+p),x] /;
FreeQ[{a,c,d,e,f,g,h,p},x] && EqQ[c*g^2+a*h^2,0] && EqQ[c^2*d*g^2-a*c*e*g*h+a^2*f*h^2,0] && IntegerQ[m]


Int[(g_+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^m_.,x_Symbol] :=
  Int[(d*g/a+f*h*x/c)^m*(a+b*x+c*x^2)^(m+p),x] /;
FreeQ[{a,b,c,d,f,g,h,p},x] && EqQ[c*g^2-b*g*h+a*h^2,0] && EqQ[c^2*d*g^2+a^2*f*h^2,0] && IntegerQ[m]


Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^m_.,x_Symbol] :=
  Int[(d*g/a+f*h*x/c)^m*(a+c*x^2)^(m+p),x] /;
FreeQ[{a,c,d,f,g,h,p},x] && EqQ[c*g^2+a*h^2,0] && EqQ[c^2*d*g^2+a^2*f*h^2,0] && IntegerQ[m]


(* Int[(g_+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Int[(g+h*x)^(m+p)*(a/g+c/h*x)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,q},x] && EqQ[c*g^2-b*g*h+a*h^2,0] && IntegerQ[p] *)


(* Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Int[(g+h*x)^(m+p)*(a/g+c/h*x)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,c,d,e,f,g,h,m,q},x] && NeQ[e^2-4*d*f,0] && EqQ[c*g^2+a*h^2,0] && IntegerQ[p] *)


(* Int[(g_+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
  Int[(g+h*x)^(m+p)*(a/g+c/h*x)^p*(d+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,f,g,h,m,q},x] && NeQ[b^2-4*a*c,0] && EqQ[c*g^2-b*g*h+a*h^2,0] && IntegerQ[p] *)


(* Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
  Int[(g+h*x)^(m+p)*(a/g+c/h*x)^p*(d+f*x^2)^q,x] /;
FreeQ[{a,c,d,f,g,h,m,q},x] && EqQ[c*g^2+a*h^2,0] && IntegerQ[p] *)


(* Int[(g_+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((g+h*x)^FracPart[p]*(a/g+(c*x)/h)^FracPart[p])*Int[(g+h*x)^(m+p)*(a/g+c/h*x)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,q},x] && EqQ[c*g^2-b*g*h+a*h^2,0] && Not[IntegerQ[p]] *)


(* Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (a+c*x^2)^FracPart[p]/((g+h*x)^FracPart[p]*(a/g+(c*x)/h)^FracPart[p])*Int[(g+h*x)^(m+p)*(a/g+c/h*x)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,c,d,e,f,g,h,m,q},x] && NeQ[e^2-4*d*f,0] && EqQ[c*g^2+a*h^2,0] && Not[IntegerQ[p]] *)


(* Int[(g_+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((g+h*x)^FracPart[p]*(a/g+(c*x)/h)^FracPart[p])*Int[(g+h*x)^(m+p)*(a/g+c/h*x)^p*(d+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,f,g,h,m,q},x] && NeQ[b^2-4*a*c,0] && EqQ[c*g^2-b*g*h+a*h^2,0] && Not[IntegerQ[p]] *)


(* Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_*(d_.+f_.*x_^2)^q_,x_Symbol] :=
  (a+c*x^2)^FracPart[p]/((g+h*x)^FracPart[p]*(a/g+(c*x)/h)^FracPart[p])*Int[(g+h*x)^(m+p)*(a/g+c/h*x)^p*(d+f*x^2)^q,x] /;
FreeQ[{a,c,d,f,g,h,m,q},x] && EqQ[c*g^2+a*h^2,0] && Not[IntegerQ[p]] *)


Int[x_^p_*(a_.+b_.*x_+c_.*x_^2)^p_*(e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Int[(a/e+c/f*x)^p*(e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,e,f,q},x] && NeQ[b^2-4*a*c,0] && EqQ[c*e^2-b*e*f+a*f^2,0] && IntegerQ[p]


Int[x_^p_*(a_+c_.*x_^2)^p_*(e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Int[(a/e+c/f*x)^p*(e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,c,e,f,q},x] && EqQ[c*e^2+a*f^2,0] && IntegerQ[p]


Int[(g_+h_.*x_)/((a_+c_.*x_^2)^(1/3)*(d_+f_.*x_^2)),x_Symbol] :=
  Sqrt[3]*h*ArcTan[1/Sqrt[3]-2^(2/3)*(1-3*h*x/g)^(2/3)/(Sqrt[3]*(1+3*h*x/g)^(1/3))]/(2^(2/3)*a^(1/3)*f) + 
  h*Log[d+f*x^2]/(2^(5/3)*a^(1/3)*f) - 
  3*h*Log[(1-3*h*x/g)^(2/3)+2^(1/3)*(1+3*h*x/g)^(1/3)]/(2^(5/3)*a^(1/3)*f) /;
FreeQ[{a,c,d,f,g,h},x] && EqQ[c*d+3*a*f,0] && EqQ[c*g^2+9*a*h^2,0] && GtQ[a,0]


Int[(g_+h_.*x_)/((a_+c_.*x_^2)^(1/3)*(d_+f_.*x_^2)),x_Symbol] :=
  (1+c*x^2/a)^(1/3)/(a+c*x^2)^(1/3)*Int[(g+h*x)/((1+c*x^2/a)^(1/3)*(d+f*x^2)),x] /;
FreeQ[{a,c,d,f,g,h},x] && EqQ[c*d+3*a*f,0] && EqQ[c*g^2+9*a*h^2,0] && Not[GtQ[a,0]]


Int[(g_+h_.*x_)*(a_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_,x_Symbol] :=
  g*Int[(a+c*x^2)^p*(d+f*x^2)^q,x] + h*Int[x*(a+c*x^2)^p*(d+f*x^2)^q,x] /;
FreeQ[{a,c,d,f,g,h,p,q},x]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(g+h*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && IGtQ[p,0] && IntegerQ[q]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(g+h*x),x],x] /;
FreeQ[{a,c,d,e,f,g,h},x] && NeQ[e^2-4*d*f,0] && IntegersQ[p,q] && (GtQ[p,0] || GtQ[q,0])


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  (g*b-2*a*h-(b*h-2*g*c)*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/((b^2-4*a*c)*(p+1)) - 
  1/((b^2-4*a*c)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
      Simp[e*q*(g*b-2*a*h)-d*(b*h-2*g*c)*(2*p+3)+
        (2*f*q*(g*b-2*a*h)-e*(b*h-2*g*c)*(2*p+q+3))*x-
        f*(b*h-2*g*c)*(2*p+2*q+3)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  (a*h-g*c*x)*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/(2*a*c*(p+1)) + 
  2/(4*a*c*(p+1))*
    Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
      Simp[g*c*d*(2*p+3)-a*(h*e*q)+(g*c*e*(2*p+q+3)-a*(2*h*f*q))*x+g*c*f*(2*p+2*q+3)*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g,h},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  (g*b-2*a*h-(b*h-2*g*c)*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q/((b^2-4*a*c)*(p+1)) - 
  1/((b^2-4*a*c)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1)*
      Simp[-d*(b*h-2*g*c)*(2*p+3)+(2*f*q*(g*b-2*a*h))*x-f*(b*h-2*g*c)*(2*p+2*q+3)*x^2,x],x] /;
FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[q,0]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  (a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))*
    (g*c*(2*a*c*e-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(b*e+2*a*f))+
      c*(g*(2*c^2*d+b^2*f-c*(b*e+2*a*f))-h*(b*c*d-2*a*c*e+a*b*f))*x) + 
  1/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
      Simp[(b*h-2*g*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)+
        (b^2*(g*f)-b*(h*c*d+g*c*e+a*h*f)+2*(g*c*(c*d-a*f)-a*(-h*c*e)))*(a*f*(p+1)-c*d*(p+2))-
        e*((g*c)*(2*a*c*e-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
        (2*f*((g*c)*(2*a*c*e-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
          (b^2*g*f-b*(h*c*d+g*c*e+a*h*f)+2*(g*c*(c*d-a*f)-a*(-h*c*e)))*
          (b*f*(p+1)-c*e*(2*p+q+4)))*x-
        c*f*(b^2*(g*f)-b*(h*c*d+g*c*e+a*h*f)+2*(g*c*(c*d-a*f)+a*h*c*e))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,b,c,d,e,f,g,h,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && 
  NeQ[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  (a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))*
    (g*c*(2*a*c*e)+(-a*h)*(2*c^2*d-c*(2*a*f))+
      c*(g*(2*c^2*d-c*(2*a*f))-h*(-2*a*c*e))*x) + 
  1/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))*
    Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
      Simp[(-2*g*c)*((c*d-a*f)^2-(-a*e)*(c*e))*(p+1)+
        (2*(g*c*(c*d-a*f)-a*(-h*c*e)))*(a*f*(p+1)-c*d*(p+2))-
        e*((g*c)*(2*a*c*e)+(-a*h)*(2*c^2*d-c*(+2*a*f)))*(p+q+2)-
        (2*f*((g*c)*(2*a*c*e)+(-a*h)*(2*c^2*d+-c*(+2*a*f)))*(p+q+2)-(2*(g*c*(c*d-a*f)-a*(-h*c*e)))*(-c*e*(2*p+q+4)))*x-
        c*f*(2*(g*c*(c*d-a*f)-a*(-h*c*e)))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,c,d,e,f,g,h,q},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && NeQ[a*c*e^2+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  (a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q+1)/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))*
    ((g*c)*(-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(2*a*f))+
      c*(g*(2*c^2*d+b^2*f-c*(2*a*f))-h*(b*c*d+a*b*f))*x) + 
  1/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q*
      Simp[(b*h-2*g*c)*((c*d-a*f)^2-(b*d)*(-b*f))*(p+1)+
        (b^2*(g*f)-b*(h*c*d+a*h*f)+2*(g*c*(c*d-a*f)))*(a*f*(p+1)-c*d*(p+2))-
        (2*f*((g*c)*(-b*(c*d+a*f))+(g*b-a*h)*(2*c^2*d+b^2*f-c*(2*a*f)))*(p+q+2)-
          (b^2*(g*f)-b*(h*c*d+a*h*f)+2*(g*c*(c*d-a*f)))*
          (b*f*(p+1)))*x-
        c*f*(b^2*(g*f)-b*(h*c*d+a*h*f)+2*(g*c*(c*d-a*f)))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,b,c,d,f,g,h,q},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && NeQ[b^2*d*f+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  h*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^(q+1)/(2*f*(p+q+1)) - 
  (1/(2*f*(p+q+1)))*
    Int[(a+b*x+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
      Simp[h*p*(b*d-a*e)+a*(h*e-2*g*f)*(p+q+1)+
        (2*h*p*(c*d-a*f)+b*(h*e-2*g*f)*(p+q+1))*x+
        (h*p*(c*e-b*f)+c*(h*e-2*g*f)*(p+q+1))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && GtQ[p,0] && NeQ[p+q+1,0]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  h*(a+c*x^2)^p*(d+e*x+f*x^2)^(q+1)/(2*f*(p+q+1)) + 
  (1/(2*f*(p+q+1)))*
    Int[(a+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
      Simp[a*h*e*p-a*(h*e-2*g*f)*(p+q+1)-2*h*p*(c*d-a*f)*x-(h*c*e*p+c*(h*e-2*g*f)*(p+q+1))*x^2,x],x] /;
FreeQ[{a,c,d,e,f,g,h,q},x] && NeQ[e^2-4*d*f,0] && GtQ[p,0] && NeQ[p+q+1,0]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  h*(a+b*x+c*x^2)^p*(d+f*x^2)^(q+1)/(2*f*(p+q+1)) - 
  (1/(2*f*(p+q+1)))*
    Int[(a+b*x+c*x^2)^(p-1)*(d+f*x^2)^q*
      Simp[h*p*(b*d)+a*(-2*g*f)*(p+q+1)+
        (2*h*p*(c*d-a*f)+b*(-2*g*f)*(p+q+1))*x+
        (h*p*(-b*f)+c*(-2*g*f)*(p+q+1))*x^2,x],x] /;
FreeQ[{a,b,c,d,f,g,h,q},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[p+q+1,0]


Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*(d_+e_.*x_+f_.*x_^2)),x_Symbol] :=
  With[{q=Simplify[c^2*d^2-b*c*d*e+a*c*e^2+b^2*d*f-2*a*c*d*f-a*b*e*f+a^2*f^2]},
  1/q*Int[Simp[g*c^2*d-g*b*c*e+a*h*c*e+g*b^2*f-a*b*h*f-a*g*c*f+c*(h*c*d-g*c*e+g*b*f-a*h*f)*x,x]/(a+b*x+c*x^2),x] + 
  1/q*Int[Simp[-h*c*d*e+g*c*e^2+b*h*d*f-g*c*d*f-g*b*e*f+a*g*f^2-f*(h*c*d-g*c*e+g*b*f-a*h*f)*x,x]/(d+e*x+f*x^2),x] /;
 NeQ[q,0]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)),x_Symbol] :=
  With[{q=Simplify[c^2*d^2+b^2*d*f-2*a*c*d*f+a^2*f^2]},
  1/q*Int[Simp[g*c^2*d+g*b^2*f-a*b*h*f-a*g*c*f+c*(h*c*d+g*b*f-a*h*f)*x,x]/(a+b*x+c*x^2),x] + 
  1/q*Int[Simp[b*h*d*f-g*c*d*f+a*g*f^2-f*(h*c*d+g*b*f-a*h*f)*x,x]/(d+f*x^2),x] /;
 NeQ[q,0]] /;
FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0]


Int[(g_+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*g*Subst[Int[1/(b*d-a*e-b*x^2),x],x,Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0] && EqQ[h*e-2*g*f,0]


Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -(h*e-2*g*f)/(2*f)*Int[1/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] + 
  h/(2*f)*Int[(e+2*f*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[c*e-b*f,0] && NeQ[h*e-2*g*f,0]


Int[x_/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*e*Subst[Int[(1-d*x^2)/(c*e-b*f-e*(2*c*d-b*e+2*a*f)*x^2+d^2*(c*e-b*f)*x^4),x],x,
    (1+(e+Sqrt[e^2-4*d*f])*x/(2*d))/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[b*d-a*e,0]


Int[(g_+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
  g*Subst[Int[1/(a+(c*d-a*f)*x^2),x],x,x/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[b*d-a*e,0] && EqQ[2*h*d-g*e,0]


Int[(g_+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -(2*h*d-g*e)/e*Int[1/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] + 
  h/e*Int[(2*d+e*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && EqQ[b*d-a*e,0] && NeQ[2*h*d-g*e,0]


Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*g*(g*b-2*a*h)*
    Subst[Int[1/Simp[g*(g*b-2*a*h)*(b^2-4*a*c)-(b*d-a*e)*x^2,x],x],x,Simp[g*b-2*a*h-(b*h-2*g*c)*x,x]/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[b*d-a*e,0] && 
  EqQ[h^2*(b*d-a*e)-2*g*h*(c*d-a*f)+g^2*(c*e-b*f),0]


Int[(g_+h_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*a*g*h*Subst[Int[1/Simp[2*a^2*g*h*c+a*e*x^2,x],x],x,Simp[a*h-g*c*x,x]/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,c,d,e,f,g,h},x] && EqQ[a*h^2*e+2*g*h*(c*d-a*f)-g^2*c*e,0]


Int[(g_+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  -2*g*(g*b-2*a*h)*Subst[Int[1/Simp[g*(g*b-2*a*h)*(b^2-4*a*c)-b*d*x^2,x],x],x,Simp[g*b-2*a*h-(b*h-2*g*c)*x,x]/Sqrt[d+f*x^2]] /;
FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0] && EqQ[b*h^2*d-2*g*h*(c*d-a*f)-g^2*b*f,0]


Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*g-h*(b-q))/q*Int[1/((b-q+2*c*x)*Sqrt[d+e*x+f*x^2]),x] -
  (2*c*g-h*(b+q))/q*Int[1/((b+q+2*c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && PosQ[b^2-4*a*c]


Int[(g_.+h_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (h/2+c*g/(2*q))*Int[1/((-q+c*x)*Sqrt[d+e*x+f*x^2]),x] +
  (h/2-c*g/(2*q))*Int[1/((q+c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,c,d,e,f,g,h},x] && NeQ[e^2-4*d*f,0] && PosQ[-a*c]


Int[(g_.+h_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*g-h*(b-q))/q*Int[1/((b-q+2*c*x)*Sqrt[d+f*x^2]),x] -
  (2*c*g-h*(b+q))/q*Int[1/((b+q+2*c*x)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0] && PosQ[b^2-4*a*c]


Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),2]},
  1/(2*q)*Int[Simp[h*(b*d-a*e)-g*(c*d-a*f-q)-(g*(c*e-b*f)-h*(c*d-a*f+q))*x,x]/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] - 
  1/(2*q)*Int[Simp[h*(b*d-a*e)-g*(c*d-a*f+q)-(g*(c*e-b*f)-h*(c*d-a*f-q))*x,x]/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && NeQ[b*d-a*e,0] && NegQ[b^2-4*a*c]


Int[(g_.+h_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2+a*c*e^2,2]},
  1/(2*q)*Int[Simp[-a*h*e-g*(c*d-a*f-q)+(h*(c*d-a*f+q)-g*c*e)*x,x]/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x] - 
  1/(2*q)*Int[Simp[-a*h*e-g*(c*d-a*f+q)+(h*(c*d-a*f-q)-g*c*e)*x,x]/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,c,d,e,f,g,h},x] && NeQ[e^2-4*d*f,0] && NegQ[-a*c]


Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2+b^2*d*f,2]},
  1/(2*q)*Int[Simp[h*b*d-g*(c*d-a*f-q)+(h*(c*d-a*f+q)+g*b*f)*x,x]/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x] - 
  1/(2*q)*Int[Simp[h*b*d-g*(c*d-a*f+q)+(h*(c*d-a*f-q)+g*b*f)*x,x]/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0] && NegQ[b^2-4*a*c]


Int[(g_.+h_.*x_)/(Sqrt[a_+b_.*x_+c_.*x_^2]*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{s=Rt[b^2-4*a*c,2],t=Rt[e^2-4*d*f,2]},
  Sqrt[b+s+2*c*x]*Sqrt[2*a+(b+s)*x]*Sqrt[e+t+2*f*x]*Sqrt[2*d+(e+t)*x]/(Sqrt[a+b*x+c*x^2]*Sqrt[d+e*x+f*x^2])*
    Int[(g+h*x)/(Sqrt[b+s+2*c*x]*Sqrt[2*a+(b+s)*x]*Sqrt[e+t+2*f*x]*Sqrt[2*d+(e+t)*x]),x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[(g_.+h_.*x_)/(Sqrt[a_+b_.*x_+c_.*x_^2]*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{s=Rt[b^2-4*a*c,2],t=Rt[-4*d*f,2]},
  Sqrt[b+s+2*c*x]*Sqrt[2*a+(b+s)*x]*Sqrt[t+2*f*x]*Sqrt[2*d+t*x]/(Sqrt[a+b*x+c*x^2]*Sqrt[d+f*x^2])*
    Int[(g+h*x)/(Sqrt[b+s+2*c*x]*Sqrt[2*a+(b+s)*x]*Sqrt[t+2*f*x]*Sqrt[2*d+t*x]),x]] /;
FreeQ[{a,b,c,d,f,g,h},x] && NeQ[b^2-4*a*c,0]


Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)^(1/3)*(d_.+e_.*x_+f_.*x_^2)),x_Symbol] :=
  With[{q=(-9*c*h^2/(2*c*g-b*h)^2)^(1/3)},
  Sqrt[3]*h*q*ArcTan[1/Sqrt[3]-2^(2/3)*(1-(3*h*(b+2*c*x))/(2*c*g-b*h))^(2/3)/(Sqrt[3]*(1+(3*h*(b+2*c*x))/(2*c*g-b*h))^(1/3))]/f + 
  h*q*Log[d+e*x+f*x^2]/(2*f) - 
  3*h*q*Log[(1-3*h*(b+2*c*x)/(2*c*g-b*h))^(2/3)+2^(1/3)*(1+3*h*(b+2*c*x)/(2*c*g-b*h))^(1/3)]/(2*f)] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[c*e-b*f,0] && EqQ[c^2*d-f*(b^2-3*a*c),0] && EqQ[c^2*g^2-b*c*g*h-2*b^2*h^2+9*a*c*h^2,0] && 
  GtQ[-9*c*h^2/(2*c*g-b*h)^2,0]


Int[(g_.+h_.*x_)/((a_.+b_.*x_+c_.*x_^2)^(1/3)*(d_.+e_.*x_+f_.*x_^2)),x_Symbol] :=
  With[{q=-c/(b^2-4*a*c)},
  (q*(a+b*x+c*x^2))^(1/3)/(a+b*x+c*x^2)^(1/3)*Int[(g+h*x)/((q*a+b*q*x+c*q*x^2)^(1/3)*(d+e*x+f*x^2)),x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && EqQ[c*e-b*f,0] && EqQ[c^2*d-f*(b^2-3*a*c),0] && EqQ[c^2*g^2-b*c*g*h-2*b^2*h^2+9*a*c*h^2,0] && Not[GtQ[4*a-b^2/c,0]]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  Unintegrable[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(g+h*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x]


Int[(a_.+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_*(g_.+h_.*x_),x_Symbol] :=
  Unintegrable[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(g+h*x),x] /;
FreeQ[{a,c,d,e,f,g,h,p,q},x]


Int[(g_.+h_.*u_)^m_.*(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(g+h*x)^m*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && LinearQ[u,x] && NeQ[u,x]


Int[(g_.+h_.*u_)^m_.*(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(g+h*x)^m*(a+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
FreeQ[{a,c,d,e,f,g,h,m,p,q},x] && LinearQ[u,x] && NeQ[u,x]





(* ::Subsection::Closed:: *)
(*1.2.1.7 (a+b x+c x^2)^p (d+e x+f x^2)^q (A+B x+C x^2)*)
(**)


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (c/f)^p*Int[(d+e*x+f*x^2)^(p+q)*(A+B*x+C*x^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && (IntegerQ[p] || GtQ[c/f,0]) && 
  (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.*(A_.+C_.*x_^2),x_Symbol] :=
  (c/f)^p*Int[(d+e*x+f*x^2)^(p+q)*(A+C*x^2),x] /;
FreeQ[{a,b,c,d,e,f,A,C,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && (IntegerQ[p] || GtQ[c/f,0]) && 
  (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p])*Int[(d+e*x+f*x^2)^(p+q)*(A+B*x+C*x^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[GtQ[c/f,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.*(A_.+C_.*x_^2),x_Symbol] :=
  a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p])*Int[(d+e*x+f*x^2)^(p+q)*(A+C*x^2),x] /;
FreeQ[{a,b,c,d,e,f,A,C,p,q},x] && EqQ[c*d-a*f,0] && EqQ[b*d-a*e,0] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[GtQ[c/f,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q*(A+B*x+C*x^2),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,p,q},x] && EqQ[b^2-4*a*c,0]


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.*(A_.+C_.*x_^2),x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q*(A+C*x^2),x] /;
FreeQ[{a,b,c,d,e,f,A,C,p,q},x] && EqQ[b^2-4*a*c,0]


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(b+2*c*x)^(2*p)*(d+f*x^2)^q*(A+B*x+C*x^2),x] /;
FreeQ[{a,b,c,d,f,A,B,C,p,q},x] && EqQ[b^2-4*a*c,0]


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2)^q_.*(A_.+C_.*x_^2),x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(b+2*c*x)^(2*p)*(d+f*x^2)^q*(A+C*x^2),x] /;
FreeQ[{a,b,c,d,f,A,C,p,q},x] && EqQ[b^2-4*a*c,0]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (A*b*c-2*a*B*c+a*b*C-(c*(b*B-2*A*c)-C*(b^2-2*a*c))*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/(c*(b^2-4*a*c)*(p+1)) - 
  1/(c*(b^2-4*a*c)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
      Simp[e*q*(A*b*c-2*a*B*c+a*b*C)-d*(c*(b*B-2*A*c)*(2*p+3)+C*(2*a*c-b^2*(p+2)))+
        (2*f*q*(A*b*c-2*a*B*c+a*b*C)-e*(c*(b*B-2*A*c)*(2*p+q+3)+C*(2*a*c*(q+1)-b^2*(p+q+2))))*x-
        f*(c*(b*B-2*A*c)*(2*p+2*q+3)+C*(2*a*c*(2*q+1)-b^2*(p+2*q+2)))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  (A*b*c+a*b*C+(2*A*c^2+C*(b^2-2*a*c))*x)*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/(c*(b^2-4*a*c)*(p+1)) - 
  1/(c*(b^2-4*a*c)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
      Simp[A*c*(2*c*d*(2*p+3)+b*e*q)-C*(2*a*c*d-b^2*d*(p+2)-a*b*e*q)+
        (C*(2*a*b*f*q-2*a*c*e*(q+1)+b^2*e*(p+q+2))+2*A*c*(b*f*q+c*e*(2*p+q+3)))*x-
        f*(-2*A*c^2*(2*p+2*q+3)+C*(2*a*c*(2*q+1)-b^2*(p+2*q+2)))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (a*B-(A*c-a*C)*x)*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/(2*a*c*(p+1)) - 
  2/((-4*a*c)*(p+1))*
    Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
      Simp[A*c*d*(2*p+3)-a*(C*d+B*e*q)+(A*c*e*(2*p+q+3)-a*(2*B*f*q+C*e*(q+1)))*x-f*(a*C*(2*q+1)-A*c*(2*p+2*q+3))*x^2,x],x] /;
FreeQ[{a,c,d,e,f,A,B,C},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  -(A*c-a*C)*x*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q/(2*a*c*(p+1)) + 
  2/(4*a*c*(p+1))*
    Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1)*
      Simp[A*c*d*(2*p+3)-a*C*d+(A*c*e*(2*p+q+3)-a*C*e*(q+1))*x-f*(a*C*(2*q+1)-A*c*(2*p+2*q+3))*x^2,x],x] /;
FreeQ[{a,c,d,e,f,A,C},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (A*b*c-2*a*B*c+a*b*C-(c*(b*B-2*A*c)-C*(b^2-2*a*c))*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q/(c*(b^2-4*a*c)*(p+1)) - 
  1/(c*(b^2-4*a*c)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1)*
      Simp[-d*(c*(b*B-2*A*c)*(2*p+3)+C*(2*a*c-b^2*(p+2)))+
        (2*f*q*(A*b*c-2*a*B*c+a*b*C))*x-
        f*(c*(b*B-2*A*c)*(2*p+2*q+3)+C*(2*a*c*(2*q+1)-b^2*(p+2*q+2)))*x^2,x],x] /;
FreeQ[{a,b,c,d,f,A,B,C},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  (A*b*c+a*b*C+(2*A*c^2+C*(b^2-2*a*c))*x)*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q/(c*(b^2-4*a*c)*(p+1)) - 
  1/(c*(b^2-4*a*c)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1)*
      Simp[A*c*(2*c*d*(2*p+3))-C*(2*a*c*d-b^2*d*(p+2))+
        (C*(2*a*b*f*q)+2*A*c*(b*f*q))*x-
        f*(-2*A*c^2*(2*p+2*q+3)+C*(2*a*c*(2*q+1)-b^2*(p+2*q+2)))*x^2,x],x] /;
FreeQ[{a,b,c,d,f,A,C},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && GtQ[q,0] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))*
    ((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(b*e+2*a*f))+
      c*(A*(2*c^2*d+b^2*f-c*(b*e+2*a*f))-B*(b*c*d-2*a*c*e+a*b*f)+C*(b^2*d-a*b*e-2*a*(c*d-a*f)))*x) + 
  1/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
      Simp[(b*B-2*A*c-2*a*C)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)+
        (b^2*(C*d+A*f)-b*(B*c*d+A*c*e+a*C*e+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
        e*((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
        (2*f*((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
          (b^2*(C*d+A*f)-b*(B*c*d+A*c*e+a*C*e+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*
          (b*f*(p+1)-c*e*(2*p+q+4)))*x-
        c*f*(b^2*(C*d+A*f)-b*(B*c*d+A*c*e+a*C*e+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,b,c,d,e,f,A,B,C,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && 
  NeQ[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  (a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))*
    ((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b)*(2*c^2*d+b^2*f-c*(b*e+2*a*f))+
      c*(A*(2*c^2*d+b^2*f-c*(b*e+2*a*f))+C*(b^2*d-a*b*e-2*a*(c*d-a*f)))*x) + 
  1/((b^2-4*a*c)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
      Simp[(-2*A*c-2*a*C)*((c*d-a*f)^2-(b*d-a*e)*(c*e-b*f))*(p+1)+
        (b^2*(C*d+A*f)-b*(+A*c*e+a*C*e)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
        e*((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
        (2*f*((A*c-a*C)*(2*a*c*e-b*(c*d+a*f))+(A*b)*(2*c^2*d+b^2*f-c*(b*e+2*a*f)))*(p+q+2)-
          (b^2*(C*d+A*f)-b*(A*c*e+a*C*e)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*
          (b*f*(p+1)-c*e*(2*p+q+4)))*x-
        c*f*(b^2*(C*d+A*f)-b*(A*c*e+a*C*e)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,b,c,d,e,f,A,C,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && 
  NeQ[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))*
    ((A*c-a*C)*(2*a*c*e)+(-a*B)*(2*c^2*d-c*(2*a*f))+
      c*(A*(2*c^2*d-c*(2*a*f))-B*(-2*a*c*e)+C*(-2*a*(c*d-a*f)))*x) + 
  1/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))*
    Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
      Simp[(-2*A*c-2*a*C)*((c*d-a*f)^2-(-a*e)*(c*e))*(p+1)+
        (2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
        e*((A*c-a*C)*(2*a*c*e)+(-a*B)*(2*c^2*d-c*(+2*a*f)))*(p+q+2)-
        (2*f*((A*c-a*C)*(2*a*c*e)+(-a*B)*(2*c^2*d+-c*(+2*a*f)))*(p+q+2)-
          (2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*
          (-c*e*(2*p+q+4)))*x-
        c*f*(2*(A*c*(c*d-a*f)-a*(c*C*d-B*c*e-a*C*f)))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,c,d,e,f,A,B,C,q},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && NeQ[a*c*e^2+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  (a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q+1)/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))*
    ((A*c-a*C)*(2*a*c*e)+c*(A*(2*c^2*d-c*(2*a*f))+C*(-2*a*(c*d-a*f)))*x) + 
  1/((-4*a*c)*(a*c*e^2+(c*d-a*f)^2)*(p+1))*
    Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q*
      Simp[(-2*A*c-2*a*C)*((c*d-a*f)^2-(-a*e)*(c*e))*(p+1)+
        (2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
        e*((A*c-a*C)*(2*a*c*e))*(p+q+2)-
        (2*f*((A*c-a*C)*(2*a*c*e))*(p+q+2)-(2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(-c*e*(2*p+q+4)))*x-
        c*f*(2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,c,d,e,f,A,C,q},x] && NeQ[e^2-4*d*f,0] && LtQ[p,-1] && NeQ[a*c*e^2+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q+1)/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))*
    ((A*c-a*C)*(-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(2*a*f))+
      c*(A*(2*c^2*d+b^2*f-c*(2*a*f))-B*(b*c*d+a*b*f)+C*(b^2*d-2*a*(c*d-a*f)))*x) + 
  1/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q*
      Simp[(b*B-2*A*c-2*a*C)*((c*d-a*f)^2-(b*d)*(-b*f))*(p+1)+
        (b^2*(C*d+A*f)-b*(B*c*d+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
        (2*f*((A*c-a*C)*(-b*(c*d+a*f))+(A*b-a*B)*(2*c^2*d+b^2*f-c*(2*a*f)))*(p+q+2)-
          (b^2*(C*d+A*f)-b*(B*c*d+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*
          (b*f*(p+1)))*x-
        c*f*(b^2*(C*d+A*f)-b*(B*c*d+a*B*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,b,c,d,f,A,B,C,q},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && NeQ[b^2*d*f+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  (a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q+1)/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))*
    ((A*c-a*C)*(-b*(c*d+a*f))+(A*b)*(2*c^2*d+b^2*f-c*(2*a*f))+
      c*(A*(2*c^2*d+b^2*f-c*(2*a*f))+C*(b^2*d-2*a*(c*d-a*f)))*x) + 
  1/((b^2-4*a*c)*(b^2*d*f+(c*d-a*f)^2)*(p+1))*
    Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q*
      Simp[(-2*A*c-2*a*C)*((c*d-a*f)^2-(b*d)*(-b*f))*(p+1)+
        (b^2*(C*d+A*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(a*f*(p+1)-c*d*(p+2))-
        (2*f*((A*c-a*C)*(-b*(c*d+a*f))+(A*b)*(2*c^2*d+b^2*f-c*(2*a*f)))*(p+q+2)-
          (b^2*(C*d+A*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*
          (b*f*(p+1)))*x-
        c*f*(b^2*(C*d+A*f)+2*(A*c*(c*d-a*f)-a*(c*C*d-a*C*f)))*(2*p+2*q+5)*x^2,x],x]/;
FreeQ[{a,b,c,d,f,A,C,q},x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1] && NeQ[b^2*d*f+(c*d-a*f)^2,0] && Not[Not[IntegerQ[p]] && ILtQ[q,-1]] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (B*c*f*(2*p+2*q+3)+C*(b*f*p-c*e*(2*p+q+2))+2*c*C*f*(p+q+1)*x)*(a+b*x+c*x^2)^p*
    (d+e*x+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) - 
  (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3)))*
    Int[(a+b*x+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
      Simp[p*(b*d-a*e)*(C*(c*e-b*f)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
          (p+q+1)*(b^2*C*d*f*p+a*c*(C*(2*d*f-e^2*(2*p+q+2))+f*(B*e-2*A*f)*(2*p+2*q+3)))+
        (2*p*(c*d-a*f)*(C*(c*e-b*f)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
          (p+q+1)*(C*e*f*p*(b^2-4*a*c)-b*c*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d-B*e+2*A*f)*(2*p+2*q+3))))*x+
        (p*(c*e-b*f)*(C*(c*e-b*f)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
          (p+q+1)*(C*f^2*p*(b^2-4*a*c)-c^2*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d-B*e+2*A*f)*(2*p+2*q+3))))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,C,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  (C*(b*f*p-c*e*(2*p+q+2))+2*c*C*f*(p+q+1)*x)*(a+b*x+c*x^2)^p*
    (d+e*x+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) - 
  (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3)))*
    Int[(a+b*x+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
      Simp[p*(b*d-a*e)*(C*(c*e-b*f)*(q+1)-c*(C*e)*(2*p+2*q+3))+
          (p+q+1)*(b^2*C*d*f*p+a*c*(C*(2*d*f-e^2*(2*p+q+2))+f*(-2*A*f)*(2*p+2*q+3)))+
        (2*p*(c*d-a*f)*(C*(c*e-b*f)*(q+1)-c*(C*e)*(2*p+2*q+3))+
          (p+q+1)*(C*e*f*p*(b^2-4*a*c)-b*c*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x+
        (p*(c*e-b*f)*(C*(c*e-b*f)*(q+1)-c*(C*e)*(2*p+2*q+3))+
          (p+q+1)*(C*f^2*p*(b^2-4*a*c)-c^2*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,A,C,q},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (B*c*f*(2*p+2*q+3)+C*(-c*e*(2*p+q+2))+2*c*C*f*(p+q+1)*x)*(a+c*x^2)^p*
    (d+e*x+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) - 
  (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3)))*
    Int[(a+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
      Simp[p*(-a*e)*(C*(c*e)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
          (p+q+1)*(a*c*(C*(2*d*f-e^2*(2*p+q+2))+f*(B*e-2*A*f)*(2*p+2*q+3)))+
        (2*p*(c*d-a*f)*(C*(c*e)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
          (p+q+1)*(C*e*f*p*(-4*a*c)))*x+
        (p*(c*e)*(C*(c*e)*(q+1)-c*(C*e-B*f)*(2*p+2*q+3))+
          (p+q+1)*(C*f^2*p*(-4*a*c)-c^2*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d-B*e+2*A*f)*(2*p+2*q+3))))*x^2,x],x] /;
FreeQ[{a,c,d,e,f,A,B,C,q},x] && NeQ[e^2-4*d*f,0] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  (C*(-c*e*(2*p+q+2))+2*c*C*f*(p+q+1)*x)*(a+c*x^2)^p*(d+e*x+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) - 
  (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3)))*
    Int[(a+c*x^2)^(p-1)*(d+e*x+f*x^2)^q*
      Simp[p*(-a*e)*(C*(c*e)*(q+1)-c*(C*e)*(2*p+2*q+3))+(p+q+1)*(a*c*(C*(2*d*f-e^2*(2*p+q+2))+f*(-2*A*f)*(2*p+2*q+3)))+
        (2*p*(c*d-a*f)*(C*(c*e)*(q+1)-c*(C*e)*(2*p+2*q+3))+(p+q+1)*(C*e*f*p*(-4*a*c)))*x+
        (p*(c*e)*(C*(c*e)*(q+1)-c*(C*e)*(2*p+2*q+3))+
          (p+q+1)*(C*f^2*p*(-4*a*c)-c^2*(C*(e^2-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x^2,x],x] /;
FreeQ[{a,c,d,e,f,A,C,q},x] && NeQ[e^2-4*d*f,0] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(A_.+B_.*x_+C_.*x_^2),x_Symbol] :=
  (B*c*f*(2*p+2*q+3)+C*(b*f*p)+2*c*C*f*(p+q+1)*x)*(a+b*x+c*x^2)^p*
    (d+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) - 
  (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3)))*
    Int[(a+b*x+c*x^2)^(p-1)*(d+f*x^2)^q*
      Simp[p*(b*d)*(C*(-b*f)*(q+1)-c*(-B*f)*(2*p+2*q+3))+
          (p+q+1)*(b^2*C*d*f*p+a*c*(C*(2*d*f)+f*(-2*A*f)*(2*p+2*q+3)))+
        (2*p*(c*d-a*f)*(C*(-b*f)*(q+1)-c*(-B*f)*(2*p+2*q+3))+
          (p+q+1)*(-b*c*(C*(-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x+
        (p*(-b*f)*(C*(-b*f)*(q+1)-c*(-B*f)*(2*p+2*q+3))+
          (p+q+1)*(C*f^2*p*(b^2-4*a*c)-c^2*(C*(-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x^2,x],x] /;
FreeQ[{a,b,c,d,f,A,B,C,q},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_*(A_.+C_.*x_^2),x_Symbol] :=
  (C*(b*f*p)+2*c*C*f*(p+q+1)*x)*(a+b*x+c*x^2)^p*
    (d+f*x^2)^(q+1)/(2*c*f^2*(p+q+1)*(2*p+2*q+3)) - 
  (1/(2*c*f^2*(p+q+1)*(2*p+2*q+3)))*
    Int[(a+b*x+c*x^2)^(p-1)*(d+f*x^2)^q*
      Simp[p*(b*d)*(C*(-b*f)*(q+1))+
          (p+q+1)*(b^2*C*d*f*p+a*c*(C*(2*d*f)+f*(-2*A*f)*(2*p+2*q+3)))+
        (2*p*(c*d-a*f)*(C*(-b*f)*(q+1))+
          (p+q+1)*(-b*c*(C*(-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x+
        (p*(-b*f)*(C*(-b*f)*(q+1))+
          (p+q+1)*(C*f^2*p*(b^2-4*a*c)-c^2*(C*(-4*d*f)*(2*p+q+2)+f*(2*C*d+2*A*f)*(2*p+2*q+3))))*x^2,x],x] /;
FreeQ[{a,b,c,d,f,A,C,q},x] && NeQ[b^2-4*a*c,0] && GtQ[p,0] && NeQ[p+q+1,0] && NeQ[2*p+2*q+3,0] && Not[IGtQ[p,0]] && Not[IGtQ[q,0]]


Int[(A_.+B_.*x_+C_.*x_^2)/((a_+b_.*x_+c_.*x_^2)*(d_+e_.*x_+f_.*x_^2)),x_Symbol] :=
  With[{q=c^2*d^2-b*c*d*e+a*c*e^2+b^2*d*f-2*a*c*d*f-a*b*e*f+a^2*f^2},
  1/q*Int[(A*c^2*d-a*c*C*d-A*b*c*e+a*B*c*e+A*b^2*f-a*b*B*f-a*A*c*f+a^2*C*f+
    c*(B*c*d-b*C*d-A*c*e+a*C*e+A*b*f-a*B*f)*x)/(a+b*x+c*x^2),x] + 
  1/q*Int[(c*C*d^2-B*c*d*e+A*c*e^2+b*B*d*f-A*c*d*f-a*C*d*f-A*b*e*f+a*A*f^2-
    f*(B*c*d-b*C*d-A*c*e+a*C*e+A*b*f-a*B*f)*x)/(d+e*x+f*x^2),x] /;
 NeQ[q,0]] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[(A_.+C_.*x_^2)/((a_+b_.*x_+c_.*x_^2)*(d_+e_.*x_+f_.*x_^2)),x_Symbol] :=
  With[{q=c^2*d^2-b*c*d*e+a*c*e^2+b^2*d*f-2*a*c*d*f-a*b*e*f+a^2*f^2},
  1/q*Int[(A*c^2*d-a*c*C*d-A*b*c*e+A*b^2*f-a*A*c*f+a^2*C*f+
    c*(-b*C*d-A*c*e+a*C*e+A*b*f)*x)/(a+b*x+c*x^2),x] + 
  1/q*Int[(c*C*d^2+A*c*e^2-A*c*d*f-a*C*d*f-A*b*e*f+a*A*f^2-
    f*(-b*C*d-A*c*e+a*C*e+A*b*f)*x)/(d+e*x+f*x^2),x] /;
 NeQ[q,0]] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[(A_.+B_.*x_+C_.*x_^2)/((a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)),x_Symbol] :=
  With[{q=c^2*d^2+b^2*d*f-2*a*c*d*f+a^2*f^2},
  1/q*Int[(A*c^2*d-a*c*C*d+A*b^2*f-a*b*B*f-a*A*c*f+a^2*C*f+c*(B*c*d-b*C*d+A*b*f-a*B*f)*x)/(a+b*x+c*x^2),x] + 
  1/q*Int[(c*C*d^2+b*B*d*f-A*c*d*f-a*C*d*f+a*A*f^2-f*(B*c*d-b*C*d+A*b*f-a*B*f)*x)/(d+f*x^2),x] /;
 NeQ[q,0]] /;
FreeQ[{a,b,c,d,f,A,B,C},x] && NeQ[b^2-4*a*c,0]


Int[(A_.+C_.*x_^2)/((a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)),x_Symbol] :=
  With[{q=c^2*d^2+b^2*d*f-2*a*c*d*f+a^2*f^2},
  1/q*Int[(A*c^2*d-a*c*C*d+A*b^2*f-a*A*c*f+a^2*C*f+c*(-b*C*d+A*b*f)*x)/(a+b*x+c*x^2),x] + 
  1/q*Int[(c*C*d^2-A*c*d*f-a*C*d*f+a*A*f^2-f*(-b*C*d+A*b*f)*x)/(d+f*x^2),x] /;
 NeQ[q,0]] /;
FreeQ[{a,b,c,d,f,A,C},x] && NeQ[b^2-4*a*c,0]


Int[(A_.+B_.*x_+C_.*x_^2)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  C/c*Int[1/Sqrt[d+e*x+f*x^2],x] + 
  1/c*Int[(A*c-a*C+(B*c-b*C)*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,A,B,C},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[(A_.+C_.*x_^2)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  C/c*Int[1/Sqrt[d+e*x+f*x^2],x] + 1/c*Int[(A*c-a*C-b*C*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,A,C},x] && NeQ[b^2-4*a*c,0] && NeQ[e^2-4*d*f,0]


Int[(A_.+B_.*x_+C_.*x_^2)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  C/c*Int[1/Sqrt[d+e*x+f*x^2],x] + 1/c*Int[(A*c-a*C+B*c*x)/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,c,d,e,f,A,B,C},x] && NeQ[e^2-4*d*f,0]


Int[(A_.+C_.*x_^2)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  C/c*Int[1/Sqrt[d+e*x+f*x^2],x] + (A*c-a*C)/c*Int[1/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,c,d,e,f,A,C},x] && NeQ[e^2-4*d*f,0]


Int[(A_.+B_.*x_+C_.*x_^2)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  C/c*Int[1/Sqrt[d+f*x^2],x] + 1/c*Int[(A*c-a*C+(B*c-b*C)*x)/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x] /;
FreeQ[{a,b,c,d,f,A,B,C},x] && NeQ[b^2-4*a*c,0]


Int[(A_.+C_.*x_^2)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  C/c*Int[1/Sqrt[d+f*x^2],x] + 1/c*Int[(A*c-a*C-b*C*x)/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x] /;
FreeQ[{a,b,c,d,f,A,C},x] && NeQ[b^2-4*a*c,0]


Int[(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+B_.*u_+C_.*u_^2),x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(A+B*x+C*x^2),x],x,u] /;
FreeQ[{a,b,c,d,e,f,A,B,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+B_.*u_),x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(A+B*x),x],x,u] /;
FreeQ[{a,b,c,d,e,f,A,B,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+b_.*u_+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+C_.*u_^2),x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q*(A+C*x^2),x],x,u] /;
FreeQ[{a,b,c,d,e,f,A,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+B_.*u_+C_.*u_^2),x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(A+B*x+C*x^2),x],x,u] /;
FreeQ[{a,c,d,e,f,A,B,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+B_.*u_),x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(A+B*x),x],x,u] /;
FreeQ[{a,c,d,e,f,A,B,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]


Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*u_+f_.*u_^2)^q_.*(A_.+C_.*u_^2),x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q*(A+C*x^2),x],x,u] /;
FreeQ[{a,c,d,e,f,A,C,p,q},x] && LinearQ[u,x] && NeQ[u,x]


(* ::Subsection::Closed:: *)
(*1.2.1.9 P(x) (d+e x)^m (a+b x+c x^2)^p*)


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+1)*PolynomialQuotient[Pq,d+e*x,x]*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,d+e*x,x],0]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+1)*PolynomialQuotient[Pq,d+e*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,d+e*x,x],0]


Int[(d_.+e_.*x_)^m_.*P2_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{f=Coeff[P2,x,0],g=Coeff[P2,x,1],h=Coeff[P2,x,2]},
  h*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(c*e*(m+2*p+3)) /;
 EqQ[b*e*h*(m+p+2)+2*c*d*h*(p+1)-c*e*g*(m+2*p+3),0] && EqQ[b*d*h*(p+1)+a*e*h*(m+1)-c*e*f*(m+2*p+3),0]] /;
FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[P2,x,2] && NeQ[m+2*p+3,0]


Int[(d_+e_.*x_)^m_.*P2_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{f=Coeff[P2,x,0],g=Coeff[P2,x,1],h=Coeff[P2,x,2]},
  h*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(c*e*(m+2*p+3)) /;
 EqQ[2*d*h*(p+1)-e*g*(m+2*p+3),0] && EqQ[a*h*(m+1)-c*f*(m+2*p+3),0]] /;
FreeQ[{a,c,d,e,m,p},x] && PolyQ[P2,x,2] && NeQ[m+2*p+3,0]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*Pq*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && PolyQ[Pq,x] && IGtQ[p,-2]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*Pq*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,m},x] && PolyQ[Pq,x] && IGtQ[p,-2]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(d+e*x)^m*Pq*(b+2*c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[b^2-4*a*c,0]


Int[(e_.*x_)^m_.*Pq_*(b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  e*Int[(e*x)^(m-1)*PolynomialQuotient[Pq,b+c*x,x]*(b*x+c*x^2)^(p+1),x] /;
FreeQ[{b,c,e,m,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,b+c*x,x],0]


Int[(d_+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  d*e*Int[(d+e*x)^(m-1)*PolynomialQuotient[Pq,a*e+c*d*x,x]*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[PolynomialRemainder[Pq,a*e+c*d*x,x],0]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  d*e*Int[(d+e*x)^(m-1)*PolynomialQuotient[Pq,a*e+c*d*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[c*d^2+a*e^2,0] && EqQ[PolynomialRemainder[Pq,a*e+c*d*x,x],0]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a*e+c*d*x,x], f=PolynomialRemainder[Pq,a*e+c*d*x,x]},
  f*(2*c*d-b*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
    ExpandToSum[d*e*(p+1)*(b^2-4*a*c)*Q-f*(2*c*d-b*e)*(m+2*p+2),x],x]] /;
FreeQ[{a,b,c,d,e},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && ILtQ[p+1/2,0] && GtQ[m,0]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a*e+c*d*x,x], f=PolynomialRemainder[Pq,a*e+c*d*x,x]},
  -d*f*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*e*(p+1)) + 
  d/(2*a*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1)*ExpandToSum[2*a*e*(p+1)*Q+f*(m+2*p+2),x],x]] /;
FreeQ[{a,c,d,e},x] && PolyQ[Pq,x] && EqQ[c*d^2+a*e^2,0] && ILtQ[p+1/2,0] && GtQ[m,0]


Int[(d_.+e_.*x_)^m_*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)^p,(d+e*x)^m*Pq,x],x] /;
FreeQ[{a,b,c,d,e},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && EqQ[m+Expon[Pq,x]+2*p+1,0] && ILtQ[m,0]


Int[(d_+e_.*x_)^m_*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^2)^p,(d+e*x)^m*Pq,x],x] /;
FreeQ[{a,c,d,e},x] && PolyQ[Pq,x] && EqQ[c*d^2+a*e^2,0] && EqQ[m+Expon[Pq,x]+2*p+1,0] && ILtQ[m,0]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
  f*(d+e*x)^(m+q-1)*(a+b*x+c*x^2)^(p+1)/(c*e^(q-1)*(m+q+2*p+1)) + 
  1/(c*e^q*(m+q+2*p+1))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p*
    ExpandToSum[c*e^q*(m+q+2*p+1)*Pq-c*f*(m+q+2*p+1)*(d+e*x)^q+e*f*(m+p+q)*(d+e*x)^(q-2)*(b*d-2*a*e+(2*c*d-b*e)*x),x],x] /;
 NeQ[m+q+2*p+1,0]] /;
FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
  f*(d+e*x)^(m+q-1)*(a+c*x^2)^(p+1)/(c*e^(q-1)*(m+q+2*p+1)) + 
  1/(c*e^q*(m+q+2*p+1))*Int[(d+e*x)^m*(a+c*x^2)^p*
    ExpandToSum[c*e^q*(m+q+2*p+1)*Pq-c*f*(m+q+2*p+1)*(d+e*x)^q-2*e*f*(m+p+q)*(d+e*x)^(q-2)*(a*e-c*d*x),x],x] /;
 NeQ[m+q+2*p+1,0]] /;
FreeQ[{a,c,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[c*d^2+a*e^2,0] && Not[IGtQ[m,0]]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p*Pq,x] /;
FreeQ[{a,b,c,d,e,m},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && IntegerQ[p]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p*Pq,x] /;
FreeQ[{a,c,d,e,m},x] && PolyQ[Pq,x] && EqQ[c*d^2+a*e^2,0] && IntegerQ[p]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p*Pq,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && EqQ[c*d^2-b*d*e+a*e^2,0] && Not[IntegerQ[p]] && Not[IGtQ[m,0]]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p*Pq,x] /;
FreeQ[{a,c,d,e,m,p},x] && PolyQ[Pq,x] && EqQ[c*d^2+a*e^2,0] && Not[IntegerQ[p]] && Not[IGtQ[m,0]]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a+b*x+c*x^2,x],
        f=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,1]},
  (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(f*b-2*a*g+(2*c*f-b*g)*x)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
    ExpandToSum[(p+1)*(b^2-4*a*c)*(d+e*x)*Q+g*(2*a*e*m+b*d*(2*p+3))-f*(b*e*m+2*c*d*(2*p+3))-e*(2*c*f-b*g)*(m+2*p+3)*x,x],x]] /;
FreeQ[{a,b,c,d,e},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && GtQ[m,0] && 
  (IntegerQ[p] || Not[IntegerQ[m]] || Not[RationalQ[a,b,c,d,e]]) && 
  Not[IGtQ[m,0] && RationalQ[a,b,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a+c*x^2,x],
        f=Coeff[PolynomialRemainder[Pq,a+c*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[Pq,a+c*x^2,x],x,1]},
  (d+e*x)^m*(a+c*x^2)^(p+1)*(a*g-c*f*x)/(2*a*c*(p+1)) + 
  1/(2*a*c*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1)*
    ExpandToSum[2*a*c*(p+1)*(d+e*x)*Q-a*e*g*m+c*d*f*(2*p+3)+c*e*f*(m+2*p+3)*x,x],x]] /;
FreeQ[{a,c,d,e},x] && PolyQ[Pq,x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && GtQ[m,0] && 
  Not[IGtQ[m,0] && RationalQ[a,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[(d+e*x)^m*Pq,a+b*x+c*x^2,x],
        f=Coeff[PolynomialRemainder[(d+e*x)^m*Pq,a+b*x+c*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[(d+e*x)^m*Pq,a+b*x+c*x^2,x],x,1]},
  (b*f-2*a*g+(2*c*f-b*g)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
    ExpandToSum[(p+1)*(b^2-4*a*c)*(d+e*x)^(-m)*Q-(2*p+3)*(2*c*f-b*g)*(d+e*x)^(-m),x],x]] /;
FreeQ[{a,b,c,d,e},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && ILtQ[m,0]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[(d+e*x)^m*Pq,a+c*x^2,x],
        f=Coeff[PolynomialRemainder[(d+e*x)^m*Pq,a+c*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[(d+e*x)^m*Pq,a+c*x^2,x],x,1]},
  (a*g-c*f*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) + 
  1/(2*a*c*(p+1))*Int[(d+e*x)^m*(a+c*x^2)^(p+1)*
    ExpandToSum[2*a*c*(p+1)*(d+e*x)^(-m)*Q+c*f*(2*p+3)*(d+e*x)^(-m),x],x]] /;
FreeQ[{a,c,d,e},x] && PolyQ[Pq,x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && ILtQ[m,0]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a+b*x+c*x^2,x],
        f=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,1]},
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)*(f*(b*c*d-b^2*e+2*a*c*e)-a*g*(2*c*d-b*e)+c*(f*(2*c*d-b*e)-g*(b*d-2*a*e))*x)/
    ((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) + 
  1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
   ExpandToSum[(p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)*Q+
      f*(b*c*d*e*(2*p-m+2)+b^2*e^2*(p+m+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3))-
      g*(a*e*(b*e-2*c*d*m+b*e*m)-b*d*(3*c*d-b*e+2*c*d*p-b*e*p))+
      c*e*(g*(b*d-2*a*e)-f*(2*c*d-b*e))*(m+2*p+4)*x,x],x]] /;
FreeQ[{a,b,c,d,e,m},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[p,-1] && 
  Not[IGtQ[m,0] && RationalQ[a,b,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a+c*x^2,x],
        f=Coeff[PolynomialRemainder[Pq,a+c*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[Pq,a+c*x^2,x],x,1]},
  -(d+e*x)^(m+1)*(a+c*x^2)^(p+1)*(a*(e*f-d*g)+(c*d*f+a*e*g)*x)/(2*a*(p+1)*(c*d^2+a*e^2)) + 
  1/(2*a*(p+1)*(c*d^2+a*e^2))*Int[(d+e*x)^m*(a+c*x^2)^(p+1)*
   ExpandToSum[2*a*(p+1)*(c*d^2+a*e^2)*Q+c*d^2*f*(2*p+3)-a*e*(d*g*m-e*f*(m+2*p+3))+e*(c*d*f+a*e*g)*(m+2*p+4)*x,x],x]] /;
FreeQ[{a,c,d,e,m},x] && PolyQ[Pq,x] && NeQ[c*d^2+a*e^2,0] && LtQ[p,-1] && 
  Not[IGtQ[m,0] && RationalQ[a,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]


Int[(d_.+e_.*x_)^m_*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,d+e*x,x], R=PolynomialRemainder[Pq,d+e*x,x]},
  (e*R*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1))/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
     ExpandToSum[(m+1)*(c*d^2-b*d*e+a*e^2)*Q+c*d*R*(m+1)-b*e*R*(m+p+2)-c*e*R*(m+2*p+3)*x,x],x]] /;
FreeQ[{a,b,c,d,e,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && LtQ[m,-1]


Int[(d_+e_.*x_)^m_*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,d+e*x,x], R=PolynomialRemainder[Pq,d+e*x,x]},
  (e*R*(d+e*x)^(m+1)*(a+c*x^2)^(p+1))/((m+1)*(c*d^2+a*e^2)) + 
  1/((m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p*
     ExpandToSum[(m+1)*(c*d^2+a*e^2)*Q+c*d*R*(m+1)-c*e*R*(m+2*p+3)*x,x],x]] /;
FreeQ[{a,c,d,e,p},x] && PolyQ[Pq,x] && NeQ[c*d^2+a*e^2,0] && LtQ[m,-1]


Int[x_^m_.*Pq_*(a_+b_.*x_^2)^p_,x_Symbol] :=
  Module[{q=Expon[Pq,x],k},
  Int[x^m*Sum[Coeff[Pq,x,2*k]*x^(2*k),{k,0,q/2}]*(a+b*x^2)^p,x] + 
  Int[x^(m+1)*Sum[Coeff[Pq,x,2*k+1]*x^(2*k),{k,0,(q-1)/2}]*(a+b*x^2)^p,x]] /;
FreeQ[{a,b,p},x] && PolyQ[Pq,x] && Not[PolyQ[Pq,x^2]] && IGtQ[m,-2] && Not[IntegerQ[2*p]]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
  f*(d+e*x)^(m+q-1)*(a+b*x+c*x^2)^(p+1)/(c*e^(q-1)*(m+q+2*p+1)) + 
  1/(c*e^q*(m+q+2*p+1))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p*ExpandToSum[c*e^q*(m+q+2*p+1)*Pq-c*f*(m+q+2*p+1)*(d+e*x)^q-
    f*(d+e*x)^(q-2)*(b*d*e*(p+1)+a*e^2*(m+q-1)-c*d^2*(m+q+2*p+1)-e*(2*c*d-b*e)*(m+q+p)*x),x],x] /;
 GtQ[q,1] && NeQ[m+q+2*p+1,0]] /;
FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IGtQ[m,0] && RationalQ[a,b,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x],f=Coeff[Pq,x,Expon[Pq,x]]},
  f*(d+e*x)^(m+q-1)*(a+c*x^2)^(p+1)/(c*e^(q-1)*(m+q+2*p+1)) + 
  1/(c*e^q*(m+q+2*p+1))*Int[(d+e*x)^m*(a+c*x^2)^p*ExpandToSum[c*e^q*(m+q+2*p+1)*Pq-c*f*(m+q+2*p+1)*(d+e*x)^q-
    f*(d+e*x)^(q-2)*(a*e^2*(m+q-1)-c*d^2*(m+q+2*p+1)-2*c*d*e*(m+q+p)*x),x],x] /;
 GtQ[q,1] && NeQ[m+q+2*p+1,0]] /;
FreeQ[{a,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[c*d^2+a*e^2,0] && Not[EqQ[d,0] && True] && 
  Not[IGtQ[m,0] && RationalQ[a,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]


Int[(d_.+e_.*x_)^m_.*Pq_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Coeff[Pq,x,q]/e^q*Int[(d+e*x)^(m+q)*(a+b*x+c*x^2)^p,x] + 
  1/e^q*Int[(d+e*x)^m*(a+b*x+c*x^2)^p*ExpandToSum[e^q*Pq-Coeff[Pq,x,q]*(d+e*x)^q,x],x]] /;
FreeQ[{a,b,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && NeQ[c*d^2-b*d*e+a*e^2,0] && 
  Not[IGtQ[m,0] && RationalQ[a,b,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]


Int[(d_+e_.*x_)^m_.*Pq_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{q=Expon[Pq,x]},
  Coeff[Pq,x,q]/e^q*Int[(d+e*x)^(m+q)*(a+c*x^2)^p,x] + 
  1/e^q*Int[(d+e*x)^m*(a+c*x^2)^p*ExpandToSum[e^q*Pq-Coeff[Pq,x,q]*(d+e*x)^q,x],x]] /;
FreeQ[{a,c,d,e,m,p},x] && PolyQ[Pq,x] && NeQ[c*d^2+a*e^2,0] && 
  Not[IGtQ[m,0] && RationalQ[a,c,d,e] && (IntegerQ[p] || ILtQ[p+1/2,0])]





(* ::Subsection::Closed:: *)
(*1.2.1.8 P(x) (a+b x+c x^2)^p*)


Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Pq*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && IGtQ[p,-2]


Int[Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[x*PolynomialQuotient[Pq,x,x]*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && EqQ[PolynomialRemainder[Pq,x,x],0] && Not[MatchQ[Pq,x^m_.*u_. /; IntegerQ[m]]]


Int[Pq_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[Pq*(b+2*c*x)^(2*p),x] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && EqQ[b^2-4*a*c,0]


Int[Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{Q=PolynomialQuotient[Pq,a+b*x+c*x^2,x],
        f=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,0],
        g=Coeff[PolynomialRemainder[Pq,a+b*x+c*x^2,x],x,1]},
  (b*f-2*a*g+(2*c*f-b*g)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*Int[(a+b*x+c*x^2)^(p+1)*ExpandToSum[(p+1)*(b^2-4*a*c)*Q-(2*p+3)*(2*c*f-b*g),x],x]] /;
FreeQ[{a,b,c},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && LtQ[p,-1]


Int[Pq_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Expon[Pq,x],e=Coeff[Pq,x,Expon[Pq,x]]},
  e*x^(q-1)*(a+b*x+c*x^2)^(p+1)/(c*(q+2*p+1)) + 
  1/(c*(q+2*p+1))*Int[(a+b*x+c*x^2)^p*
    ExpandToSum[c*(q+2*p+1)*Pq-a*e*(q-1)*x^(q-2)-b*e*(q+p)*x^(q-1)-c*e*(q+2*p+1)*x^q,x],x]] /;
FreeQ[{a,b,c,p},x] && PolyQ[Pq,x] && NeQ[b^2-4*a*c,0] && Not[LeQ[p,-1]]



