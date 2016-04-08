(* ::Package:: *)

(* ::Section:: *)
(*Quadratic Product Rules*)


(* ::Subsection::Closed:: *)
(*2.1 (a+b x+c x^2)^p*)


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  (b/2+c*x)/Sqrt[a+b*x+c*x^2]*Int[1/(b/2+c*x),x] /;
FreeQ[{a,b,c},x] && ZeroQ[b^2-4*a*c]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) /;
FreeQ[{a,b,c,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*p+1]


Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[1/Simp[b/2-q/2+c*x,x],x] -
  c/q*Int[1/Simp[b/2+q/2+c*x,x],x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PosQ[b^2-4*a*c] && PerfectSquareQ[b^2-4*a*c]


Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  -2*ArcTanh[(b+2*c*x)/Rt[b^2-4*a*c,2]]/Rt[b^2-4*a*c,2] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PosQ[b^2-4*a*c] && Not[PerfectSquareQ[b^2-4*a*c]]


Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  2*ArcTan[b/Rt[4*a*c-b^2,2]+2*c*x/Rt[4*a*c-b^2,2]]/Rt[4*a*c-b^2,2] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && NegQ[b^2-4*a*c] && RationalQ[b/Rt[4*a*c-b^2,2]]


Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  2*ArcTan[(b+2*c*x)/Rt[4*a*c-b^2,2]]/Rt[4*a*c-b^2,2] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && NegQ[b^2-4*a*c]


Int[1/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
  -1/(b*Sqrt[-c/b^2])*ArcSin[1+2*c*x/b] /;
FreeQ[{b,c},x] && PositiveQ[-c/b^2]


Int[1/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
  2*Subst[Int[1/(1-c*x^2),x],x,x/Sqrt[b*x+c*x^2]] /;
FreeQ[{b,c},x]


(* Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  Subst[Int[1/Sqrt[a-b^2/(4*c)+c*x^2],x],x,b/(2*c)+x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] *)


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  ArcSinh[(b+2*c*x)/(Rt[c,2]*Sqrt[4*a-b^2/c])]/Rt[c,2] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveQ[4*a-b^2/c] && PosQ[c]


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  -ArcSin[(b+2*c*x)/(Rt[-c,2]*Sqrt[4*a-b^2/c])]/Rt[-c,2] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveQ[4*a-b^2/c] && NegQ[c]


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*Subst[Int[1/(4*c-x^2),x],x,(b+2*c*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && Not[PositiveQ[4*a-b^2/c]]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  1/c^p*Int[Simp[b/2-q/2+c*x,x]^p*Simp[b/2+q/2+c*x,x]^p,x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p] && PerfectSquareQ[b^2-4*a*c]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p] && Not[PerfectSquareQ[b^2-4*a*c]]


Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) -
  p*(b^2-4*a*c)/(2*c*(2*p+1))*Int[(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p>0 && Not[IntegerQ[p]]


Int[1/(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
  -2*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]


Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) -
  2*c*(2*p+3)/((p+1)*(b^2-4*a*c))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p<-1 && p!=-3/2


Int[(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(a+b*x+c*x^2)^(p+1)/((p+1)*q*((q-b-2*c*x)/(2*q))^(p+1))*Hypergeometric2F1[-p,p+1,p+2,(b+q+2*c*x)/(2*q)]] /;
FreeQ[{a,b,c,p},x] && NonzeroQ[b^2-4*a*c] && Not[IntegerQ[2*p]]


Int[(a_.+b_.*u_+c_.*v_^2)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,p},x] && ZeroQ[u-v] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*2.2 (d+e x)^m (a+b x+c x^2)^p*)


Int[(d_+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^m*(a+b*x+c*x^2)^(p+(m+1)/2)/(c^((m+1)/2)*(m+2*p+1)) /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && IntegerQ[(m+1)/2]


Int[(d_+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p*Log[RemoveContent[d+e*x,x]]/e /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && ZeroQ[m+2*p+1]


Int[(d_+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+1]


Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((m+1)*(2*c*d-b*e)) /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && ZeroQ[m+2*p+2] && NonzeroQ[m+1]


Int[Sqrt[a_+b_.*x_+c_.*x_^2]/(d_.+e_.*x_)^2,x_Symbol] :=
  Sqrt[a+b*x+c*x^2]/(b+2*c*x)*Int[(b+2*c*x)/(d+e*x)^2,x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e]


Int[(d_.+e_.*x_)^m_*Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  (d+e*x)^(m+1)*Sqrt[a+b*x+c*x^2]/(e*(m+2)) - 
  (2*c*d-b*e)*Sqrt[a+b*x+c*x^2]/(e*(m+2)*(b+2*c*x))*Int[(d+e*x)^m,x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && NonzeroQ[m+2]


Int[1/((d_.+e_.*x_)^2*Sqrt[a_+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -4*c*e*Sqrt[a+b*x+c*x^2]/((2*c*d-b*e)^2*(d+e*x)) + 
  2*c/(2*c*d-b*e)*Int[1/((d+e*x)*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -2*c*e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m*p-1)*(2*c*d-b*e)^2) - 
  (d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((m+2)*(2*c*d-b*e)) /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && ZeroQ[m+2*p+3] && NonzeroQ[m+2]


Int[(d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) + 
  (2*c*d-b*e)/(2*c)*Int[(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && NonzeroQ[p+3/2]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  p*(d+e*x)^(m+2)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1)/(e^2*(m+1)*(m+2*p+1)) + 
  p*(2*p-1)*(2*c*d-b*e)/(e^2*(m+1)*(m+2*p+1))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && RationalQ[m,p] && p>1 && -2<=m<-1 && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  p*(d+e*x)^(m+2)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1)/(e^2*(m+1)*(m+2)) + 
  2*c*p*(2*p-1)/(e^2*(m+1)*(m+2))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && RationalQ[m,p] && p>1 && m<-2 && IntegerQ[2*p] && 
  Not[NegativeIntegerQ[m+2*p+3] && m+3*p+3>0]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  p*(2*c*d-b*e)*(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1)/(2*c*e^2*(m+2*p)*(m+2*p+1)) + 
  p*(2*p-1)*(2*c*d-b*e)^2/(2*c*e^2*(m+2*p)*(m+2*p+1))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && RationalQ[p] && p>0 && 
  NonzeroQ[m+2*p] && NonzeroQ[m+2*p+1] && Not[NegativeIntegerQ[m+2*p+3] && m+3*p+3>0] && 
  Not[RationalQ[m] && m<-2] && Not[IntegerQ[m] && 0<m<2*p] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(m+2*p+2)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*p+1)*(2*c*d-b*e)) + 
  (d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((2*p+1)*(2*c*d-b*e)) + 
  e^2*m*(m+2*p+2)/((p+1)*(2*p+1)*(2*c*d-b*e))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && RationalQ[m,p] && p<-1 && 0<m<=1 && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*m*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)*(2*p+1)) + 
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) + 
  e^2*m*(m-1)/(2*c*(p+1)*(2*p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && RationalQ[m,p] && p<-1 && m>1 && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -2*c*e*(m+2*p+2)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*p+1)*(2*c*d-b*e)^2) + 
  (d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((2*p+1)*(2*c*d-b*e)) + 
  2*c*e^2*(m+2*p+2)*(m+2*p+3)/((p+1)*(2*p+1)*(2*c*d-b*e)^2)*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && RationalQ[m,p] && p<-1 && NonzeroQ[m+p+1] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(m+2*p+1)) + 
  m*(2*c*d-b*e)/(2*c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && RationalQ[m] && m>0 && 
  NonzeroQ[m+2*p+1] && (Not[RationalQ[p]] || -1<=p<0 || IntegerQ[m] && 0<m<2*p || m==1/2 && p<0) && (IntegerQ[m] || IntegerQ[2*p])


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((m+1)*(2*c*d-b*e)) + 
  2*c*(m+2*p+2)/((m+1)*(2*c*d-b*e))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && RationalQ[m] && m<-1 && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p]))*Int[(d+e*x)^m*(b/2+c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && (IntegerQ[p] || PositiveQ[a] && PositiveQ[d] && IntegerQ[m+p])


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && ZeroQ[m+p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(p+1)) /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && ZeroQ[m+p]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*c*d-b*e)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && ZeroQ[m+2*p+2]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && ZeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^2*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) - e^2*(p+2)/(c*(p+1))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && RationalQ[p] && p<-1


Int[(d_+e_.*x_)^2*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)*(a+c*x^2)^(p+1)/(c*(p+1)) - e^2*(p+2)/(c*(p+1))*Int[(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,p},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && RationalQ[p] && p<-1


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(a+b*x+c*x^2)^(m+p)/(a/d+c*x/e)^m,x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && IntegerQ[m] && 
  RationalQ[p] && (0<-m<p || p<-m<0) && m!=2 && m!=-1


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  d^(2*m)/a^m*Int[(a+c*x^2)^(m+p)/(d-e*x)^m,x] /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && IntegerQ[m] && 
  RationalQ[p] && (0<-m<p || p<-m<0) && m!=2 && m!=-1


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  Simplify[m+p]*(2*c*d-b*e)/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && PositiveIntegerQ[Simplify[m+p]]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  2*c*d*Simplify[m+p]/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && PositiveIntegerQ[Simplify[m+p]]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((m+p+1)*(2*c*d-b*e)) + 
  c*Simplify[m+2*p+2]/((m+p+1)*(2*c*d-b*e))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && 
  NegativeIntegerQ[Simplify[m+2*p+2]]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) + 
  Simplify[m+2*p+2]/(2*d*(m+p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && NegativeIntegerQ[Simplify[m+2*p+2]]


Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  2*e*Subst[Int[1/(2*c*d-b*e+e^2*x^2),x],x,Sqrt[a+b*x+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2]


Int[1/(Sqrt[d_+e_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  2*e*Subst[Int[1/(2*c*d+e^2*x^2),x],x,Sqrt[a+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+p+1)) - 
  c*p/(e^2*(m+p+1))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m,p] && p>0 && 
  (m<-2 || ZeroQ[m+2*p+1]) && NonzeroQ[m+p+1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+p+1)) - 
  c*p/(e^2*(m+p+1))*Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] && RationalQ[m,p] && p>0 && 
  (m<-2 || ZeroQ[m+2*p+1]) && NonzeroQ[m+p+1] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  p*(2*c*d-b*e)/(e^2*(m+2*p+1))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m,p] && p>0 && 
  (-2<=m<0 || m+p+1==0) && NonzeroQ[m+2*p+1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+2*p+1)) - 
  2*c*d*p/(e^2*(m+2*p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] && RationalQ[m,p] && p>0 && 
  (-2<=m<0 || m+p+1==0) && NonzeroQ[m+2*p+1] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (2*c*d-b*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) - 
  (2*c*d-b*e)*(m+2*p+2)/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m,p] && p<-1 && 0<m<=1 && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -d*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*e*(p+1)) + 
  d*(m+2*p+2)/(2*a*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] && RationalQ[m,p] && p<-1 && 0<m<=1 && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) - 
  e^2*(m+p)/(c*(p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m,p] && p<-1 && m>1 && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(p+1)) - 
  e^2*(m+p)/(c*(p+1))*Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] && RationalQ[m,p] && p<-1 && m>1 && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  (m+p)*(2*c*d-b*e)/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m] && m>=1 && 
  NonzeroQ[m+2*p+1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  2*c*d*(m+p)/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && ZeroQ[c*d^2+a*e^2] && RationalQ[m] && m>=1 && NonzeroQ[m+2*p+1] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((m+p+1)*(2*c*d-b*e)) + 
  c*(m+2*p+2)/((m+p+1)*(2*c*d-b*e))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m] && m<0 && NonzeroQ[m+p+1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) + 
  (m+2*p+2)/(2*d*(m+p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && ZeroQ[c*d^2+a*e^2] && RationalQ[m] && m<0 && NonzeroQ[m+p+1] && IntegerQ[2*p]


Int[(e_.*x_)^m_.*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (e*x)^m*(b*x+c*x^2)^p/(x^(m+p)*(b+c*x)^p)*Int[x^(m+p)*(b+c*x)^p,x] /;
FreeQ[{b,c,e,m},x] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && PositiveQ[a] && PositiveQ[d]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[1/((d_+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  -4*b*c/(d*(b^2-4*a*c))*Int[1/(b+2*c*x),x] + 
  b^2/(d^2*(b^2-4*a*c))*Int[(d+e*x)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*c*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && ZeroQ[m+2*p+3] && NonzeroQ[p+1]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && PositiveIntegerQ[p] && Not[ZeroQ[m-3] && p!=1]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  b*p/(d*e*(m+1))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && RationalQ[m,p] && p>0 && m<-1 && 
  Not[EvenQ[m] && m+2*p+3<0] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  d*p*(b^2-4*a*c)/(b*e*(m+2*p+1))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && RationalQ[p] && p>0 && 
  Not[RationalQ[m] && m<-1] && Not[PositiveIntegerQ[(m-1)/2] && (Not[IntegerQ[p]] || m<2*p)] && RationalQ[m] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  d*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)) - 
  d*e*(m-1)/(b*(p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && RationalQ[m,p] && p<-1 && m>1 && 
  IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*c*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) - 
  2*c*e*(m+2*p+3)/(e*(p+1)*(b^2-4*a*c))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && RationalQ[p] && p<-1 && 
  Not[RationalQ[m] && m>1] && RationalQ[m] && IntegerQ[2*p]


Int[1/(Sqrt[d_+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  4*(b^2-4*a*c)^(1/4)*Sqrt[-c*(a+b*x+c*x^2)/(b^2-4*a*c)]/(e*Rt[b/d,2]*Sqrt[a+b*x+c*x^2])*
    EllipticF[ArcSin[Rt[b/d,2]*(Sqrt[d+e*x]/(b^2-4*a*c)^(1/4))],-1] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && Not[NegativeQ[c/(b^2-4*a*c)]]


Int[Sqrt[d_+e_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*(b^2-4*a*c)^(3/4)*Sqrt[-c*(a+b*x+c*x^2)/(b^2-4*a*c)]/(c*Rt[b/d,2]*Sqrt[a+b*x+c*x^2])*
    EllipticE[ArcSin[Rt[b/d,2]*(Sqrt[d+e*x]/(b^2-4*a*c)^(1/4))],-1] - 
  e*Sqrt[b^2-4*a*c]/(2*c)*Int[1/(Sqrt[d+e*x]*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && Not[NegativeQ[c/(b^2-4*a*c)]]


Int[1/((d_+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  4*c*Subst[Int[1/(b^2*e-4*a*c*e+4*c*e*x^2),x],x,Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*d*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(b*(m+2*p+1)) + 
  d^2*(m-1)*(b^2-4*a*c)/(b^2*(m+2*p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && RationalQ[m] && m>1 && 
  NonzeroQ[m+2*p+1] && (IntegerQ[2*p] || IntegerQ[m] && RationalQ[p] || OddQ[m])


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -2*b*d*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(d^2*(m+1)*(b^2-4*a*c)) + 
  b^2*(m+2*p+3)/(d^2*(m+1)*(b^2-4*a*c))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && RationalQ[m] && m<-1 && 
  (IntegerQ[2*p] || IntegerQ[m] && RationalQ[p] || IntegerQ[(m+2*p+3)/2])


Int[(d_+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  1/e*Subst[Int[x^m*(a-b^2/(4*c)+(c*x^2)/e^2)^p,x],x,d+e*x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  PositiveIntegerQ[p]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[p] && Not[ZeroQ[m-1] && p>1] 


Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (c*d-e*(b/2-q/2))/q*Int[1/(b/2-q/2+c*x),x] -
  (c*d-e*(b/2+q/2))/q*Int[1/(b/2+q/2+c*x),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  NiceSqrtQ[b^2-4*a*c]


Int[(d_+e_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (e/2+c*d/(2*q))*Int[1/(-q+c*x),x] +
  (e/2-c*d/(2*q))*Int[1/(q+c*x),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NiceSqrtQ[-a*c]


Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  e/(2*c)*Int[(b+2*c*x)/(a+b*x+c*x^2),x] + 
  (2*c*d-b*e)/(2*c)*Int[1/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  Not[NiceSqrtQ[b^2-4*a*c]]


Int[(d_+e_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  d*Int[1/(a+c*x^2),x] + 
  e*Int[x/(a+c*x^2),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && Not[NiceSqrtQ[-a*c]]


(* Int[Sqrt[d_.+e_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[(c*d^2-b*d*e+a*e^2)/c,2]},
  1/2*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x] + 
  1/2*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  NegativeQ[b^2-4*a*c] *)


(* Int[Sqrt[d_+e_.*x_]/(a_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[(c*d^2+a*e^2)/c,2]},
  1/2*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x] + 
  1/2*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NegativeQ[-a*c] *)


(* Int[Sqrt[d_.+e_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-b*e+e*q)/q*Int[1/(Sqrt[d+e*x]*(b-q+2*c*x)),x] - 
  (2*c*d-b*e-e*q)/q*Int[1/(Sqrt[d+e*x]*(b+q+2*c*x)),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] (* && 
  Not[NegativeQ[b^2-4*a*c]] *) *)


(* Int[Sqrt[d_+e_.*x_]/(a_+c_.*x_^2),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (c*d+e*q)/(2*q)*Int[1/(Sqrt[d+e*x]*(-q+c*x)),x] - 
  (c*d-e*q)/(2*q)*Int[1/(Sqrt[d+e*x]*(+q+c*x)),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] (* && Not[NegativeQ[-a*c]] *) *)


Int[Sqrt[d_.+e_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  2*e*Subst[Int[x^2/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e]


Int[Sqrt[d_+e_.*x_]/(a_+c_.*x_^2),x_Symbol] :=
  2*e*Subst[Int[x^2/(c*d^2+a*e^2-2*c*d*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[PolynomialDivide[(d+e*x)^m,a+b*x+c*x^2,x],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  IntegerQ[m] && m>1 && (NonzeroQ[d] || m>2)


Int[(d_+e_.*x_)^m_/(a_+c_.*x_^2),x_Symbol] :=
  Int[PolynomialDivide[(d+e*x)^m,a+c*x^2,x],x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[m] && m>1 && (NonzeroQ[d] || m>2)


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m-1)/(c*(m-1)) + 
  1/c*Int[(d+e*x)^(m-2)*Simp[c*d^2-a*e^2+e*(2*c*d-b*e)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && RationalQ[m] && m>1


Int[(d_+e_.*x_)^m_/(a_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m-1)/(c*(m-1)) + 
  1/c*Int[(d+e*x)^(m-2)*Simp[c*d^2-a*e^2+2*c*d*e*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m] && m>1


Int[1/((d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  e^2/(c*d^2-b*d*e+a*e^2)*Int[1/(d+e*x),x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(c*d-b*e-c*e*x)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e]


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)),x_Symbol] :=
  e^2/(c*d^2+a*e^2)*Int[1/(d+e*x),x] + 
  1/(c*d^2+a*e^2)*Int[(c*d-c*e*x)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


(* Int[1/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  With[{q=Rt[(c*d^2-b*d*e+a*e^2)/c,2]},
  1/(2*q)*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x] - 
  1/(2*q)*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  NegativeQ[b^2-4*a*c] *)


(* Int[1/(Sqrt[d_+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  With[{q=Rt[(c*d^2+a*e^2)/c,2]},
  1/(2*q)*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x] - 
  1/(2*q)*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NegativeQ[-a*c] *)


(* Int[1/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(Sqrt[d+e*x]*(b-q+2*c*x)),x] - 
  2*c/q*Int[1/(Sqrt[d+e*x]*(b+q+2*c*x)),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] (* && 
  Not[NegativeQ[b^2-4*a*c]] *) *)


(* Int[1/(Sqrt[d_+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  c/(2*q)*Int[1/(Sqrt[d+e*x]*(-q+c*x)),x] - 
  c/(2*q)*Int[1/(Sqrt[d+e*x]*(q+c*x)),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] (* && Not[NegativeQ[-a*c]] *) *)


Int[1/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  2*e*Subst[Int[1/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e]


Int[1/(Sqrt[d_+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  2*e*Subst[Int[1/(c*d^2+a*e^2-2*c*d*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x)^(m+1)*Simp[c*d-b*e-c*e*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && RationalQ[m] && m<-1


Int[(d_+e_.*x_)^m_/(a_+c_.*x_^2),x_Symbol] :=
  e*(d+e*x)^(m+1)/((m+1)*(c*d^2+a*e^2)) + 
  c/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*(d-e*x)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m] && m<-1


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,1/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && Not[IntegerQ[m]]


Int[(d_+e_.*x_)^m_/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,1/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[m]]


Int[(d_.+e_.*x_)/(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
  -2*(b*d-2*a*e+(2*c*d-b*e)*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)/(a_+c_.*x_^2)^(3/2),x_Symbol] :=
  (-a*e+c*d*x)/(a*c*Sqrt[a+c*x^2]) /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b*d-2*a*e+(2*c*d-b*e)*x)/((p+1)*(b^2-4*a*c))*(a+b*x+c*x^2)^(p+1) - 
  (2*p+3)*(2*c*d-b*e)/((p+1)*(b^2-4*a*c))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[p] && p<-1 && p!=-3/2


Int[(d_+e_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a*e-c*d*x)/(2*a*c*(p+1))*(a+c*x^2)^(p+1) + 
  d*(2*p+3)/(2*a*(p+1))*Int[(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[p] && p<-1 && p!=-3/2


Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) + 
  (2*c*d-b*e)/(2*c)*Int[(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  Not[RationalQ[p] && p<=-1]


Int[(d_+e_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(a+c*x^2)^(p+1)/(2*c*(p+1)) + 
  d*Int[(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && NonzeroQ[c*d^2+a*e^2] && Not[RationalQ[p] && p<=-1]


Int[(d_.+e_.*x_)^m_/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
  Int[(d+e*x)^m/(Sqrt[x]*Sqrt[b+c*x]),x] /;
FreeQ[{b,c,d,e},x] && NonzeroQ[2*c*d-b*e] && NonzeroQ[c*d-b*e] && RationalQ[m] && m^2==1/4 && PositiveQ[b] && NegativeQ[c]


Int[(d_.+e_.*x_)^m_/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
  Sqrt[x]*Sqrt[b+c*x]/Sqrt[b*x+c*x^2]*Int[(d+e*x)^m/(Sqrt[x]*Sqrt[b+c*x]),x] /;
FreeQ[{b,c,d,e},x] && NonzeroQ[2*c*d-b*e] && NonzeroQ[c*d-b*e] && RationalQ[m] && m^2==1/4


Int[(d_.+e_.*x_)^m_/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*Rt[b^2-4*a*c,2]*(d+e*x)^m*Sqrt[-c*(a+b*x+c*x^2)/(b^2-4*a*c)]/
    (c*Sqrt[a+b*x+c*x^2]*(2*c*(d+e*x)/(2*c*d-b*e-e*Rt[b^2-4*a*c,2]))^m)*
    Subst[Int[(1+2*e*Rt[b^2-4*a*c,2]*x^2/(2*c*d-b*e-e*Rt[b^2-4*a*c,2]))^m/Sqrt[1-x^2],x],x,
      Sqrt[(b+Rt[b^2-4*a*c,2]+2*c*x)/(2*Rt[b^2-4*a*c,2])]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && ZeroQ[m^2-1/4]


Int[(d_+e_.*x_)^m_/Sqrt[a_+c_.*x_^2],x_Symbol] :=
  2*a*Rt[-c/a,2]*(d+e*x)^m*Sqrt[(a+c*x^2)/a]/(c*Sqrt[a+c*x^2]*(c*(d+e*x)/(c*d-a*e*Rt[-c/a,2]))^m)*
    Subst[Int[(1+2*a*e*Rt[-c/a,2]*x^2/(c*d-a*e*Rt[-c/a,2]))^m/Sqrt[1-x^2],x],x,Sqrt[(1-Rt[-c/a,2]*x)/2]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && ZeroQ[m^2-1/4]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^p/(2*(m+1)*(c*d^2-b*d*e+a*e^2)) + 
  p*(b^2-4*a*c)/(2*(m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && m+2*p+2==0 && p>0


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(-2*a*e+(2*c*d)*x)*(a+c*x^2)^p/(2*(m+1)*(c*d^2+a*e^2)) - 
  4*a*c*p/(2*(m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && m+2*p+2==0 && p>0


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) - 
  2*(2*p+3)*(c*d^2-b*d*e+a*e^2)/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && m+2*p+2==0 && p<-1


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(a*e-c*d*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) + 
  (2*p+3)*(c*d^2+a*e^2)/(2*a*c*(p+1))*Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && m+2*p+2==0 && p<-1


Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -2*Subst[Int[1/(4*c*d^2-4*b*d*e+4*a*e^2-x^2),x],x,(2*a*e-b*d-(2*c*d-b*e)*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e]


Int[1/((d_+e_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  -Subst[Int[1/(c*d^2+a*e^2-x^2),x],x,(a*e-c*d*x)/Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e},x]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(b-Rt[b^2-4*a*c,2]+2*c*x)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/
    ((m+1)*(2*c*d-b*e+e*Rt[b^2-4*a*c,2])*
      ((2*c*d-b*e+e*Rt[b^2-4*a*c,2])*(b+Rt[b^2-4*a*c,2]+2*c*x)/((2*c*d-b*e-e*Rt[b^2-4*a*c,2])*(b-Rt[b^2-4*a*c,2]+2*c*x)))^p)*
    Hypergeometric2F1[m+1,-p,m+2,-4*c*Rt[b^2-4*a*c,2]*(d+e*x)/((2*c*d-b*e-e*Rt[b^2-4*a*c,2])*(b-Rt[b^2-4*a*c,2]+2*c*x))] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && Not[IntegerQ[p]] && 
  ZeroQ[m+2*p+2]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (Rt[-a*c,2]-c*x)*(d+e*x)^(m+1)*(a+c*x^2)^p/
    ((m+1)*(c*d+e*Rt[-a*c,2])*((c*d+e*Rt[-a*c,2])*(Rt[-a*c,2]+c*x)/((c*d-e*Rt[-a*c,2])*(-Rt[-a*c,2]+c*x)))^p)*
    Hypergeometric2F1[m+1,-p,m+2,2*c*Rt[-a*c,2]*(d+e*x)/((c*d-e*Rt[-a*c,2])*(Rt[-a*c,2]-c*x))] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && ZeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  m*(2*c*d-b*e)/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && ZeroQ[m+2*p+3] && 
  RationalQ[p] && p<-1


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^m*(2*c*x)*(a+c*x^2)^(p+1)/(4*a*c*(p+1)) - 
  m*(2*c*d)/(4*a*c*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && ZeroQ[m+2*p+3] && RationalQ[p] && p<-1


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  (2*c*d-b*e)/(2*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && ZeroQ[m+2*p+3]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  c*d/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && ZeroQ[m+2*p+3]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  p/(e*(m+1))*Int[(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && RationalQ[p] && p>0 && 
  (IntegerQ[p] || RationalQ[m] && m<-1) && NonzeroQ[m+1] && Not[NegativeIntegerQ[m+2*p+1]] && 
  (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+1)) - 
  2*c*p/(e*(m+1))*Int[x*(d+e*x)^(m+1)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[p] && p>0 && 
  (IntegerQ[p] || RationalQ[m] && m<-1) && NonzeroQ[m+1] && Not[NegativeIntegerQ[m+2*p+1]] && 
  (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  p/(e*(m+2*p+1))*Int[(d+e*x)^m*Simp[b*d-2*a*e+(2*c*d-b*e)*x,x]*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && RationalQ[p] && p>0 && 
  NonzeroQ[m+2*p+1] && (Not[RationalQ[m]] || m<1) && Not[NegativeIntegerQ[m+2*p]] && 
  (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+2*p+1)) + 
  2*p/(e*(m+2*p+1))*Int[(d+e*x)^m*Simp[a*e-c*d*x,x]*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[p] && p>0 && 
  NonzeroQ[m+2*p+1] && (Not[RationalQ[m]] || m<1) && Not[NegativeIntegerQ[m+2*p]] && 
  (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) - 
  1/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(b*e*m+2*c*d*(2*p+3)+2*c*e*(m+2*p+3)*x)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && p<-1 && m>0 && (m<1 || NegativeIntegerQ[m+2*p+3] && m!=2) && 
  (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -x*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*(p+1)) + 
  1/(2*a*(p+1))*Int[(d+e*x)^(m-1)*(d*(2*p+3)+e*(m+2*p+3)*x)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[m,p] && p<-1 && m>0 && (m<1 || NegativeIntegerQ[m+2*p+3] && m!=2) && 
  (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*
    Int[(d+e*x)^(m-2)*
      Simp[e*(2*a*e*(m-1)+b*d*(2*p-m+4))-2*c*d^2*(2*p+3)+e*(b*e-2*d*c)*(m+2*p+2)*x,x]*
      (a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && p<-1 && m>1 && (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(a*e-c*d*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) + 
  1/((p+1)*(-2*a*c))*
    Int[(d+e*x)^(m-2)*Simp[a*e^2*(m-1)-c*d^2*(2*p+3)-d*c*e*(m+2*p+2)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[m,p] && p<-1 && m>1 && (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(b*c*d-b^2*e+2*a*c*e+c*(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) + 
  1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^m*
      Simp[b*c*d*e*(2*p-m+2)+b^2*e^2*(m+p+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3)-c*e*(2*c*d-b*e)*(m+2*p+4)*x,x]*
      (a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[p] && p<-1 && (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(a*e+c*d*x)*(a+c*x^2)^(p+1)/(2*a*(p+1)*(c*d^2+a*e^2)) + 
  1/(2*a*(p+1)*(c*d^2+a*e^2))*
    Int[(d+e*x)^m*Simp[c*d^2*(2*p+3)+a*e^2*(m+2*p+3)+c*e*d*(m+2*p+4)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[p] && p<-1 && (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  1/(c*(m+2*p+1))*
    Int[(d+e*x)^(m-2)*
      Simp[c*d^2*(m+2*p+1)-e*(a*e*(m-1)+b*d*(p+1))+e*(2*c*d-b*e)*(m+p)*x,x]*
      (a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  If[RationalQ[m], m>1, SumSimplerQ[m,-2]] && NonzeroQ[m+2*p+1] && (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  1/(c*(m+2*p+1))*
    Int[(d+e*x)^(m-2)*Simp[c*d^2*(m+2*p+1)-a*e^2*(m-1)+2*c*d*e*(m+p)*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && 
  If[RationalQ[m], m>1, SumSimplerQ[m,-2]] && NonzeroQ[m+2*p+1] && (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p])


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^(m+1)*Simp[c*d*(m+1)-b*e*(m+p+2)-c*e*(m+2*p+3)*x,x]*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  (RationalQ[m] && m<-1 && (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p]) || 
   SumSimplerQ[m,1] && IntegerQ[p] && NonzeroQ[m+1] || 
   NegativeIntegerQ[Simplify[m+2*p+3]] && NonzeroQ[m+1])


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  c/((m+1)*(c*d^2+a*e^2))*
    Int[(d+e*x)^(m+1)*Simp[d*(m+1)-e*(m+2*p+3)*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && 
  (RationalQ[m] && m<-1 && (IntegerQ[p] || PositiveIntegerQ[m] || IntegerQ[2*m] && IntegerQ[2*p]) || 
   SumSimplerQ[m,1] && IntegerQ[p] && NonzeroQ[m+1] || 
   NegativeIntegerQ[Simplify[m+2*p+3]] && NonzeroQ[m+1])


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(1/4)),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*(a+c*x^2)^(1/4)),x] - e*Int[x/((d^2-e^2*x^2)*(a+c*x^2)^(1/4)),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(3/4)),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*(a+c*x^2)^(3/4)),x] - e*Int[x/((d^2-e^2*x^2)*(a+c*x^2)^(3/4)),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2^(2*p)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)*(e*(b-q+2*c*x)/(c*(d+e*x)))^p*(e*(b+q+2*c*x)/(c*(d+e*x)))^p)*
    AppellF1[-m-2*p-1,-p,-p,-m-2*p,(2*c*d-b*e-e*q)/(2*c*(d+e*x)),(2*c*d-b*e+e*q)/(2*c*(d+e*x))]] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && Not[IntegerQ[p]] && 
  NegativeIntegerQ[m]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  2^(2*p)*(d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+2*p+1)*(2*e*(-q+c*x)/(c*(d+e*x)))^p*(2*e*(q+c*x)/(c*(d+e*x)))^p)*
    AppellF1[-m-2*p-1,-p,-p,-m-2*p,(c*d-e*q)/(c*(d+e*x)),(c*d+e*q)/(c*(d+e*x))]] /;
FreeQ[{a,c,d,e,p},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && NegativeIntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)*(1-2*c*(d+e*x)/(2*c*d-b*e-e*q))^p*(1-2*c*(d+e*x)/(2*c*d-b*e+e*q))^p)*
    AppellF1[m+1,-p,-p,m+2,2*c*(d+e*x)/(2*c*d-b*e-e*q),2*c*(d+e*x)/(2*c*d-b*e+e*q)]] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && Not[IntegerQ[p]] && 
  Not[NegativeIntegerQ[m]] && Not[NegativeIntegerQ[m+2*p+1]]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+1)*(1-c*(d+e*x)/(c*d-e*q))^p*(1-c*(d+e*x)/(c*d+e*q))^p)*
    AppellF1[m+1,-p,-p,m+2,c*(d+e*x)/(c*d-e*q),c*(d+e*x)/(c*d+e*q)]] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && Not[NegativeIntegerQ[m]] && Not[NegativeIntegerQ[m+2*p+1]]


Int[(d_.+e_.*u_)^m_.*(a_+b_.*v_+c_.*w_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(d_.+e_.*u_)^m_.*(a_+c_.*w_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(a+c*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*2.3 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p*)


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  (f+g*x)/Sqrt[a+b*x+c*x^2]*Int[(d+e*x)^m,x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*f-b*g]


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -f*g*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)*(e*f-d*g)) /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  ZeroQ[m+2*p+3]


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) - 
  e*g*m/(2*c*(p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  RationalQ[m,p] && p<-1 && m>0


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -f*g*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)*(e*f-d*g)) + 
  e*f*g*(m+2*p+3)/(b*(p+1)*(e*f-d*g))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  RationalQ[p] && p<-1 && Not[RationalQ[m] && m>0]


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(f+g*x)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  g*(2*p+1)/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  RationalQ[m] && m<-1 && NonzeroQ[2*p+1] && 
  (Not[RationalQ[p]] || p>0 && (Not[IntegerQ[m]] || m>=-2*p-2 || m<-4*(p+1)))


Int[(d_.+e_.*x_)^m_*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  2*f*g*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(b*(m+1)*(e*f-d*g)) - 
  g*(m+2*p+3)/((m+1)*(e*f-d*g))*Int[(d+e*x)^(m+1)*(f+g*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  RationalQ[m] && m<-1 && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) - 
  b*m*(e*f-d*g)/(2*c*f*(m+2*p+2))*Int[(d+e*x)^(m-1)*(f+g*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  PositiveIntegerQ[m] && NonzeroQ[m+2*p+2] && (Not[RationalQ[p]] || m<2*p+2)


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(f+g*x)*(a+b*x+c*x^2)^p/(e*(m+2*p+2)) + 
  (e*f-d*g)*(2*p+1)/(e*(m+2*p+2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && ZeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  NonzeroQ[m+2*p+2]


Int[(f_.+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  (2*c*f-b*g)/(2*c*d-b*e)*Int[(a+b*x+c*x^2)^p,x] - 
  (e*f-d*g)/(2*c*d-b*e)*Int[(b+2*c*x)*(a+b*x+c*x^2)^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  NonzeroQ[2*c*d-b*e] && RationalQ[p] && p<0


Int[(d_.+e_.*x_)^m_.*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (e*f-d*g)/e*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] + 
  g/e*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  (ZeroQ[m+2*p+2] && NonzeroQ[m+1] || ZeroQ[2*c*d-b*e] && NonzeroQ[m-1])


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (2*c*f-b*g)/(2*c*d-b*e)*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] - 
  (e*f-d*g)/(2*c*d-b*e)*Int[(d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  NonzeroQ[2*c*d-b*e] && ZeroQ[m+2*p+3]


Int[(d_.+e_.*x_)^m_*(f_+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/(e*(m+1)*(2*c*d-b*e)) + 
  (2*c*e*f*(m+2*p+2)-g*(2*c*d*(2*p+1)+b*e*(m+1)))/(e*(m+1)*(2*c*d-b*e))*
    Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  NonzeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[m] && m<-1


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*e*(m+2*p+2)) + 
  (2*c*e*f*(m+2*p+2)-g*(b*e*(m+1)+2*c*(d+2*d*p)))/(2*c*e*(m+2*p+2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*c*f-b*g] && Not[IntegerQ[p]] && 
  NonzeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && Not[RationalQ[m] && m<-1] && Not[ZeroQ[m-1] && SimplerQ[f+g*x,d+e*x]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/(c^IntPart[p]*(b/2+c*x)^(2*FracPart[p]))*Int[(d+e*x)^m*(f+g*x)^n*(b/2+c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  (IntegerQ[p] || PositiveQ[a] && PositiveQ[d] && ZeroQ[m+p])


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g)]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && ZeroQ[m*(d*g+e*f)+2*e*f*(p+1)]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (g*(c*d-b*e)+c*e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(2*c*d-b*e)) - 
  e*(m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*(p+1)*(2*c*d-b*e))*
    Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m,p] && p<-1 && m>0


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d*g+e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) - 
  e*(m*(d*g+e*f)+2*e*f*(p+1))/(2*c*d*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && RationalQ[m,p] && p<-1 && m>0


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (g*(c*d-b*e)+c*e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(2*c*d-b*e)) - 
  e*(m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*(p+1)*(2*c*d-b*e))*
    Int[(d+e*x)^Simplify[m-1]*(a+b*x+c*x^2)^Simplify[p+1],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  SumSimplerQ[p,1] && SumSimplerQ[m,-1] && NonzeroQ[p+1]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d*g+e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) - 
  e*(m*(d*g+e*f)+2*e*f*(p+1))/(2*c*d*(p+1))*Int[(d+e*x)^Simplify[m-1]*(a+c*x^2)^Simplify[p+1],x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && SumSimplerQ[p,1] && SumSimplerQ[m,-1] && NonzeroQ[p+1]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d*g-e*f)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((2*c*d-b*e)*(m+p+1)) + 
  (m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(e*(2*c*d-b*e)*(m+p+1))*
    Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  (RationalQ[m] && m<-1 && Not[PositiveIntegerQ[m+p+1]] || RationalQ[m,p] && m<0 && p<-1 || ZeroQ[m+2*p+2]) && NonzeroQ[m+p+1]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d*g-e*f)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) + 
  (m*(g*c*d+c*e*f)+2*e*c*f*(p+1))/(e*(2*c*d)*(m+p+1))*
    Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  (RationalQ[m] && m<-1 && Not[PositiveIntegerQ[m+p+1]] || RationalQ[m,p] && m<0 && p<-1 || ZeroQ[m+2*p+2]) && NonzeroQ[m+p+1]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  (m*(g*(c*d-b*e)+c*e*f)+e*(p+1)*(2*c*f-b*g))/(c*e*(m+2*p+2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[m+2*p+2]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  (m*(d*g+e*f)+2*e*f*(p+1))/(e*(m+2*p+2))*Int[(d+e*x)^m*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && NonzeroQ[m+2*p+2]


Int[x_^2*(f_+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  x^2*(a*g-c*f*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) - 
  1/(2*a*c*(p+1))*Int[x*Simp[2*a*g-c*f*(2*p+5)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,f,g},x] && ZeroQ[a*g^2+f^2*c] && RationalQ[p] && p<-2


Int[x_^2*(f_+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  1/c*Int[(f+g*x)*(a+c*x^2)^(p+1),x] - f^2/c*Int[(a+c*x^2)^(p+1)/(f-g*x),x] /;
FreeQ[{a,c,f,g,p},x] && ZeroQ[a*g^2+f^2*c]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(f+g*x)^n*(a+b*x+c*x^2)^(m+p)/(a/d+c*x/e)^m,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && 
  IntegersQ[m,n] && RationalQ[p] && (0<-m<p+1 || p<-m<0)


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  d^(2*m)/a^m*Int[(f+g*x)^n*(a+c*x^2)^(m+p)/(d-e*x)^m,x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && 
  IntegersQ[m,n] && RationalQ[p] && (0<-m<p+1 || p<-m<0)


Int[(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  -(f+g*x)^n*(a+b*x+c*x^2)^p*(a*(2*c*d-b*e)+c*(b*d-2*a*e)*x)/(d*e*p*(b^2-4*a*c)) - 
  1/(d*e*p*(b^2-4*a*c))*Int[(f+g*x)^(n-1)*(a+b*x+c*x^2)^p*
    Simp[b*(a*e*g*n-c*d*f*(2*p+1))-2*a*c*(d*g*n-e*f*(2*p+1))-c*g*(b*d-2*a*e)*(n+2*p+1)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && 
  PositiveIntegerQ[n] && NegativeIntegerQ[n+2*p]


Int[(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  (f+g*x)^n*(a+c*x^2)^p*(d-e*x)/(2*d*e*p) - 
  1/(2*d*e*p)*Int[(f+g*x)^(n-1)*(a+c*x^2)^p*Simp[d*g*n-e*f*(2*p+1)-e*g*(n+2*p+1)*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && 
  PositiveIntegerQ[n] && NegativeIntegerQ[n+2*p]


Int[(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  -(f+g*x)^(n+1)*(a+b*x+c*x^2)^p*(a*c*d*(2*c*f-b*g)-a*e*(b*c*f-b^2*g+2*a*c*g)+c*(c*d*(b*f-2*a*g)-a*e*(2*c*f-b*g))*x)/
    (d*e*p*(b^2-4*a*c)*(c*f^2-b*f*g+a*g^2)) - 
  (1/(d*e*p*(b^2-4*a*c)*(c*f^2-b*f*g+a*g^2)))*Int[(f+g*x)^n*(a+b*x+c*x^2)^p*
    Simp[b^2*g*(c*d*f*p-a*e*g*(n+p+1))+b*c*(a*g*(d*g*(n+1)+e*f*(n-2*p))-c*d*f^2*(2*p+1))+
      2*a*c*(a*e*g^2*(n+2*p+1)+c*f*(e*f-d*g*n+2*e*f*p))+
      c*g*(2*a*c*(e*f+d*g)-b*(c*d*f+a*e*g))*(n+2*p+2)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && 
  NegativeIntegerQ[n] && NegativeIntegerQ[n+2*p]


Int[(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  (f+g*x)^(n+1)*(a+c*x^2)^p*(c*d*f-a*e*g-c*(e*f+d*g)*x)/(2*d*e*p*(c*f^2+a*g^2)) + 
  (1/(2*d*e*p*(c*f^2+a*g^2)))*Int[(f+g*x)^n*(a+c*x^2)^p*
    Simp[(a*e*g^2*(n+2*p+1)-c*f*(d*g*n-e*(f+2*f*p)))+c*g*(e*f+d*g)*(n+2*p+2)*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && 
  NegativeIntegerQ[n] && NegativeIntegerQ[n+2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(m-n-1)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && ZeroQ[c*e*f+c*d*g-b*e*g] && NonzeroQ[m-n-1]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(m-n-1)) /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && ZeroQ[e*f+d*g] && NonzeroQ[m-n-1]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g-b*e*g)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && ZeroQ[m-n-2]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*(n+1)*(e*f+d*g)) /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && ZeroQ[m-n-2]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p/(g*(n+1)) + 
  c*m/(e*g*(n+1))*Int[(d+e*x)^(m+1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n,p] && p>0 && n<-1 && Not[IntegerQ[n+p] && n+p+2<=0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p/(g*(n+1)) + 
  c*m/(e*g*(n+1))*Int[(d+e*x)^(m+1)*(f+g*x)^(n+1)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n,p] && p>0 && n<-1 && Not[IntegerQ[n+p] && n+p+2<=0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p/(g*(m-n-1)) - 
  m*(c*e*f+c*d*g-b*e*g)/(e^2*g*(m-n-1))*Int[(d+e*x)^(m+1)*(f+g*x)^n*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n,p] && p>0 && NonzeroQ[m-n-1] && Not[PositiveIntegerQ[n]] && 
  Not[IntegerQ[n+p] && n+p+2<0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p/(g*(m-n-1)) - 
  c*m*(e*f+d*g)/(e^2*g*(m-n-1))*Int[(d+e*x)^(m+1)*(f+g*x)^n*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n,p] && p>0 && NonzeroQ[m-n-1] && Not[PositiveIntegerQ[n]] && 
  Not[IntegerQ[n+p] && n+p+2<0]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) - 
  e*g*n/(c*(p+1))*Int[(d+e*x)^(m-1)*(f+g*x)^(n-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n,p] && p<-1 && n>0


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(p+1)) - 
  e*g*n/(c*(p+1))*Int[(d+e*x)^(m-1)*(f+g*x)^(n-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n,p] && p<-1 && n>0


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((p+1)*(c*e*f+c*d*g-b*e*g)) + 
  e^2*g*(m-n-2)/((p+1)*(c*e*f+c*d*g-b*e*g))*Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n,p] && p<-1


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*(p+1)*(e*f+d*g)) + 
  e^2*g*(m-n-2)/(c*(p+1)*(e*f+d*g))*Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n,p] && p<-1


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^(p+1)/(c*(m-n-1)) - 
  n*(c*e*f+c*d*g-b*e*g)/(c*e*(m-n-1))*Int[(d+e*x)^m*(f+g*x)^(n-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n] && n>0 && NonzeroQ[m-n-1] && (IntegerQ[2*p] || IntegerQ[n])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^(p+1)/(c*(m-n-1)) - 
  n*(e*f+d*g)/(e*(m-n-1))*Int[(d+e*x)^m*(f+g*x)^(n-1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n] && n>0 && NonzeroQ[m-n-1] && (IntegerQ[2*p] || IntegerQ[n])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g-b*e*g)) - 
  c*e*(m-n-2)/((n+1)*(c*e*f+c*d*g-b*e*g))*Int[(d+e*x)^m*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n] && n<-1 && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -e^2*(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/((n+1)*(c*e*f+c*d*g)) - 
  e*(m-n-2)/((n+1)*(e*f+d*g))*Int[(d+e*x)^m*(f+g*x)^(n+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p] && RationalQ[n] && n<-1 && IntegerQ[2*p]


Int[Sqrt[d_+e_.*x_]/((f_.+g_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  2*e^2*Subst[Int[1/(c*(e*f+d*g)-b*e*g+e^2*g*x^2),x],x,Sqrt[a+b*x+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2]


Int[Sqrt[d_+e_.*x_]/((f_.+g_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  2*e^2*Subst[Int[1/(c*(e*f+d*g)+e^2*g*x^2),x],x,Sqrt[a+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(c*g*(n+p+2)) /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p-1] && ZeroQ[b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3)] && NonzeroQ[n+p+2]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+p+2)) /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p-1] && ZeroQ[e*f*(p+1)-d*g*(2*n+p+3)] && NonzeroQ[n+p+2]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(e*f-d*g)*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(g*(n+1)*(c*e*f+c*d*g-b*e*g)) - 
  e*(b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3))/(g*(n+1)*(c*e*f+c*d*g-b*e*g))*
    Int[(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p-1] && RationalQ[n] && n<-1 && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(e*f-d*g)*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+1)*(e*f+d*g)) - 
  e*(e*f*(p+1)-d*g*(2*n+p+3))/(g*(n+1)*(e*f+d*g))*Int[(d+e*x)^(m-1)*(f+g*x)^(n+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p-1] && RationalQ[n] && n<-1 && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p+1)/(c*g*(n+p+2)) - 
  (b*e*g*(n+1)+c*e*f*(p+1)-c*d*g*(2*n+p+3))/(c*g*(n+p+2))*Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p-1] && Not[RationalQ[n] && n<-1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e^2*(d+e*x)^(m-2)*(f+g*x)^(n+1)*(a+c*x^2)^(p+1)/(c*g*(n+p+2)) - 
  (e*f*(p+1)-d*g*(2*n+p+3))/(g*(n+p+2))*Int[(d+e*x)^(m-1)*(f+g*x)^n*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[p]] && ZeroQ[m+p-1] && Not[RationalQ[n] && n<-1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && (PositiveIntegerQ[m] || IntegersQ[m,n])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[1/Sqrt[a+c*x^2],(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^(p+1/2),x],x] /;
FreeQ[{a,c,d,e,f,g,n,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && IntegerQ[p-1/2] && IntegersQ[m,n] && Not[m<0 && p<0] && p!=1/2


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g,n,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && (PositiveIntegerQ[m] || IntegersQ[m,n])


Int[x_^2*(a_.+b_.*x_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  d^2/e^2*Int[(a+b*x+c*x^2)^p/(d+e*x),x] - 1/e^2*Int[(d-e*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2]


Int[x_^2*(a_+c_.*x_^2)^p_/(d_+e_.*x_),x_Symbol] :=
  d^2/e^2*Int[(a+c*x^2)^p/(d+e*x),x] - 1/e^2*Int[(d-e*x)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && ZeroQ[c*d^2+a*e^2]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^2*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(f+g*x)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+3)) - 
  1/(c*e^2*(m+2*p+3))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p*
    Simp[b*e*g*(d*g+e*f*(m+p+1))-c*(d^2*g^2+d*e*f*g*m+e^2*f^2*(m+2*p+3))+
      e*g*(b*e*g*(m+p+2)-c*(d*g*m+e*f*(m+2*p+4)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]] && 
  NonzeroQ[m+2*p+3]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^2*(a_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(f+g*x)*(a+c*x^2)^(p+1)/(c*(m+2*p+3)) - 
  1/(c*e^2*(m+2*p+3))*Int[(d+e*x)^m*(a+c*x^2)^p*
    Simp[-c*(d^2*g^2+d*e*f*g*m+e^2*f^2*(m+2*p+3))-c*e*g*(d*g*m+e*f*(m+2*p+4))*x,x],x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && NonzeroQ[m+2*p+3]


Int[(e_.*x_)^m_*(f_.+g_.*x_)^n_.*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (e*x)^m*(b*x+c*x^2)^p/(x^(m+p)*(b+c*x)^p)*Int[x^(m+p)*(f+g*x)^n*(b+c*x)^p,x] /;
FreeQ[{b,c,e,f,g,m,n},x] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && PositiveQ[a] && PositiveQ[d]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
(*(a+b*x+c*x^2)^p/((d+e*x)^p*(a*e+c*d*x)^p)*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a*e+c*d*x)^p,x] /; *)
  (a+b*x+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a+c*x^2)^FracPart[p]/((d+e*x)^FracPart[p]*(a/d+(c*x)/e)^FracPart[p])*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[p]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[p]


Int[(f_.+g_.*x_)/((d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  e*(e*f-d*g)/(c*d^2-b*d*e+a*e^2)*Int[1/(d+e*x),x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[Simp[c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[(f_.+g_.*x_)/((d_.+e_.*x_)*(a_+c_.*x_^2)),x_Symbol] :=
  e*(e*f-d*g)/(c*d^2+a*e^2)*Int[1/(d+e*x),x] + 
  1/(c*d^2+a*e^2)*Int[Simp[c*d*f+a*e*g-c*(e*f-d*g)*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(2*(p+1)*(c*d^2-b*d*e+a*e^2)) /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[Simplify[m+2*p+3]] && ZeroQ[b*(e*f+d*g)-2*(c*d*f+a*e*g)]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(2*(p+1)*(c*d^2+a*e^2)) /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && ZeroQ[Simplify[m+2*p+3]] && ZeroQ[c*d*f+a*e*g]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(b*f-2*a*g+(2*c*f-b*g)*x)/((p+1)*(b^2-4*a*c)) - 
  m*(b*(e*f+d*g)-2*(c*d*f+a*e*g))/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[Simplify[m+2*p+3]] && RationalQ[p] && p<-1 && Not[m==1 && (ZeroQ[d] || ZeroQ[2*c*d-b*e])]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a+c*x^2)^(p+1)*(a*g-c*f*x)/(2*a*c*(p+1)) - 
  m*(c*d*f+a*e*g)/(2*a*c*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  ZeroQ[Simplify[m+2*p+3]] && RationalQ[p] && p<-1 && Not[m==1 && ZeroQ[d]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(2*(p+1)*(c*d^2-b*d*e+a*e^2)) - 
  (b*(e*f+d*g)-2*(c*d*f+a*e*g))/(2*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[Simplify[m+2*p+3]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  -(e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/(2*(p+1)*(c*d^2+a*e^2)) + 
  (c*d*f+a*e*g)/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && ZeroQ[Simplify[m+2*p+3]]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(b*e*g*(p+2)-c*(e*f+d*g)*(2*p+3)-2*c*e*g*(p+1)*x)*(a+b*x+c*x^2)^(p+1)/(2*c^2*(p+1)*(2*p+3)) /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3)]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  ((e*f+d*g)*(2*p+3)+2*e*g*(p+1)*x)*(a+c*x^2)^(p+1)/(2*c*(p+1)*(2*p+3)) /;
FreeQ[{a,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && ZeroQ[a*e*g-c*d*f*(2*p+3)]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(2*a*c*(e*f+d*g)-b*(c*d*f+a*e*g)-(b^2*e*g-b*c*(e*f+d*g)+2*c*(c*d*f-a*e*g))*x)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(b^2-4*a*c)) - 
  (b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3))/(c*(p+1)*(b^2-4*a*c))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[p] && p<-1


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(c*d*f*x-a*(d*g+e*(f+g*x)))*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) - 
  (a*e*g-c*d*f*(2*p+3))/(2*a*c*(p+1))*Int[(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && RationalQ[p] && p<-1


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(b*e*g*(p+2)-c*(e*f+d*g)*(2*p+3)-2*c*e*g*(p+1)*x)*(a+b*x+c*x^2)^(p+1)/(2*c^2*(p+1)*(2*p+3)) + 
  (b^2*e*g*(p+2)-2*a*c*e*g+c*(2*c*d*f-b*(e*f+d*g))*(2*p+3))/(2*c^2*(2*p+3))*Int[(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[RationalQ[p] && p<=-1]


Int[(d_.+e_.*x_)*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  ((e*f+d*g)*(2*p+3)+2*e*g*(p+1)*x)*(a+c*x^2)^(p+1)/(2*c*(p+1)*(2*p+3)) - 
  (a*e*g-c*d*f*(2*p+3))/(c*(2*p+3))*Int[(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && Not[RationalQ[p] && p<=-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e^2*(m+1)*(m+2)*(c*d^2-b*d*e+a*e^2))*
    ((d*g-e*f*(m+2))*(c*d^2-b*d*e+a*e^2)-d*p*(2*c*d-b*e)*(e*f-d*g)-e*(g*(m+1)*(c*d^2-b*d*e+a*e^2)+p*(2*c*d-b*e)*(e*f-d*g))*x) - 
  p/(e^2*(m+1)*(m+2)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1)*
    Simp[2*a*c*e*(e*f-d*g)*(m+2)+b^2*e*(d*g*(p+1)-e*f*(m+p+2))+b*(a*e^2*g*(m+1)-c*d*(d*g*(2*p+1)-e*f*(m+2*p+2)))-
      c*(2*c*d*(d*g*(2*p+1)-e*f*(m+2*p+2))-e*(2*a*e*g*(m+1)-b*(d*g*(m-2*p)+e*f*(m+2*p+2))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[m,p] && p>0 && m<-2 && m+2*p<0 && Not[NegativeIntegerQ[m+2*p+3]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  -(d+e*x)^(m+1)*(a+c*x^2)^p/(e^2*(m+1)*(m+2)*(c*d^2+a*e^2))*
    ((d*g-e*f*(m+2))*(c*d^2+a*e^2)-2*c*d^2*p*(e*f-d*g)-e*(g*(m+1)*(c*d^2+a*e^2)+2*c*d*p*(e*f-d*g))*x) - 
  p/(e^2*(m+1)*(m+2)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1)*
    Simp[2*a*c*e*(e*f-d*g)*(m+2)-c*(2*c*d*(d*g*(2*p+1)-e*f*(m+2*p+2))-2*a*e^2*g*(m+1))*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[m,p] && p>0 && m<-2 && m+2*p<0 && Not[NegativeIntegerQ[m+2*p+3]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(e*f*(m+2*p+2)-d*g*(2*p+1)+e*g*(m+1)*x)*(a+b*x+c*x^2)^p/(e^2*(m+1)*(m+2*p+2)) + 
  p/(e^2*(m+1)*(m+2*p+2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1)*
    Simp[g*(b*d+2*a*e+2*a*e*m+2*b*d*p)-f*b*e*(m+2*p+2)+(g*(2*c*d+b*e+b*e*m+4*c*d*p)-2*c*e*f*(m+2*p+2))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[p] && p>0 && 
  (RationalQ[m] && m<-1 || p==1 || IntegerQ[p] && Not[RationalQ[m]]) && NonzeroQ[m+1] && Not[NegativeIntegerQ[m+2*p+1]] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(e*f*(m+2*p+2)-d*g*(2*p+1)+e*g*(m+1)*x)*(a+c*x^2)^p/(e^2*(m+1)*(m+2*p+2)) + 
  p/(e^2*(m+1)*(m+2*p+2))*Int[(d+e*x)^(m+1)*(a+c*x^2)^(p-1)*
    Simp[g*(2*a*e+2*a*e*m)+(g*(2*c*d+4*c*d*p)-2*c*e*f*(m+2*p+2))*x,x],x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && RationalQ[p] && p>0 && 
  (RationalQ[m] && m<-1 || p==1 || IntegerQ[p] && Not[RationalQ[m]]) && NonzeroQ[m+1] && Not[NegativeIntegerQ[m+2*p+1]] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(c*e*f*(m+2*p+2)-g*(c*d+2*c*d*p-b*e*p)+g*c*e*(m+2*p+1)*x)*(a+b*x+c*x^2)^p/
    (c*e^2*(m+2*p+1)*(m+2*p+2)) - 
  p/(c*e^2*(m+2*p+1)*(m+2*p+2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1)*
    Simp[c*e*f*(b*d-2*a*e)*(m+2*p+2)+g*(a*e*(b*e-2*c*d*m+b*e*m)+b*d*(b*e*p-c*d-2*c*d*p))+
      (c*e*f*(2*c*d-b*e)*(m+2*p+2)+g*(b^2*e^2*(p+m+1)-2*c^2*d^2*(1+2*p)-c*e*(b*d*(m-2*p)+2*a*e*(m+2*p+1))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[p] && p>0 && (IntegerQ[p] || Not[RationalQ[m]] || -1<=m<0) && Not[NegativeIntegerQ[m+2*p]] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(c*e*f*(m+2*p+2)-g*c*d*(2*p+1)+g*c*e*(m+2*p+1)*x)*(a+c*x^2)^p/
    (c*e^2*(m+2*p+1)*(m+2*p+2)) + 
  2*p/(c*e^2*(m+2*p+1)*(m+2*p+2))*Int[(d+e*x)^m*(a+c*x^2)^(p-1)*
    Simp[f*a*c*e^2*(m+2*p+2)+a*c*d*e*g*m-(c^2*f*d*e*(m+2*p+2)-g*(c^2*d^2*(2*p+1)+a*c*e^2*(m+2*p+1)))*x,x],x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[p] && p>0 && (IntegerQ[p] || Not[RationalQ[m]] || -1<=m<0) && Not[NegativeIntegerQ[m+2*p]] && 
  (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -(d+e*x)^(m-1)*(2*a*c*(e*f+d*g)-b*(c*d*f+a*e*g)-(2*c^2*d*f+b^2*e*g-c*(b*e*f+b*d*g+2*a*e*g))*x)*
    (a+b*x+c*x^2)^(p+1)/(c*(p+1)*(b^2-4*a*c)) - 
  1/(c*(p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1)*
    Simp[2*c^2*d^2*f*(2*p+3)+b*e*g*(a*e*(m-1)+b*d*(p+2))-c*(2*a*e*(e*f*(m-1)+d*g*m)+b*d*(d*g*(2*p+3)-e*f*(m-2*p-4))) + 
      e*(b^2*e*g*(m+p+1)+2*c^2*d*f*(m+2*p+2)-c*(2*a*e*g*m+b*(e*f+d*g)*(m+2*p+2)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[m,p] && p<-1 && m>1 && (m==2 && p==-3 && RationalQ[a,b,c,d,e,f,g] || Not[NegativeIntegerQ[m+2*p+3]])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m-1)*(2*a*(e*f+d*g)-(2*c*d*f-2*a*e*g)*x)*(a+c*x^2)^(p+1)/(4*a*c*(p+1)) - 
  1/(4*a*c*(p+1))*Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1)*
    Simp[2*a*e*(e*f*(m-1)+d*g*m)-2*c*d^2*f*(2*p+3)+e*(2*a*e*g*m-2*c*d*f*(m+2*p+2))*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[m,p] && p<-1 && m>1 && (m==2 && p==-3 && RationalQ[a,c,d,e,f,g] || Not[NegativeIntegerQ[m+2*p+3]])


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a+b*x+c*x^2)^(p+1)*(f*b-2*a*g+(2*c*f-b*g)*x)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)*
    Simp[g*(2*a*e*m+b*d*(2*p+3))-f*(b*e*m+2*c*d*(2*p+3))-e*(2*c*f-b*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[m,p] && p<-1 && m>0 && Not[m==1 && SimplerQ[d+e*x,f+g*x]] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a+c*x^2)^(p+1)*(a*g-c*f*x)/(2*a*c*(p+1)) - 
  1/(2*a*c*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1)*Simp[a*e*g*m-c*d*f*(2*p+3)-c*e*f*(m+2*p+3)*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[m,p] && p<-1 && m>0 && Not[m==1 && SimplerQ[d+e*x,f+g*x]] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(f*(b*c*d-b^2*e+2*a*c*e)-a*g*(2*c*d-b*e)+c*(f*(2*c*d-b*e)-g*(b*d-2*a*e))*x)*(a+b*x+c*x^2)^(p+1)/
    ((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) + 
  1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1)*
    Simp[f*(b*c*d*e*(2*p-m+2)+b^2*e^2*(p+m+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3))-
      g*(a*e*(b*e-2*c*d*m+b*e*m)-b*d*(3*c*d-b*e+2*c*d*p-b*e*p))+
      c*e*(g*(b*d-2*a*e)-f*(2*c*d-b*e))*(m+2*p+4)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[p] && p<-1 && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(f*a*c*e-a*g*c*d+c*(c*d*f+a*e*g)*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)*(c*d^2+a*e^2)) + 
  1/(2*a*c*(p+1)*(c*d^2+a*e^2))*Int[(d+e*x)^m*(a+c*x^2)^(p+1)*
    Simp[f*(c^2*d^2*(2*p+3)+a*c*e^2*(m+2*p+3))-a*c*d*e*g*m+c*e*(c*d*f+a*e*g)*(m+2*p+4)*x,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[p] && p<-1 && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[m]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  g*(d+e*x)^m/(c*m) + 
  1/c*Int[(d+e*x)^(m-1)*Simp[c*d*f-a*e*g+(g*c*d-b*e*g+c*e*f)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && FractionQ[m] && m>0


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  g*(d+e*x)^m/(c*m) + 
  1/c*Int[(d+e*x)^(m-1)*Simp[c*d*f-a*e*g+(g*c*d+c*e*f)*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && FractionQ[m] && m>0


Int[(f_.+g_.*x_)/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  2*Subst[Int[(e*f-d*g+g*x^2)/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[(f_.+g_.*x_)/(Sqrt[d_.+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  2*Subst[Int[(e*f-d*g+g*x^2)/(c*d^2+a*e^2-2*c*d*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x)^(m+1)*Simp[c*d*f-f*b*e+a*e*g-c*(e*f-d*g)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && FractionQ[m] && m<-1


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)/((m+1)*(c*d^2+a*e^2)) + 
  1/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*Simp[c*d*f+a*e*g-c*(e*f-d*g)*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && FractionQ[m] && m<-1


Int[(e_.*x_)^m_*(f_+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  f*Int[(e*x)^m/(a+c*x^2),x] + g/e*Int[(e*x)^(m+1)/(a+c*x^2),x] /;
FreeQ[{a,c,e,f,g},x] && Not[RationalQ[m]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,(f+g*x)/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[RationalQ[m]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,(f+g*x)/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && Not[RationalQ[m]]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  g*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  1/(c*(m+2*p+2))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p*
    Simp[m*(c*d*f-a*e*g)+d*(2*c*f-b*g)*(p+1)+(m*(c*e*f+c*d*g-b*e*g)+e*(p+1)*(2*c*f-b*g))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m] && m>0 && 
  NonzeroQ[m+2*p+2] && Not[m==1 && SimplerQ[f+g*x,d+e*x]] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  g*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  1/(c*(m+2*p+2))*Int[(d+e*x)^(m-1)*(a+c*x^2)^p*
    Simp[c*d*f*(m+2*p+2)-a*e*g*m+c*(e*f*(m+2*p+2)+d*g*m)*x,x],x] /;
FreeQ[{a,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m] && m>0 && 
  NonzeroQ[m+2*p+2] && Not[m==1 && SimplerQ[f+g*x,d+e*x]] && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
    Simp[(c*d*f-f*b*e+a*e*g)*(m+1)+b*(d*g-e*f)*(p+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[m] && m<-1 && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  1/((m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p*Simp[(c*d*f+a*e*g)*(m+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,c,d,e,f,g,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[m] && m<-1 && (IntegerQ[m] || IntegerQ[p] || IntegersQ[2*m,2*p])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p*
    Simp[(c*d*f-f*b*e+a*e*g)*(m+1)+b*(d*g-e*f)*(p+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  NegativeIntegerQ[Simplify[m+2*p+3]] && NonzeroQ[m+1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (e*f-d*g)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  1/((m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p*Simp[(c*d*f+a*e*g)*(m+1)-c*(e*f-d*g)*(m+2*p+3)*x,x],x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && NegativeIntegerQ[m+2*p+3] && NonzeroQ[m+1]


Int[(f_+g_.*x_)/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  4*f*(a-d)/(b*d-a*e)*Subst[Int[1/(4*(a-d)-x^2),x],x,(2*(a-d)+(b-e)*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,g},x] && ZeroQ[4*c*(a-d)-(b-e)^2] && ZeroQ[e*f*(b-e)-2*g*(b*d-a*e)] && NonzeroQ[b*d-a*e]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  g/e*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] + (e*f-d*g)/e*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  g/e*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] + (e*f-d*g)/e*Int[(d+e*x)^m*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegersQ[m,n,p]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[c*d^2+a*e^2] && IntegersQ[m,n,p]


Int[(a_.+b_.*x_+c_.*x_^2)^p_/((d_.+e_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  (c*d^2-b*d*e+a*e^2)/(e*(e*f-d*g))*Int[(a+b*x+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[Simp[c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x,x]*(a+b*x+c*x^2)^(p-1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && FractionQ[p] && p>0


Int[(a_+c_.*x_^2)^p_/((d_.+e_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  (c*d^2+a*e^2)/(e*(e*f-d*g))*Int[(a+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[Simp[c*d*f+a*e*g-c*(e*f-d*g)*x,x]*(a+c*x^2)^(p-1)/(f+g*x),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && FractionQ[p] && p>0


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{q=Denominator[m]},
  q/e*Subst[Int[x^(q*(m+1)-1)*((e*f-d*g)/e+g*x^q/e)^n*
    ((c*d^2-b*d*e+a*e^2)/e^2-(2*c*d-b*e)*x^q/e^2+c*x^(2*q)/e^2)^p,x],x,(d+e*x)^(1/q)]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegersQ[n,p] && FractionQ[m]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  With[{q=Denominator[m]},
  q/e*Subst[Int[x^(q*(m+1)-1)*((e*f-d*g)/e+g*x^q/e)^n*((c*d^2+a*e^2)/e^2-2*c*d*x^q/e^2+c*x^(2*q)/e^2)^p,x],x,(d+e*x)^(1/q)]] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && IntegersQ[n,p] && FractionQ[m]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[(a+b*x)*(d+e*x)^m*(f+g*x)^n,x] + c*Int[x^2*(d+e*x)^m*(f+g*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m,n]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2),x_Symbol] :=
  a*Int[(d+e*x)^m*(f+g*x)^n,x] + c*Int[x^2*(d+e*x)^m*(f+g*x)^n,x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,n]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  g/c^2*Int[Simp[2*c*e*f+c*d*g-b*e*g+c*e*g*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2),x] + 
  1/c^2*Int[Simp[c^2*d*f^2-2*a*c*e*f*g-a*c*d*g^2+a*b*e*g^2+(c^2*e*f^2+2*c^2*d*f*g-2*b*c*e*f*g-b*c*d*g^2+b^2*e*g^2-a*c*e*g^2)*x,x]*
    (d+e*x)^(m-1)*(f+g*x)^(n-2)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[m]] && Not[IntegerQ[n]] && RationalQ[m,n] && m>0 && n>1


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
  g/c*Int[Simp[2*e*f+d*g+e*g*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2),x] + 
  1/c*Int[Simp[c*d*f^2-2*a*e*f*g-a*d*g^2+(c*e*f^2+2*c*d*f*g-a*e*g^2)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-2)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && RationalQ[m,n] && m>0 && n>1


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  e*g/c*Int[(d+e*x)^(m-1)*(f+g*x)^(n-1),x] + 
  1/c*Int[Simp[c*d*f-a*e*g+(c*e*f+c*d*g-b*e*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-1)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[m]] && Not[IntegerQ[n]] && RationalQ[m,n] && m>0 && n>0


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
  e*g/c*Int[(d+e*x)^(m-1)*(f+g*x)^(n-1),x] + 
  1/c*Int[Simp[c*d*f-a*e*g+(c*e*f+c*d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n-1)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && RationalQ[m,n] && m>0 && n>0


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  -g*(e*f-d*g)/(c*f^2-b*f*g+a*g^2)*Int[(d+e*x)^(m-1)*(f+g*x)^n,x] + 
  1/(c*f^2-b*f*g+a*g^2)*
    Int[Simp[c*d*f-b*d*g+a*e*g+c*(e*f-d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n+1)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[m]] && Not[IntegerQ[n]] && RationalQ[m,n] && m>0 && n<-1


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
  -g*(e*f-d*g)/(c*f^2+a*g^2)*Int[(d+e*x)^(m-1)*(f+g*x)^n,x] + 
  1/(c*f^2+a*g^2)*
    Int[Simp[c*d*f+a*e*g+c*(e*f-d*g)*x,x]*(d+e*x)^(m-1)*(f+g*x)^(n+1)/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && RationalQ[m,n] && m>0 && n<-1


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n,1/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[m]] && Not[IntegerQ[n]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n,1/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[m]] && Not[IntegerQ[n]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  (IntegerQ[p] || IntegersQ[m,n])


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && (IntegerQ[p] || IntegersQ[m,n])


Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  (c*d^2-b*d*e+a*e^2)/(e*(e*f-d*g))*Int[(f+g*x)^(n+1)*(a+b*x+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[(f+g*x)^n*(c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[n]] && Not[IntegerQ[p]] && RationalQ[n,p] && p>0 && n<-1


Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  (c*d^2+a*e^2)/(e*(e*f-d*g))*Int[(f+g*x)^(n+1)*(a+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[(f+g*x)^n*(c*d*f+a*e*g-c*(e*f-d*g)*x)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[n]] && Not[IntegerQ[p]] && RationalQ[n,p] && p>0 && n<-1


Int[(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  e*(e*f-d*g)/(c*d^2-b*d*e+a*e^2)*Int[(f+g*x)^(n-1)*(a+b*x+c*x^2)^(p+1)/(d+e*x),x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(f+g*x)^(n-1)*(c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[n]] && Not[IntegerQ[p]] && RationalQ[n,p] && p<-1 && n>0


Int[(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  e*(e*f-d*g)/(c*d^2+a*e^2)*Int[(f+g*x)^(n-1)*(a+c*x^2)^(p+1)/(d+e*x),x] + 
  1/(c*d^2+a*e^2)*Int[(f+g*x)^(n-1)*(c*d*f+a*e*g-c*(e*f-d*g)*x)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && 
  Not[IntegerQ[n]] && Not[IntegerQ[p]] && RationalQ[n,p] && p<-1 && n>0


Int[1/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -2*Sqrt[-g*(b-q+2*c*x)/(2*c*f-b*g+g*q)]*Sqrt[-g*(b+q+2*c*x)/(2*c*f-b*g-g*q)]/
    ((e*f-d*g)*Sqrt[2*c/(2*c*f-b*g+g*q)]*Sqrt[a+b*x+c*x^2])*
    EllipticPi[e*(2*c*f-b*g+g*q)/(2*c*(e*f-d*g)),ArcSin[Sqrt[2*c/(2*c*f-b*g+g*q)]*Sqrt[f+g*x]],(2*c*f-b*g+g*q)/(2*c*f-b*g-g*q)]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[1/((d_.+e_.*x_)*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  -2*Sqrt[g*(q-c*x)/(c*f+g*q)]*Sqrt[-g*(q+c*x)/(c*f-g*q)]/((e*f-d*g)*Sqrt[c/(c*f+g*q)]*Sqrt[a+c*x^2])*
    EllipticPi[e*(c*f+g*q)/(c*(e*f-d*g)),ArcSin[Sqrt[c/(c*f+g*q)]*Sqrt[f+g*x]],(c*f+g*q)/(c*f-g*q)]] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2]


Int[(f_.+g_.*x_)^n_/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  Int[ExpandIntegrand[1/(Sqrt[f+g*x]*Sqrt[a+b*x+c*x^2]),(f+g*x)^(n+1/2)/(d+e*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[n+1/2]


Int[(f_.+g_.*x_)^n_/((d_.+e_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  Int[ExpandIntegrand[1/(Sqrt[f+g*x]*Sqrt[a+c*x^2]),(f+g*x)^(n+1/2)/(d+e*x),x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[n+1/2]


Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[f_.+g_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -2*(d+e*x)*Sqrt[(e*f-d*g)*(b-q+2*c*x)/((2*c*f-g*(b-q))*(d+e*x))]*Sqrt[(e*f-d*g)*(b+q+2*c*x)/((2*c*f-g*(b+q))*(d+e*x))]/
    ((e*f-d*g)*Sqrt[(2*c*d-e*(b+q))/(2*c*f-g*(b+q))]*Sqrt[a+b*x+c*x^2])*
    EllipticF[ArcSin[Sqrt[(2*c*d-e*(b+q))/(2*c*f-g*(b+q))]*Sqrt[f+g*x]/Sqrt[d+e*x]],
      (2*c*d-e*(b-q))*(2*c*f-g*(b+q))/((2*c*f-g*(b-q))*(2*c*d-e*(b+q)))]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[f_.+g_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  -2*(d+e*x)*Sqrt[-(e*f-d*g)*(q-c*x)/((c*f+g*q)*(d+e*x))]*Sqrt[(e*f-d*g)*(q+c*x)/((c*f-g*q)*(d+e*x))]/
    ((e*f-d*g)*Sqrt[(c*d-e*q)/(c*f-g*q)]*Sqrt[a+c*x^2])*
    EllipticF[ArcSin[Sqrt[(c*d-e*q)/(c*f-g*q)]*Sqrt[f+g*x]/Sqrt[d+e*x]],(c*d+e*q)*(c*f-g*q)/((c*f+g*q)*(c*d-e*q))]] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  g/e*Int[(d+e*x)^(m+1)*(f+g*x)^(n-1)*(a+b*x+c*x^2)^p,x] + 
  (e*f-d*g)/e*Int[(d+e*x)^m*(f+g*x)^(n-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  g/e*Int[(d+e*x)^(m+1)*(f+g*x)^(n-1)*(a+c*x^2)^p,x] + 
  (e*f-d*g)/e*Int[(d+e*x)^m*(f+g*x)^(n-1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[n]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x]


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Defer[Int][(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x]


Int[(d_.+e_.*u_)^m_.*(f_.+g_.*v_)^n_.*(a_+b_.*w_+c_.*z_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(d_.+e_.*u_)^m_.*(f_.+g_.*v_)^n_.*(a_+c_.*z_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && ZeroQ[u-v] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*2.4 (a+b x+c x^2)^p (d+e x+f x^2)^q*)


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  (c/f)^p*Int[(d+e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && ZeroQ[c*d-a*f] && ZeroQ[b*d-a*e] && (IntegerQ[p] || PositiveQ[c/f]) && 
  (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])


Int[(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p])*Int[(d+e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && ZeroQ[c*d-a*f] && ZeroQ[b*d-a*e] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[PositiveQ[c/f]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(b+2*c*x)^(2*p)*(d+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,f,p,q},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_+b_.*x_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (b*f*(2*q+3)-c*e*(q+2)+2*c*f*(q+1)*x)*(d+e*x+f*x^2)^(q+1)/(2*f^2*(q+1)*(2*q+3)) /;
FreeQ[{a,b,c,d,e,f,q},x] && ZeroQ[f*(2*a*f-b*e)*(2*q+3)+c*(e^2*(q+2)-2*d*f)] && NonzeroQ[q+1] && NonzeroQ[2*q+3]


Int[(a_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (-c*e*(q+2)+2*c*f*(q+1)*x)*(d+e*x+f*x^2)^(q+1)/(2*f^2*(q+1)*(2*q+3)) /;
FreeQ[{a,c,d,e,f,q},x] && ZeroQ[2*a*f^2*(2*q+3)+c*(e^2*(q+2)-2*d*f)] && NonzeroQ[q+1] && NonzeroQ[2*q+3]


Int[(a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)^q_,x_Symbol] :=
  (b*d+2*a*f*(q+1)*x)*(d+f*x^2)^(q+1)/(2*d*f*(q+1)) /;
FreeQ[{a,b,c,d,f,q},x] && NonzeroQ[q+1] && ZeroQ[3*a*f-c*d+2*a*f*q]


Int[(a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)^q_,x_Symbol] :=
  b*Int[x*(d+f*x^2)^q,x] + Int[(a+c*x^2)*(d+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,f,q},x] && PositiveIntegerQ[q+2]


Int[(a_+b_.*x_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)*(d+e*x+f*x^2)^q,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[e^2-4*d*f] && PositiveIntegerQ[q+2]


Int[(a_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^2)*(d+e*x+f*x^2)^q,x],x] /;
FreeQ[{a,c,d,e,f},x] && NonzeroQ[e^2-4*d*f] && PositiveIntegerQ[q+2]


Int[(a_+b_.*x_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (a*e*f-2*b*d*f+c*d*e+(f*(2*a*f-b*e)+c*(e^2-2*d*f))*x)*(d+e*x+f*x^2)^(q+1)/(f*(q+1)*(e^2-4*d*f)) - 
  (f*(2*a*f-b*e)*(2*q+3)+c*(e^2*(q+2)-2*d*f))/(f*(q+1)*(e^2-4*d*f))*Int[(d+e*x+f*x^2)^(q+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[e^2-4*d*f] && RationalQ[q] && q<-1 && NonzeroQ[f*(2*a*f-b*e)*(2*q+3)+c*(e^2*(q+2)-2*d*f)]


Int[(a_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (a*e*f+c*d*e+(2*a*f^2+c*(e^2-2*d*f))*x)*(d+e*x+f*x^2)^(q+1)/(f*(q+1)*(e^2-4*d*f)) - 
  (2*a*f^2*(2*q+3)+c*(e^2*(q+2)-2*d*f))/(f*(q+1)*(e^2-4*d*f))*Int[(d+e*x+f*x^2)^(q+1),x] /;
FreeQ[{a,c,d,e,f},x] && NonzeroQ[e^2-4*d*f] && RationalQ[q] && q<-1 && NonzeroQ[2*a*f^2*(2*q+3)+c*(e^2*(q+2)-2*d*f)]


Int[(a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)^q_,x_Symbol] :=
  (b*d-(a*f-c*d)*x)*(d+f*x^2)^(q+1)/(2*d*f*(q+1)) + 
  (3*a*f-c*d+2*a*f*q)/(2*d*f*(q+1))*Int[(d+f*x^2)^(q+1),x] /;
FreeQ[{a,b,c,d,f},x] && RationalQ[q] && q<-1 && NonzeroQ[3*a*f-c*d+2*a*f*q]


Int[(a_+b_.*x_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (b*f*(2*q+3)-c*e*(q+2)+2*c*f*(q+1)*x)*(d+e*x+f*x^2)^(q+1)/(2*f^2*(q+1)*(2*q+3)) + 
  (f*(2*a*f-b*e)*(2*q+3)+c*(e^2*(q+2)-2*d*f))/(2*f^2*(2*q+3))*Int[(d+e*x+f*x^2)^q,x] /;
FreeQ[{d,e,f,a,b,c,q},x] && NonzeroQ[e^2-4*d*f] && Not[PositiveIntegerQ[q]] && Not[RationalQ[q] && q<=-1] && 
  NonzeroQ[f*(2*a*f-b*e)*(2*q+3)+c*(e^2*(q+2)-2*d*f)]


Int[(a_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (-c*e*(q+2)+2*c*f*(q+1)*x)*(d+e*x+f*x^2)^(q+1)/(2*f^2*(q+1)*(2*q+3)) + 
  (2*a*f^2*(2*q+3)+c*(e^2*(q+2)-2*d*f))/(2*f^2*(2*q+3))*Int[(d+e*x+f*x^2)^q,x] /;
FreeQ[{d,e,f,a,c,q},x] && NonzeroQ[e^2-4*d*f] && Not[PositiveIntegerQ[q]] && Not[RationalQ[q] && q<=-1] && 
  NonzeroQ[2*a*f^2*(2*q+3)+c*(e^2*(q+2)-2*d*f)]


Int[(a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)^q_,x_Symbol] :=
  (b*f*(2*q+3)+2*c*f*(q+1)*x)*(d+f*x^2)^(q+1)/(2*f^2*(q+1)*(2*q+3)) + 
  (3*a*f-c*d+2*a*f*q)/(f*(2*q+3))*Int[(d+f*x^2)^q,x] /;
FreeQ[{d,f,a,b,c,q},x] && Not[PositiveIntegerQ[q]] && Not[RationalQ[q] && q<=-1] && NonzeroQ[3*a*f-c*d+2*a*f*q]


(* Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  1/(2^(2*p+2*q+1)*c*(-c/(b^2-4*a*c))^p*(-f/(e^2-4*d*f))^q)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^p*(1+e*x^2/(b*(4*c*d-b*e)))^q,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[e^2-4*d*f] && ZeroQ[c*e-b*f] && 
  (IntegerQ[p] || PositiveQ[-c/(b^2-4*a*c)]) && (IntegerQ[q] || PositiveQ[-f/(e^2-4*d*f)]) *)


(* Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (d+e*x+f*x^2)^q/(2^(2*p+2*q+1)*c*(-c/(b^2-4*a*c))^p*(-f*(d+e*x+f*x^2)/(e^2-4*d*f))^q)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^p*(1+e*x^2/(b*(4*c*d-b*e)))^q,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[e^2-4*d*f] && ZeroQ[c*e-b*f] && 
  (IntegerQ[p] || PositiveQ[-c/(b^2-4*a*c)]) && Not[IntegerQ[q] || PositiveQ[-f/(e^2-4*d*f)]] *)


(* Int[(a_+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  (a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q/(2^(2*p+2*q+1)*c*(-c*(a+b*x+c*x^2)/(b^2-4*a*c))^p*(-f*(d+e*x+f*x^2)/(e^2-4*d*f))^q)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^p*(1+e*x^2/(b*(4*c*d-b*e)))^q,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[e^2-4*d*f] && ZeroQ[c*e-b*f] *)


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*e*Subst[Int[1/(e*(b*e-4*a*f)-(b*d-a*e)*x^2),x],x,(e+2*f*x)/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*e-b*f]


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/((b-q+2*c*x)*Sqrt[d+e*x+f*x^2]),x] -
  2*c/q*Int[1/((b+q+2*c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*e-b*f]


Int[1/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  1/2*Int[1/((a-Rt[-a*c,2]*x)*Sqrt[d+e*x+f*x^2]),x] +
  1/2*Int[1/((a+Rt[-a*c,2]*x)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,c,d,e,f},x]


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/((b-q+2*c*x)*Sqrt[d+f*x^2]),x] -
  2*c/q*Int[1/((b+q+2*c*x)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f},x] && NonzeroQ[b^2-4*a*c]


Int[1/((a_+b_.*x_+c_.*x_^2)^2*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -b*(e+2*f*x)*Sqrt[d+e*x+f*x^2]/((b*d-a*e)*(b*e-4*a*f)*(a+b*x+c*x^2)) - 
  e*(4*c*d+b*e-8*a*f)/(2*(b*d-a*e)*(b*e-4*a*f))*Int[1/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*e-b*f] && NonzeroQ[b*d-a*e] && NonzeroQ[b*e-4*a*f]


Int[1/((a_+b_.*x_+c_.*x_^2)^2*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  e*(b*(3*c*d-b*e)+c*(2*c*d-b*e)*x)*Sqrt[d+e*x+f*x^2]/(a*d*(4*c*d-b*e)*(c*e-b*f)*(a+b*x+c*x^2)) + 
  e/(2*a*d*(4*c*d-b*e)*(c*e-b*f))*
    Int[Simp[(4*c*d-b*e)*(c*d+b*e-2*a*f)+c*e*(2*c*d-b*e+2*a*f)*x,x]/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[b*d-a*e] && NonzeroQ[c*e-b*f] && NonzeroQ[4*c*d-b*e]


Int[1/((a_+b_.*x_+c_.*x_^2)^2*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*c^2*Sqrt[d+e*x+f*x^2]/((c*e-b*f)*(b^2-4*a*c)*(a+b*x+c*x^2)) - 
  c/((c*e-b*f)*(b^2-4*a*c))*Int[(3*c*e-2*b*f+2*c*f*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[b^2*f-c*(b*e-2*(c*d-a*f))]


Int[1/((a_+c_.*x_^2)^2*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  Sqrt[d+e*x+f*x^2]/(2*a*e*(a+c*x^2)) + 
  1/(4*a*e)*Int[(3*e+2*f*x)/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[c*d-a*f]


Int[1/((a_+b_.*x_+c_.*x_^2)^2*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  2*c^2*Sqrt[d+f*x^2]/(b*f*(b^2-4*a*c)*(a+b*x+c*x^2)) - 
  2*c/(b*(b^2-4*a*c))*Int[(b-c*x)/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x] /;
FreeQ[{a,b,c,d,f},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[b^2*f+2*c*(c*d-a*f)]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,q},x] && (IntegersQ[p,q] || PositiveIntegerQ[p])


Int[(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^2)^p*(d+e*x+f*x^2)^q,x],x] /;
FreeQ[{a,c,d,e,f,q},x] && (IntegersQ[p,q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  f/c*Int[(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1),x] + 
  1/c*Int[Simp[c*d-a*f+(c*e-b*f)*x,x]*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^(q-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[p,q] && p<=-1 && q>0


Int[(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  f/c*Int[(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1),x] + 
  1/c*Int[Simp[c*d-a*f+c*e*x,x]*(a+c*x^2)^p*(d+e*x+f*x^2)^(q-1),x] /;
FreeQ[{a,c,d,e,f},x] && RationalQ[p,q] && p<=-1 && q>0


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_,x_Symbol] :=
  f/c*Int[(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1),x] + 
  1/c*Int[Simp[c*d-a*f-b*f*x,x]*(a+b*x+c*x^2)^p*(d+f*x^2)^(q-1),x] /;
FreeQ[{a,b,c,d,f},x] && RationalQ[p,q] && p<=-1 && q>0


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  -1/(c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2)*
    Int[Simp[f*(b*e-a*f)-c*(e^2-d*f)-f*(c*e-b*f)*x,x]*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q,x] + 
  1/(c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2)*
    Int[Simp[(b^2*f+c*(c*d-b*e-a*f))-c*(c*e-b*f)*x,x]*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^(q+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[p,q] && p<=-1 && q<=-1 && NonzeroQ[c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2]


Int[(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  -1/(c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2)*
    Int[Simp[-a*f^2-c*(e^2-d*f)-c*e*f*x,x]*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q,x] + 
  1/((c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2))*
    Int[Simp[(c*(c*d-a*f))-c^2*e*x,x]*(a+c*x^2)^p*(d+e*x+f*x^2)^(q+1),x] /;
FreeQ[{a,c,d,e,f},x] && RationalQ[p,q] && p<=-1 && q<=-1 && NonzeroQ[c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2]


Int[(a_.+b_.*x_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Defer[Int][(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,p,q},x]


Int[(a_+c_.*x_^2)^p_*(d_.+e_.*x_+f_.*x_^2)^q_,x_Symbol] :=
  Defer[Int][(a+c*x^2)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,c,d,e,f,p,q},x]


Int[(a_.+b_.*u_+c_.*v_^2)^p_.*(d_.+e_.*w_+f_.*z_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+c_.*u_^2)^p_.*(d_.+e_.*v_+f_.*w_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
FreeQ[{a,c,d,e,f,p,q},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*2.5 (g+h x)^m (a+b x+c x^2)^p (d+e x+f x^2)^q*)


Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  (c/f)^p*Int[(g+h*x)^m*(d+e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && ZeroQ[c*d-a*f] && ZeroQ[b*d-a*e] && (IntegerQ[p] || PositiveQ[c/f]) && 
  (Not[IntegerQ[q]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])


Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  a^IntPart[p]*(a+b*x+c*x^2)^FracPart[p]/(d^IntPart[p]*(d+e*x+f*x^2)^FracPart[p])*Int[(g+h*x)^m*(d+e*x+f*x^2)^(p+q),x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && ZeroQ[c*d-a*f] && ZeroQ[b*d-a*e] && Not[IntegerQ[p]] && Not[IntegerQ[q]] && Not[PositiveQ[c/f]]


Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(g+h*x)^m*(b+2*c*x)^(2*p)*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p,q},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(g_.+h_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  (a+b*x+c*x^2)^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x)^(2*FracPart[p]))*Int[(g+h*x)^m*(b+2*c*x)^(2*p)*(d+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,f,g,h,m,p,q},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[x_^m_.*(a_.+b_.*x_+c_.*x_^2)^m_.*(e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[(a/e+c/f*x)^m*(e*x+f*x^2)^(m+q),x] /;
FreeQ[{a,b,c,e,f,q},x] && ZeroQ[c*e^2-b*e*f+a*f^2] && IntegerQ[m]


Int[x_^m_.*(a_.+c_.*x_^2)^m_.*(e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[(a/e+c/f*x)^m*(e*x+f*x^2)^(m+q),x] /;
FreeQ[{a,c,e,f,q},x] && ZeroQ[c*e^2+a*f^2] && IntegerQ[m]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[(a*g/d+c*h/f*x)^m*(d+e*x+f*x^2)^(m+q),x] /;
FreeQ[{a,b,c,d,e,f,g,h,q},x] && ZeroQ[f*g^2-e*g*h+d*h^2] && ZeroQ[a*f^2*g^2-b*d*f*g*h+c*d^2*h^2] && IntegerQ[m]


Int[(g_.+h_.*x_)^m_.*(a_.+c_.*x_^2)^m_.*(d_+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[(a*g/d+c*h/f*x)^m*(d+e*x+f*x^2)^(m+q),x] /;
FreeQ[{a,c,d,e,f,g,h,q},x] && ZeroQ[f*g^2-e*g*h+d*h^2] && ZeroQ[a*f^2*g^2+c*d^2*h^2] && IntegerQ[m]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[(a*g/d+c*h/f*x)^m*(d+f*x^2)^(m+q),x] /;
FreeQ[{a,b,c,d,f,g,h,q},x] && ZeroQ[f*g^2+d*h^2] && ZeroQ[a*f^2*g^2-b*d*f*g*h+c*d^2*h^2] && IntegerQ[m]


Int[(g_+h_.*x_)^m_.*(a_.+c_.*x_^2)^m_.*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[(a*g/d+c*h/f*x)^m*(d+f*x^2)^(m+q),x] /;
FreeQ[{a,c,d,f,g,h,q},x] && ZeroQ[f*g^2+d*h^2] && ZeroQ[a*f^2*g^2+c*d^2*h^2] && IntegerQ[m]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2),x_Symbol] :=
  f*(g+h*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(c*h*(m+2*p+3)) /;
FreeQ[{a,b,c,d,e,f,g,h,m,p},x] && ZeroQ[b*f*h*(m+p+2)+c*(2*f*g*(p+1)-e*h*(m+2*p+3))] && 
  ZeroQ[b*f*g*(p+1)+h*(a*f*(m+1)-c*d*(m+2*p+3))] && NonzeroQ[m+2*p+3]


Int[(g_.+h_.*x_)^m_.*(a_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2),x_Symbol] :=
  f*(g+h*x)^(m+1)*(a+c*x^2)^(p+1)/(c*h*(m+2*p+3)) /;
FreeQ[{a,c,d,e,f,g,h,m,p},x] && ZeroQ[c*(2*f*g*(p+1)-e*h*(m+2*p+3))] && 
  ZeroQ[h*(a*f*(m+1)-c*d*(m+2*p+3))] && NonzeroQ[m+2*p+3]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_+f_.*x_^2),x_Symbol] :=
  f*(g+h*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(c*h*(m+2*p+3)) /;
FreeQ[{a,b,c,d,f,g,h,m,p},x] && ZeroQ[b*f*h*(m+p+2)+c*(2*f*g*(p+1))] && 
  ZeroQ[b*f*g*(p+1)+h*(a*f*(m+1)-c*d*(m+2*p+3))] && NonzeroQ[m+2*p+3]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)^m*(a+b*x+c*x^2)^p*(d+e*x+f*x^2),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && PositiveIntegerQ[p]


Int[(g_.+h_.*x_)^m_.*(a_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)^m*(a+c*x^2)^p*(d+e*x+f*x^2),x],x] /;
FreeQ[{a,c,d,e,f,g,h,m},x] && PositiveIntegerQ[p]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_+f_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)^m*(a+b*x+c*x^2)^p*(d+f*x^2),x],x] /;
FreeQ[{a,b,c,d,f,g,h,m},x] && PositiveIntegerQ[p]


Int[(g_+h_.*x_)^m_.*(a_+c_.*x_^2)^p_.*(d_.+f_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)^m*(a+c*x^2)^p*(d+f*x^2),x],x] /;
FreeQ[{a,c,d,f,g,h,m},x] && PositiveIntegerQ[p]


Int[(g_.+h_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2),x_Symbol] :=
  (f*g^2-e*g*h+d*h^2)*(g+h*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(h*(m+1)*(c*g^2-b*g*h+a*h^2)) + 
  1/(h*(m+1)*(c*g^2-b*g*h+a*h^2))*Int[(g+h*x)^(m+1)*(a+b*x+c*x^2)^p*
    Simp[h*(c*d*g-a*f*g+a*e*h)*(m+1)-b*(f*g^2*(p+1)-h*(e*g*(p+1)-d*h*(m+p+2)))-
      (f*h*(b*g-a*h)*(m+1)+c*(2*f*g^2*(p+1)-h*(e*g-d*h)*(m+2*p+3)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p},x] && RationalQ[m] && m<-1 && NonzeroQ[c*g^2-b*g*h+a*h^2]


Int[(g_.+h_.*x_)^m_*(a_.+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2),x_Symbol] :=
  (f*g^2-e*g*h+d*h^2)*(g+h*x)^(m+1)*(a+c*x^2)^(p+1)/(h*(m+1)*(c*g^2+a*h^2)) + 
  1/(h*(m+1)*(c*g^2+a*h^2))*Int[(g+h*x)^(m+1)*(a+c*x^2)^p*
    Simp[h*(c*d*g-a*f*g+a*e*h)*(m+1)+(a*f*h^2*(m+1)-c*(2*f*g^2*(p+1)-h*(e*g-d*h)*(m+2*p+3)))*x,x],x] /;
FreeQ[{a,c,d,e,f,g,h,p},x] && RationalQ[m] && m<-1 && NonzeroQ[c*g^2+a*h^2]


Int[(g_.+h_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+f_.*x_^2),x_Symbol] :=
  (f*g^2+d*h^2)*(g+h*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(h*(m+1)*(c*g^2-b*g*h+a*h^2)) + 
  1/(h*(m+1)*(c*g^2-b*g*h+a*h^2))*Int[(g+h*x)^(m+1)*(a+b*x+c*x^2)^p*
    Simp[h*(c*d*g-a*f*g)*(m+1)-b*(f*g^2*(p+1)+d*h^2*(m+p+2))-
      (f*h*(b*g-a*h)*(m+1)+c*(2*f*g^2*(p+1)+d*h^2*(m+2*p+3)))*x,x],x] /;
FreeQ[{a,b,c,d,f,g,h,p},x] && RationalQ[m] && m<-1 && NonzeroQ[c*g^2-b*g*h+a*h^2]


Int[(g_+h_.*x_)^m_*(a_.+c_.*x_^2)^p_.*(d_.+f_.*x_^2),x_Symbol] :=
  (f*g^2+d*h^2)*(g+h*x)^(m+1)*(a+c*x^2)^(p+1)/(h*(m+1)*(c*g^2+a*h^2)) + 
  1/(h*(m+1)*(c*g^2+a*h^2))*Int[(g+h*x)^(m+1)*(a+c*x^2)^p*
    Simp[h*(c*d*g-a*f*g)*(m+1)+(a*f*h^2*(m+1)-c*(2*f*g^2*(p+1)+d*h^2*(m+2*p+3)))*x,x],x] /;
FreeQ[{a,c,d,f,g,h,p},x] && RationalQ[m] && m<-1 && NonzeroQ[c*g^2+a*h^2]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2),x_Symbol] :=
  f*(g+h*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(c*h*(m+2*p+3)) - 
  1/(c*h*(m+2*p+3))*Int[(g+h*x)^m*(a+b*x+c*x^2)^p*
    Simp[b*f*g*(p+1)+h*(a*f*(m+1)-c*d*(m+2*p+3))+(b*f*h*(m+p+2)+c*(2*f*g*(p+1)-e*h*(m+2*p+3)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,p},x] && NonzeroQ[m+2*p+3]


Int[(g_.+h_.*x_)^m_.*(a_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2),x_Symbol] :=
  f*(g+h*x)^(m+1)*(a+c*x^2)^(p+1)/(c*h*(m+2*p+3)) - 
  1/(c*h*(m+2*p+3))*Int[(g+h*x)^m*(a+c*x^2)^p*
    Simp[h*(a*f*(m+1)-c*d*(m+2*p+3))+(c*(2*f*g*(p+1)-e*h*(m+2*p+3)))*x,x],x] /;
FreeQ[{a,c,d,e,f,g,h,m,p},x] && NonzeroQ[m+2*p+3]


Int[(g_.+h_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_+f_.*x_^2),x_Symbol] :=
  f*(g+h*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(c*h*(m+2*p+3)) - 
  1/(c*h*(m+2*p+3))*Int[(g+h*x)^m*(a+b*x+c*x^2)^p*
    Simp[b*f*g*(p+1)+h*(a*f*(m+1)-c*d*(m+2*p+3))+f*(b*h*(m+p+2)+2*c*g*(p+1))*x,x],x] /;
FreeQ[{a,b,c,d,f,g,h,m,p},x] && NonzeroQ[m+2*p+3]


Int[(g_+h_.*x_)^m_.*(a_.+c_.*x_^2)^p_.*(d_+f_.*x_^2),x_Symbol] :=
  f*(g+h*x)^(m+1)*(a+c*x^2)^(p+1)/(c*h*(m+2*p+3)) - 
  1/(c*h*(m+2*p+3))*Int[(g+h*x)^m*(a+c*x^2)^p*Simp[h*(a*f*(m+1)-c*d*(m+2*p+3))+2*c*f*g*(p+1)*x,x],x] /;
FreeQ[{a,c,d,f,g,h,m,p},x] && NonzeroQ[m+2*p+3]


Int[(A_+B_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*A*Subst[Int[1/(b*d-a*e-b*x^2),x],x,Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*e-b*f] && ZeroQ[B*e-2*A*f]


Int[(A_.+B_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -(B*e-2*A*f)/(2*f)*Int[1/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] + 
  B/(2*f)*Int[(e+2*f*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*e-b*f] && NonzeroQ[B*e-2*A*f]


Int[(A_+B_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
  A*Subst[Int[1/(a+(c*d-a*f)*x^2),x],x,x/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[b*d-a*e] && ZeroQ[2*B*d-A*e]


(* Int[(A_.+B_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -(2*B*d-A*e)/e*Int[1/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] + 
  B/e*Int[(2*d+e*x)/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[b*d-a*e] && NonzeroQ[2*B*d-A*e] *)


Int[(A_+B_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*A*(A*b-2*a*B)*Subst[Int[1/Simp[A*(A*b-2*a*B)*(b^2-4*a*c)-(b*d-a*e)*x^2,x],x],x,Simp[A*b-2*a*B-(b*B-2*A*c)*x,x]/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[b*d-a*e] && ZeroQ[B^2*(b*d-a*e)-2*A*B*(c*d-a*f)+A^2*(c*e-b*f)]


Int[(A_+B_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*a*A*B*Subst[Int[1/Simp[2*a^2*A*B*c+a*e*x^2,x],x],x,Simp[a*B-A*c*x,x]/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,c,d,e,f,A,B},x] && ZeroQ[a*B^2*e+2*A*B*(c*d-a*f)-A^2*c*e]


Int[(A_+B_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  -2*A*(A*b-2*a*B)*Subst[Int[1/Simp[A*(A*b-2*a*B)*(b^2-4*a*c)-b*d*x^2,x],x],x,Simp[A*b-2*a*B-(b*B-2*A*c)*x,x]/Sqrt[d+f*x^2]] /;
FreeQ[{a,b,c,d,f,A,B},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[b*B^2*d-2*A*B*(c*d-a*f)-A^2*b*f]


Int[(A_+B_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f),2]},
  1/(2*q)*Int[Simp[B*(b*d-a*e)-A*(c*d-a*f-q)-(A*(c*e-b*f)-B*(c*d-a*f+q))*x,x]/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] - 
  1/(2*q)*Int[Simp[B*(b*d-a*e)-A*(c*d-a*f+q)-(A*(c*e-b*f)-B*(c*d-a*f-q))*x,x]/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[b*d-a*e] && NonzeroQ[B^2*(b*d-a*e)-2*A*B*(c*d-a*f)+A^2*(c*e-b*f)] && 
  PositiveQ[(c*d-a*f)^2-(b*d-a*e)*(c*e-b*f)]


Int[(A_+B_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2+a*c*e^2,2]},
  1/(2*q)*Int[Simp[-a*B*e-A*(c*d-a*f-q)+(B*(c*d-a*f+q)-A*c*e)*x,x]/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x] - 
  1/(2*q)*Int[Simp[-a*B*e-A*(c*d-a*f+q)+(B*(c*d-a*f-q)-A*c*e)*x,x]/((a+c*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,c,d,e,f,A,B},x] && NonzeroQ[a*B^2*e+2*A*B*(c*d-a*f)-A^2*c*e] && PositiveQ[(c*d-a*f)^2+a*c*e^2]


Int[(A_+B_.*x_)/((a_.+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[(c*d-a*f)^2+b^2*d*f,2]},
  1/(2*q)*Int[Simp[B*b*d-A*(c*d-a*f-q)+(B*(c*d-a*f+q)+A*b*f)*x,x]/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x] - 
  1/(2*q)*Int[Simp[B*b*d-A*(c*d-a*f+q)+(B*(c*d-a*f-q)+A*b*f)*x,x]/((a+b*x+c*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f,A,B},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[B^2*b*d-2*A*B*(c*d-a*f)-A^2*b*f] && PositiveQ[(c*d-a*f)^2+b^2*d*f]


Int[(A_.+B_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*A-B*(b-q))/q*Int[1/((b-q+2*c*x)*Sqrt[d+e*x+f*x^2]),x] -
  (2*c*A-B*(b+q))/q*Int[1/((b+q+2*c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[2*c*A-b*B] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*A^2-b*A*B+a*B^2]


Int[(A_.+B_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (B/2+c*A/(2*q))*Int[1/((-q+c*x)*Sqrt[d+e*x+f*x^2]),x] +
  (B/2-c*A/(2*q))*Int[1/((q+c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,c,d,e,f,A,B},x] && NonzeroQ[c*A^2+a*B^2]


Int[(A_.+B_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*A-B*(b-q))/q*Int[1/((b-q+2*c*x)*Sqrt[d+f*x^2]),x] -
  (2*c*A-B*(b+q))/q*Int[1/((b+q+2*c*x)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f,A,B},x] && NonzeroQ[2*c*A-b*B] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*A^2-b*A*B+a*B^2]


Int[(A_+B_.*x_)/((a_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (c*A+B*q)/(2*q)*Int[1/((-q+c*x)*Sqrt[d+f*x^2]),x] -
  (c*A-B*q)/(2*q)*Int[1/((q+c*x)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,c,d,f,A,B},x] && NonzeroQ[c*A^2+a*B^2] && Not[NegativeQ[-a*c]]


Int[(A_.+B_.*x_)/((a_+b_.*x_+c_.*x_^2)^2*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -(e*(A*b-2*a*B)-b*(B*e-2*A*f)*x)*Sqrt[d+e*x+f*x^2]/((b*d-a*e)*(b*e-4*a*f)*(a+b*x+c*x^2)) - 
  1/(2*(b*d-a*e)*(b*e-4*a*f))*
    Int[Simp[2*a*e*(B*e-4*A*f)-b*(2*B*d*e-A*(e^2+4*d*f))+B*e*(b*e-4*a*f)*x,x]/((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*e-b*f] && NonzeroQ[b*d-a*e] && NonzeroQ[b*e-4*a*f]


Int[(A_.+B_.*x_)/((a_+b_.*x_+c_.*x_^2)^2*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -(b*(B*d*(2*c*d-b*e)-A*e*(3*c*d-b*e))-c*e*(b*B*d+A*(2*c*d-b*e))*x)*Sqrt[d+e*x+f*x^2]/
    (a*d*(c*e-b*f)*(4*c*d-b*e)*(a+b*x+c*x^2)) + 
  e/(2*a*d*(c*e-b*f)*(4*c*d-b*e))*
    Int[Simp[(4*c*d-b*e)*(A*(c*d+b*e-2*a*f)-b*B*d)+c*(A*e*(2*c*d-b*e+2*a*f)+B*d*(b*e-4*a*f))*x,x]/
      ((a+b*x+c*x^2)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[b*d-a*e] && NonzeroQ[c*e-b*f] && NonzeroQ[4*c*d-b*e]


Int[(g_.+h_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,q},x] && (IntegersQ[p,q] || PositiveIntegerQ[p])


Int[(g_.+h_.*x_)*(a_.+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)*(a+c*x^2)^p*(d+e*x+f*x^2)^q,x],x] /;
FreeQ[{a,c,d,e,f,g,h,q},x] && (IntegersQ[p,q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(g_+h_.*x_)*(a_.+c_.*x_^2)^p_.*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  Int[ExpandIntegrand[(g+h*x)*(a+c*x^2)^p*(d+f*x^2)^q,x],x] /;
FreeQ[{a,c,d,f,g,h,q},x] && (IntegersQ[p,q] || PositiveIntegerQ[p])


Int[(g_.+h_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  1/c^2*Int[Simp[g*c*f+h*(c*e-b*f)+h*c*f*x,x]*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1),x] + 
  1/c^2*Int[Simp[g*c*(c*d-a*f)-a*h*(c*e-b*f)+(g*c*(c*e-b*f)+h*(c*(c*d-a*f)-b*(c*e-b*f)))*x,x]*
      (a+b*x+c*x^2)^p*(d+e*x+f*x^2)^(q-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && RationalQ[p,q] && p<=-1 && q>0


Int[(g_.+h_.*x_)*(a_.+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  1/c*Int[Simp[g*f+h*e+h*f*x,x]*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^(q-1),x] + 
  1/c*Int[Simp[g*(c*d-a*f)-a*h*e+(g*c*e+h*(c*d-a*f))*x,x]*(a+c*x^2)^p*(d+e*x+f*x^2)^(q-1),x] /;
FreeQ[{a,c,d,e,f,g,h},x] && RationalQ[p,q] && p<=-1 && q>0


Int[(g_.+h_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  1/c^2*Int[Simp[g*c*f-b*h*f+h*c*f*x,x]*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^(q-1),x] + 
  1/c^2*Int[Simp[g*c*(c*d-a*f)+a*b*h*f+(-g*b*c*f+h*(c*(c*d-a*f)+b^2*f))*x,x]*
      (a+b*x+c*x^2)^p*(d+f*x^2)^(q-1),x] /;
FreeQ[{a,b,c,d,f,g,h},x] && RationalQ[p,q] && p<=-1 && q>0


Int[(g_+h_.*x_)*(a_.+c_.*x_^2)^p_.*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  1/c*Int[Simp[g*f+h*f*x,x]*(a+c*x^2)^(p+1)*(d+f*x^2)^(q-1),x] + 
  1/c*Int[Simp[g*(c*d-a*f)+h*(c*d-a*f)*x,x]*(a+c*x^2)^p*(d+f*x^2)^(q-1),x] /;
FreeQ[{a,c,d,f,g,h},x] && RationalQ[p,q] && p<=-1 && q>0


Int[(g_.+h_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  -1/(c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2)*
    Int[Simp[h*d*(c*e-b*f)+g*(f*(b*e-a*f)-c*(e^2-d*f))+f*(h*(c*d-a*f)-g*(c*e-b*f))*x,x]*(a+b*x+c*x^2)^(p+1)*(d+e*x+f*x^2)^q,x] + 
  1/(c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2)*
    Int[Simp[a*h*(c*e-b*f)+g*(b^2*f+c*(c*d-b*e-a*f))+c*(h*(c*d-a*f)-g*(c*e-b*f))*x,x]*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^(q+1),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && RationalQ[p,q] && p<=-1 && q<=-1


Int[(g_.+h_.*x_)*(a_.+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  -1/(c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2)*
    Int[Simp[h*c*d*e+g*(-a*f^2-c*(e^2-d*f))+f*(h*(c*d-a*f)-g*c*e)*x,x]*(a+c*x^2)^(p+1)*(d+e*x+f*x^2)^q,x] + 
  1/(c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2)*
    Int[Simp[a*h*c*e+g*c*(c*d-a*f)+c*(h*(c*d-a*f)-g*c*e)*x,x]*(a+c*x^2)^p*(d+e*x+f*x^2)^(q+1),x] /;
FreeQ[{a,c,d,e,f,g,h},x] && RationalQ[p,q] && p<=-1 && q<=-1


Int[(g_.+h_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  -1/(c^2*d^2-(2*a*c*d-b^2*d)*f+a^2*f^2)*
    Int[Simp[-h*b*d*f+g*(-a*f^2+c*d*f)+f*(h*(c*d-a*f)+g*b*f)*x,x]*(a+b*x+c*x^2)^(p+1)*(d+f*x^2)^q,x] + 
  1/(c^2*d^2-(2*a*c*d-b^2*d)*f+a^2*f^2)*
    Int[Simp[-a*b*h*f+g*(b^2*f+c*(c*d-a*f))+c*(h*(c*d-a*f)+g*b*f)*x,x]*(a+b*x+c*x^2)^p*(d+f*x^2)^(q+1),x] /;
FreeQ[{a,b,c,d,f,g,h},x] && RationalQ[p,q] && p<=-1 && q<=-1


Int[(g_+h_.*x_)*(a_.+c_.*x_^2)^p_.*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  -1/(c^2*d^2-2*a*c*d*f+a^2*f^2)*
    Int[Simp[g*(-a*f^2+c*d*f)+f*h*(c*d-a*f)*x,x]*(a+c*x^2)^(p+1)*(d+f*x^2)^q,x] + 
  1/(c^2*d^2-2*a*c*d*f+a^2*f^2)*
    Int[Simp[g*c*(c*d-a*f)+c*h*(c*d-a*f)*x,x]*(a+c*x^2)^p*(d+f*x^2)^(q+1),x] /;
FreeQ[{a,c,d,f,g,h},x] && RationalQ[p,q] && p<=-1 && q<=-1


Int[(g_+h_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  g*Int[(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x] + 
  h*Int[x*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x]


Int[(g_+h_.*x_)*(a_.+c_.*x_^2)^p_.*(d_.+e_.*x_+f_.*x_^2)^q_.,x_Symbol] :=
  g*Int[(a+c*x^2)^p*(d+e*x+f*x^2)^q,x] + 
  h*Int[x*(a+c*x^2)^p*(d+e*x+f*x^2)^q,x] /;
FreeQ[{a,c,d,e,f,g,h,p,q},x]


Int[(g_+h_.*x_)*(a_.+c_.*x_^2)^p_.*(d_+f_.*x_^2)^q_.,x_Symbol] :=
  g*Int[(a+c*x^2)^p*(d+f*x^2)^q,x] + 
  h*Int[x*(a+c*x^2)^p*(d+f*x^2)^q,x] /;
FreeQ[{a,c,d,f,g,h,p,q},x]


Int[(g_+h_.*y_)*(a_.+b_.*u_+c_.*v_^2)^p_.*(d_.+e_.*w_+f_.*z_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(g+h*x)*(a+b*x+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
FreeQ[{a,b,c,d,e,f,g,h,p,q},x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && ZeroQ[u-y] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(g_+h_.*u_)*(a_.+c_.*v_^2)^p_.*(d_.+e_.*w_+f_.*z_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(g+h*x)*(a+c*x^2)^p*(d+e*x+f*x^2)^q,x],x,u] /;
FreeQ[{a,c,d,e,f,g,h,p,q},x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(g_+h_.*u_)*(a_.+c_.*v_^2)^p_.*(d_.+f_.*w_^2)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(g+h*x)*(a+c*x^2)^p*(d+f*x^2)^q,x],x,u] /;
FreeQ[{a,c,d,f,g,h,p,q},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[z_^m_.*u_^p_.*v_^q_.,x_Symbol] :=
  Int[ExpandToSum[z,x]^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{m,p,q},x] && LinearQ[z,x] && QuadraticQ[{u,v},x] && Not[LinearMatchQ[z,x] && QuadraticMatchQ[{u,v},x]]



