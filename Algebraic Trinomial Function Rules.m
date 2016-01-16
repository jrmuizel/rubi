(* ::Package:: *)

(* ::Section:: *)
(*Algebraic Trinomial Function Rules*)


(* ::Subsection::Closed:: *)
(*3.1.1 (a+b x+c x^2)^p*)


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[Cancel[(b/2+c*x)^(2*p)/c^p],x] /;
FreeQ[{a,b,c},x] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  (b/2+c*x)/Sqrt[a+b*x+c*x^2]*Int[1/(b/2+c*x),x] /;
FreeQ[{a,b,c},x] && ZeroQ[b^2-4*a*c]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) /;
FreeQ[{a,b,c,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*p+1]


Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
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


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  ArcSinh[(b+2*c*x)/(Rt[c,2]*Sqrt[4*a-b^2/c])]/Rt[c,2] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveQ[4*a-b^2/c] && PosQ[c]


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  -ArcSin[(b+2*c*x)/(Rt[-c,2]*Sqrt[4*a-b^2/c])]/Rt[-c,2] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveQ[4*a-b^2/c] && NegQ[c]


Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*Subst[Int[1/(4*c-x^2),x],x,(b+2*c*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && Not[PositiveQ[4*a-b^2/c]]


Int[1/(a_+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
  -2*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  1/c^p*Int[Simp[b/2-q/2+c*x,x]^p*Simp[b/2+q/2+c*x,x]^p,x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p] && PerfectSquareQ[b^2-4*a*c]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p] && Not[PerfectSquareQ[b^2-4*a*c]]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) -
  p*(b^2-4*a*c)/(2*c*(2*p+1))*Int[(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p>0 && Not[IntegerQ[p]]


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) -
  2*c*(2*p+3)/((p+1)*(b^2-4*a*c))*Int[(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p<-1 && p!=-3/2


Int[(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  2^(p-1)*(b-Rt[b^2-4*a*c,2]+2*c*x)*(a+b*x+c*x^2)^p/(c*(p+1)*((b+Rt[b^2-4*a*c,2]+2*c*x)/Rt[b^2-4*a*c,2])^p)*
    Hypergeometric2F1[-p,p+1,p+2,(-b+Rt[b^2-4*a*c,2]-2*c*x)/(2*Rt[b^2-4*a*c,2])] /;
FreeQ[{a,b,c,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[p+1]


Int[(a_+b_.*u_+c_.*v_^2)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,p},x] && ZeroQ[u-v] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && QuadraticQ[u,x] && Not[QuadraticMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*3.1.2 (d+e x)^m (a+b x+c x^2)^p*)


Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^m*Cancel[(b/2+c*x)^(2*p)/c^p],x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(d_+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e^m*(a+b*x+c*x^2)^(p+(m+1)/2)/(c^((m+1)/2)*(m+2*p+1)) /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[2*c*d-b*e] && OddQ[m]


Int[(d_+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p*Log[RemoveContent[d+e*x,x]]/e /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[2*c*d-b*e] && ZeroQ[m+2*p+1]


Int[(d_+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+1]


Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((m+1)*(2*c*d-b*e)) /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  ZeroQ[m+2*p+2] && NonzeroQ[m+1]


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
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && ZeroQ[m+2*p+3] && NonzeroQ[m+2]


Int[(d_.+e_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) + 
  (2*c*d-b*e)/(2*c)*Int[(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && NonzeroQ[p+3/2]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  p*(d+e*x)^(m+2)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1)/(e^2*(m+1)*(m+2*p+1)) + 
  p*(2*p-1)*(2*c*d-b*e)/(e^2*(m+1)*(m+2*p+1))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[m,p] && p>1 && -2<=m<-1


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  p*(d+e*x)^(m+2)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1)/(e^2*(m+1)*(m+2)) + 
  2*c*p*(2*p-1)/(e^2*(m+1)*(m+2))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[m,p] && p>1 && m<-2 && Not[NegativeIntegerQ[m+2*p+3] && m+3*p+3>0]


Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*(m+2*p+2)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*p+1)*(2*c*d-b*e)) + 
  (d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((2*p+1)*(2*c*d-b*e)) + 
  e^2*m*(m+2*p+2)/((p+1)*(2*p+1)*(2*c*d-b*e))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[m,p] && p<-1 && 0<m<=1


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -e*m*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)*(2*p+1)) + 
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(2*p+1)) + 
  e^2*m*(m-1)/(2*c*(p+1)*(2*p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[m,p] && p<-1 && m>1


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  p*(2*c*d-b*e)*(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1)/(2*c*e^2*(m+2*p)*(m+2*p+1)) + 
  p*(2*p-1)*(2*c*d-b*e)^2/(2*c*e^2*(m+2*p)*(m+2*p+1))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[p] && p>0 && NonzeroQ[m+2*p] && 
  NonzeroQ[m+2*p+1] && Not[NegativeIntegerQ[m+2*p+3] && m+3*p+3>0] && 
  Not[RationalQ[m] && m<-2] && Not[IntegerQ[m] && m>0 && (Not[IntegerQ[2*p]] || m<2*p)]


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -2*c*e*(m+2*p+2)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*p+1)*(2*c*d-b*e)^2) + 
  (d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((2*p+1)*(2*c*d-b*e)) + 
  2*c*e^2*(m+2*p+2)*(m+2*p+3)/((p+1)*(2*p+1)*(2*c*d-b*e)^2)*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[p] && p<-1 && NonzeroQ[m+p+1]


Int[(d_.+e_.*x_)^m_.*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*(m+2*p+1)) + 
  m*(2*c*d-b*e)/(2*c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[m] && m>0 && NonzeroQ[m+2*p+1] && 
  (Not[RationalQ[p]] || -1<=p<0 || IntegerQ[m] && 0<m<2*p || m==1/2 && p<0)


Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/((m+1)*(2*c*d-b*e)) + 
  2*c*(m+2*p+2)/((m+1)*(2*c*d-b*e))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e] && 
  NonzeroQ[m+2*p+2] && RationalQ[m] && m<-1


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^p/(b/2+c*x)^(2*p)*Int[(d+e*x)^m*(b/2+c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NonzeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m},x] && ZeroQ[c*d^2+a*e^2] && IntegerQ[p]


Int[1/(Sqrt[d_.+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  2*e*Subst[Int[1/(2*c*d-b*e+e^2*x^2),x],x,Sqrt[a+b*x+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2]


Int[1/(Sqrt[d_+e_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  2*e*Subst[Int[1/(2*c*d+e^2*x^2),x],x,Sqrt[a+c*x^2]/Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && ZeroQ[m+p] && NonzeroQ[p+1]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(p+1)) /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && ZeroQ[m+p] && NonzeroQ[p+1]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((p+1)*(2*c*d-b*e)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && ZeroQ[m+2*p+2] && NonzeroQ[p+1] && NonzeroQ[p+2]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[c*d^2+a*e^2] && ZeroQ[m+2*p+2] && NonzeroQ[p+1] && NonzeroQ[p+2]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e^2*(m+2*p+1)) - 
  p*(2*c*d-b*e)/(e^2*(m+2*p+1))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  NonzeroQ[m+p] && NonzeroQ[m+2*p+2] && RationalQ[m,p] && p>0 && 
  (-1<=m<0 || m+p+1==0) && NonzeroQ[m+2*p+1] && Not[NegativeIntegerQ[m+2*p+2]] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+c*x^2)^p/(e^2*(m+2*p+1)) - 
  2*c*d*p/(e^2*(m+2*p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] && 
  NonzeroQ[m+p] && NonzeroQ[m+2*p+2] && RationalQ[m,p] && p>0 && 
  (-1<=m<0 || m+p+1==0) && NonzeroQ[m+2*p+1] && Not[NegativeIntegerQ[m+2*p+2]] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+p+1)) - 
  c*p/(e^2*(m+p+1))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[m+p] && 
  NonzeroQ[m+2*p+2] && RationalQ[m,p] && p>0 && m<-1 && NonzeroQ[m+p+1] && 
  Not[NegativeIntegerQ[m+2*p+2]] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+p+1)) - 
  c*p/(e^2*(m+p+1))*Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] && 
  NonzeroQ[m+p] && NonzeroQ[m+2*p+2] && RationalQ[m,p] && p>0 && m<-1 && NonzeroQ[m+p+1] && 
  Not[NegativeIntegerQ[m+2*p+2]] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (2*c*d-b*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) - 
  e*(2*c*d-b*e)*(m+2*p+2)/(e*(p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  NonzeroQ[m+p] && NonzeroQ[m+2*p+2] && RationalQ[m,p] && p<-1 && 0<m<=1 && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -d*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*e*(p+1)) + 
  d*(m+2*p+2)/(2*a*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] && 
  NonzeroQ[m+p] && NonzeroQ[m+2*p+2] && RationalQ[m,p] && p<-1 && 0<m<=1 && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(p+1)) - 
  e^2*(m+p)/(c*(p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  NonzeroQ[m+p] && NonzeroQ[m+2*p+2] && RationalQ[m,p] && p<-1 && m>1 && Not[NegativeIntegerQ[m+2*p+2]] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(p+1)) - 
  e^2*(m+p)/(c*(p+1))*Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] && 
  NonzeroQ[m+p] && NonzeroQ[m+2*p+2] && RationalQ[m,p] && p<-1 && m>1 && Not[NegativeIntegerQ[m+2*p+2]] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  (m+p)*(2*c*d-b*e)/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[m+p] && 
  NonzeroQ[m+2*p+2] && RationalQ[m] && (m>=1 || PositiveIntegerQ[m+p]) && NonzeroQ[m+2*p+1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  2*c*d*(m+p)/(c*(m+2*p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && ZeroQ[c*d^2+a*e^2] && NonzeroQ[m+p] && 
  NonzeroQ[m+2*p+2] && RationalQ[m] && (m>=1 || PositiveIntegerQ[m+p]) && NonzeroQ[m+2*p+1] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -e*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((m+p+1)*(2*c*d-b*e)) + 
  c*(m+2*p+2)/((m+p+1)*(2*c*d-b*e))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[m+p] && 
  NonzeroQ[m+2*p+2] && RationalQ[m] && m<0 && NonzeroQ[m+p+1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  -e*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) + 
  (m+2*p+2)/(2*d*(m+p+1))*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,p},x] && ZeroQ[c*d^2+a*e^2] && NonzeroQ[m+p] && 
  NonzeroQ[m+2*p+2] && RationalQ[m] && m<0 && NonzeroQ[m+p+1] && IntegerQ[2*p]


Int[(e_.*x_)^m_*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (e*x)^m*(b*x+c*x^2)^p/(x^(m+p)*(b+c*x)^p)*Int[x^(m+p)*(b+c*x)^p,x] /;
FreeQ[{b,c,e,m},x] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && PositiveQ[a] && PositiveQ[d]


Int[(d_+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^p/((d+e*x)^p*(a/d+(c*x)/e)^p)*Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a+c*x^2)^p/((d+e*x)^p*(a/d+(c*x)/e)^p)*Int[(d+e*x)^(m+p)*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,m},x] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  d/b*Log[RemoveContent[a+b*x+c*x^2,x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  d*(a+b*x+c*x^2)^(p+1)/(b*(p+1)) /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[p+1]


Int[(d_.+e_.*x_)^m_/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Module[{n=Denominator[m]},
  -4*c*e*n*Subst[Int[x^(n*(m+1)-1)/(e^2*(b^2-4*a*c)-4*c^2*x^(2*n)),x],x,(d+e*x)^(1/n)]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && RationalQ[m] && -1<m<1


Int[1/(Sqrt[d_+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -2*Sqrt[a+b*x+c*x^2]/((b^2-4*a*c)^(1/4)*Sqrt[b+2*c*x]*Sqrt[d+e*x]*Sqrt[c*(a+b*x+c*x^2)/(b+2*c*x)^2])*
    EllipticF[ArcSin[(b^2-4*a*c)^(1/4)/Sqrt[b+2*c*x]],-1] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e]


Int[Sqrt[d_+e_.*x_]/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
  2*(b^2-4*a*c)^(3/4)*Sqrt[d+e*x]*Sqrt[-c*(a+b*x+c*x^2)/(b^2-4*a*c)]/(c*Sqrt[b+2*c*x]*Sqrt[a+b*x+c*x^2])*
    EllipticE[ArcSin[Sqrt[b+2*c*x]/(b^2-4*a*c)^(1/4)],-1] - 
  d*Sqrt[b^2-4*a*c]/b*Int[1/(Sqrt[d+e*x]*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e]


Int[1/((d_+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  4*c*Subst[Int[1/(b^2*e-4*a*c*e+4*c*e*x^2),x],x,Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e]


Int[1/((d_+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  -4*b*c/(d*(b^2-4*a*c))*Int[1/(b+2*c*x),x] + 
  b^2/(d^2*(b^2-4*a*c))*Int[(d+e*x)/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*c*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && ZeroQ[m+2*p+3] && NonzeroQ[p+1]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && PositiveIntegerQ[p] && 
  Not[OddQ[m] && 0<m<=3 && p!=1]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  b*p/(d*e*(m+1))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && 
  RationalQ[m,p] && m<-1 && p>0


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  d*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)) - 
  d*e*(m-1)/(b*(p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && 
  RationalQ[m,p] && p<-1 && m>1


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  d*p*(b^2-4*a*c)/(b*e*(m+2*p+1))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && 
  RationalQ[p] && p>0 && Not[RationalQ[m] && m<-1] && Not[OddQ[m] && m>0 && (Not[IntegerQ[p]] || m<2*p)]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*c*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(e*(p+1)*(b^2-4*a*c)) - 
  2*c*e*(m+2*p+3)/(e*(p+1)*(b^2-4*a*c))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && 
  RationalQ[p] && p<-1 && Not[RationalQ[m] && m>1]


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  2*d*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(b*(m+2*p+1)) + 
  d^2*(m-1)*(b^2-4*a*c)/(b^2*(m+2*p+1))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && 
  RationalQ[m] && m>1 && Not[RationalQ[p] && p<-1] && NonzeroQ[m+2*p+1] && 
  (Not[RationalQ[p]] || -1<=p<0 || OddQ[m])


Int[(d_+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  -2*b*d*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(d^2*(m+1)*(b^2-4*a*c)) + 
  b^2*(m+2*p+3)/(d^2*(m+1)*(b^2-4*a*c))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+3] && 
  RationalQ[m] && m<-1 && (Not[RationalQ[p]] || -1<=p<0)


Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (c*d-e*(b/2-q/2))/q*Int[1/(b/2-q/2+c*x),x] -
  (c*d-e*(b/2+q/2))/q*Int[1/(b/2+q/2+c*x),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  NiceSqrtQ[b^2-4*a*c]


Int[(d_+e_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
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
  Module[{q=Rt[(c*d^2-b*d*e+a*e^2)/c,2]},
  1/2*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x] + 
  1/2*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  NegativeQ[b^2-4*a*c] *)


(* Int[Sqrt[d_+e_.*x_]/(a_+c_.*x_^2),x_Symbol] :=
  Module[{q=Rt[(c*d^2+a*e^2)/c,2]},
  1/2*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x] + 
  1/2*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NegativeQ[-a*c] *)


(* Int[Sqrt[d_.+e_.*x_]/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-b*e+e*q)/q*Int[1/(Sqrt[d+e*x]*(b-q+2*c*x)),x] - 
  (2*c*d-b*e-e*q)/q*Int[1/(Sqrt[d+e*x]*(b+q+2*c*x)),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] (* && 
  Not[NegativeQ[b^2-4*a*c]] *) *)


(* Int[Sqrt[d_+e_.*x_]/(a_+c_.*x_^2),x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
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
  Module[{q=Rt[(c*d^2-b*d*e+a*e^2)/c,2]},
  1/(2*q)*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x] - 
  1/(2*q)*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+b*x+c*x^2)),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  NegativeQ[b^2-4*a*c] *)


(* Int[1/(Sqrt[d_+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  Module[{q=Rt[(c*d^2+a*e^2)/c,2]},
  1/(2*q)*Int[(d+q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x] - 
  1/(2*q)*Int[(d-q+e*x)/(Sqrt[d+e*x]*(a+c*x^2)),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NegativeQ[-a*c] *)


(* Int[1/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/(Sqrt[d+e*x]*(b-q+2*c*x)),x] - 
  2*c/q*Int[1/(Sqrt[d+e*x]*(b+q+2*c*x)),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] (* && 
  Not[NegativeQ[b^2-4*a*c]] *) *)


(* Int[1/(Sqrt[d_+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
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


Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  PositiveIntegerQ[p]


Int[(d_+e_.*x_)*(a_+c_.*x_^2),x_Symbol] :=
  Int[a*d + a*e*x + c*d*x^2 + c*e*x^3,x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


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


Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -2*Subst[Int[1/(4*c*d^2-4*b*d*e+4*a*e^2-x^2),x],x,(2*a*e-b*d-(2*c*d-b*e)*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e]


Int[1/((d_+e_.*x_)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  -Subst[Int[1/(c*d^2+a*e^2-x^2),x],x,(a*e-c*d*x)/Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e},x]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^p/(2*(m+1)*(c*d^2-b*d*e+a*e^2)) + 
  p*(b^2-4*a*c)/(2*(m+1)*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+2)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && m+2*p+2==0 && p>0 && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(-2*a*e+(2*c*d)*x)*(a+c*x^2)^p/(2*(m+1)*(c*d^2+a*e^2)) - 
  4*a*c*p/(2*(m+1)*(c*d^2+a*e^2))*Int[(d+e*x)^(m+2)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && m+2*p+2==0 && p>0 && Not[IntegerQ[p]]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) - 
  4*(m-1)*(c*d^2-b*d*e+a*e^2)/(m*(b^2-4*a*c))*Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && m+2*p+2==0 && p<-1


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(a*e-c*d*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) + 
  (m-1)*(c*d^2+a*e^2)/(a*c*m)*Int[(d+e*x)^(m-2)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && m+2*p+2==0 && p<-1


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  m*(2*c*d-b*e)/((p+1)*(b^2-4*a*c))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && m+2*p+3==0 && m>0


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^m*(2*c*x)*(a+c*x^2)^(p+1)/(4*a*c*(p+1)) - 
  m*(2*c*d)/(4*a*c*(p+1))*Int[(d+e*x)^(m-1)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && m+2*p+3==0 && m>0


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  (2*c*d-b*e)/(2*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && m+2*p+3==0 && m<-1 && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  c*d/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && m+2*p+3==0 && m<-1 && Not[IntegerQ[p]]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(b*c*d-b^2*e+2*a*c*e+c*(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) + 
  (4*c*(c*d^2-b*d*e+a*e^2)+m*(2*c*d-b*e)^2)/(2*(p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && m+2*p+4==0 && p<-1


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(a*e+c*d*x)*(a+c*x^2)^(p+1)/(2*a*(p+1)*(c*d^2+a*e^2)) - 
  ((c*d^2+a*e^2)+c*d^2*m)/(2*a*(p+1)*(c*d^2+a*e^2))*Int[(d+e*x)^m*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && m+2*p+4==0 && p<-1


Int[(d_.+e_.*x_)^m_/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
  Sqrt[x]*Sqrt[b+c*x]/Sqrt[b*x+c*x^2]*Int[(d+e*x)^m/(Sqrt[x]*Sqrt[b+c*x]),x] /;
FreeQ[{b,c,d,e},x] && NonzeroQ[2*c*d-b*e] && NonzeroQ[c*d-b*e] && RationalQ[m] && m^2==1/4


Int[(e_.*x_)^m_/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x/(b-q)]*Sqrt[1+2*c*x/(b+q)]/Sqrt[a+b*x+c*x^2]*Int[(e*x)^m/(Sqrt[1+2*c*x/(b-q)]*Sqrt[1+2*c*x/(b+q)]),x]] /;
FreeQ[{a,b,c,e},x] && NonzeroQ[b^2-4*a*c] && RationalQ[m] && m^2==1/4


Int[(d_+e_.*x_)^m_/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  Sqrt[(q*e-b*e-2*c*e*x)/(q*e-b*e+2*c*d)]*Sqrt[(q*e+b*e+2*c*e*x)/(q*e+b*e-2*c*d)]/Sqrt[a+b*x+c*x^2]*
    Int[(d+e*x)^m/(Sqrt[(q*e-b*e)/(q*e-b*e+2*c*d)-2*c*e*x/(q*e-b*e+2*c*d)]*Sqrt[(q*e+b*e)/(q*e+b*e-2*c*d)+2*c*e*x/(q*e+b*e-2*c*d)]),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && RationalQ[m] && m^2==1/4


Int[(d_+e_.*x_)^m_/Sqrt[a_+c_.*x_^2],x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
  Sqrt[(q*e-c*e*x)/(q*e+c*d)]*Sqrt[(q*e+c*e*x)/(q*e-c*d)]/Sqrt[a+c*x^2]*
    Int[(d+e*x)^m/(Sqrt[q*e/(q*e+c*d)-c*e*x/(q*e+c*d)]*Sqrt[q*e/(q*e-c*d)+c*e*x/(q*e-c*d)]),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m] && m^2==1/4


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  PositiveIntegerQ[p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  p/(e*(m+1))*Int[(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[p] && p>0 && NonzeroQ[m+1] && (IntegerQ[p] || RationalQ[m] && m<-1)


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+1)) - 
  2*c*p/(e*(m+1))*Int[x*(d+e*x)^(m+1)*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[p] && p>0 && NonzeroQ[m+1] && (IntegerQ[p] || RationalQ[m] && m<-1)


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+2*p+1)) - 
  p/(e*(m+2*p+1))*
    Int[(d+e*x)^m*Simp[b*d-2*a*e+(2*c*d-b*e)*x,x]*(a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[p] && p>0 && NonzeroQ[m+2*p+1] && (Not[RationalQ[m]] || m<1)


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+2*p+1)) + 
  2*p/(e*(m+2*p+1))*Int[(d+e*x)^m*Simp[a*e-c*d*x,x]*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[p] && p>0 && NonzeroQ[m+2*p+1] && (Not[RationalQ[m]] || m<1)


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) - 
  1/((p+1)*(b^2-4*a*c))*
    Int[(d+e*x)^(m-1)*(b*e*m+2*c*d*(2*p+3)+2*c*e*(m+2*p+3)*x)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && p<-1 && 0<m<1


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -x*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*a*(p+1)) + 
  1/(2*a*(p+1))*Int[(d+e*x)^(m-1)*(d*(2*p+3)+e*(m+2*p+3)*x)*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && p<-1 && 0<m<1


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(d*b-2*a*e+(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*
    Int[(d+e*x)^(m-2)*
      Simp[e*(2*a*e*(m-1)+b*d*(2*p-m+4))-2*c*d^2*(2*p+3)+e*(b*e-2*d*c)*(m+2*p+2)*x,x]*
      (a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[m,p] && p<-1 && m>1


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m-1)*(a*e-c*d*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) + 
  1/((p+1)*(-2*a*c))*
    Int[(d+e*x)^(m-2)*Simp[a*e^2*(m-1)-c*d^2*(2*p+3)-d*c*e*(m+2*p+2)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && p<-1 && m>1


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(b*c*d-b^2*e+2*a*c*e+c*(2*c*d-b*e)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) + 
  1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^m*
      Simp[b*c*d*e*(2*p-m+2)+b^2*e^2*(m+p+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3)-c*e*(2*c*d-b*e)*(m+2*p+4)*x,x]*
      (a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  RationalQ[p] && p<-1 && (Not[RationalQ[m]] || m<0)


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(a*e+c*d*x)*(a+c*x^2)^(p+1)/(2*a*(p+1)*(c*d^2+a*e^2)) + 
  1/(2*a*(p+1)*(c*d^2+a*e^2))*
    Int[(d+e*x)^m*Simp[c*d^2*(2*p+3)+a*e^2*(m+2*p+3)+c*e*d*(m+2*p+4)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[p] && p<-1 && (Not[RationalQ[m]] || m<0)


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  1/(c*(m+2*p+1))*
    Int[(d+e*x)^(m-2)*
      Simp[c*d^2*(m+2*p+1)-e*(a*e*(m-1)+b*d*(p+1))+e*(2*c*d-b*e)*(m+p)*x,x]*
      (a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  If[RationalQ[m], m>1, SumSimplerQ[m,-2]] && NonzeroQ[m+2*p+1] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m-1)*(a+c*x^2)^(p+1)/(c*(m+2*p+1)) + 
  1/(c*(m+2*p+1))*
    Int[(d+e*x)^(m-2)*Simp[c*d^2*(m+2*p+1)-a*e^2*(m-1)+2*c*d*e*(m+p)*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && If[RationalQ[m], m>1, SumSimplerQ[m,-2]] && NonzeroQ[m+2*p+1] && IntegerQ[2*p]


Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^(m+1)*Simp[c*d*(m+1)-b*e*(m+p+2)-c*e*(m+2*p+3)*x,x]*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && 
  If[RationalQ[m], m<-1, NonzeroQ[m+1] && SumSimplerQ[m,1]] && IntegerQ[2*p]


Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  e*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  c/((m+1)*(c*d^2+a*e^2))*
    Int[(d+e*x)^(m+1)*Simp[d*(m+1)-e*(m+2*p+3)*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && If[RationalQ[m], m<-1, NonzeroQ[m+1] && SumSimplerQ[m,1]] && IntegerQ[2*p]


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(1/4)),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*(a+c*x^2)^(1/4)),x] - e*Int[x/((d^2-e^2*x^2)*(a+c*x^2)^(1/4)),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[1/((d_+e_.*x_)*(a_+c_.*x_^2)^(3/4)),x_Symbol] :=
  d*Int[1/((d^2-e^2*x^2)*(a+c*x^2)^(3/4)),x] - e*Int[x/((d^2-e^2*x^2)*(a+c*x^2)^(3/4)),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[1/((d_.+e_.*x_)^(3/2)*(a_.+b_.*x_+c_.*x_^2)^(1/4)),x_Symbol] :=
  2*(b*d-2*a*e+d*Rt[b^2-4*a*c,2]+(2*c*d-b*e+e*Rt[b^2-4*a*c,2])*x)/(3*(c*d^2-b*d*e+a*e^2)*Sqrt[d+e*x]*(a+b*x+c*x^2)^(1/4))*
    ((-b*d+2*a*e+d*Rt[b^2-4*a*c,2]-(2*c*d-b*e-e*Rt[b^2-4*a*c,2])*x)/(2*Rt[b^2-4*a*c,2]*(d+e*x)))^(1/4)*
    Hypergeometric2F1[1/4,3/4,7/4,(b*d-2*a*e+d*Rt[b^2-4*a*c,2]+(2*c*d-b*e+e*Rt[b^2-4*a*c,2])*x)/(2*Rt[b^2-4*a*c,2]*(d+e*x))] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e]


Int[1/((d_+e_.*x_)^(3/2)*(a_+c_.*x_^2)^(1/4)),x_Symbol] :=
  4*(-a*e+d*Rt[-a*c,2]+(c*d+e*Rt[-a*c,2])*x)/(3*(c*d^2+a*e^2)*Sqrt[d+e*x]*(a+c*x^2)^(1/4))*
    ((a*e+d*Rt[-a*c,2]-(c*d-e*Rt[-a*c,2])*x)/(2*Rt[-a*c,2]*(d+e*x)))^(1/4)*
    Hypergeometric2F1[1/4,3/4,7/4,(-a*e+d*Rt[-a*c,2]+(c*d+e*Rt[-a*c,2])*x)/(2*Rt[-a*c,2]*(d+e*x))] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


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


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  2^(2*p)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^p/
    (e*(m+2*p+1)*(e*(b-Rt[b^2-4*a*c,2]+2*c*x)/(c*(d+e*x)))^p*(e*(b+Rt[b^2-4*a*c,2]+2*c*x)/(c*(d+e*x)))^p)*
    AppellF1[-m-2*p-1,-p,-p,-m-2*p,(2*c*d-b*e-e*Rt[b^2-4*a*c,2])/(2*c*(d+e*x)),(2*c*d-b*e+e*Rt[b^2-4*a*c,2])/(2*c*(d+e*x))] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && Not[IntegerQ[p]] && 
  NegativeIntegerQ[m]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  2^(2*p)*(d+e*x)^(m+1)*(a+c*x^2)^p/
    (e*(m+2*p+1)*(2*e*(-Rt[-a*c,2]+c*x)/(c*(d+e*x)))^p*(2*e*(Rt[-a*c,2]+c*x)/(c*(d+e*x)))^p)*
    AppellF1[-m-2*p-1,-p,-p,-m-2*p,(c*d-e*Rt[-a*c,2])/(c*(d+e*x)),(c*d+e*Rt[-a*c,2])/(c*(d+e*x))] /;
FreeQ[{a,c,d,e,p},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && NegativeIntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+b*x+c*x^2)^p/(e*(m+1)*(1-2*c*(d+e*x)/(2*c*d-b*e-e*Rt[b^2-4*a*c,2]))^p*(1-2*c*(d+e*x)/(2*c*d-b*e+e*Rt[b^2-4*a*c,2]))^p)*
    AppellF1[m+1,-p,-p,m+2,2*c*(d+e*x)/(2*c*d-b*e-e*Rt[b^2-4*a*c,2]),2*c*(d+e*x)/(2*c*d-b*e+e*Rt[b^2-4*a*c,2])] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e] && Not[IntegerQ[p]] && 
  Not[NegativeIntegerQ[m]] && Not[NegativeIntegerQ[m+2*p+1]]


Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(a+c*x^2)^p/(e*(m+1)*(1-c*(d+e*x)/(c*d-e*Rt[-a*c,2]))^p*(1-c*(d+e*x)/(c*d+e*Rt[-a*c,2]))^p)*
    AppellF1[m+1,-p,-p,m+2,c*(d+e*x)/(c*d-e*Rt[-a*c,2]),c*(d+e*x)/(c*d+e*Rt[-a*c,2])] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && Not[NegativeIntegerQ[m]] && Not[NegativeIntegerQ[m+2*p+1]]


Int[(d_.+e_.*u_)^m_.*(a_+b_.*v_+c_.*w_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,m,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(d_.+e_.*u_)^m_.*(a_+c_.*w_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(a+c*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,e,m,p},x] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && LinearQ[u,x] && QuadraticQ[v,x] && Not[LinearMatchQ[u,x] && QuadraticMatchQ[v,x]]


(* ::Subsection::Closed:: *)
(*3.1.3 (d+e x)^m (f+g x)^n (a+b x+c x^2)^p*)


Int[(d_.+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^m*(f+g*x)^n*Cancel[(b/2+c*x)^(2*p)/c^p],x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
  (A+B*x)/Sqrt[a+b*x+c*x^2]*Int[(d+e*x)^m,x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && ZeroQ[b*B-2*A*c]


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  A*B*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)*(B*d-A*e)) /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && ZeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  ZeroQ[m+2*p+3]


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  B*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) - 
  B*e*m/(2*c*(p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && ZeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  RationalQ[m,p] && p<-1 && m>0


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  A*B*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(b*(p+1)*(B*d-A*e)) - 
  A*B*e*(m+2*p+3)/(b*(p+1)*(B*d-A*e))*Int[(d+e*x)^m*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && ZeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  RationalQ[p] && p<-1 && Not[RationalQ[m] && m>0]


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(A+B*x)*(a+b*x+c*x^2)^p/(e*(m+1)) - 
  B*(2*p+1)/(e*(m+1))*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && ZeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  RationalQ[m] && m<-1 && NonzeroQ[2*p+1] && 
  (Not[RationalQ[p]] || p>0 && (Not[IntegerQ[m]] || m>=-2*p-2 || m<-4*(p+1)))


Int[(d_.+e_.*x_)^m_*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -2*A*B*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/(b*(m+1)*(B*d-A*e)) + 
  B*(m+2*p+3)/((m+1)*(B*d-A*e))*Int[(d+e*x)^(m+1)*(A+B*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && ZeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  RationalQ[m] && m<-1 && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  B*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  b*m*(B*d-A*e)/(2*A*c*(m+2*p+2))*Int[(d+e*x)^(m-1)*(A+B*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && ZeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  PositiveIntegerQ[m] && NonzeroQ[m+2*p+2] && (Not[RationalQ[p]] || m<2*p+2)


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(A+B*x)*(a+b*x+c*x^2)^p/(e*(m+2*p+2)) - 
  (B*d-A*e)*(2*p+1)/(e*(m+2*p+2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && ZeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  NonzeroQ[m+2*p+2]


Int[(A_.+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  -(b*B-2*A*c)/(2*c*d-b*e)*Int[(a+b*x+c*x^2)^p,x] + 
  (B*d-A*e)/(2*c*d-b*e)*Int[(b+2*c*x)*(a+b*x+c*x^2)^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && NonzeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  NonzeroQ[2*c*d-b*e] && RationalQ[p] && p<0


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (A*e-B*d)/e*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] + 
  B/e*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && NonzeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  (ZeroQ[m+2p+2] && NonzeroQ[m+1] || ZeroQ[2*c*d-b*e] && NonzeroQ[m-1])


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(b*B-2*A*c)/(2*c*d-b*e)*Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] + 
  (B*d-A*e)/(2*c*d-b*e)*Int[(d+e*x)^m*(b+2*c*x)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && NonzeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  NonzeroQ[2*c*d-b*e] && ZeroQ[m+2*p+3]


Int[(d_.+e_.*x_)^m_*(A_+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  -(A*e-B*d)*(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/(e*(m+1)*(2*c*d-b*e)) + 
  (2*A*c*e*(m+2*p+2)-B*(2*c*d*(2*p+1)+b*e*(m+1)))/(e*(m+1)*(2*c*d-b*e))*
    Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && NonzeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  NonzeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && RationalQ[m] && m<-1


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  B*(d+e*x)^(m+1)*(b+2*c*x)*(a+b*x+c*x^2)^p/(2*c*e*(m+2*p+2)) + 
  (2*A*c*e*(m+2*p+2)-B*(b*e*(m+1)+2*c*(d+2*d*p)))/(2*c*e*(m+2*p+2))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[b^2-4*a*c] && NonzeroQ[b*B-2*A*c] && Not[IntegerQ[p]] && 
  NonzeroQ[2*c*d-b*e] && NonzeroQ[m+2*p+2] && NonzeroQ[m+2*p+3] && Not[RationalQ[m] && m<-1]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^p/(b/2+c*x)^(2*p)*Int[(d+e*x)^m*(f+g*x)^n*(b/2+c*x)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  B*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[m*(B*(c*d-b*e)+A*c*e)-e*(p+1)*(b*B-2*A*c)]


Int[(d_+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  B*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) /;
FreeQ[{a,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[c*d^2+a*e^2] && ZeroQ[m*(B*d+A*e)+2*A*e*(p+1)]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (B*(c*d-b*e)+A*c*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(p+1)*(2*c*d-b*e)) - 
  e*(m*(B*(c*d-b*e)+A*c*e)-e*(p+1)*(b*B-2*A*c))/(c*(p+1)*(2*c*d-b*e))*
    Int[(d+e*x)^Simplify[m-1]*(a+b*x+c*x^2)^Simplify[p+1],x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  SumSimplerQ[m,-1] && SumSimplerQ[p,1] && NonzeroQ[p+1]


Int[(d_+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (B*d+A*e)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(p+1)) - 
  e*(m*(B*d+A*e)+2*A*e*(p+1))/(2*c*d*(p+1))*Int[(d+e*x)^Simplify[m-1]*(a+c*x^2)^Simplify[p+1],x] /;
FreeQ[{a,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[c*d^2+a*e^2] && SumSimplerQ[m,-1] && SumSimplerQ[p,1] && NonzeroQ[p+1]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (B*d-A*e)*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/((2*c*d-b*e)*(m+p+1)) + 
  (m*(B*(c*d-b*e)+A*c*e)-e*(p+1)*(b*B-2*A*c))/(e*(2*c*d-b*e)*(m+p+1))*
    Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  (RationalQ[m] && m<-1 && NonzeroQ[m+p] || ZeroQ[m+2*p+2]) && NonzeroQ[m+p+1]


Int[(d_+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (B*d-A*e)*(d+e*x)^m*(a+c*x^2)^(p+1)/(2*c*d*(m+p+1)) + 
  (m*(B*c*d+A*c*e)+2*e*A*c*(p+1))/(e*(2*c*d)*(m+p+1))*
    Int[(d+e*x)^(m+1)*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[c*d^2+a*e^2] && 
  (RationalQ[m] && m<-1 && NonzeroQ[m+p] || ZeroQ[m+2*p+2]) && NonzeroQ[m+p+1]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  B*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  (m*(B*(c*d-b*e)+A*c*e)-e*(p+1)*(b*B-2*A*c))/(c*e*(m+2*p+2))*
    Int[(d+e*x)^m*(a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  NonzeroQ[m+2*p+2]


Int[(d_+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  B*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  (m*(B*d+A*e)+2*A*e*(p+1))/(e*(m+2*p+2))*Int[(d+e*x)^m*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && ZeroQ[c*d^2+a*e^2] && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(A+B*x)/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[m]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(A+B*x)/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[m]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  B*(d+e*x)^m/(c*m) + 
  1/c*Int[(d+e*x)^(m-1)*Simp[A*c*d-a*B*e+(B*c*d-b*B*e+A*c*e)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && FractionQ[m] && m>0


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  B*(d+e*x)^m/(c*m) + 
  1/c*Int[(d+e*x)^(m-1)*Simp[A*c*d-a*B*e+(B*c*d+A*c*e)*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && FractionQ[m] && m>0


Int[(A_.+B_.*x_)/(Sqrt[d_.+e_.*x_]*(a_.+b_.*x_+c_.*x_^2)),x_Symbol] :=
  2*Subst[Int[(A*e-B*d+B*x^2)/(c*d^2-b*d*e+a*e^2-(2*c*d-b*e)*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[(A_.+B_.*x_)/(Sqrt[d_.+e_.*x_]*(a_+c_.*x_^2)),x_Symbol] :=
  2*Subst[Int[(A*e-B*d+B*x^2)/(c*d^2+a*e^2-2*c*d*x^2+c*x^4),x],x,Sqrt[d+e*x]] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  (A*e-B*d)*(d+e*x)^(m+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x)^(m+1)*Simp[A*c*d-A*b*e+a*B*e-c*(A*e-B*d)*x,x]/(a+b*x+c*x^2),x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && FractionQ[m] && m<-1


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  (A*e-B*d)*(d+e*x)^(m+1)/((m+1)*(c*d^2+a*e^2)) + 
  1/(c*d^2+a*e^2)*Int[(d+e*x)^(m+1)*Simp[A*c*d+a*B*e-c*(A*e-B*d)*x,x]/(a+c*x^2),x] /;
FreeQ[{a,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && FractionQ[m] && m<-1


Int[(e_.*x_)^m_*(A_+B_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  A*Int[(e*x)^m/(a+c*x^2),x] + B/e*Int[(e*x)^(m+1)/(a+c*x^2),x] /;
FreeQ[{a,c,e,A,B},x] && Not[RationalQ[m]]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)/(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,(A+B*x)/(a+b*x+c*x^2),x],x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[RationalQ[m]]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)/(a_+c_.*x_^2),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,(A+B*x)/(a+c*x^2),x],x] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && Not[RationalQ[m]]


Int[(A_.+B_.*x_)/(Sqrt[e_.*x_]*Sqrt[a_+b_.*x_+c_.*x_^2]),x_Symbol] :=
  A*Sqrt[1+B*x/A]*Sqrt[Simp[1+B*c*x/(b*B-A*c),x]]/Sqrt[a+b*x+c*x^2]*Int[Sqrt[1+B*x/A]/(Sqrt[e*x]*Sqrt[Simp[1+B*c*x/(b*B-A*c),x]]),x] /;
FreeQ[{a,b,c,e,A,B},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[A*b*B-a*B^2-A^2*c]


Int[(A_.+B_.*x_)/(Sqrt[e_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  A*Sqrt[(A^2-B^2*x^2)/A^2]/Sqrt[a+c*x^2]*Int[Sqrt[1+B*x/A]/(Sqrt[e*x]*Sqrt[1-B*x/A]),x] /;
FreeQ[{a,c,e,A,B},x] && ZeroQ[a*B^2+A^2*c]


Int[(A_.+B_.*x_)/(Sqrt[d_+e_.*x_]*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -(B*d-A*e)*Sqrt[-e*(A+B*x)/(B*d-A*e)]*Sqrt[-e*Simp[b*B-A*c+B*c*x,x]/(A*c*e+B*(c*d-b*e))]/(e*Sqrt[a+b*x+c*x^2])*
    Int[Sqrt[Simp[-A*e/(B*d-A*e)-B*e*x/(B*d-A*e),x]]/(Sqrt[d+e*x]*Sqrt[Simp[-e*(b*B-A*c)/(A*c*e+B*(c*d-b*e))-B*c*e*x/(A*c*e+B*(c*d-b*e)),x]]),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && ZeroQ[A*b*B-a*B^2-A^2*c]


Int[(A_.+B_.*x_)/(Sqrt[d_+e_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  -(B*d-A*e)*Sqrt[-e*(A+B*x)/(B*d-A*e)]*Sqrt[e*(A-B*x)/(A*e+B*d)]/(e*Sqrt[a+c*x^2])*
    Int[Sqrt[Simp[-A*e/(B*d-A*e)-B*e*x/(B*d-A*e),x]]/(Sqrt[d+e*x]*Sqrt[Simp[A*e/(A*e+B*d)-B*e*x/(A*e+B*d),x]]),x] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && ZeroQ[a*B^2+A^2*c]


Int[(A_.+B_.*x_)/(Sqrt[d_.+e_.*x_]*Sqrt[b_.*x_+c_.*x_^2]),x_Symbol] :=
  -(b*B-A*c)/c*Int[1/(Sqrt[d+e*x]*Sqrt[b*x+c*x^2]),x] + B/c*Int[Sqrt[b*x+c*x^2]/(x*Sqrt[d+e*x]),x] /;
FreeQ[{b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d-b*e] && NonzeroQ[b*B-A*c]


Int[(A_.+B_.*x_)/(Sqrt[d_.+e_.*x_]*Sqrt[a_+b_.*x_+c_.*x_^2]),x_Symbol] :=
  (2*A*c-B*(b-Rt[b^2-4*a*c,2]))/(2*c)*Int[1/(Sqrt[d+e*x]*Sqrt[a+b*x+c*x^2]),x] + 
  B/(2*c)*Int[(b-Rt[b^2-4*a*c,2]+2*c*x)/(Sqrt[d+e*x]*Sqrt[a+b*x+c*x^2]),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[A*b*B-a*B^2-A^2*c]


Int[(A_+B_.*x_)/(Sqrt[e_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  (A*c+B*Rt[-a*c,2])/(c*Sqrt[a+c*x^2])*Sqrt[(a+c*x^2)/a]*Int[1/(Sqrt[e*x]*Sqrt[1-c*x/Rt[-a*c,2]]*Sqrt[1+c*x/Rt[-a*c,2]]),x] - 
  B/c*Int[(Rt[-a*c,2]-c*x)/(Sqrt[e*x]*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,e,A,B},x] && NonzeroQ[a*B^2+A^2*c]


Int[(A_.+B_.*x_)/(Sqrt[d_.+e_.*x_]*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  (A*c+B*Rt[-a*c,2])/c*Int[1/(Sqrt[d+e*x]*Sqrt[a+c*x^2]),x] - 
  B/c*Int[(Rt[-a*c,2]-c*x)/(Sqrt[d+e*x]*Sqrt[a+c*x^2]),x] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && NonzeroQ[a*B^2+A^2*c]


Int[(A_+B_.*x_)/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  4*A*(a-d)/(b*d-a*e)*Subst[Int[1/(4*(a-d)-x^2),x],x,(2*(a-d)+(b-e)*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[4*c*(a-d)-(b-e)^2] && ZeroQ[A*e*(b-e)-2*B*(b*d-a*e)] && NonzeroQ[b*d-a*e]


Int[(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  B/e*Int[(a+b*x+c*x^2)^p,x] + 
  (A*e-B*d)/e*Int[(a+b*x+c*x^2)^p/(d+e*x),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[p] && -1<p<0


Int[(A_.+B_.*x_)*(a_+c_.*x_^2)^p_/(d_.+e_.*x_),x_Symbol] :=
  B/e*Int[(a+c*x^2)^p,x] + 
  (A*e-B*d)/e*Int[(a+c*x^2)^p/(d+e*x),x] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && RationalQ[p] && -1<p<0


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (A*e-B*d)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) /;
FreeQ[{a,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && 
  ZeroQ[A*c*d+a*B*e] && ZeroQ[m+2*p+3] && NonzeroQ[m+1]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(A+B*x)*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[p]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(A+B*x)*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,A,B,m},x] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[p]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(A*e*(m+2*p+2)-B*d*(2*p+1)+e*B*(m+1)*x)*(a+b*x+c*x^2)^p/(e^2*(m+1)*(m+2*p+2)) + 
  p/(e^2*(m+1)*(m+2*p+2))*
    Int[(d+e*x)^(m+1)*
      Simp[B*(b*d+2*a*e+2*a*e*m+2*b*d*p)-A*b*e*(m+2*p+2)+(B*(2*c*d+b*e+b*e*m+4*c*d*p)-2*A*c*e*(m+2*p+2))*x,x]*
      (a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[p] && p>0 && (RationalQ[m] && m<-1 || p==1 || IntegerQ[p] && Not[RationalQ[m]]) && NonzeroQ[m+1] && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(A*e*(m+2*p+2)-B*d*(2*p+1)+e*B*(m+1)*x)*(a+c*x^2)^p/(e^2*(m+1)*(m+2*p+2)) + 
  p/(e^2*(m+1)*(m+2*p+2))*
    Int[(d+e*x)^(m+1)*Simp[B*(2*a*e+2*a*e*m)+(B*(2*c*d+4*c*d*p)-2*A*c*e*(m+2*p+2))*x,x]*(a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[p] && p>0 && (RationalQ[m] && m<-1 || p==1 || IntegerQ[p] && Not[RationalQ[m]]) && NonzeroQ[m+1] && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_.*(A_+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  B*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(2*c*(p+1)) - 
  B*e*m/(2*c*(p+1))*Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[m,p] && m>0 && p<-1 && ZeroQ[b*B-2*A*c]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(A*b-2*a*B-(b*B-2*A*c)*x)*(a+b*x+c*x^2)^(p+1)/((p+1)*(b^2-4*a*c)) + 
  1/((p+1)*(b^2-4*a*c))*
    Int[(d+e*x)^(m-1)*
      Simp[B*(2*a*e*m+b*d*(2*p+3))-A*(b*e*m+2*c*d*(2*p+3))+e*(b*B-2*A*c)*(m+2*p+3)*x,x]*
      (a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[m,p] && p<-1 && m>0 && NonzeroQ[b*B-2*A*c]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^m*(a*B-c*A*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)) - 
  1/(2*a*c*(p+1))*
    Int[(d+e*x)^(m-1)*Simp[a*e*B*m-c*d*A*(2*p+3)-c*e*A*(m+2*p+3)*x,x]*(a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,p] && p<-1 && m>0


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(A*c*e*(m+2*p+2)-B*(c*d+2*c*d*p-b*e*p)+B*c*e*(m+2*p+1)*x)*(a+b*x+c*x^2)^p/
    (c*e^2*(m+2*p+1)*(m+2*p+2)) - 
  p/(c*e^2*(m+2*p+1)*(m+2*p+2))*
    Int[(d+e*x)^m*
      Simp[A*c*e*(b*d-2*a*e)*(m+2*p+2)+B*(a*e*(b*e-2*c*d*m+b*e*m)+b*d*(b*e*p-c*d-2*c*d*p))+
        (A*c*e*(2*c*d-b*e)*(m+2*p+2)+B*(b^2*e^2*(p+m+1)-2*c^2*d^2*(1+2*p)-c*e*(b*d*(m-2*p)+2*a*e*(m+2*p+1))))*x,x]*
      (a+b*x+c*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[p] && p>0 && (IntegerQ[p] || Not[RationalQ[m]] || -1<=m<0) && NonzeroQ[m+2*p+1] && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (d+e*x)^(m+1)*(A*c*e*(m+2*p+2)-B*c*d*(2*p+1)+B*c*e*(m+2*p+1)*x)*(a+c*x^2)^p/
    (c*e^2*(m+2*p+1)*(m+2*p+2)) + 
  2*p/(c*e^2*(m+2*p+1)*(m+2*p+2))*
    Int[(d+e*x)^m*
      Simp[A*a*c*e^2*(m+2*p+2)+B*a*c*d*e*m-(A*c^2*d*e*(m+2*p+2)-B*(c^2*d^2*(2*p+1)+a*c*e^2*(m+2*p+1)))*x,x]*
      (a+c*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[p] && p>0 && (IntegerQ[p] || Not[RationalQ[m]] || -1<=m<0) && NonzeroQ[m+2*p+1] && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (d+e*x)^(m+1)*(A*(b*c*d-b^2*e+2*a*c*e)-a*B*(2*c*d-b*e)+c*(A*(2*c*d-b*e)-B*(b*d-2*a*e))*x)*(a+b*x+c*x^2)^(p+1)/
    ((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) + 
  1/((p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^m*
      Simp[A*(b*c*d*e*(2*p-m+2)+b^2*e^2*(p+m+2)-2*c^2*d^2*(2*p+3)-2*a*c*e^2*(m+2*p+3))-
        B*(a*e*(b*e-2*c*d*m+b*e*m)+b*d*(-3*c*d+b*e-2*c*d*p+b*e*p))+
        c*e*(B*(b*d-2*a*e)-A*(2*c*d-b*e))*(m+2*p+4)*x,x]*
      (a+b*x+c*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[p] && p<-1


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_,x_Symbol] :=
  -(d+e*x)^(m+1)*(A*a*c*e-a*B*c*d+c*(A*c*d+B*a*e)*x)*(a+c*x^2)^(p+1)/(2*a*c*(p+1)*(c*d^2+a*e^2)) + 
  1/(2*a*c*(p+1)*(c*d^2+a*e^2))*
    Int[(d+e*x)^m*
      Simp[A*(c^2*d^2*(2*p+3)+a*c*e^2*(m+2*p+3))-B*a*e*c*d*m+c*e*(B*a*e+A*c*d)*(m+2*p+4)*x,x]*
      (a+c*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,A,B},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && RationalQ[p] && p<-1


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  B*(d+e*x)^m*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  1/(c*(m+2*p+2))*
    Int[(d+e*x)^(m-1)*
      Simp[m*(A*c*d-a*B*e)-d*(b*B-2*A*c)*(p+1)+((B*c*d-b*B*e+A*c*e)*m-e*(b*B-2*A*c)*(p+1))*x,x]*
      (a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  If[RationalQ[m], m>0, SumSimplerQ[m,-1]] && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_.*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  B*(d+e*x)^m*(a+c*x^2)^(p+1)/(c*(m+2*p+2)) + 
  1/(c*(m+2*p+2))*
    Int[(d+e*x)^(m-1)*Simp[c*d*A*(m+2*p+2)-B*a*e*m+c*(e*A*(m+2*p+2)+B*d*m)*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && 
  If[RationalQ[m], m>0, SumSimplerQ[m,-1]] && NonzeroQ[m+2*p+2]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  (A*e-B*d)*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(p+1)/((m+1)*(c*d^2-b*d*e+a*e^2)) + 
  1/((m+1)*(c*d^2-b*d*e+a*e^2))*
    Int[(d+e*x)^(m+1)*
      Simp[(A*c*d-A*b*e+a*B*e)*(m+1)+b*(B*d-A*e)*(p+1)-c*(A*e-B*d)*(m+2*p+3)*x,x]*
      (a+b*x+c*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  If[RationalQ[m], m<-1, NonzeroQ[m+1] && SumSimplerQ[m,1]]


Int[(d_.+e_.*x_)^m_*(A_.+B_.*x_)*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  (A*e-B*d)*(d+e*x)^(m+1)*(a+c*x^2)^(p+1)/((m+1)*(c*d^2+a*e^2)) + 
  1/((m+1)*(c*d^2+a*e^2))*
    Int[(d+e*x)^(m+1)*Simp[(A*c*d+a*B*e)*(m+1)-c*(A*e-B*d)*(m+2*p+3)*x,x]*(a+c*x^2)^p,x] /;
FreeQ[{a,c,d,e,A,B,m,p},x] && NonzeroQ[B*d-A*e] && NonzeroQ[c*d^2+a*e^2] && 
  If[RationalQ[m], m<-1, NonzeroQ[m+1] && SumSimplerQ[m,1]]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^2*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(f+g*x)*(a+b*x+c*x^2)^(p+1)/(c*(m+2*p+3)) - 
  1/(c*e^2*(m+2*p+3))*Int[(d+e*x)^m*(a+b*x+c*x^2)^p*
    Simp[b*e*g*(d*g+e*f*(m+p+1))-c*(d^2*g^2+d*e*f*g*m+e^2*f^2*(m+2*p+3))+
      e*g*(b*e*g*(m+p+2)-c*(d*g*m+e*f*(m+2*p+4)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^2*(a_+c_.*x_^2)^p_,x_Symbol] :=
  g*(d+e*x)^m*(f+g*x)*(a+c*x^2)^(p+1)/(c*(m+2*p+3)) - 
  1/(c*e^2*(m+2*p+3))*Int[(d+e*x)^m*(a+c*x^2)^p*
    Simp[-c*(d^2*g^2+d*e*f*g*m+e^2*f^2*(m+2*p+3))-c*e*g*(d*g*m+e*f*(m+2*p+4))*x,x],x] /;
FreeQ[{a,c,d,e,f,g,m,p},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[p]] && (PositiveIntegerQ[m] || IntegersQ[m,n])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && 
  (PositiveIntegerQ[m] || IntegersQ[m,n])


Int[(e_.*x_)^m_*(f_.+g_.*x_)^n_*(b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
  (e*x)^m*(b*x+c*x^2)^p/(x^(m+p)*(b+c*x)^p)*Int[x^(m+p)*(f+g*x)^n*(b+c*x)^p,x] /;
FreeQ[{b,c,e,f,g,m,n},x] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_.*(f_.+g_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]] && PositiveQ[a] && PositiveQ[d]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
(*(a+b*x+c*x^2)^p/((d+e*x)^p*(a*e+c*d*x)^p)*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a*e+c*d*x)^p,x] /; *)
  (a+b*x+c*x^2)^p/((d+e*x)^p*(a/d+(c*x)/e)^p)*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_,x_Symbol] :=
  (a+c*x^2)^p/((d+e*x)^p*(a/d+(c*x)/e)^p)*Int[(d+e*x)^(m+p)*(f+g*x)^n*(a/d+c/e*x)^p,x] /;
FreeQ[{a,c,d,e,f,g,m,n},x] && NonzeroQ[e*f-d*g] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegersQ[m,n,p]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[c*d^2+a*e^2] && IntegersQ[m,n,p]


Int[(a_.+b_.*x_+c_.*x_^2)^p_/((d_.+e_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  (c*d^2-b*d*e+a*e^2)/(e*(e*f-d*g))*Int[(a+b*x+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[(c*d*f-b*e*f+a*e*g-c*(e*f-d*g)*x)*(a+b*x+c*x^2)^(p-1)/(f+g*x),x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && FractionQ[p] && p>0


Int[(a_+c_.*x_^2)^p_/((d_.+e_.*x_)*(f_.+g_.*x_)),x_Symbol] :=
  (c*d^2+a*e^2)/(e*(e*f-d*g))*Int[(a+c*x^2)^(p-1)/(d+e*x),x] - 
  1/(e*(e*f-d*g))*Int[(c*d*f+a*e*g-c*(e*f-d*g)*x)*(a+c*x^2)^(p-1)/(f+g*x),x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[e*f-d*g] && NonzeroQ[c*d^2+a*e^2] && FractionQ[p] && p>0


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Module[{q=Denominator[m]},
  q/e*Subst[Int[x^(q*(m+1)-1)*((e*f-d*g)/e+g*x^q/e)^n*
    ((c*d^2-b*d*e+a*e^2)/e^2-(2*c*d-b*e)*x^q/e^2+c*x^(2*q)/e^2)^p,x],x,(d+e*x)^(1/q)]] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegersQ[n,p] && FractionQ[m]


Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Module[{q=Denominator[m]},
  q/e*Subst[Int[x^(q*(m+1)-1)*((e*f-d*g)/e+g*x^q/e)^n*((c*d^2+a*e^2)/e^2-2*c*d*x^q/e^2+c*x^(2*q)/e^2)^p,x],x,(d+e*x)^(1/q)]] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[c*d^2+a*e^2] && IntegersQ[n,p] && FractionQ[m]


(* Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegersQ[n,p] && Not[RationalQ[m]] *)


(* Int[(d_.+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m,(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g,m},x] && NonzeroQ[c*d^2+a*e^2] && IntegersQ[n,p] && Not[RationalQ[m]] *)


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


Int[x_^m_.*(d_+e_.*x_)^n_.*(a_+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[n]


Int[x_^m_.*(d_+e_.*x_)^n_.*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,m,p},x] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[n]


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_.+b_.*x_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,g},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  (PositiveIntegerQ[m] || PositiveIntegerQ[p] || IntegersQ[m,n,p])


Int[(d_+e_.*x_)^m_*(f_.+g_.*x_)^n_*(a_+c_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,g},x] && NonzeroQ[c*d^2+a*e^2] && 
  (PositiveIntegerQ[m] || PositiveIntegerQ[p] || IntegersQ[m,n,p])


Int[(d_.+e_.*u_)^m_.*(f_.+g_.*v_)^n_.*(a_+b_.*w_+c_.*z_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(f+g*x)^n*(a+b*x+c*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(d_.+e_.*u_)^m_.*(f_.+g_.*v_)^n_.*(a_+c_.*z_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x)^m*(f+g*x)^n*(a+c*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,e,f,g,m,n,p},x] && ZeroQ[u-v] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
FreeQ[{m,n,p},x] && LinearQ[{u,v},x] && QuadraticQ[w,x] && Not[LinearMatchQ[{u,v},x] && QuadraticMatchQ[w,x]]


(* ::Subsection::Closed:: *)
(*3.1.4 (a+b x+c x^2)^m (d+e x+f x^2)^p*)


Int[(a_+b_.*x_+c_.*x_^2)^m_.*(d_+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  (c/f)^m*Int[(d+e*x+f*x^2)^(m+p),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && ZeroQ[c*d-a*f] && ZeroQ[b*d-a*e] && (IntegerQ[m] || PositiveQ[c/f]) && 
  (Not[IntegerQ[p]] || LeafCount[d+e*x+f*x^2]<=LeafCount[a+b*x+c*x^2])


Int[(a_+b_.*x_+c_.*x_^2)^m_.*(d_+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  (a+b*x+c*x^2)^m/(d+e*x+f*x^2)^m*Int[(d+e*x+f*x^2)^(m+p),x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && ZeroQ[c*d-a*f] && ZeroQ[b*d-a*e] && Not[IntegerQ[m]] && Not[IntegerQ[p]] && Not[PositiveQ[c/f]]


Int[(a_+b_.*x_+c_.*x_^2)^m_.*(d_+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[Cancel[(b/2+c*x)^(2*m)/c^m]*(d+e*x+f*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,p},x] && ZeroQ[b^2-4*a*c] && IntegerQ[m]


Int[(a_+b_.*x_+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[Cancel[(b/2+c*x)^(2*m)/c^m]*(d+f*x^2)^p,x] /;
FreeQ[{a,b,c,d,f,p},x] && ZeroQ[b^2-4*a*c] && IntegerQ[m]


Int[(a_+b_.*x_+c_.*x_^2)^m_*(d_+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  (a+b*x+c*x^2)^m/(b+2*c*x)^(2*m)*Int[(b+2*c*x)^(2*m)*(d+e*x+f*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[m]]


Int[(a_+b_.*x_+c_.*x_^2)^m_*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  (a+b*x+c*x^2)^m/(b+2*c*x)^(2*m)*Int[(b+2*c*x)^(2*m)*(d+f*x^2)^p,x] /;
FreeQ[{a,b,c,d,f,m,p},x] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[m]]


Int[(a_+b_.*x_+c_.*x_^2)/(d_+e_.*x_+f_.*x_^2),x_Symbol] :=
  c*x/f + 1/f*Int[(a*f-c*d+(b*f-c*e)*x)/(d+e*x+f*x^2),x] /;
FreeQ[{a,b,c,d,e,f},x] && (NonzeroQ[c*d-a*f] || NonzeroQ[b*d-a*e])


Int[(a_+c_.*x_^2)/(d_+e_.*x_+f_.*x_^2),x_Symbol] :=
  c*x/f + 1/f*Int[(a*f-c*d-c*e*x)/(d+e*x+f*x^2),x] /;
FreeQ[{a,c,d,e,f},x]


Int[(a_+b_.*x_+c_.*x_^2)/(d_+f_.*x_^2),x_Symbol] :=
  c*x/f + 1/f*Int[(a*f-c*d+b*f*x)/(d+f*x^2),x] /;
FreeQ[{a,b,c,d,f},x]


Int[(a_+b_.*x_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  (b*f*(2*p+3)-c*e*(p+2)+2*c*f*(p+1)*x)*(d+e*x+f*x^2)^(p+1)/(2*f^2*(p+1)*(2*p+3)) /;
FreeQ[{a,b,c,d,e,f,p},x] && NonzeroQ[p+1] && NonzeroQ[2*p+3] && ZeroQ[f*(2*a*f-b*e)*(2*p+3)+c*(e^2*(p+2)-2*d*f)]


Int[(a_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  (-c*e*(p+2)+2*c*f*(p+1)*x)*(d+e*x+f*x^2)^(p+1)/(2*f^2*(p+1)*(2*p+3)) /;
FreeQ[{a,c,d,e,f,p},x] && NonzeroQ[p+1] && NonzeroQ[2*p+3] && ZeroQ[2*a*f^2*(2*p+3)+c*(e^2*(p+2)-2*d*f)]


Int[(a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)^p_,x_Symbol] :=
  (b*d+2*a*f*(p+1)*x)*(d+f*x^2)^(p+1)/(2*d*f*(p+1)) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[p+1] && ZeroQ[3*a*f-c*d+2*a*f*p]


Int[(a_+b_.*x_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)*(d+e*x+f*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[e^2-4*d*f] && PositiveIntegerQ[p] && NonzeroQ[f*(2*a*f-b*e)*(2*p+3)+c*(e^2*(p+2)-2*d*f)]


Int[(a_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^2)*(d+e*x+f*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f},x] && NonzeroQ[e^2-4*d*f] && PositiveIntegerQ[p] && NonzeroQ[2*a*f^2*(2*p+3)+c*(e^2*(p+2)-2*d*f)]


Int[(a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)*(d+f*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,f},x] && PositiveIntegerQ[p] && NonzeroQ[3*a*f-c*d+2*a*f*p]


Int[(a_+b_.*x_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  (a*e*f-2*b*d*f+c*d*e+(f*(2*a*f-b*e)+c*(e^2-2*d*f))*x)*(d+e*x+f*x^2)^(p+1)/(f*(p+1)*(e^2-4*d*f)) - 
  (f*(2*a*f-b*e)*(2*p+3)+c*(e^2*(p+2)-2*d*f))/(f*(p+1)*(e^2-4*d*f))*Int[(d+e*x+f*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[e^2-4*d*f] && RationalQ[p] && p<-1 && NonzeroQ[f*(2*a*f-b*e)*(2*p+3)+c*(e^2*(p+2)-2*d*f)]


Int[(a_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  (a*e*f+c*d*e+(2*a*f^2+c*(e^2-2*d*f))*x)*(d+e*x+f*x^2)^(p+1)/(f*(p+1)*(e^2-4*d*f)) - 
  (2*a*f^2*(2*p+3)+c*(e^2*(p+2)-2*d*f))/(f*(p+1)*(e^2-4*d*f))*Int[(d+e*x+f*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f},x] && NonzeroQ[e^2-4*d*f] && RationalQ[p] && p<-1 && NonzeroQ[2*a*f^2*(2*p+3)+c*(e^2*(p+2)-2*d*f)]


Int[(a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)^p_,x_Symbol] :=
  (b*d-(a*f-c*d)*x)*(d+f*x^2)^(p+1)/(2*d*f*(p+1)) + 
  (3*a*f-c*d+2*a*f*p)/(2*d*f*(p+1))*Int[(d+f*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,f},x] && RationalQ[p] && p<-1 && NonzeroQ[3*a*f-c*d+2*a*f*p]


Int[(a_+b_.*x_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  (b*f*(2*p+3)-c*e*(p+2)+2*c*f*(p+1)*x)*(d+e*x+f*x^2)^(p+1)/(2*f^2*(p+1)*(2*p+3)) + 
  (f*(2*a*f-b*e)*(2*p+3)+c*(e^2*(p+2)-2*d*f))/(2*f^2*(2*p+3))*Int[(d+e*x+f*x^2)^p,x] /;
FreeQ[{d,e,f,a,b,c,p},x] && NonzeroQ[e^2-4*d*f] && Not[PositiveIntegerQ[p]] && Not[RationalQ[p] && p<=-1] && 
  NonzeroQ[f*(2*a*f-b*e)*(2*p+3)+c*(e^2*(p+2)-2*d*f)]


Int[(a_+c_.*x_^2)*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  (-c*e*(p+2)+2*c*f*(p+1)*x)*(d+e*x+f*x^2)^(p+1)/(2*f^2*(p+1)*(2*p+3)) + 
  (2*a*f^2*(2*p+3)+c*(e^2*(p+2)-2*d*f))/(2*f^2*(2*p+3))*Int[(d+e*x+f*x^2)^p,x] /;
FreeQ[{d,e,f,a,c,p},x] && NonzeroQ[e^2-4*d*f] && Not[PositiveIntegerQ[p]] && Not[RationalQ[p] && p<=-1] && 
  NonzeroQ[2*a*f^2*(2*p+3)+c*(e^2*(p+2)-2*d*f)]


Int[(a_+b_.*x_+c_.*x_^2)*(d_+f_.*x_^2)^p_,x_Symbol] :=
  (b*f*(2*p+3)+2*c*f*(p+1)*x)*(d+f*x^2)^(p+1)/(2*f^2*(p+1)*(2*p+3)) + 
  (3*a*f-c*d+2*a*f*p)/(f*(2*p+3))*Int[(d+f*x^2)^p,x] /;
FreeQ[{d,f,a,b,c,p},x] && Not[PositiveIntegerQ[p]] && Not[RationalQ[p] && p<=-1] && NonzeroQ[3*a*f-c*d+2*a*f*p]


(* Int[(a_+b_.*x_+c_.*x_^2)^m_*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  1/(2^(2*m+2*p+1)*c*(-c/(b^2-4*a*c))^m*(-f/(e^2-4*d*f))^p)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^m*(1+e*x^2/(b*(4*c*d-b*e)))^p,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[e^2-4*d*f] && ZeroQ[c*e-b*f] && 
  (IntegerQ[m] || PositiveQ[-c/(b^2-4*a*c)]) && (IntegerQ[p] || PositiveQ[-f/(e^2-4*d*f)]) *)


(* Int[(a_+b_.*x_+c_.*x_^2)^m_*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  (d+e*x+f*x^2)^p/(2^(2*m+2*p+1)*c*(-c/(b^2-4*a*c))^m*(-f*(d+e*x+f*x^2)/(e^2-4*d*f))^p)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^m*(1+e*x^2/(b*(4*c*d-b*e)))^p,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[e^2-4*d*f] && ZeroQ[c*e-b*f] && 
  (IntegerQ[m] || PositiveQ[-c/(b^2-4*a*c)]) && Not[IntegerQ[p] || PositiveQ[-f/(e^2-4*d*f)]] *)


(* Int[(a_+b_.*x_+c_.*x_^2)^m_*(d_.+e_.*x_+f_.*x_^2)^p_,x_Symbol] :=
  (a+b*x+c*x^2)^m*(d+e*x+f*x^2)^p/(2^(2*m+2*p+1)*c*(-c*(a+b*x+c*x^2)/(b^2-4*a*c))^m*(-f*(d+e*x+f*x^2)/(e^2-4*d*f))^p)*
    Subst[Int[(1-x^2/(b^2-4*a*c))^m*(1+e*x^2/(b*(4*c*d-b*e)))^p,x],x,b+2*c*x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[e^2-4*d*f] && ZeroQ[c*e-b*f] *)


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  -2*e*Subst[Int[1/(e*(b*e-4*a*f)-(b*d-a*e)*x^2),x],x,(e+2*f*x)/Sqrt[d+e*x+f*x^2]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*e-b*f]


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[1/((b-q+2*c*x)*Sqrt[d+e*x+f*x^2]),x] -
  2*c/q*Int[1/((b+q+2*c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*e-b*f]


Int[1/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  1/2*Int[1/((a-Rt[-a*c,2]*x)*Sqrt[d+e*x+f*x^2]),x] +
  1/2*Int[1/((a+Rt[-a*c,2]*x)*Sqrt[d+e*x+f*x^2]),x] /;
FreeQ[{a,c,d,e,f},x]


Int[1/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
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


Int[(a_.+b_.*x_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && (IntegersQ[m,p] || PositiveIntegerQ[m])


Int[(a_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^2)^m*(d+e*x+f*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,p},x] && (IntegersQ[m,p] || PositiveIntegerQ[m] || PositiveIntegerQ[p])


Int[(a_.+b_.*x_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  f/c*Int[(a+b*x+c*x^2)^(m+1)*(d+e*x+f*x^2)^(p-1),x] + 
  1/c*Int[Simp[c*d-a*f+(c*e-b*f)*x,x]*(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[m,p] && m<=-1 && p>0


Int[(a_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  f/c*Int[(a+c*x^2)^(m+1)*(d+e*x+f*x^2)^(p-1),x] + 
  1/c*Int[Simp[c*d-a*f+c*e*x,x]*(a+c*x^2)^m*(d+e*x+f*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,f},x] && RationalQ[m,p] && m<=-1 && p>0


Int[(a_.+b_.*x_+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  f/c*Int[(a+b*x+c*x^2)^(m+1)*(d+f*x^2)^(p-1),x] + 
  1/c*Int[Simp[c*d-a*f-b*f*x,x]*(a+b*x+c*x^2)^m*(d+f*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,f},x] && RationalQ[m,p] && m<=-1 && p>0


Int[(a_.+b_.*x_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  -1/(c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2)*
    Int[Simp[f*(b*e-a*f)-c*(e^2-d*f)-f*(c*e-b*f)*x,x]*(a+b*x+c*x^2)^(m+1)*(d+e*x+f*x^2)^p,x] + 
  1/(c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2)*
    Int[Simp[(b^2*f+c*(c*d-b*e-a*f))-c*(c*e-b*f)*x,x]*(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[m,p] && m<=-1 && p<=-1 && NonzeroQ[c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2]


Int[(a_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  -1/(c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2)*
    Int[Simp[-a*f^2-c*(e^2-d*f)-c*e*f*x,x]*(a+c*x^2)^(m+1)*(d+e*x+f*x^2)^p,x] + 
  1/((c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2))*
    Int[Simp[(c*(c*d-a*f))-c^2*e*x,x]*(a+c*x^2)^m*(d+e*x+f*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f},x] && RationalQ[m,p] && m<=-1 && p<=-1 && NonzeroQ[c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2]


Int[(a_.+b_.*x_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Defer[Int][(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x]


Int[(a_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Defer[Int][(a+c*x^2)^m*(d+e*x+f*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,m,p},x]


Int[(a_.+b_.*u_+c_.*v_^2)^m_.*(d_.+e_.*w_+f_.*z_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+c_.*u_^2)^m_.*(d_.+e_.*v_+f_.*w_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+c*x^2)^m*(d+e*x+f*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,e,f,m,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && QuadraticQ[{u,v},x] && Not[QuadraticMatchQ[{u,v},x]]


(* ::Subsection::Closed:: *)
(*3.1.5 (A+B x) (a+b x+c x^2)^m (d+e x+f x^2)^p*)


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


Int[(A_+B_.*x_)/((d_.+e_.*x_+f_.*x_^2)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  2*A*(2*B*d-A*e)*Subst[Int[1/Simp[A*(2*B*d-A*e)*(e^2-4*d*f)-(b*d-a*e)*x^2,x],x],x,Simp[2*B*d-A*e+(B*e-2*A*f)*x,x]/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[e^2-4*d*f] && NonzeroQ[b*d-a*e] && ZeroQ[A^2*(c*e-b*f)+B^2*(b*d-a*e)-2*A*B*(c*d-a*f)]


Int[(A_+B_.*x_)/((d_+f_.*x_^2)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  -2*A*B*Subst[Int[1/(2*A*B*d*f+b*x^2),x],x,(B*d-A*f*x)/Sqrt[a+b*x+c*x^2]] /;
FreeQ[{a,b,c,d,f,A,B},x] && ZeroQ[A^2*b*f-b*B^2*d+2*A*B*(c*d-a*f)]


Int[(A_+B_.*x_)/((d_.+e_.*x_+f_.*x_^2)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  2*A*(2*B*d-A*e)*Subst[Int[1/Simp[A*(2*B*d-A*e)*(e^2-4*d*f)+a*e*x^2,x],x],x,Simp[2*B*d-A*e+(B*e-2*A*f)*x,x]/Sqrt[a+c*x^2]] /;
FreeQ[{a,c,d,e,f,A,B},x] && NonzeroQ[e^2-4*d*f] && ZeroQ[A^2*c*e-B^2*a*e-2*A*B*(c*d-a*f)]


Int[(A_+B_.*x_)/((d_.+e_.*x_+f_.*x_^2)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  Module[{R,S,lst=Solve[{R^2*(c*e-b*f)+S^2*(b*d-a*e)-2*R*S*(c*d-a*f)==0, 
    (A-R)^2*(c*e-b*f)+(B-S)^2*(b*d-a*e)-2*(A-R)*(B-S)*(c*d-a*f)==0},{R,S}]},
  Int[Simp[lst[[1,1,2]]+lst[[1,2,2]]*x,x]/((d+e*x+f*x^2)*Sqrt[a+b*x+c*x^2]),x] + 
  Int[Simp[A-lst[[1,1,2]]+(B-lst[[1,2,2]])*x,x]/((d+e*x+f*x^2)*Sqrt[a+b*x+c*x^2]),x] /;
 Length[lst]==2] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[e^2-4*d*f] && NonzeroQ[b*d-a*e] && NonzeroQ[A^2*(c*e-b*f)+B^2*(b*d-a*e)-2*A*B*(c*d-a*f)] && 
  RationalQ[a,b,c] && NegQ[e^2-4*d*f]


Int[(A_+B_.*x_)/((d_+f_.*x_^2)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
  Module[{R,S,lst=Solve[{R^2*b*f-S^2*b*d+2*R*S*(c*d-a*f)==0, (A-R)^2*b*f-(B-S)^2*b*d+2*(A-R)*(B-S)*(c*d-a*f)==0},{R,S}]},
  Int[Simp[lst[[1,1,2]]+lst[[1,2,2]]*x,x]/((d+f*x^2)*Sqrt[a+b*x+c*x^2]),x] + 
  Int[Simp[A-lst[[1,1,2]]+(B-lst[[1,2,2]])*x,x]/((d+f*x^2)*Sqrt[a+b*x+c*x^2]),x] /;
 Length[lst]==2] /;
FreeQ[{a,b,c,d,f,A,B},x] && NonzeroQ[A^2*b*f-b*B^2*d+2*A*B*(c*d-a*f)] && RationalQ[a,b,c] && PosQ[d*f]


Int[(A_+B_.*x_)/((d_.+e_.*x_+f_.*x_^2)*Sqrt[a_+c_.*x_^2]),x_Symbol] :=
  Module[{R,S,lst=Solve[{R^2*c*e-S^2*a*e-2*R*S*(c*d-a*f)==0, (A-R)^2*c*e-(B-S)^2*a*e-2*(A-R)*(B-S)*(c*d-a*f)==0},{R,S}]},
  Int[Simp[lst[[1,1,2]]+lst[[1,2,2]]*x,x]/((d+e*x+f*x^2)*Sqrt[a+c*x^2]),x] + 
  Int[Simp[A-lst[[1,1,2]]+(B-lst[[1,2,2]])*x,x]/((d+e*x+f*x^2)*Sqrt[a+c*x^2]),x] /;
 Length[lst]==2] /;
FreeQ[{a,c,d,e,f,A,B},x] && NonzeroQ[e^2-4*d*f] && NonzeroQ[A^2*c*e-B^2*a*e-2*A*B*(c*d-a*f)] && RationalQ[a,c] && NegQ[e^2-4*d*f]


Int[(A_.+B_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (2*c*A-B*(b-q))/q*Int[1/((b-q+2*c*x)*Sqrt[d+e*x+f*x^2]),x] -
  (2*c*A-B*(b+q))/q*Int[1/((b+q+2*c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[2*c*A-b*B] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*A^2-b*A*B+a*B^2]


Int[(A_.+B_.*x_)/((a_+c_.*x_^2)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
  (B/2+c*A/(2*q))*Int[1/((-q+c*x)*Sqrt[d+e*x+f*x^2]),x] +
  (B/2-c*A/(2*q))*Int[1/((q+c*x)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,c,d,e,f,A,B},x] && NonzeroQ[c*A^2+a*B^2]


Int[(A_.+B_.*x_)/((a_+b_.*x_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (2*c*A-B*(b-q))/q*Int[1/((b-q+2*c*x)*Sqrt[d+f*x^2]),x] -
  (2*c*A-B*(b+q))/q*Int[1/((b+q+2*c*x)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,c,d,f,A,B},x] && NonzeroQ[2*c*A-b*B] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*A^2-b*A*B+a*B^2]


Int[(A_+B_.*x_)/((a_+c_.*x_^2)*Sqrt[d_+f_.*x_^2]),x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
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


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  r/(3*a)*Int[1/((r+s*x)*Sqrt[d+e*x+f*x^2]),x] +
  r/(3*a)*Int[(2*r-s*x)/((r^2-r*s*x+s^2*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,d,e,f},x] && PosQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  r/(3*a)*Int[1/((r+s*x)*Sqrt[d+f*x^2]),x] +
  r/(3*a)*Int[(2*r-s*x)/((r^2-r*s*x+s^2*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,d,f},x] && PosQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+e_.*x_+f_.*x_^2]),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r/(3*a)*Int[1/((r-s*x)*Sqrt[d+e*x+f*x^2]),x] +
  r/(3*a)*Int[(2*r+s*x)/((r^2+r*s*x+s^2*x^2)*Sqrt[d+e*x+f*x^2]),x]] /;
FreeQ[{a,b,d,e,f},x] && NegQ[a/b]


Int[1/((a_+b_.*x_^3)*Sqrt[d_.+f_.*x_^2]),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r/(3*a)*Int[1/((r-s*x)*Sqrt[d+f*x^2]),x] +
  r/(3*a)*Int[(2*r+s*x)/((r^2+r*s*x+s^2*x^2)*Sqrt[d+f*x^2]),x]] /;
FreeQ[{a,b,d,f},x] && NegQ[a/b]


Int[x_^m_.*(a_.+b_.*x_+c_.*x_^2)^m_.*(e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[(a/e+c/f*x)^m*(e*x+f*x^2)^(m+p),x] /;
FreeQ[{a,b,c,e,f,p},x] && ZeroQ[c*e^2-b*e*f+a*f^2] && IntegerQ[m]


Int[x_^m_.*(a_.+c_.*x_^2)^m_.*(e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[(a/e+c/f*x)^m*(e*x+f*x^2)^(m+p),x] /;
FreeQ[{a,c,e,f,p},x] && ZeroQ[c*e^2+a*f^2] && IntegerQ[m]


Int[(A_.+B_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[(a*A/d+B*c/f*x)^m*(d+e*x+f*x^2)^(m+p),x] /;
FreeQ[{a,b,c,d,e,f,A,B,p},x] && ZeroQ[B^2*d-A*B*e+A^2*f] && ZeroQ[B^2*c*d^2-A*b*B*d*f+a*A^2*f^2] && IntegerQ[m]


Int[(A_.+B_.*x_)^m_.*(a_.+c_.*x_^2)^m_.*(d_+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[(a*A/d+B*c/f*x)^m*(d+e*x+f*x^2)^(m+p),x] /;
FreeQ[{a,c,d,e,f,A,B,p},x] && ZeroQ[B^2*d-A*B*e+A^2*f] && ZeroQ[B^2*c*d^2+a*A^2*f^2] && IntegerQ[m]


Int[(A_.+B_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[(a*A/d+B*c/f*x)^m*(d+f*x^2)^(m+p),x] /;
FreeQ[{a,b,c,d,f,A,B,p},x] && ZeroQ[B^2*d+A^2*f] && ZeroQ[B^2*c*d^2-A*b*B*d*f+a*A^2*f^2] && IntegerQ[m]


Int[(A_.+B_.*x_)^m_.*(a_.+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[(a*A/d+B*c/f*x)^m*(d+f*x^2)^(m+p),x] /;
FreeQ[{a,c,d,f,A,B,p},x] && ZeroQ[B^2*d+A^2*f] && ZeroQ[B^2*c*d^2+a*A^2*f^2] && IntegerQ[m]


Int[(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(A+B*x)*(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,p},x] && (IntegersQ[m,p] || PositiveIntegerQ[m])


Int[(A_.+B_.*x_)*(a_.+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(A+B*x)*(a+c*x^2)^m*(d+e*x+f*x^2)^p,x],x] /;
FreeQ[{a,c,d,e,f,A,B,p},x] && (IntegersQ[m,p] || PositiveIntegerQ[m] || PositiveIntegerQ[p])


Int[(A_+B_.*x_)*(a_.+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(A+B*x)*(a+c*x^2)^m*(d+f*x^2)^p,x],x] /;
FreeQ[{a,c,d,f,A,B,p},x] && (IntegersQ[m,p] || PositiveIntegerQ[m])


Int[(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  1/c^2*Int[Simp[A*c*f+B*(c*e-b*f)+B*c*f*x,x]*(a+b*x+c*x^2)^(m+1)*(d+e*x+f*x^2)^(p-1),x] + 
  1/c^2*Int[Simp[A*c*(c*d-a*f)-a*B*(c*e-b*f)+(A*c*(c*e-b*f)+B*(c*(c*d-a*f)-b*(c*e-b*f)))*x,x]*
      (a+b*x+c*x^2)^m*(d+e*x+f*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && RationalQ[m,p] && m<=-1 && p>0


Int[(A_.+B_.*x_)*(a_.+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  1/c*Int[Simp[A*f+B*e+B*f*x,x]*(a+c*x^2)^(m+1)*(d+e*x+f*x^2)^(p-1),x] + 
  1/c*Int[Simp[A*(c*d-a*f)-a*B*e+(A*c*e+B*(c*d-a*f))*x,x]*(a+c*x^2)^m*(d+e*x+f*x^2)^(p-1),x] /;
FreeQ[{a,c,d,e,f,A,B},x] && RationalQ[m,p] && m<=-1 && p>0


Int[(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  1/c^2*Int[Simp[A*c*f-b*B*f+B*c*f*x,x]*(a+b*x+c*x^2)^(m+1)*(d+f*x^2)^(p-1),x] + 
  1/c^2*Int[Simp[A*c*(c*d-a*f)+a*b*B*f+(-A*b*c*f+B*(c*(c*d-a*f)+b^2*f))*x,x]*
      (a+b*x+c*x^2)^m*(d+f*x^2)^(p-1),x] /;
FreeQ[{a,b,c,d,f,A,B},x] && RationalQ[m,p] && m<=-1 && p>0


Int[(A_+B_.*x_)*(a_.+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  1/c*Int[Simp[A*f+B*f*x,x]*(a+c*x^2)^(m+1)*(d+f*x^2)^(p-1),x] + 
  1/c*Int[Simp[A*(c*d-a*f)+B*(c*d-a*f)*x,x]*(a+c*x^2)^m*(d+f*x^2)^(p-1),x] /;
FreeQ[{a,c,d,f,A,B},x] && RationalQ[m,p] && m<=-1 && p>0


Int[(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  -1/(c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2)*
    Int[Simp[B*d*(c*e-b*f)+A*(f*(b*e-a*f)-c*(e^2-d*f))+f*(B*(c*d-a*f)-A*(c*e-b*f))*x,x]*(a+b*x+c*x^2)^(m+1)*(d+e*x+f*x^2)^p,x] + 
  1/(c*(c*d^2-e*(b*d-a*e))-(2*a*c*d-b*(b*d-a*e))*f+a^2*f^2)*
    Int[Simp[a*B*(c*e-b*f)+A*(b^2*f+c*(c*d-b*e-a*f))+c*(B*(c*d-a*f)-A*(c*e-b*f))*x,x]*(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && RationalQ[m,p] && m<=-1 && p<=-1


Int[(A_.+B_.*x_)*(a_.+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  -1/(c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2)*
    Int[Simp[B*c*d*e+A*(-a*f^2-c*(e^2-d*f))+f*(B*(c*d-a*f)-A*c*e)*x,x]*(a+c*x^2)^(m+1)*(d+e*x+f*x^2)^p,x] + 
  1/(c*(c*d^2+a*e^2)-2*a*c*d*f+a^2*f^2)*
    Int[Simp[a*B*c*e+A*c*(c*d-a*f)+c*(B*(c*d-a*f)-A*c*e)*x,x]*(a+c*x^2)^m*(d+e*x+f*x^2)^(p+1),x] /;
FreeQ[{a,c,d,e,f,A,B},x] && RationalQ[m,p] && m<=-1 && p<=-1


Int[(A_.+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  -1/(c^2*d^2-(2*a*c*d-b^2*d)*f+a^2*f^2)*
    Int[Simp[-B*b*d*f+A*(-a*f^2+c*d*f)+f*(B*(c*d-a*f)+A*b*f)*x,x]*(a+b*x+c*x^2)^(m+1)*(d+f*x^2)^p,x] + 
  1/(c^2*d^2-(2*a*c*d-b^2*d)*f+a^2*f^2)*
    Int[Simp[-a*b*B*f+A*(b^2*f+c*(c*d-a*f))+c*(B*(c*d-a*f)+A*b*f)*x,x]*(a+b*x+c*x^2)^m*(d+f*x^2)^(p+1),x] /;
FreeQ[{a,b,c,d,f,A,B},x] && RationalQ[m,p] && m<=-1 && p<=-1


Int[(A_+B_.*x_)*(a_.+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  -1/(c^2*d^2-2*a*c*d*f+a^2*f^2)*
    Int[Simp[A*(-a*f^2+c*d*f)+f*B*(c*d-a*f)*x,x]*(a+c*x^2)^(m+1)*(d+f*x^2)^p,x] + 
  1/(c^2*d^2-2*a*c*d*f+a^2*f^2)*
    Int[Simp[A*c*(c*d-a*f)+c*B*(c*d-a*f)*x,x]*(a+c*x^2)^m*(d+f*x^2)^(p+1),x] /;
FreeQ[{a,c,d,f,A,B},x] && RationalQ[m,p] && m<=-1 && p<=-1


Int[(A_+B_.*x_)*(a_.+b_.*x_+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  A*Int[(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^p,x] + 
  B*Int[x*(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^p,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,p},x]


Int[(A_+B_.*x_)*(a_.+c_.*x_^2)^m_.*(d_.+e_.*x_+f_.*x_^2)^p_.,x_Symbol] :=
  A*Int[(a+c*x^2)^m*(d+e*x+f*x^2)^p,x] + 
  B*Int[x*(a+c*x^2)^m*(d+e*x+f*x^2)^p,x] /;
FreeQ[{a,c,d,e,f,A,B,m,p},x]


Int[(A_+B_.*x_)*(a_.+c_.*x_^2)^m_.*(d_+f_.*x_^2)^p_.,x_Symbol] :=
  A*Int[(a+c*x^2)^m*(d+f*x^2)^p,x] + 
  B*Int[x*(a+c*x^2)^m*(d+f*x^2)^p,x] /;
FreeQ[{a,c,d,f,A,B,m,p},x]


Int[(A_+B_.*y_)*(a_.+b_.*u_+c_.*v_^2)^m_.*(d_.+e_.*w_+f_.*z_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(A+B*x)*(a+b*x+c*x^2)^m*(d+e*x+f*x^2)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,f,A,B,m,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && ZeroQ[u-y] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(A_+B_.*u_)*(a_.+c_.*v_^2)^m_.*(d_.+e_.*w_+f_.*z_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(A+B*x)*(a+c*x^2)^m*(d+e*x+f*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,e,f,A,B,m,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(A_+B_.*u_)*(a_.+c_.*v_^2)^m_.*(d_.+f_.*w_^2)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(A+B*x)*(a+c*x^2)^m*(d+f*x^2)^p,x],x,u] /;
FreeQ[{a,c,d,f,A,B,m,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[z_*u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[z,x]*ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && LinearQ[z,x] && QuadraticQ[{u,v},x] && Not[LinearMatchQ[z,x] && QuadraticMatchQ[{u,v},x]]


(* ::Subsection::Closed:: *)
(*3.2.1 (a+b x^n+c x^(2 n))^p*)


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  1/c^p*Int[(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[n*(2*p+1)+1]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a*(2*p+1)) + 
  x*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*(n+1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && 
  ZeroQ[2*n*(p+1)+1] && NonzeroQ[2*p+1]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Sqrt[a+b*x^n+c*x^(2*n)]/(b+2*c*x^n)*Int[(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p-1/2),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && (ZeroQ[2*n*p+1] || ZeroQ[n*(2*p-1)+1]) && 
  RationalQ[p] && p>0 && IntegerQ[p+1/2]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^p/(b+2*c*x^n)^(2*p)*Int[(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && (ZeroQ[2*n*p+1] || ZeroQ[n*(2*p-1)+1]) && 
  RationalQ[p] && p>0 && Not[IntegerQ[2*p]]


Int[Sqrt[a_+b_.*x_^n_+c_.*x_^j_],x_Symbol] :=
  x*Sqrt[a+b*x^n+c*x^(2*n)]/(n+1) + 
  b*n*x*Sqrt[a+b*x^n+c*x^(2*n)]/((n+1)*(b+2*c*x^n)) /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && NonzeroQ[n+1] && NonzeroQ[2*n+1] && NonzeroQ[3*n+1]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Sign[n]/Denominator[n]},
  1/g*Subst[Int[x^(1/g-1)*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g]] /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && 
  RationalQ[n] && Not[PositiveIntegerQ[n]]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x*(a+b*x^n+c*x^(2*n))^p/(2*n*p+1) + 
  n*p*x*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/((2*n*p+1)*(n*(2*p-1)+1)) + 
  2*a*n^2*p*(2*p-1)/((2*n*p+1)*(n*(2*p-1)+1))*Int[(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && 
  NonzeroQ[2*n*p+1] && NonzeroQ[n*(2*p-1)+1] && RationalQ[p] && p>1


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  -(n*(2*p+1)+1)*x*(a+b*x^n+c*x^(2*n))^(p+1)/(2*a*n^2*(p+1)*(2*p+1)) - 
  x*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*n*(2*p+1)) + 
  (n*(2*p+1)+1)*(2*n*(p+1)+1)/(2*a*n^2*(p+1)*(2*p+1))*Int[(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && 
  NonzeroQ[n*(2*p+1)+1] && NonzeroQ[2*n*(p+1)+1] && RationalQ[p] && p<-1


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^p/(b/2+c*x^n)^(2*p)*Int[(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p]


Int[1/(a_+b_.*x_^2+c_.*x_^4),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[1/(b/2-q/2+c*x^2),x] -
  c/q*Int[1/(b/2+q/2+c*x^2),x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && Not[NegativeQ[b^2-4*a*c]]


Int[1/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  Module[{q=Rt[a/c,2]},
  c*q/(2*a)*Int[(q+x^2)/(a+b*x^2+c*x^4),x] +
  c*q/(2*a)*Int[(q-x^2)/(a+b*x^2+c*x^4),x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && Not[PositiveQ[b^2-4*a*c]] && 
  (NegativeQ[b^2-4*a*c] || RationalQ[a/c]) && PosQ[a/c]


Int[1/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  Module[{q=Rt[-a/c,2]},
  -c*q/(2*a)*Int[(q+x^2)/(a+b*x^2+c*x^4),x] -
  c*q/(2*a)*Int[(q-x^2)/(a+b*x^2+c*x^4),x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && Not[PositiveQ[b^2-4*a*c]] && 
(NegativeQ[b^2-4*a*c] || RationalQ[a/c]) && NegQ[a/c]


Int[1/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[2*c*Rt[a*c,2]-b*c,2]},
  Rt[a*c,2]/(2*a*q)*Int[(q-c*x^(n/2))/(Rt[a*c,2]-q*x^(n/2)+c*x^n),x] + 
  Rt[a*c,2]/(2*a*q)*Int[(q+c*x^(n/2))/(Rt[a*c,2]+q*x^(n/2)+c*x^n),x]] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && n>2 && 
  NegativeQ[b^2-4*a*c] && IntegerQ[n/2] && PosQ[a*c]


Int[1/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[1/(b/2-q/2+c*x^n),x] -
  c/q*Int[1/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && n>2 && 
  Not[NegativeQ[b^2-4*a*c] && IntegerQ[n/2] && PosQ[a*c]]


Int[1/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  x/a - 1/a*Int[(c+b*x^(-n))/(c+b*x^(-n)+a*x^(-2*n)),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  1/Sqrt[a]*Int[1/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PositiveQ[a] && NegativeQ[c] && (PositiveQ[b] || NegativeQ[b])


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[1/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Sign[n]/Denominator[n]},
  1/g*Subst[Int[x^(1/g-1)*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g]] /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[p+1] && RationalQ[n] && Not[PositiveIntegerQ[n]]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x*(a+b*x^n+c*x^(2*n))^p/(2*n*p+1) + 
  n*p/(2*n*p+1)*Int[(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p>0 && Not[IntegerQ[p]] && 
  NonzeroQ[2*n*p+1]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  -x*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^j)^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) +
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[(b^2-2*a*c+n*(p+1)*(b^2-4*a*c)+b*c*(n*(2*p+3)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p<-1


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x*(a+b*x^n+c*x^(2*n))^p/((1+2*c*x^n/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^n/(b-Sqrt[b^2-4*a*c]))^p)*
    AppellF1[1/n,-p,-p,1+1/n,-2*c*x^n/(b+Sqrt[b^2-4*a*c]),-2*c*x^n/(b-Sqrt[b^2-4*a*c])] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j-2*n]


Int[(a_+b_.*u_^n_+c_.*v_^j_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j-2*n] && ZeroQ[u-v] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(a_.+b_.*(d_./x_)^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  -d*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^2,x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[j+2*n] && IntegerQ[2*n]


Int[(a_.+b_.*(d_./x_)^n_+c_.*(d_./x_)^j_.)^p_.,x_Symbol] :=
  -d*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^2,x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[j-2*n]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*3.2.2 x^m (a+b x^n+c x^(2 n))^p*)


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  1/c^p*Int[x^m*(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*c*n*(2*p+1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[m-n+1] && NonzeroQ[2*p+1]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(b*(m+1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[m+n*(2*p+1)+1] && NonzeroQ[m+1]


Int[Sqrt[a_+b_.*x_^n_+c_.*x_^j_.]/x_,x_Symbol] :=
  Sqrt[a+b*x^n+c*x^(2*n)]/n + 
  b*Sqrt[a+b*x^n+c*x^(2*n)]*Log[x]/(b+2*c*x^n) /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c]


Int[x_^m_.*Sqrt[a_+b_.*x_^n_+c_.*x_^j_.],x_Symbol] :=
  Sqrt[a+b*x^n+c*x^(2*n)]/(b+2*c*x^n)*Int[b*x^m+2*c*x^(m+n),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && NonzeroQ[m+1] && ZeroQ[m+n+1]


Int[x_^m_.*Sqrt[a_+b_.*x_^n_+c_.*x_^j_.],x_Symbol] :=
  x^(m+1)*Sqrt[a+b*x^n+c*x^(2*n)]/(m+n+1) + 
  b*n*x^(m+1)*Sqrt[a+b*x^n+c*x^(2*n)]/((m+1)*(m+n+1)*(b+2*c*x^n)) /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && NonzeroQ[m-n+1] && NonzeroQ[m+1] && NonzeroQ[m+n+1]


Int[x_^m_./Sqrt[a_+b_.*x_^n_+c_.*x_^j_.],x_Symbol] :=
  -x^(m+1)*Sqrt[a+b*x^n+c*x^(2*n)]/(a*n) - 
  b/(2*a)*Int[1/(x*Sqrt[a+b*x^n+c*x^(2*n)]),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && ZeroQ[m+n+1]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(2*a*n*(p+1)*(2*p+1)) - 
  x^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*n*(2*p+1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[m+2*n(p+1)+1] && NonzeroQ[2*p+1]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^(p+1)/(2*c*n*(p+1)) - 
  b/(2*c)*Int[x^(n-1)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[m-2*n+1] && NonzeroQ[p+3/2]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n+c*x^(2*n))^p/(m+2*n*p+1) + 
  n*p*x^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/((m+1)*(m+2*n*p+1)) - 
  b*p*n^2*(2*p-1)/((m+1)*(m+2*n*p+1))*Int[x^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && RationalQ[m,n,p] && Not[IntegerQ[p]] && 
  NonzeroQ[m+2*n*p+1] && -2<=m<-1 && n>0 && p>1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (m-n*(2*p-1)+1)*x^(m+1)*(a+b*x^n+c*x^(2*n))^p/((m+1)*(m+n+1)) + 
  n*p*x^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/((m+1)*(m+n+1)) + 
  2*c*p*n^2*(2*p-1)/((m+1)*(m+n+1))*Int[x^(m+2*n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && RationalQ[m,n,p] && Not[IntegerQ[p]] && 
  NonzeroQ[m+n+1] && m<-2 && n>0 && p>1 && Not[NegativeIntegerQ[(m+2*n(p+1)+1)/n] && (m+2*n(p+1)+1)/n+p>0]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n+c*x^(2*n))^p/(m+2*n*p+1) + 
  n*p*x^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/((m+2*n*p+1)*(m+n*(2*p-1)+1)) + 
  2*a*n^2*p*(2*p-1)/((m+2*n*p+1)*(m+n*(2*p-1)+1))*Int[x^m*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && 
  NonzeroQ[m+2*n*p+1] && NonzeroQ[m+n*(2*p-1)+1] && RationalQ[p] && p>1 && 
  Not[NegativeIntegerQ[(m+2*n(p+1)+1)/n] && (m+2*n(p+1)+1)/n+p>0] && 
  Not[IntegersQ[m,n] && m>0 && n>0 && Divisible[m+1,n] && (Not[IntegerQ[2*p]] || (m+1)/n-1<2*p)]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (m+n*(2*p+1)+1)*x^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(b*n^2*(p+1)*(2*p+1)) - 
  x^(m+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(b*n*(2*p+1)) - 
  (m-n+1)*(m+n*(2*p+1)+1)/(b*n^2*(p+1)*(2*p+1))*Int[x^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && RationalQ[m,n,p] && Not[IntegerQ[p]] && 
  NonzeroQ[m+n*(2*p+1)+1] && 0<n<m+1<=2*n && p<-1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  -(m-3*n-2*n*p+1)*x^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(2*c*n^2*(p+1)*(2*p+1)) - 
  x^(m-2*n+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*c*n*(2*p+1)) + 
  (m-n+1)*(m-2*n+1)/(2*c*n^2*(p+1)*(2*p+1))*Int[x^(m-2*n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && RationalQ[m,n,p] && Not[IntegerQ[p]] && 
  NonzeroQ[m-n+1] && NonzeroQ[m-2*n+1] && 0<2*n<m+1 && p<-1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  -(m+n*(2*p+1)+1)*x^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(2*a*n^2*(p+1)*(2*p+1)) - 
  x^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*n*(2*p+1)) + 
  (m+n*(2*p+1)+1)*(m+2*n*(p+1)+1)/(2*a*n^2*(p+1)*(2*p+1))*Int[x^m*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && 
  NonzeroQ[m+n*(2*p+1)+1] && NonzeroQ[m+2*n*(p+1)+1] && RationalQ[p] && p<-1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m-n+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*c*(m+2*n*p+1)) - 
  b*(m-n+1)/(2*c*(m+2*n*p+1))*Int[x^(m-n)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && RationalQ[m,n] && Not[IntegerQ[p]] && 
  NonzeroQ[m-n+1] && NonzeroQ[m+2*n*p+1] && 0<n<m+1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(b*(m+1)) - 
  2*c*(m+n*(2*p+1)+1)/(b*(m+1))*Int[x^(m+n)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && RationalQ[m,n] && Not[IntegerQ[p]] && 
  NonzeroQ[m+n*(2*p+1)+1] && m<-1 && n>0


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^p/(b/2+c*x^n)^(2*p)*Int[x^m*(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[m-n+1]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Int[x^(m+2*n*p)*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,m},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p] && RationalQ[n] && n<0


Int[1/(x_*(a_+b_.*x_^n_+c_.*x_^j_.)),x_Symbol] :=
  Log[x]/a - 1/a*Int[x^(n-1)*(b+c*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c]


Int[x_^2/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  Module[{q=Rt[a/c,2]},
  1/2*Int[(q+x^2)/(a+b*x^2+c*x^4),x] -
  1/2*Int[(q-x^2)/(a+b*x^2+c*x^4),x]] /;
FreeQ[{a,b,c},x] && NegativeQ[b^2-4*a*c] && PosQ[a*c]


Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q-b*c,2]},
  c/(2*r)*Int[x^(m-n/2)/(q-r*x^(n/2)+c*x^n),x] - 
  c/(2*r)*Int[x^(m-n/2)/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NegativeQ[b^2-4*a*c] && PositiveIntegerQ[n/2] && IntegerQ[m] && 
  CoprimeQ[m+1,n] && 1<n/2<=m<2*n && PosQ[a*c]


Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[x^m/(b-q+2*c*x^n),x] -
  2*c/q*Int[x^m/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m] && 
  CoprimeQ[m+1,n] && 0<m<n && Not[IntegerQ[n/2] && NegativeQ[b^2-4*a*c] && PosQ[a*c]]


Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (b/(2*q)+1/2)*Int[x^(m-n)/(b/2+q/2+c*x^n),x] -
  (b/(2*q)-1/2)*Int[x^(m-n)/(b/2-q/2+c*x^n),x]] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m] && 
  CoprimeQ[m+1,n] && n<=m<2*n && Not[IntegerQ[n/2] && NegativeQ[b^2-4*a*c] && PosQ[a*c]]


Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Module[{g=Gcd[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)/(a+b*x^(n/g)+c*x^(2*n/g)),x],x,x^g] /;
 g!=1] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[m,n] && 0<m+1<2*n


Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Int[PolynomialDivide[x^m,(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && IntegersQ[m,n] && 0<3*n<m+1


Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  x^(m-2*n+1)/(c*(m-2*n+1)) -
  1/c*Int[x^(m-2*n)*(a+b*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[m,n] && 0<2*n<m+1


Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  x^(m+1)/(a*(m+1)) -
  1/a*Int[x^(m+n)*(b+c*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[m,n] && n>0 && m+1<0


Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)/(a+b*x+c*x^2),x],x,x^n] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[x^m/(b-q+2*c*x^n),x] -
  2*c/q*Int[x^m/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c]


Int[(a_+b_.*x_^n_+c_.*x_^j_.)^p_/x_,x_Symbol] :=
  1/n*Subst[Int[(a+b*x+c*x^2)^p/x,x],x,x^n] /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4], x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  -(b-q)/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + 
  1/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Gcd[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g]] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[m,n,p] && Not[PositiveIntegerQ[p]] && m!=-1 && 
  (Not[PositiveIntegerQ[n]] || 0<m+1<2*n && -1<=p<0 && Not[IntegerQ[m] && CoprimeQ[m+1,n]])


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Simplify[(m+1)/n]},
  1/n*Subst[Int[x^(g-1)*(a+b*x+c*x^2)^p,x],x,x^n] /;
 IntegerQ[g] && (g>0 || Not[PositiveIntegerQ[n]])] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && NonzeroQ[m+1] && NonzeroQ[n-1]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Simplify[n/(m+1)]},
  1/(m+1)*Subst[Int[(a+b*x^g+c*x^(2*g))^p,x],x,x^(m+1)] /;
 IntegerQ[g] && (g>0 || Not[PositiveIntegerQ[n]])] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && -1<=p<0 && NonzeroQ[m+1]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m-n+1)*(b*n*p+c*(m+n*(2*p-1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/(c*(m+2*n*p+1)*(m+n*(2*p-1)+1)) + 
  (n*p)/(c*(m+2*n*p+1)*(m+n*(2*p-1)+1))*
    Int[x^(m-n)*
      Simp[-a*b*(m-n+1)+(2*a*c*(m+n*(2*p-1)+1)-b^2*(m+n*(p-1)+1))*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && 
  NonzeroQ[m+1] && NonzeroQ[p+1] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p>0 && m-n>=0 && m+2*n*p+1!=0 && m+n*(2*p-1)+1!=0


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n+c*x^(2*n))^p/(m+1) - 
  n*p/(m+1)*Int[x^(m+n)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && 
  NonzeroQ[m+1] && NonzeroQ[p+1] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p>0 && m+n<=0


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n+c*x^(2*n))^p/(m+2*n*p+1) + 
  n*p/(m+2*n*p+1)*Int[x^m*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && 
  NonzeroQ[m+1] && NonzeroQ[p+1] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p>0 && m+n>0 && m+2*n*p+1!=0


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  -x^(m-2*n+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) + 
  1/(n*(p+1)*(b^2-4*a*c))*
    Int[x^(m-2*n)*(2*a*(m-2*n+1)+b*(m+n*(2*p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && 
  NonzeroQ[m+1] && NonzeroQ[p+1] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m>2*n-1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m-n+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) - 
  1/(n*(p+1)*(b^2-4*a*c))*
    Int[x^(m-n)*(b*(m-n+1)+2*c*(m+2*n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && 
  NonzeroQ[m+1] && NonzeroQ[p+1] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && n-1<m<2*n-1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  -x^(m+1)*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[x^m*
      Simp[b^2*(n*(p+1)+m+1)-2*a*c*(m+2*n*(p+1)+1)+b*c*(2*n*p+3*n+m+1)*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && 
  NonzeroQ[m+1] && NonzeroQ[p+1] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m<n-1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+2*n*p+1)) - 
  1/(c*(m+2*n*p+1))*
    Int[x^(m-2*n)*Simp[a*(m-2*n+1)+b*(m+n*(p-1)+1)*x^n,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && 
  NonzeroQ[m+1] && NonzeroQ[p+1] && PositiveIntegerQ[n] && RationalQ[m,p] && -1<=p<0 && m>=2*n && m+2*n*p+1!=0


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*(m+1)) - 
  1/(a*(m+1))*
    Int[x^(m+n)*(b*(m+n*(p+1)+1)+c*(m+2*n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && Not[PositiveIntegerQ[p]] && 
  NonzeroQ[m+1] && NonzeroQ[p+1] && PositiveIntegerQ[n] && RationalQ[m,p] && -1<=p<0 && m<-1


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n+c*x^(2*n))^p/((m+1)*(1-2*c*x^n/(-b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^n/(b+Sqrt[b^2-4*a*c]))^p)*
    AppellF1[(m+1)/n,-p,-p,1+(m+1)/n,-2*c*x^n/(b+Sqrt[b^2-4*a*c]),2*c*x^n/(-b+Sqrt[b^2-4*a*c])] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && Not[PositiveIntegerQ[p]] && NonzeroQ[m+1]


Int[u_^m_.*(a_+b_.*v_^n_+c_.*w_^j_.)^p_,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j-2*n] && LinearPairQ[u,v,x] && ZeroQ[v-w]


Int[(a_.+b_.*x_^j_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[(b+a*x^n+c*x^(2*n))^p/x^(n*p),x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j+n] && IntegerQ[p] && PosQ[n]


Int[(a_.+b_.*x_^j_+c_.*x_^n_.)^p_.,x_Symbol] :=
  x^(n*p)*(a+b/x^n+c*x^n)^p/(b+a*x^n+c*x^(2*n))^p*Int[(b+a*x^n+c*x^(2*n))^p/x^(n*p),x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[j+n] && Not[IntegerQ[p]] && PosQ[n]


Int[x_^m_.*(a_.+b_.*x_^j_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^(m-n*p)*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j+n] && IntegerQ[p] && PosQ[n]


Int[x_^m_.*(a_.+b_.*x_^j_+c_.*x_^n_.)^p_.,x_Symbol] :=
  x^(n*p)*(a+b/x^n+c*x^n)^p/(b+a*x^n+c*x^(2*n))^p*Int[x^(m-n*p)*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[j+n] && Not[IntegerQ[p]] && PosQ[n]


Int[x_^m_.*(a_.+b_.*(d_./x_)^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  -d^(m+1)*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[j+2*n] && IntegerQ[2*n] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*(d_./x_)^n_+c_.*(d_./x_)^j_.)^p_.,x_Symbol] :=
  -d^(m+1)*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[j-2*n] && IntegerQ[m]


Int[x_^m_.*(a_.+b_.*(d_./x_)^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  -d*x^m*(d/x)^m*Subst[Int[(a+b*x^n+c/d^(2*n)*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[j+2*n] && IntegerQ[2*n] && Not[IntegerQ[m]]


Int[x_^m_.*(a_.+b_.*(d_./x_)^n_+c_.*(d_./x_)^j_.)^p_.,x_Symbol] :=
  -d*x^m*(d/x)^m*Subst[Int[(a+b*x^n+c*x^(2*n))^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,m,n,p},x] && ZeroQ[j-2*n] && Not[IntegerQ[m]]


Int[x_^m_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p},x] && TrinomialQ[u,x] && Not[TrinomialMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*3.2.3 (d+e x^n)^m (a+b x^n+c x^(2 n))^p*)


Int[(d_.+e_.*x_^n_)^m_.*(b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[x^(n*p)*(d+e*x^n)^m*(b+c*x^n)^p,x] /;
FreeQ[{b,c,d,e,m,n},x] && ZeroQ[j-2*n] && IntegerQ[p]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (b*e-d*c)*(b*x^n+c*x^(2*n))^(p+1)/(b*c*n*(p+1)*x^(2*n*(p+1))) + 
  e/c*Int[x^(-n)*(b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{b,c,d,e,n,p},x] && ZeroQ[j-2*n] && Not[IntegerQ[p]] && ZeroQ[n*(2*p+1)+1]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  e*x^(-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(n*(2*p+1)+1)) /;
FreeQ[{b,c,d,e,n,p},x] && ZeroQ[j-2*n] && Not[IntegerQ[p]] && NonzeroQ[n*(2*p+1)+1] && ZeroQ[b*e*(n*p+1)-c*d*(n*(2*p+1)+1)]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  e*x^(-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(n*(2*p+1)+1)) - 
  (b*e*(n*p+1)-c*d*(n*(2*p+1)+1))/(c*(n*(2*p+1)+1))*Int[(b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{b,c,d,e,n,p},x] && ZeroQ[j-2*n] && Not[IntegerQ[p]] && NonzeroQ[n*(2*p+1)+1] && NonzeroQ[b*e*(n*p+1)-c*d*(n*(2*p+1)+1)]


Int[(d_.+e_.*x_^n_)^m_.*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (b*x^n+c*x^(2*n))^p/(x^(n*p)*(b+c*x^n)^p)*Int[x^(n*p)*(d+e*x^n)^m*(b+c*x^n)^p,x] /;
FreeQ[{b,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  1/c^p*Int[(d+e*x^n)^m*(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Sqrt[a+b*x^n+c*x^(2*n)]/((4*c)^(p-1/2)*(b+2*c*x^n))*Int[(d+e*x^n)^m*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[p+1/2]


Int[(d_+e_.*x_^n_)^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (b+2*c*x^n)/((4*c)^(p+1/2)*Sqrt[a+b*x^n+c*x^(2*n)])*Int[(d+e*x^n)^m*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && NegativeIntegerQ[p-1/2]


Int[(d_+e_.*x_^n_)^m_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
(*(a+b*x^n+c*x^(2*n))^p/(b/2+c*x^n)^(2*p)*Int[(d+e*x^n)^m*(b/2+c*x^n)^(2*p),x] /; *)
  (a+b*x^n+c*x^(2*n))^p/(b+2*c*x^n)^(2*p)*Int[(d+e*x^n)^m*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[2*p]]


Int[(d_+e_.*x_^n_)^m_.*(a_+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(m+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^m_.*(a_+c_.*x_^j_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(m+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,m,n},x] && ZeroQ[j-2*n] && ZeroQ[c*d^2+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^m_*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^p/((d+e*x^n)^p*(a/d+(c*x^n)/e)^p)*Int[(d+e*x^n)^(m+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^m_*(a_+c_.*x_^j_)^p_,x_Symbol] :=
  (a+c*x^(2*n))^p/((d+e*x^n)^p*(a/d+(c*x^n)/e)^p)*Int[(d+e*x^n)^(m+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^m_*(a_.+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  -(c*d^2-b*d*e+a*e^2)*x*(d+e*x^n)^(m+1)/(d*e^2*n*(m+1)) + 
  1/(n*(m+1)*d*e^2)*Int[(d+e*x^n)^(m+1)*Simp[c*d^2-b*d*e+a*e^2*(n*(m+1)+1)+c*d*e*n*(m+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[m] && m!=-1 && Not[PositiveIntegerQ[m]]


Int[(d_+e_.*x_^n_)^m_*(a_+c_.*x_^j_),x_Symbol] :=
  -(c*d^2+a*e^2)*x*(d+e*x^n)^(m+1)/(d*e^2*n*(m+1)) + 
  1/(n*(m+1)*d*e^2)*Int[(d+e*x^n)^(m+1)*Simp[c*d^2+a*e^2*(n*(m+1)+1)+c*d*e*n*(m+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m] && m!=-1 && Not[PositiveIntegerQ[m]]


(* Int[(d_+e_.*x_^n_)^m_*(a_.+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  x*(d+e*x^n)^m*(a/(m*n+1)+b*x^n/(m*n+n+1)+c*x^(2*n)/(m*n+2*n+1)) + 
  n*d*m/((m*n+1)*(m*n+n+1)*(m*n+2*n+1))*
   Int[(d+e*x^n)^(m-1)*(a*(m*n+n+1)*(m*n+2*n+1)+b*(m*n+1)*(m*n+2*n+1)*x^n+c*(m*n+1)*(m*n+n+1)*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  RationalQ[m] && m>0 && NonzeroQ[(m*n+1)*(m*n+n+1)*(m*n+2*n+1)] && Not[IntegerQ[m]] *)


(* Int[(d_+e_.*x_^n_)^m_*(a_.+c_.*x_^j_),x_Symbol] :=
  x*(d+e*x^n)^m*(a/(m*n+1)+c*x^(2*n)/(m*n+2*n+1)) + 
  n*d*m/((m*n+1)*(m*n+n+1)*(m*n+2*n+1))*
   Int[(d+e*x^n)^(m-1)*(a*(m*n+n+1)*(m*n+2*n+1)+c*(m*n+1)*(m*n+n+1)*x^(2*n)),x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && 
  RationalQ[m] && m>0 && NonzeroQ[(m*n+1)*(m*n+n+1)*(m*n+2*n+1)] && Not[IntegerQ[m]] *)


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  Module[{r=Rt[-e/c*(2*c*d+b*e),2]},
  e^2/(2*c*r)*Int[(r+2*e*x)/(d-r*x-e*x^2),x] + 
  e^2/(2*c*r)*Int[(r-2*e*x)/(d+r*x-e*x^2),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[c*d^2-a*e^2] && NegQ[e/c*(2*c*d+b*e)] && Not[PosQ[e/c*(2*c*d-b*e)]]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
  Module[{r=Rt[-2*d*e,2]},
  e^2/(2*c*r)*Int[(r+2*e*x)/(d-r*x-e*x^2),x] + 
  e^2/(2*c*r)*Int[(r-2*e*x)/(d+r*x-e*x^2),x]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2-a*e^2] && NegQ[d*e]


(* Int[(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
  Module[{r=Rt[-2*d*e,2]},
  d/(2*a)*Int[(d-r*x)/(d-r*x-e*x^2),x] + 
  d/(2*a)*Int[(d+r*x)/(d+r*x-e*x^2),x]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2-a*e^2] && NegQ[d*e] *)


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  Module[{r=Rt[e/c*(2*c*d-b*e),2]},
  e^2/(2*c)*Int[1/(d-r*x+e*x^2),x] + 
  e^2/(2*c)*Int[1/(d+r*x+e*x^2),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[c*d^2-a*e^2] && Not[NegativeQ[e/c*(2*c*d-b*e)]]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
  e^2/(2*c)*Int[1/(d-Rt[2*d*e,2]*x+e*x^2),x] + 
  e^2/(2*c)*Int[1/(d+Rt[2*d*e,2]*x+e*x^2),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2-a*e^2] && Not[NegativeQ[d*e]]


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  (q*d+a*e)/(2*a*c)*Int[(q+c*x^2)/(a+b*x^2+c*x^4),x] +
  (q*d-a*e)/(2*a*c)*Int[(q-c*x^2)/(a+b*x^2+c*x^4),x]] /;
FreeQ[{a,b,c,d,e},x] && NegativeQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[c*d^2-a*e^2] && PosQ[a*c/b^2]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  (q*d+a*e)/(2*a*c)*Int[(q+c*x^2)/(a+c*x^4),x] +
  (q*d-a*e)/(2*a*c)*Int[(q-c*x^2)/(a+c*x^4),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NonzeroQ[c*d^2-a*e^2] && PosQ[a*c]


Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
  -(q*d-a*e)/(2*a*c)*Int[(q+c*x^2)/(a+b*x^2+c*x^4),x] -
  (q*d+a*e)/(2*a*c)*Int[(q-c*x^2)/(a+b*x^2+c*x^4),x]] /;
FreeQ[{a,b,c,d,e},x] && NegativeQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[c*d^2-a*e^2] && NegQ[a*c/b^2]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
  -(q*d-a*e)/(2*a*c)*Int[(q+c*x^2)/(a+c*x^4),x] -
  (q*d+a*e)/(2*a*c)*Int[(q-c*x^2)/(a+c*x^4),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NonzeroQ[c*d^2-a*e^2] && NegQ[a*c]


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q-b*c,2]},
  c/(2*q*r)*Int[(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NegativeQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && EvenQ[n] && n>2 && PosQ[a*c]


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q,2]},
  c/(2*q*r)*Int[(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && EvenQ[n] && n>2 && PositiveQ[a*c]


Int[(d_+e_.*x_^n_)^m_./(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^m/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[m]


Int[(d_+e_.*x_^n_)^m_./(a_+c_.*x_^j_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^m/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[m]


Int[(d_+e_.*x_^n_)^m_/(a_.+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^m,1/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[m]]


Int[(d_+e_.*x_^n_)^m_/(a_+c_.*x_^j_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^m,1/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[m]]


Int[(A_+B_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  1/Sqrt[a]*Int[(A+B*x^2)/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c,A,B},x] && NonzeroQ[b^2-4*a*c] && PositiveQ[a] && NegativeQ[c] && (PositiveQ[b] || NegativeQ[b])


Int[(A_+B_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
  1/Sqrt[a]*Int[(A+B*x^2)/(Sqrt[1-c*x^2/q]*Sqrt[1+c*x^2/q]),x]] /;
FreeQ[{a,c,A,B},x] && PositiveQ[a] && NegativeQ[c]


Int[(A_+B_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[(A+B*x^2)/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c,A,B},x] && NonzeroQ[b^2-4*a*c]


Int[(A_+B_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
  Sqrt[1-c*x^2/q]*Sqrt[1+c*x^2/q]/Sqrt[a+c*x^4]*
    Int[(A+B*x^2)/(Sqrt[1-c*x^2/q]*Sqrt[1+c*x^2/q]),x]] /;
FreeQ[{a,c,A,B},x]


Int[(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(A+B*x^n)*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,A,B,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p]


Int[(A_+B_.*x_^n_)*(a_+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(A+B*x^n)*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,A,B,n},x] && ZeroQ[j-2*n] && PositiveIntegerQ[p]


Int[(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Sign[n]/Denominator[n]},
  1/g*Subst[Int[x^(1/g-1)*(A+B*x^(n/g))*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g]] /;
FreeQ[{a,b,c,A,B,p},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[p+1] && RationalQ[n] && Not[PositiveIntegerQ[n]]


Int[(A_+B_.*x_^n_)*(a_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Sign[n]/Denominator[n]},
  1/g*Subst[Int[x^(1/g-1)*(A+B*x^(n/g))*(a+c*x^(2*n/g))^p,x],x,x^g]] /;
FreeQ[{a,c,A,B,p},x] && ZeroQ[j-2*n] && NonzeroQ[p+1] && RationalQ[n] && Not[PositiveIntegerQ[n]]


Int[(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  x*(b*B*n*p+c*A*(2*n*p+n+1)+c*B*(2*n*p+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/(c*(2*n*p+1)*(2*n*p+n+1)) + 
  n*p/(c*(2*n*p+1)*(2*n*p+n+1))*
    Int[Simp[2*a*c*A*(2*n*p+n+1)-a*b*B+(2*a*c*B*(2*n*p+1)+b*A*c*(2*n*p+n+1)-b^2*B*(n*p+1))*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,A,B,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p>0 && 
  Not[IntegerQ[p]] && NonzeroQ[2*n*p+1] && NonzeroQ[2*n*p+n+1]


Int[(A_+B_.*x_^n_)*(a_+c_.*x_^j_.)^p_.,x_Symbol] :=
  x*(A*(2*n*p+n+1)+B*(2*n*p+1)*x^n)*(a+c*x^(2*n))^p/((2*n*p+1)*(2*n*p+n+1)) + 
  2*a*n*p/((2*n*p+1)*(2*n*p+n+1))*Int[(A*(2*n*p+n+1)+B*(2*n*p+1)*x^n)*(a+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,c,A,B,n},x] && ZeroQ[j-2*n] && RationalQ[p] && p>0 && Not[IntegerQ[p]] && 
  NonzeroQ[2*n*p+1] && NonzeroQ[2*n*p+n+1]


Int[(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  -x*(A*b^2-a*b*B-2*a*c*A+(b*A-2*a*B)*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[Simp[(n*p+n+1)*A*b^2-a*b*B-2*a*c*A*(2*n*p+2*n+1)+(2*n*p+3*n+1)*(A*b-2*a*B)*c*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,A,B,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p<-1


Int[(A_+B_.*x_^n_)*(a_+c_.*x_^j_.)^p_.,x_Symbol] :=
  -x*(A+B*x^n)*(a+c*x^(2*n))^(p+1)/(2*a*n*(p+1)) + 
  1/(2*a*n*(p+1))*Int[(A*(2*n*p+2*n+1)+B*(2*n*p+3*n+1)*x^n)*(a+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,c,A,B,n},x] && ZeroQ[j-2*n] && RationalQ[p] && p<-1


Int[(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  A*Int[(a+b*x^n+c*x^(2*n))^p,x] + 
  B*Int[x^n*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,A,B,n,p},x] && ZeroQ[j-2*n]


Int[(A_+B_.*x_^n_)*(a_+c_.*x_^j_.)^p_.,x_Symbol] :=
  A*Int[(a+c*x^(2*n))^p,x] + 
  B*Int[x^n*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,A,B,n,p},x] && ZeroQ[j-2*n]


Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^4]),x_Symbol] :=
  Simp[1/(a*Sqrt[c]*Rt[-Rt[-d/c,2],2])*EllipticPi[b/(a*Rt[-d/c,2]), ArcSin[Rt[-Rt[-d/c,2],2]*x], -1],x] /;
FreeQ[{a,b,c,d},x] && PositiveQ[c]


Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^4]),x_Symbol] :=
  Sqrt[(c+d*x^4)/c]/Sqrt[c+d*x^4]*Int[1/((a+b*x^2)*Sqrt[1+(d*x^4)/c]),x] /;
FreeQ[{a,b,c,d},x] && Not[PositiveQ[c]]


Int[Sqrt[c_+d_.*x_^4]/(a_+b_.*x_^2),x_Symbol] :=
  -d/b^2*Int[(a-b*x^2)/Sqrt[c+d*x^4],x] + 
  (b^2*c+a^2*d)/b^2*Int[1/((a+b*x^2)*Sqrt[c+d*x^4]), x] /;
FreeQ[{a,b,c,d},x]


Int[(d_+e_.*x_^2)^m_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  a^(p-1/2)*Sqrt[a+b*x^2+c*x^4]/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)])*
    Int[(d+e*x^2)^m*(1+2*c*x^2/(b-q))^p*(1+2*c*x^2/(b+q))^p,x]] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p-1/2]


Int[(d_+e_.*x_^2)^m_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  Module[{q=Rt[-a*c,2]},
  a^(p-1/2)*Sqrt[a+c*x^4]/(Sqrt[1-c*x^2/q]*Sqrt[1+c*x^2/q])*
    Int[(d+e*x^2)^m*(1-c*x^2/q)^p*(1+c*x^2/q)^p,x]] /;
FreeQ[{a,c,d,e,m},x] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[p-1/2]


Int[(d_+e_.*u_^n_)^m_.*(a_+b_.*v_^n_+c_.*w_^j_.)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x^n)^m*(a+b*x^n+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(d_+e_.*u_^n_)^m_.*(a_+c_.*w_^j_.)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x^n)^m*(a+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && BinomialQ[u,x] && TrinomialQ[v,x] && Not[BinomialMatchQ[u,x] && TrinomialMatchQ[v,x]]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && BinomialQ[u,x] && BinomialQ[v,x] && Not[BinomialMatchQ[u,x] && BinomialMatchQ[v,x]]


(* ::Subsection::Closed:: *)
(*3.2.4 x^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p*)


Int[x_^m_.*(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  d*x^(m-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(b*(m+n*p+1)) /;
FreeQ[{b,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && ZeroQ[b*e*(m+n*p+1)-c*d*(m+n*(2*p+1)+1)] && NonzeroQ[m+n*p+1]


Int[x_^m_.*(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  d*x^(m-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(b*(m+n*p+1)) + 
  (b*e*(m+n*p+1)-c*d*(m+n+2*n*p+1))/(b*(m+n*p+1))*Int[x^(m+n)*(b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b*e-c*d] && NonzeroQ[b*e*(m+n*p+1)-c*d*(m+n+2*n*p+1)] && 
  RationalQ[m,n,p] && m+n*p<-1 && n>0


Int[x_^m_.*(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (b*e-c*d)*x^(m-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(b*c*n*(p+1)) - 
  (b*e*(m+n*p+1)-c*d*(m+n*p+n*(p+1)+1))/(b*c*n*(p+1))*Int[x^(m-n)*(b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b*e-c*d] && NonzeroQ[b*e*(m+1)-c*d*(m+n*(p+1)+1)] && 
  RationalQ[m,n,p] && 0<n<=m && p<-1


Int[x_^m_.*(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  e*x^(m-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(m+n*(2*p+1)+1)) - 
  (b*e*(m+n*p+1)-c*d*(m+n*(2*p+1)+1))/(c*(m+n*(2*p+1)+1))*Int[x^m*(b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{b,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && NonzeroQ[b*e*(m+n*p+1)-c*d*(m+n*(2*p+1)+1)] && NonzeroQ[m+n*(2*p+1)+1]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (b*x^n+c*x^(2*n))^p/(x^(n*p)*(b+c*x^n)^p)*Int[x^(m+n*p)*(d+e*x^n)^q*(b+c*x^n)^p,x] /;
FreeQ[{b,c,d,e,m,n,p,q},x] && ZeroQ[j-2*n] && Not[IntegerQ[p]]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && ZeroQ[j-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+c_.*x_^j_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x)^q*(a+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,c,d,e,m,n,p,q},x] && ZeroQ[j-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  1/c^p*Int[x^m*(d+e*x^n)^q*(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && IntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Sqrt[a+b*x^n+c*x^(2*n)]/((4*c)^(p-1/2)*(b+2*c*x^n))*Int[x^m*(d+e*x^n)^q*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[p+1/2]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (b+2*c*x^n)/((4*c)^(p+1/2)*Sqrt[a+b*x^n+c*x^(2*n)])*Int[x^m*(d+e*x^n)^q*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && NegativeIntegerQ[p-1/2]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^p/(b+2*c*x^n)^(2*p)*Int[x^m*(d+e*x^n)^q*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && ZeroQ[j-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[2*p]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  Int[x^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^j_)^p_.,x_Symbol] :=
  Int[x^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,q,m,n,q},x] && ZeroQ[j-2*n] && ZeroQ[c*d^2+a*e^2] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^p/((d+e*x^n)^p*(a/d+(c*x^n)/e)^p)*Int[x^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^j_)^p_,x_Symbol] :=
  (a+c*x^(2*n))^p/((d+e*x^n)^p*(a/d+(c*x^n)/e)^p)*Int[x^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,m,n,p,q},x] && ZeroQ[j-2*n] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[x^m(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,m,n},x] && ZeroQ[j-2*n] && PositiveIntegerQ[p]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Gcd[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*(d+e*x^(n/g))^q*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g]] /; 
FreeQ[{a,b,c,d,e,q},x] && ZeroQ[j-2*n] && RationalQ[m,n,p] && Not[PositiveIntegerQ[p]] && m+1!=0 && 
  (Not[PositiveIntegerQ[n]] || 0<m+1<2*n && -1<=p<0 && Not[IntegerQ[m] && CoprimeQ[m+1,n]])


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Gcd[m+1,n]},
  1/g*Subst[Int[x^((m+1)/g-1)*(d+e*x^(n/g))^q*(a+c*x^(2*n/g))^p,x],x,x^g]] /; 
FreeQ[{a,c,d,e,q},x] && ZeroQ[j-2*n] && RationalQ[m,n,p] && Not[PositiveIntegerQ[p]] && m+1!=0 && 
  (Not[PositiveIntegerQ[n]] || 0<m+1<2*n && -1<=p<0 && Not[IntegerQ[m] && CoprimeQ[m+1,n]])


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Simplify[n/(m+1)]},
  1/(m+1)*Subst[Int[(d+e*x^g)^q*(a+b*x^g+c*x^(2*g))^p,x],x,x^(m+1)] /;
 IntegerQ[g] && (g>0 || Not[PositiveIntegerQ[n]])] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && ZeroQ[j-2*n] && RationalQ[p] && -1<=p<0 && NonzeroQ[m+1]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_.*(a_+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{g=Simplify[n/(m+1)]},
  1/(m+1)*Subst[Int[(d+e*x^g)^q*(a+c*x^(2*g))^p,x],x,x^(m+1)] /;
 IntegerQ[g] && (g>0 || Not[PositiveIntegerQ[n]])] /;
FreeQ[{a,c,d,e,m,n,q},x] && ZeroQ[j-2*n] && RationalQ[p] && -1<=p<0 && NonzeroQ[m+1]


Int[(d_+e_.*x_^n_)/(x_*(a_+b_.*x_^n_+c_.*x_^j_.)),x_Symbol] :=
  d*Log[x]/a + 
  1/a*Int[x^(n-1)*Simp[a*e-b*d-c*d*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[(d_+e_.*x_^n_)/(x_*(a_+c_.*x_^j_.)),x_Symbol] :=
  d*Log[x]/a + 
  1/a*Int[x^(n-1)*(a*e-c*d*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2]


Int[x_^m_*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  d*x^(m+1)/(a*(m+1)) - 
  1/a*Int[x^(m+n)*Simp[b*d-a*e+c*d*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_*(d_+e_.*x_^n_)/(a_+c_.*x_^j_),x_Symbol] :=
  d*x^(m+1)/(a*(m+1)) + 
  1/a*Int[x^(m+n)*(a*e-c*d*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  e*x^(m-n+1)/(c*(m-n+1)) -
  1/c*Int[x^(m-n)*Simp[a*e+(b*e-c*d)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  PositiveIntegerQ[n] && RationalQ[m] && m-n+1>0


Int[x_^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^j_),x_Symbol] :=
  e*x^(m-n+1)/(c*(m-n+1)) -
  1/c*Int[x^(m-n)*(a*e-c*d*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[n] && RationalQ[m] && m-n+1>0


Int[x_^m_*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q-b*c,2]},
  c/(2*q*r)*Int[x^m*Simp[d*r-(c*d-e*q)*x^(n/2),x]/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[x^m*Simp[d*r+(c*d-e*q)*x^(n/2),x]/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NegativeQ[b^2-4*a*c] && IntegersQ[m,n/2] && 
  0<m<n && CoprimeQ[m+1,n] && PosQ[a*c]


Int[x_^m_*(d_+e_.*x_^n_)/(a_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q,2]},
  c/(2*q*r)*Int[x^m*Simp[d*r-(c*d-e*q)*x^(n/2),x]/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[x^m*Simp[d*r+(c*d-e*q)*x^(n/2),x]/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && PositiveQ[a*c] && IntegersQ[m,n/2] && 0<m<n && CoprimeQ[m+1,n]


Int[x_^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[b^2-4*a*c,2]},
  (e+(2*c*d-b*e)/q)*Int[x^m/(b-q+2*c*x^n),x] +
  (e-(2*c*d-b*e)/q)*Int[x^m/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && IntegersQ[m,n] && 
  0<m<n && CoprimeQ[m+1,n] && Not[IntegerQ[n/2] && NegativeQ[b^2-4*a*c] && PosQ[a*c]]


Int[x_^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^j_),x_Symbol] :=
  Module[{q=2*Rt[-a*c,2]},
  (e+c*d/(2*q))*Int[x^m/(-q+c*x^n),x] +
  (e-c*d/(2*q))*Int[x^m/(q+c*x^n),x]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && IntegersQ[m,n] && 
  0<m<n && CoprimeQ[m+1,n] && Not[IntegerQ[n/2] && PositiveQ[a*c]]


Int[x_^m_.*(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  Module[{r=Rt[c/e*(2*c*d-b*e),2]},
  e/2*Int[x^m/(c*d/e-r*x+c*x^2),x] + 
  e/2*Int[x^m/(c*d/e+r*x+c*x^2),x]] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  ZeroQ[c*d^2-a*e^2] && PositiveQ[d/e] && PosQ[c/e*(2*c*d-b*e)]


Int[x_^m_.*(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
  Module[{r=Rt[2*c^2*d/e,2]},
  e/2*Int[x^m/(c*d/e-r*x+c*x^2),x] + 
  e/2*Int[x^m/(c*d/e+r*x+c*x^2),x]] /;
FreeQ[{a,c,d,e,m},x] && ZeroQ[c*d^2-a*e^2] && PositiveQ[d/e]


Int[x_^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q-b*c,2]},
  c/(2*q*r)*Int[x^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[x^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[j-2*n] && NegativeQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && EvenQ[n] && n>2 && PosQ[a*c]


Int[x_^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^j_),x_Symbol] :=
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q,2]},
  c/(2*q*r)*Int[x^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[x^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e,m},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && EvenQ[n] && n>2 && PositiveQ[a*c]


Int[x_^m_.*(d_+e_.*x_^n_)^q_./(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegersQ[q,m]


Int[x_^m_.*(d_+e_.*x_^n_)^q_./(a_+c_.*x_^j_),x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && IntegersQ[q,m]


Int[x_^m_.*(d_+e_.*x_^n_)^q_./(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
  Int[ExpandIntegrand[x^m,(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[q] && Not[IntegerQ[m]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_./(a_+c_.*x_^j_),x_Symbol] :=
  Int[ExpandIntegrand[x^m,(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,m,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[q] && Not[IntegerQ[m]]


Int[x_^m_.*(d_.+e_.*x_^n_)^q_/(a_.+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  1/c^2*Int[x^(m-2*n)*(c*d-b*e+c*e*x^n)*(d+e*x^n)^(q-1),x] - 
  1/c^2*Int[x^(m-2*n)*Simp[a*(c*d-b*e)+(b*c*d-b^2*e+a*c*e)*x^n,x]*(d+e*x^n)^(q-1)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[q]] && RationalQ[m,n,q] && q>0 && 0<2*n<m+1


Int[x_^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^j_.),x_Symbol] :=
  1/c*Int[x^(m-2*n)*(d+e*x^n)^q,x] - 
  a/c*Int[x^(m-2*n)*(d+e*x^n)^q/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,q},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[q]] && RationalQ[m,n] && 0<2*n<m+1


Int[x_^m_.*(d_.+e_.*x_^n_)^q_/(a_.+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  e/c*Int[x^(m-n)*(d+e*x^n)^(q-1),x] - 
  1/c*Int[x^(m-n)*Simp[a*e-(c*d-b*e)*x^n,x]*(d+e*x^n)^(q-1)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[q]] && RationalQ[m,n,q] && q>0 && 0<n<m+1<=2*n


Int[x_^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^j_.),x_Symbol] :=
  e/c*Int[x^(m-n)*(d+e*x^n)^(q-1),x] - 
  1/c*Int[x^(m-n)*Simp[a*e-c*d*x^n,x]*(d+e*x^n)^(q-1)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[q]] && RationalQ[m,n,q] && q>0 && 0<n<m+1<=2*n


Int[x_^m_*(d_.+e_.*x_^n_)^q_/(a_.+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  d/a*Int[x^m*(d+e*x^n)^(q-1),x] - 
  1/a*Int[x^(m+n)*Simp[b*d-a*e+c*d*x^n,x]*(d+e*x^n)^(q-1)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[q]] && RationalQ[m,n,q] && q>0 && m<0 && n>0


Int[x_^m_*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^j_.),x_Symbol] :=
  d/a*Int[x^m*(d+e*x^n)^(q-1),x] + 
  1/a*Int[x^(m+n)*Simp[a*e-c*d*x^n,x]*(d+e*x^n)^(q-1)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[q]] && RationalQ[m,n,q] && q>0 && m<0 && n>0


Int[x_^m_.*(d_.+e_.*x_^n_)^q_/(a_.+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  -d*e/(c*d^2-b*d*e+a*e^2)*Int[x^(m-n)*(d+e*x^n)^q,x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[x^(m-n)*(a*e+c*d*x^n)*(d+e*x^n)^(q+1)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  Not[IntegerQ[q]] && RationalQ[m,n,q] && q<0 && 0<n<m+1


Int[x_^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^j_.),x_Symbol] :=
  -d*e/(c*d^2+a*e^2)*Int[x^(m-n)*(d+e*x^n)^q,x] + 
  1/(c*d^2+a*e^2)*Int[x^(m-n)*(a*e+c*d*x^n)*(d+e*x^n)^(q+1)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[q]] && RationalQ[m,n,q] && q<0 && 0<n<m+1


Int[x_^m_.*(d_+e_.*x_^n_)^q_/(a_.+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q,x^m/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,q,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[q]] && IntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^j_.),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q,x^m/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,q,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[q]] && IntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^n_)^q_/(a_.+b_.*x_^n_+c_.*x_^j_.),x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^n)^q,1/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,m,q,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[q]] && 
  Not[IntegerQ[m]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^j_.),x_Symbol] :=
  Int[ExpandIntegrand[x^m*(d+e*x^n)^q,1/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,m,q,n},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[q]] && Not[IntegerQ[m]]


Int[(A_.+B_.*x_^n_)/(x_*Sqrt[a_+b_.*x_^n_+c_.*x_^j_.]),x_Symbol] :=
  A*Int[1/(x*Sqrt[a+b*x^n+c*x^(2*n)]),x] + 
  B*Int[x^(n-1)/Sqrt[a+b*x^n+c*x^(2*n)],x] /;
FreeQ[{a,b,c,A,B,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c]


Int[(A_.+B_.*x_^n_)/(x_*Sqrt[a_+c_.*x_^j_.]),x_Symbol] :=
  A*Int[1/(x*Sqrt[a+c*x^(2*n)]),x] + 
  B*Int[x^(n-1)/Sqrt[a+c*x^(2*n)],x] /;
FreeQ[{a,c,A,B,n},x] && ZeroQ[j-2*n]


Int[x_^m_.*(A_+B_.*x_^n_)*(a_.+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  x^(m+1)*(A*(m+n*(2*p+1)+1)+B*(m+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/((m+1)*(m+n*(2*p+1)+1)) + 
  n*p/((m+1)*(m+n*(2*p+1)+1))*
    Int[x^(n+m)*
      Simp[2*a*B*(m+1)-A*b*(m+n*(2*p+1)+1)+(b*B*(m+1)-2*c*A*(m+n*(2*p+1)+1))*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p>0 && m<=-n && m+1!=0 && m+n*(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+c_.*x_^j_)^p_.,x_Symbol] :=
  x^(m+1)*(A*(m+n*(2*p+1)+1)+B*(m+1)*x^n)*(a+c*x^(2*n))^p/((m+1)*(m+n*(2*p+1)+1)) + 
  2*n*p/((m+1)*(m+n*(2*p+1)+1))*
    Int[x^(n+m)*(a*B*(m+1)-c*A*(m+n*(2*p+1)+1)*x^n)*(a+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,c,A,B},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p>0 && m<=-n && m+1!=0 && m+n*(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^n_)*(a_.+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  x^(m+1)*(b*B*n*p+c*A*(m+n*(2*p+1)+1)+c*B*(2*n*p+m+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/
    (c*(2*n*p+m+1)*(m+n*(2*p+1)+1)) + 
  n*p/(c*(2*n*p+m+1)*(m+n*(2*p+1)+1))*
    Int[x^m*
      Simp[2*a*c*A*(m+n*(2*p+1)+1)-a*b*B*(m+1)+(2*a*c*B*(2*n*p+m+1)+A*b*c*(m+n*(2*p+1)+1)-b^2*B*(m+n*p+1))*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p>0 && m>-n && 2*n*p+m+1!=0 && m+n*(2*p+1)+1!=0 && m+1!=n


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+c_.*x_^j_)^p_.,x_Symbol] :=
  x^(m+1)*(c*A*(m+n*(2*p+1)+1)+c*B*(2*n*p+m+1)*x^n)*(a+c*x^(2*n))^p/(c*(2*n*p+m+1)*(m+n*(2*p+1)+1)) + 
  2*a*n*p/((2*n*p+m+1)*(m+n*(2*p+1)+1))*
    Int[x^m*(A*(m+n*(2*p+1)+1)+B*(2*n*p+m+1)*x^n)*(a+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,c,A,B},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p>0 && m>-n && 2*n*p+m+1!=0 && m+n*(2*p+1)+1!=0 && m+1!=n


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  x^(m-n+1)*(A*b-2*a*B-(b*B-2*c*A)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) + 
  1/(n*(p+1)*(b^2-4*a*c))*
    Int[x^(m-n)*
      Simp[(n-m-1)*(A*b-2*a*B)+(2*n*p+2*n+m+1)*(b*B-2*c*A)*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m>n-1


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+c_.*x_^j_)^p_.,x_Symbol] :=
  x^(m-n+1)*(a*B-c*A*x^n)*(a+c*x^(2*n))^(p+1)/(2*a*c*n*(p+1)) + 
  1/(2*a*c*n*(p+1))*Int[x^(m-n)*(a*B*(n-m-1)+c*A*(2*n*p+2*n+m+1)*x^n)*(a+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,c,A,B},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m>n-1


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  -x^(m+1)*(A*(b^2-2*a*c)-a*b*B+(A*b-2*a*B)*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[x^m*
      Simp[A*(b^2*(m+n*(p+1)+1)-2*a*c*(m+2*n*(p+1)+1))-a*b*B*(m+1)+(m+n*(2*p+3)+1)*(A*b-2*a*B)*c*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m<n-1


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+c_.*x_^j_)^p_.,x_Symbol] :=
  -x^(m+1)*(A+B*x^n)*(a+c*x^(2*n))^(p+1)/(2*a*n*(p+1)) + 
  1/(2*a*n*(p+1))*Int[x^m*(A*(m+2*n*(p+1)+1)+B*(m+n*(2*p+3)+1)*x^n)*(a+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,c,A,B},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m<n-1


Int[x_^m_.*(A_+B_.*x_^n_)*(a_.+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  B*x^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+n(2*p+1)+1)) - 
  1/(c*(m+n(2*p+1)+1))*
    Int[x^(m-n)*Simp[a*B*(m-n+1)+(b*B*(m+n*p+1)-c*A*(m+n(2*p+1)+1))*x^n,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && m>=n && -1<=p<0 && m+n(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+c_.*x_^j_)^p_.,x_Symbol] :=
  B*x^(m-n+1)*(a+c*x^(2*n))^(p+1)/(c*(m+n(2*p+1)+1)) - 
  1/(c*(m+n(2*p+1)+1))*
    Int[x^(m-n)*(a*B*(m-n+1)-c*A*(m+n(2*p+1)+1)*x^n)*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,A,B},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && m>=n && -1<=p<0 && m+n(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_.,x_Symbol] :=
  A*x^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*(m+1)) + 
  1/(a*(m+1))*
    Int[x^(m+n)*Simp[a*B*(m+1)-A*b*(m+n*(p+1)+1)-c*A*(m+2*n(p+1)+1)*x^n,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && m<=-n && (-1<=p<0 || m+n*(2*p+1)+1==0) && m+1!=0


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+c_.*x_^j_)^p_.,x_Symbol] :=
  A*x^(m+1)*(a+c*x^(2*n))^(p+1)/(a*(m+1)) + 
  1/(a*(m+1))*Int[x^(m+n)*(a*B*(m+1)-c*A*(m+2*n(p+1)+1)*x^n)*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,A,B},x] && ZeroQ[j-2*n] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && m<=-n && -1<=p<0 && m+1!=0


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_.)^p_.,x_Symbol] :=
  A*Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] + 
  B*Int[x^(m+n)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,A,B,m,n,p},x] && ZeroQ[j-2*n]


Int[x_^m_.*(A_+B_.*x_^n_)*(a_+c_.*x_^j_.)^p_.,x_Symbol] :=
  A*Int[x^m*(a+c*x^(2*n))^p,x] + 
  B*Int[x^(m+n)*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,A,B,m,n,p},x] && ZeroQ[j-2*n]


Int[x_^m_*(a_.+b_.*x_^n_+c_.*x_^j_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  1/(d*e)*Int[x^m*(a*e+c*d*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] - 
  (c*d^2-b*d*e+a*e^2)/(d*e)*Int[x^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m,n,p] && m<0 && n>0 && p>0


Int[x_^m_*(a_+c_.*x_^j_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  1/(d*e)*Int[x^m*(a*e+c*d*x^n)*(a+c*x^(2*n))^(p-1),x] - 
  (c*d^2+a*e^2)/(d*e)*Int[x^(m+n)*(a+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,n,p] && m<0 && n>0 && p>0


Int[x_^m_.*(a_.+b_.*x_^n_+c_.*x_^j_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  1/(c*d^2-b*d*e+a*e^2)*Int[x^(m-n)*(a*e+c*d*x^n)*(a+b*x^n+c*x^(2*n))^p,x] - 
  d*e/(c*d^2-b*d*e+a*e^2)*Int[x^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[m,n,p] && m>0 && n>0 && p<-1


Int[x_^m_.*(a_+c_.*x_^j_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  1/(c*d^2+a*e^2)*Int[x^(m-n)*(a*e+c*d*x^n)*(a+c*x^(2*n))^p,x] - 
  d*e/(c*d^2+a*e^2)*Int[x^(m-n)*(a+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[j-2*n] && NonzeroQ[c*d^2+a*e^2] && RationalQ[m,n,p] && m>0 && n>0 && p<-1


Int[u_^m_.*(d_.+e_.*v_^n_)^q_.*(a_+b_.*w_^n_+c_.*z_^j_.)^p_,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && ZeroQ[j-2*n] && LinearPairQ[u,v,x] && ZeroQ[v-w] && ZeroQ[v-z]


Int[u_^m_.*(d_.+e_.*v_^n_)^q_.*(a_+c_.*z_^j_.)^p_,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,c,d,e,m,n,p},x] && ZeroQ[j-2*n] && LinearPairQ[u,v,x] && ZeroQ[v-z]


Int[x_^m_.*z_^q_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p,q},x] && BinomialQ[z,x] && TrinomialQ[u,x] && Not[BinomialMatchQ[z,x] && TrinomialMatchQ[u,x]]


Int[x_^m_.*z_^q_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[z,x]^q*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p,q},x] && BinomialQ[z,x] && BinomialQ[u,x] && Not[BinomialMatchQ[z,x] && BinomialMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*3.3.1 (a x^q+b x^n+c x^(2 n-q))^p*)


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Int[((a+b+c)*x^n)^p,x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n-q] && ZeroQ[r-n]


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Int[x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,n,q},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && IntegerQ[p]


Int[Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))])*
    Int[x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
FreeQ[{a,b,c,n,q},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q]


Int[1/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[1/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]),x] /;
FreeQ[{a,b,c,n,q},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q]


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x*(a*x^q+b*x^n+c*x^(2*n-q))^p/(p*(2*n-q)+1) + 
  (n-q)*p/(p*(2*n-q)+1)*
    Int[x^q*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c,n,q},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p>0 && 
  NonzeroQ[p*(2*n-q)+1]


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  1/(a*(n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(-q)*((p*q+1)*(b^2-2*a*c)+(n-q)*(p+1)*(b^2-4*a*c)+b*c*(p*q+(n-q)*(2*p+3)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c,n,q},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p<-1


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n+c*x^(2*n-q))^p/(x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p)*
    Int[x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,n,p,q},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]]


Int[(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Defer[Int][(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c,n,p,q},x] && ZeroQ[r-(2*n-q)]


Int[(a_.*u_^q_.+b_.*v_^n_.+c_.*w_^r_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,n,p,q},x] && ZeroQ[r-(2*n-q)] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && GeneralizedTrinomialQ[u,x] && Not[GeneralizedTrinomialMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*3.3.2 x^m (a x^q+b x^n+c x^(2 n-q))^p*)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
  Int[x^m*((a+b+c)*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[q-n] && ZeroQ[r-n]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
  Int[x^(m+p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,m,n,q},x] && ZeroQ[r-(2*n-q)] && IntegerQ[p] && PosQ[n-q]


Int[x_^m_./Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[x^(m-q/2)/Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
FreeQ[{a,b,c,m,n,q},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && (ZeroQ[m-1] && ZeroQ[n-3] && ZeroQ[q-2]  ||  
  (ZeroQ[m+1/2] || ZeroQ[m-3/2] || ZeroQ[m-1/2] || ZeroQ[m-5/2]) && ZeroQ[n-3] && ZeroQ[q-1])


Int[x_^m_./(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^(3/2),x_Symbol] :=
  -2*x^((n-1)/2)*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a*x^(n-1)+b*x^n+c*x^(n+1)]) /;
FreeQ[{a,b,c,n},x] && ZeroQ[m-3*(n-1)/2] && ZeroQ[q-n+1] && ZeroQ[r-n-1] && NonzeroQ[b^2-4*a*c]


Int[x_^m_./(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^(3/2),x_Symbol] :=
  x^((n-1)/2)*(4*a+2*b*x)/((b^2-4*a*c)*Sqrt[a*x^(n-1)+b*x^n+c*x^(n+1)]) /;
FreeQ[{a,b,c,n},x] && ZeroQ[m-(3*n-1)/2] && ZeroQ[q-n+1] && ZeroQ[r-n-1] && NonzeroQ[b^2-4*a*c]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-n)*(a*x^(n-1)+b*x^n+c*x^(n+1))^(p+1)/(2*c*(p+1)) - 
  b/(2*c)*Int[x^(m-1)*(a*x^(n-1)+b*x^n+c*x^(n+1))^p,x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && m+p*(n-1)-1==0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-n+q+1)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/(2*c*(n-q)*(2*p+1)) - 
  p*(b^2-4*a*c)/(2*c*(2*p+1))*Int[x^(m+q)*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q+1==n-q


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-n+q+1)*(b*(n-q)*p+c*(m+p*q+(n-q)*(2*p-1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p-1)+1)) + 
  (n-q)*p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p-1)+1))*
    Int[x^(m-(n-2*q))*
      Simp[-a*b*(m+p*q-n+q+1)+(2*a*c*(m+p*q+(n-q)*(2*p-1)+1)-b^2*(m+p*q+(n-q)*(p-1)+1))*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q+1>n-q && m+p*(2*n-q)+1!=0 && m+p*q+(n-q)*(2*p-1)+1!=0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m+1)*(a*x^q+b*x^n+c*x^(2*n-q))^p/(m+p*q+1) - 
  (n-q)*p/(m+p*q+1)*Int[x^(m+n)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q+1<=-(n-q)+1 && NonzeroQ[m+p*q+1]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m+1)*(a*x^q+b*x^n+c*x^(2*n-q))^p/(m+p*(2*n-q)+1) + 
  (n-q)*p/(m+p*(2*n-q)+1)*Int[x^(m+q)*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q+1>-(n-q) && m+p*(2*n-q)+1!=0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(m-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  (2*a*c-b^2*(p+2))/(a*(p+1)*(b^2-4*a*c))*
    Int[x^(m-q)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q+1==-(n-q)*(2*p+3)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(m-2*n+q+1)*(2*a+b*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) + 
  1/((n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-2*n+q)*(2*a*(m+p*q-2*(n-q)+1)+b*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q+1>2*(n-q)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(m-q+1)*(b^2-2*a*c+b*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  1/(a*(n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-q)*
      (b^2*(m+p*q+(n-q)*(p+1)+1)-2*a*c*(m+p*q+2*(n-q)*(p+1)+1)+b*c*(m+p*q+(n-q)*(2*p+3)+1)*x^(n-q))*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q+1<n-q


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-n+1)*(b+2*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) - 
  1/((n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-n)*(b*(m+p*q-n+q+1)+2*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && n-q<m+p*q+1<2*(n-q)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-2*n+q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(2*c*(n-q)*(p+1)) - 
  b/(2*c)*Int[x^(m-n+q)*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q+1==2*(n-q)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  -x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(2*a*(n-q)*(p+1)) - 
  b/(2*a)*Int[x^(m+n-q)*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q+1==-2*(n-q)*(p+1)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-2*n+q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(c*(m+p*q+2*(n-q)*p+1)) - 
  1/(c*(m+p*q+2*(n-q)*p+1))*
    Int[x^(m-2*(n-q))*(a*(m+p*q-2*(n-q)+1)+b*(m+p*q+(n-q)*(p-1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q+1>2*(n-q)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) - 
  1/(a*(m+p*q+1))*
    Int[x^(m+n-q)*(b*(m+p*q+(n-q)*(p+1)+1)+c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c},x] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q+1<0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n+c*x^(2*n-q))^p/(x^(p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p)*
    Int[x^(m+p*q)*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,m,n,p,q},x] && ZeroQ[r-(2*n-q)] && Not[IntegerQ[p]] && PosQ[n-q]


Int[u_^m_.*(a_.*v_^q_.+b_.*w_^n_.+c_.*z_^r_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[x^m*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,m,n,p,q},x] && ZeroQ[r-(2*n-q)] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && LinearQ[u,x] && NonzeroQ[u-x]


Int[x_^m_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p},x] && GeneralizedTrinomialQ[u,x] && Not[GeneralizedTrinomialMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*3.3.3 (A+B x^(n-q)) (a x^q+b x^n+c x^(2 n-q))^p*)


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[x^(p*q)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,n,q},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && IntegerQ[p] && PosQ[n-q]


(* Int[(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))])*
    Int[x^(q*p)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && PositiveIntegerQ[p+1/2] *)


(* Int[(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[x^(q*p)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && NegativeIntegerQ[p-1/2] *)


(* Int[(A_+B_.*x_^j_.)*Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))])*
    Int[x^(q/2)*(A+B*x^(n-q))*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
FreeQ[{a,b,c,A,B,n,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && PosQ[n-q] *)


Int[(A_+B_.*x_^j_.)/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[(A+B*x^(n-q))/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]),x] /;
FreeQ[{a,b,c,A,B,n,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && 
  ZeroQ[n-3] && ZeroQ[q-2]


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_,x_Symbol] :=
  x*(b*B*(n-q)*p+A*c*(p*q+(n-q)*(2*p+1)+1)+B*c*(p*(2*n-q)+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/
    (c*(p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/(c*(p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1))*
    Int[x^q*
      (2*a*A*c*(p*q+(n-q)*(2*p+1)+1)-a*b*B*(p*q+1)+(2*a*B*c*(p*(2*n-q)+1)+A*b*c*(p*q+(n-q)*(2*p+1)+1)-b^2*B*(p*q+(n-q)*p+1))*x^(n-q))*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c,A,B,n,q},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p>0 && 
  NonzeroQ[p*(2*n-q)+1] && NonzeroQ[p*q+(n-q)*(2*p+1)+1]


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{n=q+r},
  x*(A*(p*q+(n-q)*(2*p+1)+1)+B*(p*(2*n-q)+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/((p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/((p*(2*n-q)+1)*(p*q+(n-q)*(2*p+1)+1))*
    Int[x^q*(2*a*A*(p*q+(n-q)*(2*p+1)+1)+(2*a*B*(p*(2*n-q)+1))*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
 ZeroQ[j-(2*n-q)] && NonzeroQ[p*(2*n-q)+1] && NonzeroQ[p*q+(n-q)*(2*p+1)+1]] /;
FreeQ[{a,c,A,B,q},x] && Not[IntegerQ[p]] && RationalQ[p] && p>0


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_,x_Symbol] :=
  -x^(-q+1)*(A*b^2-a*b*B-2*a*A*c+(A*b-2*a*B)*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  1/(a*(n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(-q)*
      ((A*b^2*(p*q+(n-q)*(p+1)+1)-a*b*B*(p*q+1)-2*a*A*c*(p*q+2*(n-q)*(p+1)+1)+(p*q+(n-q)*(2*p+3)+1)*(A*b-2*a*B)*c*x^(n-q))*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p+1)),x] /;
FreeQ[{a,b,c,A,B,n,q},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p<-1


Int[(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_,x_Symbol] :=
  Module[{n=q+r},
  -x^(-q+1)*(a*A*c+a*B*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(2*a*c)) + 
  1/(a*(n-q)*(p+1)*(2*a*c))*
    Int[x^(-q)*((a*A*c*(p*q+2*(n-q)*(p+1)+1)+a*B*c*(p*q+(n-q)*(2*p+3)+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)),x] /;
 ZeroQ[j-(2*n-q)]] /;
FreeQ[{a,c,A,B,q},x] && Not[IntegerQ[p]] && RationalQ[p] && p<-1


(* Int[(A_+B_.*x_^q_)*(a_.*x_^j_.+b_.*x_^k_.+c_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^k+c*x^n)^p/(x^(j*p)*(a+b*x^(k-j)+c*x^(2*(k-j)))^p)*
    Int[x^(j*p)*(A+B*x^(k-j))*(a+b*x^(k-j)+c*x^(2*(k-j)))^p,x] /;
FreeQ[{a,b,c,A,B,j,k,p},x] && ZeroQ[q-(k-j)] && ZeroQ[n-(2*k-j)] && PosQ[k-j] && Not[IntegerQ[p]] *)


Int[(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_.,x_Symbol] :=
  Defer[Int][(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)]


Int[(A_+B_.*u_^j_.)*(a_.*v_^q_.+b_.*w_^n_.+c_.*z_^r_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && LinearQ[u,x] && 
  NonzeroQ[u-x]


Int[z_*u_^p_.,x_Symbol] :=
  Int[ExpandToSum[z,x]*ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && BinomialQ[z,x] && GeneralizedTrinomialQ[u,x] && 
  ZeroQ[BinomialDegree[z,x]-GeneralizedTrinomialDegree[u,x]] && Not[BinomialMatchQ[z,x] && GeneralizedTrinomialMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*3.3.4 x^m (A+B x^(n-q)) (a x^q+b x^n+c x^(2 n-q))^p*)


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Int[x^(m+p*q)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,m,n,q},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && IntegerQ[p] && PosQ[n-q]


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(n+m)*
      Simp[2*a*B*(m+p*q+1)-A*b*(m+p*q+(n-q)*(2*p+1)+1)+(b*B*(m+p*q+1)-2*A*c*(m+p*q+(n-q)*(2*p+1)+1))*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q<=-(n-q) && m+p*q+1!=0 && m+p*q+(n-q)*(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Module[{n=q+r},
  x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1)) + 
  2*(n-q)*p/((m+p*q+1)*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(n+m)*Simp[a*B*(m+p*q+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
 ZeroQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q<=-(n-q) && m+p*q+1!=0 && m+p*q+(n-q)*(2*p+1)+1!=0] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && p>0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  x^(m-n+1)*(A*b-2*a*B-(b*B-2*A*c)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/((n-q)*(p+1)*(b^2-4*a*c)) + 
  1/((n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-n)*
      Simp[(m+p*q-n+q+1)*(2*a*B-A*b)+(m+p*q+2*(n-q)*(p+1)+1)*(b*B-2*A*c)*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q>n-q-1


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Module[{n=q+r},
  x^(m-n+1)*(a*B-A*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(2*a*c*(n-q)*(p+1)) - 
  1/(2*a*c*(n-q)*(p+1))*
    Int[x^(m-n)*Simp[a*B*(m+p*q-n+q+1)-A*c*(m+p*q+(n-q)*2*(p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p+1),x] /;
 ZeroQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q>n-q-1] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && p<-1


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  x^(m+1)*(b*B*(n-q)*p+A*c*(m+p*q+(n-q)*(2*p+1)+1)+B*c*(m+p*q+2*(n-q)*p+1)*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p/
    (c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/(c*(m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(m+q)*
      Simp[2*a*A*c*(m+p*q+(n-q)*(2*p+1)+1)-a*b*B*(m+p*q+1)+
        (2*a*B*c*(m+p*q+2*(n-q)*p+1)+A*b*c*(m+p*q+(n-q)*(2*p+1)+1)-b^2*B*(m+p*q+(n-q)*p+1))*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p-1),x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p>0 && m+p*q>-(n-q)-1 && m+p*(2*n-q)+1!=0 && m+p*q+(n-q)*(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Module[{n=q+r},
  x^(m+1)*(A*(m+p*q+(n-q)*(2*p+1)+1)+B*(m+p*q+2*(n-q)*p+1)*x^(n-q))*(a*x^q+c*x^(2*n-q))^p/
    ((m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1)) + 
  (n-q)*p/((m+p*(2*n-q)+1)*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(m+q)*Simp[2*a*A*(m+p*q+(n-q)*(2*p+1)+1)+2*a*B*(m+p*q+2*(n-q)*p+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p-1),x] /;
 ZeroQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q>-(n-q) && m+p*q+2*(n-q)*p+1!=0 && m+p*q+(n-q)*(2*p+1)+1!=0 && m+1!=n] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && p>0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  -x^(m-q+1)*(A*b^2-a*b*B-2*a*A*c+(A*b-2*a*B)*c*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(n-q)*(p+1)*(b^2-4*a*c)) + 
  1/(a*(n-q)*(p+1)*(b^2-4*a*c))*
    Int[x^(m-q)*
      Simp[A*b^2*(m+p*q+(n-q)*(p+1)+1)-a*b*B*(m+p*q+1)-2*a*A*c*(m+p*q+2*(n-q)*(p+1)+1)+
        (m+p*q+(n-q)*(2*p+3)+1)*(A*b-2*a*B)*c*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^(p+1),x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && p<-1 && m+p*q<n-q-1


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Module[{n=q+r},
  -x^(m-q+1)*(A*c+B*c*x^(n-q))*(a*x^q+c*x^(2*n-q))^(p+1)/(2*a*c*(n-q)*(p+1)) + 
  1/(2*a*c*(n-q)*(p+1))*
    Int[x^(m-q)*Simp[A*c*(m+p*q+2*(n-q)*(p+1)+1)+B*(m+p*q+(n-q)*(2*p+3)+1)*c*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^(p+1),x] /;
 ZeroQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q<n-q-1] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && p<-1


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  B*x^(m-n+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(c*(m+p*q+(n-q)*(2*p+1)+1)) - 
  1/(c*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(m-n+q)*
      Simp[a*B*(m+p*q-n+q+1)+(b*B*(m+p*q+(n-q)*p+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1))*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && -1<=p<0 && m+p*q>=n-q-1 && m+p*q+(n-q)*(2*p+1)+1!=0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Module[{n=q+r},
  B*x^(m-n+1)*(a*x^q+c*x^(2*n-q))^(p+1)/(c*(m+p*q+(n-q)*(2*p+1)+1)) - 
  1/(c*(m+p*q+(n-q)*(2*p+1)+1))*
    Int[x^(m-n+q)*Simp[a*B*(m+p*q-n+q+1)-A*c*(m+p*q+(n-q)*(2*p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^p,x] /;
 ZeroQ[j-(2*n-q)] && PositiveIntegerQ[n] && m+p*q>=n-q-1 && m+p*q+(n-q)*(2*p+1)+1!=0] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q] && -1<=p<0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  A*x^(m-q+1)*(a*x^q+b*x^n+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) + 
  1/(a*(m+p*q+1))*
    Int[x^(m+n-q)*
      Simp[a*B*(m+p*q+1)-A*b*(m+p*q+(n-q)*(p+1)+1)-A*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q),x]*
      (a*x^q+b*x^n+c*x^(2*n-q))^p,x] /;
FreeQ[{a,b,c,A,B},x] && ZeroQ[r-(n-q)] && ZeroQ[j-(2*n-q)] && Not[IntegerQ[p]] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p,q] && (-1<=p<0 || m+p*q+(n-q)*(2*p+1)+1==0) && m+p*q<=-(n-q) && m+p*q+1!=0


Int[x_^m_.*(A_+B_.*x_^r_.)*(a_.*x_^q_.+c_.*x_^j_.)^p_.,x_Symbol] :=
  Module[{n=q+r},
  A*x^(m-q+1)*(a*x^q+c*x^(2*n-q))^(p+1)/(a*(m+p*q+1)) + 
  1/(a*(m+p*q+1))*
    Int[x^(m+n-q)*Simp[a*B*(m+p*q+1)-A*c*(m+p*q+2*(n-q)*(p+1)+1)*x^(n-q),x]*(a*x^q+c*x^(2*n-q))^p,x] /;
 ZeroQ[j-(2*n-q)] && PositiveIntegerQ[n] && (-1<=p<0 || m+p*q+(n-q)*(2*p+1)+1==0) && m+p*q<=-(n-q) && m+p*q+1!=0] /;
FreeQ[{a,c,A,B},x] && Not[IntegerQ[p]] && RationalQ[m,p,q]


Int[x_^m_.*(A_+B_.*x_^j_.)/Sqrt[a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[x^(m-q/2)*(A+B*x^(n-q))/Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))],x] /;
FreeQ[{a,b,c,A,B,m,n,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && PosQ[n-q] && 
	(ZeroQ[m-1/2] || ZeroQ[m+1/2]) && ZeroQ[n-3] && ZeroQ[q-1]


(* Int[x_^m_.*(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]/(x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))])*
    Int[x^(m+q*p)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,m,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && PositiveIntegerQ[p+1/2] && PosQ[n-q] *)


(* Int[x_^m_.*(A_+B_.*x_^j_.)*(a_.*x_^q_.+b_.*x_^n_.+c_.*x_^r_.)^p_,x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)+c*x^(2*(n-q))]/Sqrt[a*x^q+b*x^n+c*x^(2*n-q)]*
    Int[x^(m+q*p)*(A+B*x^(n-q))*(a+b*x^(n-q)+c*x^(2*(n-q)))^p,x] /;
FreeQ[{a,b,c,A,B,m,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && NegativeIntegerQ[p-1/2] && PosQ[n-q] *)


Int[x_^m_.*(A_+B_.*x_^q_)*(a_.*x_^j_.+b_.*x_^k_.+c_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^j+b*x^k+c*x^n)^p/(x^(j*p)*(a+b*x^(k-j)+c*x^(2*(k-j)))^p)*
    Int[x^(m+j*p)*(A+B*x^(k-j))*(a+b*x^(k-j)+c*x^(2*(k-j)))^p,x] /;
FreeQ[{a,b,c,A,B,j,k,m,p},x] && ZeroQ[q-(k-j)] && ZeroQ[n-(2*k-j)] && Not[IntegerQ[p]] && PosQ[k-j]


Int[y_^m_.*(A_+B_.*u_^j_.)*(a_.*v_^q_.+b_.*w_^n_.+c_.*z_^r_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[x^m*(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,A,B,m,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z] && ZeroQ[u-y] && 
  LinearQ[u,x] && NonzeroQ[u-x]


Int[x_^m_.*z_*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[z,x]*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p},x] && BinomialQ[z,x] && GeneralizedTrinomialQ[u,x] && 
  ZeroQ[BinomialDegree[z,x]-GeneralizedTrinomialDegree[u,x]] && Not[BinomialMatchQ[z,x] && GeneralizedTrinomialMatchQ[u,x]]
