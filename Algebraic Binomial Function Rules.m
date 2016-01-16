(* ::Package:: *)

(* ::Section:: *)
(*Algebraic Binomial Function Rules*)


(* ::Subsection::Closed:: *)
(*2.1.1 (a+b x)^m*)


Int[1/x_,x_Symbol] :=
  Log[x]


Int[x_^m_.,x_Symbol] :=
  x^(m+1)/(m+1) /;
FreeQ[m,x] && NonzeroQ[m+1]


Int[1/(a_+b_.*x_),x_Symbol] :=
  Log[RemoveContent[a+b*x,x]]/b /;
FreeQ[{a,b},x]


Int[(a_.+b_.*x_)^m_,x_Symbol] :=
  (a+b*x)^(m+1)/(b*(m+1)) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]


Int[(a_.+b_.*u_)^m_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m,x],x,u] /;
FreeQ[{a,b,m},x] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^m_,x_Symbol] :=
  Int[ExpandToSum[u,x]^m,x] /;
FreeQ[m,x] && LinearQ[u,x] && Not[LinearMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*2.1.2 (a+b x)^m (c+d x)^n*)


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  ArcCosh[b*x/a]/b /;
FreeQ[{a,b,c,d},x] && ZeroQ[b-d] && ZeroQ[a+c] && PositiveQ[a]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2/b*Subst[Int[1/Sqrt[c-a+x^2],x],x,Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && ZeroQ[b-d]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  ArcSin[(a-c+2*b*x)/(a+c)]/b /;
FreeQ[{a,b,c,d},x] && ZeroQ[b+d] && PositiveQ[a+c]


(* Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2*ArcSin[Sqrt[a+b*x]/Sqrt[a+c]]/b /;
FreeQ[{a,b,c,d},x] && ZeroQ[b+d] && PositiveQ[a+c] *)


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  2/Sqrt[b]*Subst[Int[1/Sqrt[b*c-a*d+d*x^2],x],x,Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && PositiveQ[b] && Not[PositiveQ[d] && NegativeQ[b*c-a*d]]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  2*Subst[Int[1/(b-d*x^2),x],x,Sqrt[a+b*x]/Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  -b*x*(a+b*x)^(m+1)*(c+d*x)^(n+1)/(a*(m+1)*(b*c-a*d)) /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[m+n+3] && ZeroQ[a*d*(m+1)-b*c*(m+2)]


Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m-n] && ZeroQ[b*c+a*d] && (IntegerQ[m] || PositiveQ[a] && PositiveQ[c])


Int[(c_.+d_.*x_)^n_./(a_.+b_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(c+d*x)^n/(a+b*x),x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && IntegerQ[n]


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  (c+d*x)^n/(b*n) + 
  (b*c-a*d)/b*Int[(c+d*x)^(n-1)/(a+b*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && Not[IntegerQ[n]] && RationalQ[n] && n>0


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)),x_Symbol] :=
  -Log[RemoveContent[a+b*x,x]]/(2*b*Rt[(b*c-a*d)/b,3]) - 
  3/(2*b*Rt[(b*c-a*d)/b,3])*Subst[Int[1/(Rt[(b*c-a*d)/b,3]-x),x],x,(c+d*x)^(1/3)] + 
  3/(2*b)*Subst[Int[1/(Rt[(b*c-a*d)/b,3]^2+Rt[(b*c-a*d)/b,3]*x+x^2),x],x,(c+d*x)^(1/3)] /;
FreeQ[{a,b,c,d},x] && PosQ[(b*c-a*d)/b]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)),x_Symbol] :=
  Log[RemoveContent[a+b*x,x]]/(2*b*Rt[-(b*c-a*d)/b,3]) - 
  3/(2*b*Rt[-(b*c-a*d)/b,3])*Subst[Int[1/(Rt[-(b*c-a*d)/b,3]+x),x],x,(c+d*x)^(1/3)] + 
  3/(2*b)*Subst[Int[1/(Rt[-(b*c-a*d)/b,3]^2-Rt[-(b*c-a*d)/b,3]*x+x^2),x],x,(c+d*x)^(1/3)] /;
FreeQ[{a,b,c,d},x] && NegQ[(b*c-a*d)/b]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  -Log[RemoveContent[a+b*x,x]]/(2*b*Rt[(b*c-a*d)/b,3]^2) - 
  3/(2*b*Rt[(b*c-a*d)/b,3]^2)*Subst[Int[1/(Rt[(b*c-a*d)/b,3]-x),x],x,(c+d*x)^(1/3)] - 
  3/(2*b*Rt[(b*c-a*d)/b,3])*Subst[Int[1/(Rt[(b*c-a*d)/b,3]^2+Rt[(b*c-a*d)/b,3]*x+x^2),x],x,(c+d*x)^(1/3)] /;
FreeQ[{a,b,c,d},x] && PosQ[(b*c-a*d)/b]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  -Log[RemoveContent[a+b*x,x]]/(2*b*Rt[-(b*c-a*d)/b,3]^2) + 
  3/(2*b*Rt[-(b*c-a*d)/b,3]^2)*Subst[Int[1/(Rt[-(b*c-a*d)/b,3]+x),x],x,(c+d*x)^(1/3)] + 
  3/(2*b*Rt[-(b*c-a*d)/b,3])*Subst[Int[1/(Rt[-(b*c-a*d)/b,3]^2-Rt[-(b*c-a*d)/b,3]*x+x^2),x],x,(c+d*x)^(1/3)] /;
FreeQ[{a,b,c,d},x] && NegQ[(b*c-a*d)/b]


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  Module[{p=Denominator[n]},
  p*Subst[Int[x^(p*(n+1)-1)/(a*d-b*c+b*x^p),x],x,(c+d*x)^(1/p)]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[n] && -1<n<0


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  -(c+d*x)^(n+1)/((n+1)*(b*c-a*d)) + 
  b*(n+1)/((n+1)*(b*c-a*d))*Int[(c+d*x)^(n+1)/(a+b*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && Not[IntegerQ[n]] && RationalQ[n] && n<-1


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  -(c+d*x)^(n+1)/((n+1)*(b*c-a*d))*Hypergeometric2F1[1,n+1,n+2,(c+d*x)/(c-a*d/b)] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && Not[RationalQ[n]] && (ZeroQ[a] || ZeroQ[c])


Int[(c_+d_.*x_)^n_/(a_+b_.*x_),x_Symbol] :=
  (c+d*x)^(n+1)/(d*n*(a+b*x))*Hypergeometric2F1[1,1,1-n,-(b*c-a*d)/(d*(a+b*x))] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && Not[RationalQ[n]]


Int[(a_.+b_.*x_)^m_.*(c_+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[m+n+2] && NonzeroQ[m+1]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  Int[(a*c-b*(a-c)*x-b^2*x^2)^m,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[m-n] && FractionQ[m] && ZeroQ[b+d] && PositiveQ[a+c]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[m] && 
  (Not[IntegerQ[n]] || ZeroQ[c] && 7*m+4*n<=0 || 9*m+5*(n+1)<0 || m+n+2>0)


Int[(a_+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[m] && IntegerQ[n] && Not[PositiveIntegerQ[n] && m+n+2<0]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+1)) - 
  d*n/(b*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && NonzeroQ[m+n+2] && RationalQ[m,n] && m<-1 && n>0 && 
  Not[IntegerQ[n] && Not[IntegerQ[m]]] && 
  Not[IntegerQ[m+n] && m+n+2<=0 && (FractionQ[m] || 2*n+m+1>=0)]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) + 
  (n*(b*c-a*d))/(b*(m+n+1))*Int[(a+b*x)^m*(c+d*x)^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && m+n+2!=0 && n>0 && m+n+1!=0 && 
  Not[PositiveIntegerQ[m] && (Not[IntegerQ[n]] || 0<m<n)] && 
  Not[IntegerQ[m+n] && m+n+2<0]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) + 
  (n*(b*c-a*d))/(b*(m+n+1))*Int[(a+b*x)^m*(c+d*x)^Simplify[n-1],x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[Simplify[m+n+1]] && SumSimplerQ[n,-1] && Not[RationalQ[m]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) - 
  d*(m+n+2)/((b*c-a*d)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && m+n+2!=0 && m<-1 && 
  Not[n<-1 && (ZeroQ[a] || NonzeroQ[c] && m<n && IntegerQ[n])]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) - 
  d*(m+n+2)/((b*c-a*d)*(m+1))*Int[(a+b*x)^Simplify[m+1]*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[Simplify[m+n+2]] && SumSimplerQ[m,1] && Not[RationalQ[m]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^n/(a*c+b*d*x^2)^m*Int[(a*c+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m-n] && ZeroQ[b*c+a*d] && Not[IntegerQ[m]]


Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  -Sqrt[3]/(Rt[b,3]*Rt[d,3]^2)*ArcTan[1/Sqrt[3]*(1+2*Rt[d,3]*(a+b*x)^(1/3)/(Rt[b,3]*(c+d*x)^(1/3)))] - 
  3/(2*Rt[b,3]*Rt[d,3]^2)*Log[Rt[d,3]*(a+b*x)^(1/3)-Rt[b,3]*(c+d*x)^(1/3)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && PosQ[b] && PosQ[d]


Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  -Sqrt[3]/(Rt[b,3]*Rt[-d,3]^2)*ArcTan[1/Sqrt[3]*(1-2*Rt[-d,3]*(a+b*x)^(1/3)/(Rt[b,3]*(c+d*x)^(1/3)))] - 
  3/(2*Rt[b,3]*Rt[-d,3]^2)*Log[Rt[-d,3]*(a+b*x)^(1/3)+Rt[b,3]*(c+d*x)^(1/3)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && PosQ[b] && NegQ[d]


Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  Sqrt[3]/(Rt[-b,3]*Rt[d,3]^2)*ArcTan[1/Sqrt[3]*(1-2*Rt[d,3]*(a+b*x)^(1/3)/(Rt[-b,3]*(c+d*x)^(1/3)))] + 
  3/(2*Rt[-b,3]*Rt[d,3]^2)*Log[Rt[d,3]*(a+b*x)^(1/3)+Rt[-b,3]*(c+d*x)^(1/3)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && NegQ[b] && PosQ[d]


Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  Sqrt[3]/(Rt[-b,3]*Rt[-d,3]^2)*ArcTan[1/Sqrt[3]*(1+2*Rt[-d,3]*(a+b*x)^(1/3)/(Rt[-b,3]*(c+d*x)^(1/3)))] + 
  3/(2*Rt[-b,3]*Rt[-d,3]^2)*Log[Rt[-d,3]*(a+b*x)^(1/3)-Rt[-b,3]*(c+d*x)^(1/3)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && NegQ[b] && NegQ[d]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  Module[{p=Denominator[m]},
  p*Subst[Int[x^(p*(m+1)-1)/(b-d*x^p),x],x,(a+b*x)^(1/p)/(c+d*x)^(1/p)]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && -1<m<0 && m+n+1==0


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  Module[{p=Denominator[m]},
  p/b*Subst[Int[x^(p*(m+1)-1)*(c-a*d/b+d*x^p/b)^n,x],x,(a+b*x)^(1/p)]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && -1<m<0 && -1<n<0 && Denominator[n]<=Denominator[m]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^(n+1)/(d*(m+n+1))*Hypergeometric2F1[1,-m,-m-n,-(b*c-a*d)/(d*(a+b*x))] /;
(*(a+b*x)^m*(c+d*x)^(n+1)/(d*(m+n+1)*(d*(a+b*x)/(b*(c+d*x)))^m)*Hypergeometric2F1[-m,-m-n-1,-m-n,(b*c-a*d)/(b*(c+d*x))] /; *)
FreeQ[{a,b,c,d,m},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[n+1] && Not[PositiveIntegerQ[m+n+2]]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  (a-b*c/d)^m*(c+d*x)^(n+1)/(d*(n+1))*Hypergeometric2F1[-m,n+1,n+2,TogetherSimplify[(c+d*x)/(c-a*d/b)]] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && Not[NegativeIntegerQ[n]] && (IntegerQ[m] || PositiveQ[a-b*c/d])


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^(n+1)/(d*(n+1)*(-d*(a+b*x)/(b*c-a*d))^m)*Hypergeometric2F1[-m,n+1,n+2,TogetherSimplify[b*(c+d*x)/(b*c-a*d)]] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && Not[NegativeIntegerQ[n]] && 
  (PositiveIntegerQ[Simplify[m+n+2]] || FractionQ[Simplify[m+n]] || Not[RationalQ[m]] && Not[IntegerQ[n]])


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  -(a+b*x)^(m+1)*(c+d*x)^(n+1)/((n+1)*(b*c-a*d))*Hypergeometric2F1[1,m+n+2,n+2,TogetherSimplify[b*(c+d*x)/(b*c-a*d)]] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && Not[NegativeIntegerQ[n]] && Not[NegativeIntegerQ[m+n+1]]


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*v_)^n_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n,x],x,u] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[u-v] && LinearQ[u,x] && NonzeroQ[Coefficient[u,x,0]]


Int[u_^m_.*v_^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n,x] /;
FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


(* ::Subsection::Closed:: *)
(*2.1.3 (a+b x)^m (c+d x)^n (e+f x)^p*)


Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[b*c+a*d] && ZeroQ[m-n] && 
  (IntegerQ[m] || ZeroQ[e] && PositiveQ[a] && PositiveQ[c] && Not[RationalQ[m]])


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+2)) /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  ZeroQ[a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1))] && NonzeroQ[n+p+2]


Int[(a_+b_.*x_)*(d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)*(d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && PositiveIntegerQ[p] && (NonzeroQ[n+1] || p==1) &&
  (Not[IntegerQ[n]] || 9*p+5*n<0 || n+p+1>=0 || n+p+2>=0 && RationalQ[a,b,d,e,f])


Int[(a_.+b_.*x_)*(c_+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && 
  (NegativeIntegerQ[n,p] || ZeroQ[p-1] || 
    PositiveIntegerQ[p] && (Not[IntegerQ[n]] || 9*p+5*(n+2)<=0 || n+p+1>=0 || n+p+2>=0 && RationalQ[a,b,c,d,e,f]))


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) - 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(f*(p+1)*(c*f-d*e))*Int[(c+d*x)^n*(e+f*x)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[p] && p<-1 && 
  (Not[RationalQ[n] && n<-1] || IntegerQ[p] || Not[IntegerQ[n] || Not[ZeroQ[e] || Not[ZeroQ[c] || p<n]]])


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) - 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(f*(p+1)*(c*f-d*e))*Int[(c+d*x)^n*(e+f*x)^Simplify[p+1],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  Not[RationalQ[p]] && SumSimplerQ[p,1]


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+2)) + 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(d*f*(n+p+2))*Int[(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && NonzeroQ[n+p+2]


Int[(e_.+f_.*x_)^p_./((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^p/((a+b*x)*(c+d*x)),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && IntegerQ[p]


Int[(e_.+f_.*x_)^p_./((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)/(a+b*x),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && RationalQ[p] && 0<p<1


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  f*(e+f*x)^(p-1)/(b*d*(p-1)) + 
 1/(b*d)*Int[(b*d*e^2-a*c*f^2+f*(2*b*d*e-b*c*f-a*d*f)*x)*(e+f*x)^(p-2)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && RationalQ[p] && p>1


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  f*(e+f*x)^(p+1)/((p+1)*(b*e-a*f)*(d*e-c*f)) + 
  1/((b*e-a*f)*(d*e-c*f))*Int[(b*d*e-b*c*f-a*d*f-b*d*f*x)*(e+f*x)^(p+1)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && RationalQ[p] && p<-1


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  b/(b*c-a*d)*Int[(e+f*x)^p/(a+b*x),x] - 
  d/(b*c-a*d)*Int[(e+f*x)^p/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && Not[IntegerQ[p]]


Int[(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_/(a_.+b_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^FractionalPart[p],((c+d*x)^n*(e+f*x)^IntegerPart[p])/(a+b*x),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  PositiveIntegerQ[n] && FractionQ[p] && p<-1


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && IntegersQ[m,n] && 
  (IntegerQ[p] || m>0 && n>=-1)


Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (b*c-a*d)^2*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d^2*(d*e-c*f)*(n+1)) - 
  1/(d^2*(d*e-c*f)*(n+1))*Int[(c+d*x)^(n+1)*(e+f*x)^p*
    Simp[a^2*d^2*f*(n+p+2)+b^2*c*(d*e*(n+1)+c*f*(p+1))-2*a*b*d*(d*e*(n+1)+c*f*(p+1))-b^2*d*(d*e-c*f)*(n+1)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  (RationalQ[n] && n<-1 || ZeroQ[n+p+3] && NonzeroQ[n+1] && (SumSimplerQ[n,1] || Not[SumSimplerQ[p,1]]))


Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+3)) + 
  1/(d*f*(n+p+3))*Int[(c+d*x)^n*(e+f*x)^p*
    Simp[a^2*d*f*(n+p+3)-b*(b*c*e+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(n+p+4)-b*(d*e*(n+2)+c*f*(p+2)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && NonzeroQ[n+p+3]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(2/3)),x_Symbol] :=
  -Log[a+b*x]/(2*Rt[b*c-a*d,3]*Rt[b*e-a*f,3]^2) + 
  Sqrt[3]/(Rt[b*c-a*d,3]*Rt[b*e-a*f,3]^2)*ArcTan[1/Sqrt[3]*(1+2*Rt[b*e-a*f,3]*(c+d*x)^(1/3)/(Rt[b*c-a*d,3]*(e+f*x)^(1/3)))] + 
  3/(2*Rt[b*c-a*d,3]*Rt[b*e-a*f,3]^2)*Log[Rt[b*e-a*f,3]*(c+d*x)^(1/3)-Rt[b*c-a*d,3]*(e+f*x)^(1/3)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && PosQ[b*c-a*d] && PosQ[b*e-a*f]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(2/3)),x_Symbol] :=
  -Log[a+b*x]/(2*Rt[b*c-a*d,3]*Rt[-(b*e-a*f),3]^2) + 
  Sqrt[3]/(Rt[b*c-a*d,3]*Rt[-(b*e-a*f),3]^2)*ArcTan[1/Sqrt[3]*(1-2*Rt[-(b*e-a*f),3]*(c+d*x)^(1/3)/(Rt[b*c-a*d,3]*(e+f*x)^(1/3)))] + 
  3/(2*Rt[b*c-a*d,3]*Rt[-(b*e-a*f),3]^2)*Log[Rt[-(b*e-a*f),3]*(c+d*x)^(1/3)+Rt[b*c-a*d,3]*(e+f*x)^(1/3)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && PosQ[b*c-a*d] && NegQ[b*e-a*f]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(2/3)),x_Symbol] :=
  Log[a+b*x]/(2*Rt[-(b*c-a*d),3]*Rt[b*e-a*f,3]^2) - 
  Sqrt[3]/(Rt[-(b*c-a*d),3]*Rt[b*e-a*f,3]^2)*ArcTan[1/Sqrt[3]*(1-2*Rt[b*e-a*f,3]*(c+d*x)^(1/3)/(Rt[-(b*c-a*d),3]*(e+f*x)^(1/3)))] - 
  3/(2*Rt[-(b*c-a*d),3]*Rt[b*e-a*f,3]^2)*Log[Rt[b*e-a*f,3]*(c+d*x)^(1/3)+Rt[-(b*c-a*d),3]*(e+f*x)^(1/3)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && NegQ[b*c-a*d] && PosQ[b*e-a*f]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(2/3)),x_Symbol] :=
  Log[a+b*x]/(2*Rt[-(b*c-a*d),3]*Rt[-(b*e-a*f),3]^2) - 
  Sqrt[3]/(Rt[-(b*c-a*d),3]*Rt[-(b*e-a*f),3]^2)*
    ArcTan[1/Sqrt[3]*(1+2*Rt[-(b*e-a*f),3]*(c+d*x)^(1/3)/((-(b*c-a*d))^(1/3)*(e+f*x)^(1/3)))] - 
  3/(2*Rt[-(b*c-a*d),3]*Rt[-(b*e-a*f),3]^2)*Log[Rt[-(b*e-a*f),3]*(c+d*x)^(1/3)-(-(b*c-a*d))^(1/3)*(e+f*x)^(1/3)] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && NegQ[b*c-a*d] && NegQ[b*e-a*f]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_),x_Symbol] :=
  Module[{q=Denominator[m]},
  q*Subst[Int[x^(q*(m+1)-1)/(b*e-a*f-(d*e-c*f)*x^q),x],x,(a+b*x)^(1/q)/(c+d*x)^(1/q)]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && ZeroQ[m+n+1] && RationalQ[m,n] && -1<m<0 && 
  SimplerQ[a+b*x,c+d*x]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((m+1)*(b*e-a*f)) - 
  n*(d*e-c*f)/((m+1)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && ZeroQ[m+n+p+2] && 
  RationalQ[n] && n>0 && Not[SumSimplerQ[p,1] && Not[SumSimplerQ[m,1]]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_,x_Symbol] :=
  (b*c-a*d)^n*(a+b*x)^(m+1)/((m+1)*(b*e-a*f)^(n+1)*(e+f*x)^(m+1))*
    Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  ZeroQ[m+n+p+2] && NegativeIntegerQ[n]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((b*e-a*f)*(m+1))*((b*e-a*f)*(c+d*x)/((b*c-a*d)*(e+f*x)))^(-n)*
    Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  ZeroQ[m+n+p+2] && Not[IntegerQ[n]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && ZeroQ[Simplify[m+n+p+3]] && 
  ZeroQ[a*d*f*(m+1)+b*c*f*(n+1)+b*d*e*(p+1)] && NonzeroQ[m+1]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  (a*d*f*(m+1)+b*c*f*(n+1)+b*d*e*(p+1))/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && ZeroQ[Simplify[m+n+p+3]] && 
  (RationalQ[m] && m<-1 || SumSimplerQ[m,1])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p/(b*(m+1)) - 
  1/(b*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^(p-1)*Simp[d*e*n+c*f*p+d*f*(n+p)*x,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m,n,p] && m<-1 && n>0 && p>0 && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (b*c-a*d)*(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) + 
  1/(b*(b*e-a*f)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-2)*(e+f*x)^p*
    Simp[a*d*(d*e*(n-1)+c*f*(p+1))+b*c*(d*e*(m-n+2)-c*f*(m+p+2))+d*(a*d*f*(n+p)+b*(d*e*(m+1)-c*f*(m+n+p+1)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m,n,p] && m<-1 && n>1 && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((m+1)*(b*e-a*f)) - 
  1/((m+1)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[d*e*n+c*f*(m+p+2)+d*f*(m+n+p+2)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m,n,p] && m<-1 && n>0 && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^n*(e+f*x)^(p+1)/(f*(m+n+p+1)) - 
  1/(f*(m+n+p+1))*Int[(a+b*x)^(m-1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[c*m*(b*e-a*f)+a*n*(d*e-c*f)+(d*m*(b*e-a*f)+b*n*(d*e-c*f))*x,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m,n,p] && m>0 && n>0 && NonzeroQ[m+n+p+1] && (IntegersQ[2*m,2*n,2*p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+1)) + 
  1/(d*f*(m+n+p+1))*Int[(a+b*x)^(m-2)*(c+d*x)^n*(e+f*x)^p*
    Simp[a^2*d*f*(m+n+p+1)-b*(b*c*e*(m-1)+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(2*m+n+p)-b*(d*e*(m+n)+c*f*(m+p)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m] && m>1 && NonzeroQ[m+n+p+1] && (IntegerQ[m] || IntegersQ[2*m,2*n,2*p] || NegativeIntegerQ[m+n+p+1])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  NegativeIntegerQ[m+n+p+2] && Not[RationalQ[m]] && SumSimplerQ[m,1]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m] && m<-1 && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n] || IntegersQ[m,n+p])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_),x_Symbol] :=
  b/f*Int[(a+b*x)^(m-1)*(c+d*x)^n,x] - (b*e-a*f)/f*Int[(a+b*x)^(m-1)*(c+d*x)^n/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && PositiveIntegerQ[Simplify[m+n+1]] && 
  (RationalQ[m] && m>0 || Not[RationalQ[m]] && (SumSimplerQ[m,-1] || Not[SumSimplerQ[n,-1]]))


(* Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  b/f*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^(p+1),x] - (b*e-a*f)/f*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && NegativeIntegerQ[p] && 
  PositiveIntegerQ[m+n+p+2] && Not[SimplerQ[c+d*x,a+b*x]] *)


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(1/4)),x_Symbol] :=
  2*Rt[(d*e-c*f)/d,4]^3*Sqrt[-f*(c+d*x)/(d*e-c*f)]/((b*e-a*f)*Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2]*Sqrt[c+d*x])*
   (EllipticPi[Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2],-ArcSin[(e+f*x)^(1/4)/Rt[(d*e-c*f)/d,4]],-1] - 
    EllipticPi[-Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2],-ArcSin[(e+f*x)^(1/4)/Rt[(d*e-c*f)/d,4]],-1]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f]


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(3/4)),x_Symbol] :=
  2*Rt[(d*e-c*f)/d,4]*Sqrt[-f*(c+d*x)/(d*e-c*f)]/((b*e-a*f)*Sqrt[c+d*x])*
    (EllipticPi[-Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2],-ArcSin[(e+f*x)^(1/4)/Rt[(d*e-c*f)/d,4]],-1] + 
     EllipticPi[Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2],-ArcSin[(e+f*x)^(1/4)/Rt[(d*e-c*f)/d,4]],-1]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2*Sqrt[e]/b*Rt[-b/d,2]*EllipticE[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && PositiveQ[c] && PositiveQ[e] && Not[NegativeQ[-b/d]]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[-b*x]/Sqrt[b*x]*Int[Sqrt[e+f*x]/(Sqrt[-b*x]*Sqrt[c+d*x]),x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && PositiveQ[c] && PositiveQ[e] && NegativeQ[-b/d]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[e+f*x]*Sqrt[(c+d*x)/c]/(Sqrt[c+d*x]*Sqrt[(e+f*x)/e])*Int[Sqrt[1+f*x/e]/(Sqrt[b*x]*Sqrt[1+d*x/c]),x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && Not[PositiveQ[c] && PositiveQ[e]]


Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2/b*Rt[-(b*c-a*d)/d,2]*Sqrt[(b*e-a*f)/(b*c-a*d)]*
    EllipticE[ArcSin[Sqrt[a+b*x]/Rt[-(b*c-a*d)/d,2]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)] && Not[NegativeQ[-(b*c-a*d)/d]] && SimplerQ[a+b*x,c+d*x]


Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[-a-b*x]/Sqrt[a+b*x]*Int[Sqrt[e+f*x]/(Sqrt[-a-b*x]*Sqrt[c+d*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)] && NegativeQ[-(b*c-a*d)/d] && SimplerQ[a+b*x,c+d*x]


(* Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  f/b*Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]),x] - 
  f/b*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && ZeroQ[b*e-f*(a-1)] *)


Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[e+f*x]*Sqrt[b*(c+d*x)/(b*c-a*d)]/(Sqrt[c+d*x]*Sqrt[b*(e+f*x)/(b*e-a*f)])*
    Int[Sqrt[Simp[b*e/(b*e-a*f)+b*f*x/(b*e-a*f),x]]/(Sqrt[a+b*x]*Sqrt[Simp[b*c/(b*c-a*d)+b*d*x/(b*c-a*d),x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  Not[PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)]] && SimplerQ[a+b*x,c+d*x]


Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  2/(b*Sqrt[e])*Rt[-b/d,2]*EllipticF[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && PositiveQ[c] && PositiveQ[e] && Not[NegativeQ[-b/d]]


Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  Sqrt[-b*x]/Sqrt[b*x]*Int[1/(Sqrt[-b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && PositiveQ[c] && PositiveQ[e] && NegativeQ[-b/d]


Int[1/(Sqrt[b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]),x_Symbol] :=
  Sqrt[(c+d*x)/c]*Sqrt[(e+f*x)/e]/(Sqrt[c+d*x]*Sqrt[e+f*x])*Int[1/(Sqrt[b*x]*Sqrt[1+d*x/c]*Sqrt[1+f*x/e]),x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && Not[PositiveQ[c] && PositiveQ[e]]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  2/b*Rt[-(b*c-a*d)/d,2]*Sqrt[b^2/((b*c-a*d)*(b*e-a*f))]*
    EllipticF[ArcSin[Sqrt[a+b*x]/Rt[-(b*c-a*d)/d,2]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && PositiveQ[b/(b*c-a*d)] && 
  PositiveQ[b/(b*e-a*f)] && Not[NegativeQ[-(b*c-a*d)/d]] && SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  Sqrt[-a-b*x]/Sqrt[a+b*x]*Int[1/(Sqrt[-a-b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)] && NegativeQ[-(b*c-a*d)/d] && SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  Sqrt[b*(c+d*x)/(b*c-a*d)]*Sqrt[b*(e+f*x)/(b*e-a*f)]/(Sqrt[c+d*x]*Sqrt[e+f*x])*
    Int[1/(Sqrt[a+b*x]*Sqrt[Simp[b*c/(b*c-a*d)+b*d*x/(b*c-a*d),x]]*Sqrt[Simp[b*e/(b*e-a*f)+b*f*x/(b*e-a*f),x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  Not[PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)]] && SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m*(f*x)^p,x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && ZeroQ[b*c+a*d] && ZeroQ[m-n] && PositiveQ[a] && PositiveQ[c]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^m/(a*c+b*d*x^2)^m*Int[(a*c+b*d*x^2)^m*(f*x)^p,x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && ZeroQ[b*c+a*d] && ZeroQ[m-n]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
   Int[ExpandIntegrand[(a+b*x)^n*(c+d*x)^n*(f*x)^p,(a+b*x)^(m-n),x],x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && ZeroQ[b*c+a*d] && PositiveIntegerQ[m-n]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && NegativeIntegerQ[m,n]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  NegativeIntegerQ[m+n+p+2] && NonzeroQ[m+1] && 
  (SumSimplerQ[m,1] || Not[NonzeroQ[n+1] && SumSimplerQ[n,1]] && Not[NonzeroQ[p+1] && SumSimplerQ[p,1]])


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p/(b*(m+1)*(b*(c+d*x)/(b*c-a*d))^n*(b*(e+f*x)/(b*e-a*f))^p)*
    AppellF1[m+1,-n,-p,m+2,-(d*(a+b*x)/(b*c-a*d)),-(f*(a+b*x)/(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  Not[NegativeIntegerQ[m]] && Not[PositiveIntegerQ[p+1]] && Not[ZeroQ[c] && Not[NegativeIntegerQ[n]]]


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*v_)^n_.*(e_+f_.*w_)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
FreeQ[{m,n,p},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


(* ::Subsection::Closed:: *)
(*2.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q*)


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(A_.+B_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(A+B*x),x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  (IntegersQ[m,n,p] || PositiveIntegerQ[n,p])


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_.*(A_.+B_.*x_),x_Symbol] :=
  -(B*c-A*d)*(a+b*x)^m*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*(n+1)*(d*e-c*f)) + 
  1/(d*(n+1)*(d*e-c*f))*Int[(a+b*x)^(m-1)*(c+d*x)^(n+1)*(e+f*x)^p*
    Simp[a*d*(B*e-A*f)*(n+1)+(B*c-A*d)*(b*e*m+a*f*(p+1))+b*(d*(B*e-A*f)*(n+1)+f*(B*c-A*d)*(m+p+1))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m,n] && m>0 && n<-1 && Not[m==1 && SimplerQ[A+B*x,a+b*x]]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(A_.+B_.*x_),x_Symbol] :=
  B*(a+b*x)^m*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+2)) + 
  1/(d*f*(m+n+p+2))*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*A*d*f*(m+n+p+2)-B*(b*c*e*m+a*(d*e*(n+1)+c*f*(p+1)))+(A*b*d*f*(m+n+p+2)+B*(a*d*f*m-b*(d*e*(m+n+1)+c*f*(m+p+1))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m] && m>0 && NonzeroQ[m+n+p+2] && Not[m==1 && SimplerQ[A+B*x,a+b*x]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(A_.+B_.*x_),x_Symbol] :=
  (A*b-a*B)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[(b*B*c*e+A*(a*d*f-b*(d*e+c*f)))*(m+1)-(A*b-a*B)*(d*e*(n+1)+c*f*(p+1))-d*f*(A*b-a*B)*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,A,B,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m] && m<-1


Int[(e_.+f_.*x_)^p_*(A_.+B_.*x_)/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  (A*b-a*B)/(b*c-a*d)*Int[(e+f*x)^p/(a+b*x),x] + 
  (B*c-A*d)/(b*c-a*d)*Int[(e+f*x)^p/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f]


Int[(A_.+B_.*x_)/(Sqrt[a_.+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  B/f*Int[Sqrt[e+f*x]/(Sqrt[a+b*x]*Sqrt[c+d*x]),x] - (B*e-A*f)/f*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  SimplerQ[a+b*x,e+f*x] && SimplerQ[c+d*x,e+f*x]


Int[(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(A_.+B_.*x_)/(a_.+b_.*x_),x_Symbol] :=
  B/b*Int[(c+d*x)^n*(e+f*x)^p,x] + (A*b-a*B)/b*Int[(c+d*x)^n*(e+f*x)^p/(a+b*x),x] /;
FreeQ[{a,b,c,d,e,f,A,B,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_*(A_.+B_.*x_),x_Symbol] :=
  B/b*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] + (A*b-a*B)/b*Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,A,B,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]] && Not[SumSimplerQ[p,1]])


Int[(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)*(g+h*x)^q/(a+b*x),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)*(g+h*x)^q/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,q},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[b*g-a*h] && NonzeroQ[d*e-c*f] && 
  NonzeroQ[d*g-c*h] && NonzeroQ[f*g-e*h] && RationalQ[p] && 0<p<1


Int[Sqrt[a_.+b_.*x_]/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*(f*g-e*h)*(a+b*x)^(3/2)*Sqrt[(b*g-a*h)*(c+d*x)/((d*g-c*h)*(a+b*x))]*Sqrt[-(b*e-a*f)*(b*g-a*h)*(e+f*x)*(g+h*x)/((f*g-e*h)^2*(a+b*x)^2)]/
    (h*(b*e-a*f)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
    EllipticPi[-b*(f*g-e*h)/((b*e-a*f)*h),ArcSin[Sqrt[-(b*e-a*f)*(g+h*x)/((f*g-e*h)*(a+b*x))]],(b*c-a*d)*(f*g-e*h)/((b*e-a*f)*(d*g-c*h))] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[b*g-a*h] && NonzeroQ[d*e-c*f] && 
  NonzeroQ[d*g-c*h] && NonzeroQ[f*g-e*h]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*Sqrt[a+b*x]*Sqrt[g+h*x]*Sqrt[(b*g-a*h)*(c+d*x)/((d*g-c*h)*(a+b*x))]*Sqrt[(b*g-a*h)*(e+f*x)/((f*g-e*h)*(a+b*x))]/
    ((b*g-a*h)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[-(b*e-a*f)*(g+h*x)/((f*g-e*h)*(a+b*x))])*
    EllipticF[ArcSin[Sqrt[-(b*e-a*f)*(g+h*x)/((f*g-e*h)*(a+b*x))]],(b*c-a*d)*(f*g-e*h)/((b*e-a*f)*(d*g-c*h))] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[b*g-a*h] && NonzeroQ[d*e-c*f] && 
  NonzeroQ[d*g-c*h] && NonzeroQ[f*g-e*h]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && IntegersQ[p,q]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
  Defer[Int][(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x]


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*v_)^n_.*(e_.+f_.*w_)^p_.*(g_.+h_.*z_)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x,u] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && LinearQ[u,x] && NonzeroQ[u-x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z]


Int[u_^m_.*v_^n_.*w_^p_.*z_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p*ExpandToSum[z,x]^q,x] /;
FreeQ[{m,n,p,q},x] && LinearQ[{u,v,w,z},x] && Not[LinearMatchQ[{u,v,w,z},x]]


Int[Sqrt[i_.*(a_.+b_.*x_)/((c_.+d_.*x_)*(e_.+f_.*x_)*(g_.+h_.*x_))],x_Symbol] :=
  Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/Sqrt[a+b*x]*Sqrt[i*(a+b*x)/((c+d*x)*(e+f*x)*(g+h*x))]*
    Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i},x]


Int[Sqrt[i_./((a_.+b_.*x_)*(c_.+d_.*x_)*(e_.+f_.*x_)*(g_.+h_.*x_))],x_Symbol] :=
  Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]*Sqrt[i/((a+b*x)*(c+d*x)*(e+f*x)*(g+h*x))]*
    Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i},x]


(* ::Subsection::Closed:: *)
(*2.2.1 (a+b x^n)^p*)


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*(a+b*x^n)^(p+1)/a /;
FreeQ[{a,b,n,p},x] && ZeroQ[n*(p+1)+1]


Int[(a_+b_.*x_^n_)^2,x_Symbol] :=
  Int[a^2+2*a*b*x^n+b^2*x^(2*n),x] /;
FreeQ[{a,b,n},x] && NonzeroQ[3*n+1]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[x^(n*p)*(b+a*x^(-n))^p,x] /;
FreeQ[{a,b},x] && RationalQ[n] && n<0 && IntegerQ[p]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^p,x],x] /;
FreeQ[{a,b},x] && NonzeroQ[n*(p+1)+1] && PositiveIntegerQ[n,p]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*(a+b*x^n)^p/(n*p+1) +
  a*n*p/(n*p+1)*Int[(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && NonzeroQ[n*(p+1)+1] && PositiveIntegerQ[n] && RationalQ[p] && p>0 && (IntegerQ[2*p] || IntegerQ[p+1/n])


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -x*(a+b*x^n)^(p+1)/(a*n*(p+1)) +
  (n*(p+1)+1)/(a*n*(p+1))*Int[(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && NonzeroQ[n*(p+1)+1] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && (IntegerQ[2*p] || IntegerQ[p+1/n])


Int[1/(a_+b_.*x_^3),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  r/(3*a)*Int[1/(r+s*x),x] +
  r/(3*a)*Int[(2*r-s*x)/(r^2-r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b},x] && PosQ[a/b]


Int[1/(a_+b_.*x_^3),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r/(3*a)*Int[1/(r-s*x),x] +
  r/(3*a)*Int[(2*r+s*x)/(r^2+r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b},x] && NegQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
  u=Int[(r-s*Cos[(2*k-1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  r/(a*n)*Int[1/(r+s*x),x] + Dist[2*r/(a*n),Sum[u,{k,1,(n-1)/2}],x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[(n-3)/2] && PosQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
  u=Int[(r+s*Cos[(2*k-1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  r/(a*n)*Int[1/(r-s*x),x] + Dist[2*r/(a*n),Sum[u,{k,1,(n-1)/2}],x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[(n-3)/2] && NegQ[a/b]


Int[1/(a_+b_.*x_^2),x_Symbol] :=
(*Rt[b/a,2]/b*ArcTan[Rt[b/a,2]*x] /; *)
  Rt[a/b,2]/a*ArcTan[x/Rt[a/b,2]] /;
FreeQ[{a,b},x] && PosQ[a/b]


Int[1/(a_+b_.*x_^2),x_Symbol] :=
(*-Rt[-b/a,2]/b*ArcTanh[Rt[-b/a,2]*x] /; *)
  Rt[-a/b,2]/a*ArcTanh[x/Rt[-a/b,2]] /;
FreeQ[{a,b},x] && NegQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u, v},
  u=Int[(r-s*Cos[(2*k-1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x] + 
    Int[(r+s*Cos[(2*k-1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  2*r^2/(a*n)*Int[1/(r^2+s^2*x^2),x] + Dist[2*r/(a*n),Sum[u,{k,1,(n-2)/4}],x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[(n-2)/4] && PosQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
  u=Int[(r-s*Cos[(2*k*Pi)/n]*x)/(r^2-2*r*s*Cos[(2*k*Pi)/n]*x+s^2*x^2),x] + 
    Int[(r+s*Cos[(2*k*Pi)/n]*x)/(r^2+2*r*s*Cos[(2*k*Pi)/n]*x+s^2*x^2),x];
  2*r^2/(a*n)*Int[1/(r^2-s^2*x^2),x] + Dist[2*r/(a*n),Sum[u,{k,1,(n-2)/4}],x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[(n-2)/4] && NegQ[a/b]


Int[1/(a_+b_.*x_^4),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,2]], s=Denominator[Rt[a/b,2]]},
  1/(2*r)*Int[(r-s*x^2)/(a+b*x^4),x] +
  1/(2*r)*Int[(r+s*x^2)/(a+b*x^4),x]] /;
FreeQ[{a,b},x] && (PositiveQ[a/b] || PosQ[a/b] && NonsumQ[a] && NonsumQ[b])


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,4]], s=Denominator[Rt[a/b,4]]},
  r/(2*Sqrt[2]*a)*Int[(Sqrt[2]*r-s*x^(n/4))/(r^2-Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x] +
  r/(2*Sqrt[2]*a)*Int[(Sqrt[2]*r+s*x^(n/4))/(r^2+Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[n/4] && n>4 && PositiveQ[a/b]


Int[1/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  r/(2*a)*Int[1/(r-s*x^(n/2)),x] +
  r/(2*a)*Int[1/(r+s*x^(n/2)),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[n/4] && Not[PositiveQ[a/b]]


Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
  ArcSinh[Rt[b,2]*x/Sqrt[a]]/Rt[b,2] /;
FreeQ[{a,b},x] && PositiveQ[a] && PosQ[b]


Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
  ArcSin[Rt[-b,2]*x/Sqrt[a]]/Rt[-b,2] /;
FreeQ[{a,b},x] && PositiveQ[a] && NegQ[b]


Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
  Subst[Int[1/(1-b*x^2),x],x,x/Sqrt[a+b*x^2]] /;
FreeQ[{a,b},x] && Not[PositiveQ[a]]


Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  Sqrt[a^(1/3)+b^(1/3)*x]*
  Sqrt[a^(1/3)*Sqrt[-3*b^(2/3)]+a^(1/3)*b^(1/3)-2*b^(2/3)*x]*
  Sqrt[a^(1/3)*Sqrt[-3*b^(2/3)]-a^(1/3)*b^(1/3)+2*b^(2/3)*x]/
    Sqrt[a+b*x^3]*
    Int[1/(Sqrt[a^(1/3)+b^(1/3)*x]*
           Sqrt[a^(1/3)*Sqrt[-3*b^(2/3)]+a^(1/3)*b^(1/3)-2*b^(2/3)*x]*
           Sqrt[a^(1/3)*Sqrt[-3*b^(2/3)]-a^(1/3)*b^(1/3)+2*b^(2/3)*x]),x] /;
FreeQ[{a,b},x] && PosQ[b]


Int[1/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  Sqrt[a^(1/3)-(-b)^(1/3)*x]*
  Sqrt[a^(1/3)*Sqrt[-3*(-b)^(2/3)]-a^(1/3)*(-b)^(1/3)-2*(-b)^(2/3)*x]*
  Sqrt[a^(1/3)*Sqrt[-3*(-b)^(2/3)]+a^(1/3)*(-b)^(1/3)+2*(-b)^(2/3)*x]/
    Sqrt[a+b*x^3]*
    Int[1/(Sqrt[a^(1/3)-(-b)^(1/3)*x]*
           Sqrt[a^(1/3)*Sqrt[-3*(-b)^(2/3)]-a^(1/3)*(-b)^(1/3)-2*(-b)^(2/3)*x]*
           Sqrt[a^(1/3)*Sqrt[-3*(-b)^(2/3)]+a^(1/3)*(-b)^(1/3)+2*(-b)^(2/3)*x]),x] /;
FreeQ[{a,b},x] && NegQ[b]


Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  EllipticF[ArcSin[Rt[-b/a,4]*x],-1]/(Sqrt[a]*Rt[-b/a,4]) /;
FreeQ[{a,b},x] && PositiveQ[a]


Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  Sqrt[(a+b*x^4)/a]/Sqrt[a+b*x^4]*Int[1/Sqrt[1+b*x^4/a],x] /;
FreeQ[{a,b},x] && Not[PositiveQ[a]]


Int[1/Sqrt[a_+b_.*x_^6],x_Symbol] :=
  x*(a^(1/3)+b^(1/3)*x^2)*Sqrt[(a^(2/3)-a^(1/3)*b^(1/3)*x^2+b^(2/3)*x^4)/(a^(1/3)+(1+Sqrt[3])*b^(1/3)*x^2)^2]/
    (2*3^(1/4)*a^(1/3)*Sqrt[(b^(1/3)*x^2*(a^(1/3)+b^(1/3)*x^2))/(a^(1/3)+(1+Sqrt[3])*b^(1/3)*x^2)^2]*Sqrt[a+b*x^6])*
    EllipticF[ArcCos[(a^(1/3)-(-1+Sqrt[3])*b^(1/3)*x^2)/(a^(1/3)+(1+Sqrt[3])*b^(1/3)*x^2)],(1/4)*(2+Sqrt[3])] /;
FreeQ[{a,b},x]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Denominator[p]},
  q*a^(p+1/n)/n*Subst[Int[x^(q/n-1)/(1-b*x^q)^(p+1/n+1),x],x,x^(n/q)/(a+b*x^n)^(1/q)]] /;
FreeQ[{a,b},x] && NonzeroQ[n*(p+1)+1] && PositiveIntegerQ[n] && RationalQ[p] && -1<p<0 && p!=-1/2 && IntegerQ[p+1/n]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p/x^2,x],x,1/x] /;
FreeQ[{a,b,p},x] && NonzeroQ[n*(p+1)+1] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{d=Denominator[n]},
  d*Subst[Int[x^(d-1)*(a+b*x^(d*n))^p,x],x,x^(1/d)]] /;
FreeQ[{a,b,p},x] && NonzeroQ[n*(p+1)+1] && FractionQ[n]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,n},x] && NonzeroQ[n*(p+1)+1] && PositiveIntegerQ[p]


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  a^p*x*Hypergeometric2F1[-p,1/n,1/n+1,-b*x^n/a] /;
FreeQ[{a,b,n,p},x] && NonzeroQ[n*(p+1)+1] && Not[PositiveIntegerQ[p]] && Not[IntegerQ[1/n]] && 
  Not[NegativeIntegerQ[Simplify[1/n+p]]] && (IntegerQ[p] || PositiveQ[a])


(* Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*(a+b*x^n)^(p+1)/a*Hypergeometric2F1[1,1/n+p+1,1/n+1,-b*x^n/a] /;
FreeQ[{a,b,n,p},x] && NonzeroQ[n*(p+1)+1] && Not[PositiveIntegerQ[p]] && Not[IntegerQ[1/n]] && 
  Not[NegativeIntegerQ[Simplify[1/n+p]]] && Not[IntegerQ[p] || PositiveQ[a]] *)


Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x*(a+b*x^n)^p/((a+b*x^n)/a)^p*Hypergeometric2F1[-p,1/n,1/n+1,-b*x^n/a] /;
FreeQ[{a,b,n,p},x] && NonzeroQ[n*(p+1)+1] && Not[PositiveIntegerQ[p]] && Not[IntegerQ[1/n]] && 
  Not[NegativeIntegerQ[Simplify[1/n+p]]] && Not[IntegerQ[p] || PositiveQ[a]]


Int[(a_+b_.*u_^n_)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n)^p,x],x,u] /;
FreeQ[{a,b,n,p},x] && LinearQ[u,x] && NonzeroQ[u-x]


(* Int[u_^p_,x_Symbol] :=
  Int[NormalizePseudoBinomial[u,x]^p,x] /;
FreeQ[p,x] && PseudoBinomialQ[u,x] *)


Int[(a_.+b_.*(c_./x_)^n_)^p_,x_Symbol] :=
  -c*Subst[Int[(a+b*x^n)^p/x^2,x],x,c/x] /;
FreeQ[{a,b,c,n,p},x]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[(a_.+b_.*(c_.*x_^n_)^q_)^p_.,x_Symbol] :=
  x/(c*x^n)^(1/n)*Subst[Int[(a+b*x^(n*q))^p,x],x,(c*x^n)^(1/n)] /;
FreeQ[{a,b,c,q,n,p},x] && IntegerQ[n*q]


(* ::Subsection::Closed:: *)
(*2.2.2 (a+b x^n)^m (c+d x^n)^p*)


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  -b*x*(a+b*x^n)^(m+1)*(c+d*x^n)^(p+1)/(a*n*(m+1)*(b*c-a*d)) /;
FreeQ[{a,b,c,d,m,n,p},x] && NonzeroQ[b*c-a*d] && ZeroQ[n*(m+p+2)+1] && ZeroQ[b*c+n*(m+1)*(b*c-a*d)]


Int[(a_+b_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
  a*x/c + (b*c-a*d)/c*Int[1/(d+c*x^(-n)),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && RationalQ[n] && n<0


Int[(a_+b_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
  b*x/d - (b*c-a*d)/d*Int[1/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && Not[RationalQ[n] && n<0]


Int[(a_+b_.*x_^n_)*(c_+d_.*x_^n_)^p_.,x_Symbol] :=
  a*x*(c+d*x^n)^(p+1)/c /;
FreeQ[{a,b,c,d,n,p},x] && NonzeroQ[b*c-a*d] && ZeroQ[b*c-a*d*(n*(p+1)+1)] && NonzeroQ[p+1]


Int[(a_+b_.*x_^n_)*(c_+d_.*x_^n_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)*(c+d*x^n)^p,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*c-a*d*(n*(p+1)+1)] && PositiveIntegerQ[p]


Int[(a_+b_.*x_^n_)*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  (b*c-a*d)*x*(c+d*x^n)^(p+1)/(c*d*n*(p+1)) - 
  (b*c-a*d*(n*(p+1)+1))/(c*d*n*(p+1))*Int[(c+d*x^n)^(p+1),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*c-a*d*(n*(p+1)+1)] && 
  RationalQ[p] && p<-1


Int[(a_+b_.*x_^n_)*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  b*x*(c+d*x^n)^(p+1)/(d*(n*(p+1)+1)) - 
  (b*c-a*d*(n*(p+1)+1))/(d*(n*(p+1)+1))*Int[(c+d*x^n)^p,x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*c-a*d*(n*(p+1)+1)] && 
  Not[PositiveIntegerQ[p]] && Not[RationalQ[p] && p<-1]


Int[1/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*x^n),x] - 
  d/(b*c-a*d)*Int[1/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d]


Int[Sqrt[a_+b_.*x_^n_]/(c_+d_.*x_^n_),x_Symbol] :=
  b/d*Int[1/Sqrt[a+b*x^n],x] - 
  (b*c-a*d)/d*Int[1/(Sqrt[a+b*x^n]*(c+d*x^n)),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d]


Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Subst[Int[1/Simp[a+(b*c-a*d)*x^2,x],x],x,x/Sqrt[c+d*x^2]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[1/((a_+b_.*x_^2)*(c_+d_.*x_^2)^(1/4)),x_Symbol] :=
  c^(3/4)*Sqrt[-d*x^2/c]/((b*c-a*d)*Sqrt[b*c/(b*c-a*d)]*x)*
    (EllipticPi[Sqrt[b*c/(b*c-a*d)],-ArcSin[(c+d*x^2)^(1/4)/c^(1/4)],-1] - 
     EllipticPi[-Sqrt[b*c/(b*c-a*d)],-ArcSin[(c+d*x^2)^(1/4)/c^(1/4)],-1]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[1/((a_+b_.*x_^2)*(c_+d_.*x_^2)^(3/4)),x_Symbol] :=
  c^(1/4)*Sqrt[-d*x^2/c]/((b*c-a*d)*x)*
    (EllipticPi[Sqrt[b*c/(b*c-a*d)],-ArcSin[(c+d*x^2)^(1/4)/c^(1/4)],-1] + 
     EllipticPi[-Sqrt[b*c/(b*c-a*d)],-ArcSin[(c+d*x^2)^(1/4)/c^(1/4)],-1]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  1/(Sqrt[a]*Sqrt[c]*Rt[-d/c,2])*EllipticF[ArcSin[Rt[-d/c,2]*x],b*c/(a*d)] /;
FreeQ[{a,b,c,d},x] && PositiveQ[a] && PositiveQ[c] && Not[SimplerSqrtQ[-b/a,-d/c]]


Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
  Sqrt[(a+b*x^2)/a]*Sqrt[(c+d*x^2)/c]/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2])*Int[1/(Sqrt[1+b/a*x^2]*Sqrt[1+d/c*x^2]),x] /;
FreeQ[{a,b,c,d},x] && Not[PositiveQ[a] && PositiveQ[c]]


Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[a]/(Sqrt[c]*Rt[-d/c,2])*EllipticE[ArcSin[Rt[-d/c,2]*x],b*c/(a*d)] /;
FreeQ[{a,b,c,d},x] && PositiveQ[a] && PositiveQ[c]


Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2]*Sqrt[(c+d*x^2)/c]/(Sqrt[c+d*x^2]*Sqrt[(a+b*x^2)/a])*Int[Sqrt[1+b/a*x^2]/Sqrt[1+d/c*x^2],x] /;
FreeQ[{a,b,c,d},x] && Not[PositiveQ[a] && PositiveQ[c]]


Int[Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2],x_Symbol] :=
  x*Sqrt[a+b*x^2]*Sqrt[c+d*x^2]/3 + 
  1/3*Int[(2*a*c+(b*c+a*d)*x^2)/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[1/((a_+b_.*x_^4)*Sqrt[c_+d_.*x_^4]),x_Symbol] :=
  1/(2*a)*Int[1/((1-Rt[-b/a,2]*x^2)*Sqrt[c+d*x^4]),x] + 
  1/(2*a)*Int[1/((1+Rt[-b/a,2]*x^2)*Sqrt[c+d*x^4]),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[1/((a_+b_.*x_^4)^(1/4)*(c_+d_.*x_^4)),x_Symbol] :=
  Subst[Int[1/(c-(b*c-a*d)*x^4),x],x,x/(a+b*x^4)^(1/4)] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  Int[PolynomialDivide[(a+b*x^n)^m,(c+d*x^n)^(-p),x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n,m] && NegativeIntegerQ[p] && m>=-p


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  -x*(a+b*x^n)^(m+1)*(c+d*x^n)^p/(a*n*(m+1)) + 
  1/(a*n*(m+1))*
    Int[Simp[c*(n*(m+1)+1)+d*(n*(m+p+1)+1)*x^n,x]*(a+b*x^n)^(m+1)*(c+d*x^n)^(p-1),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && RationalQ[m,p] && m<-1 && p>0 && p<1


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  (a*d-c*b)*x*(a+b*x^n)^(m+1)*(c+d*x^n)^(p-1)/(a*b*n*(m+1)) - 
  1/(a*b*n*(m+1))*
    Int[Simp[c*(a*d-c*b*(n*(m+1)+1))+d*(a*d*(n*(p-1)+1)-b*c*(n*(m+p)+1))*x^n,x]*(a+b*x^n)^(m+1)*(c+d*x^n)^(p-2),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && RationalQ[m,p] && m<-1 && p>1


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  -b*x*(a+b*x^n)^(m+1)*(c+d*x^n)^(p+1)/(a*n*(m+1)*(b*c-a*d)) + 
  1/(a*n*(m+1)*(b*c-a*d))*
    Int[Simp[b*c+n*(m+1)*(b*c-a*d)+d*b*(n*(m+p+2)+1)*x^n,x]*(a+b*x^n)^(m+1)*(c+d*x^n)^p,x] /;
FreeQ[{a,b,c,d,n,p},x] && NonzeroQ[b*c-a*d] && RationalQ[m] && m<-1


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n)^m*(c+d*x^n)^p,x],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && IntegersQ[m,p] && m+p>0


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  d*x*(a+b*x^n)^(m+1)*(c+d*x^n)^(p-1)/(b*(n*(m+p)+1)) + 
  1/(b*(n*(m+p)+1))*
    Int[Simp[c*(b*c*(n*(m+p)+1)-a*d)+d*(b*c*(n*(m+2*p-1)+1)-a*d*(n*(p-1)+1))*x^n,x]*(a+b*x^n)^m*(c+d*x^n)^(p-2),x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p>1 && NonzeroQ[n*(m+p)+1]


Int[(c_+d_.*x_^n_)^p_/(a_+b_.*x_^n_),x_Symbol] :=
  x*(1+b*x^n/a)/((a+b*x^n)*(c+d*x^n)^(1/n))*Hypergeometric2F1[1,1/n,1+1/n,-(b*c-a*d)*x^n/(a*(c+d*x^n))] /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[p+1/n] && NonzeroQ[b*c-a*d] && NonzeroQ[n+1]


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_,x_Symbol] :=
  x*(a+b*x^n)^m*(c+d*x^n)^p/((1+b*x^n/a)^m*(1+d*x^n/c)^p)*AppellF1[1/n,-m,-p,1+1/n,-((b*x^n)/a),-((d*x^n)/c)] /;
FreeQ[{a,b,c,d,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[n+1]


Int[(a_.+b_.*u_^n_)^m_.*(c_.+d_.*v_^n_)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n)^m*(c+d*x^n)^p,x],x,u] /;
FreeQ[{a,b,c,d,m,n,p},x] && ZeroQ[u-v] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[NormalizePseudoBinomial[u,x]^m*NormalizePseudoBinomial[v,x]^p,x] /;
FreeQ[{m,p},x] && PseudoBinomialPairQ[u,v,x]


Int[u_^m_.*v_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p,x] /;
FreeQ[{m,p},x] && BinomialQ[{u,v},x] && ZeroQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && Not[BinomialMatchQ[{u,v},x]]


(* ::Subsection::Closed:: *)
(*2.2.3 (a+b x^n)^m (c+d x^n)^p (e+f x^n)^q*)


Int[(e_+f_.*x_^n_)/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[1/(a+b*x^n),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[1/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f]


Int[(e_+f_.*x_^n_)/((a_+b_.*x_^n_)*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  f/b*Int[1/Sqrt[c+d*x^n],x] + 
  (b*e-a*f)/b*Int[1/((a+b*x^n)*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f]


Int[(e_+f_.*x_^n_)/(Sqrt[a_+b_.*x_^n_]*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  f/b*Int[Sqrt[a+b*x^n]/Sqrt[c+d*x^n],x] + 
  (b*e-a*f)/b*Int[1/(Sqrt[a+b*x^n]*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && Not[n==2 && SimplerSqrtQ[-b/a,-d/c]]


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_.*(e_+f_.*x_^n_),x_Symbol] :=
  -(b*e-a*f)*x*(a+b*x^n)^(m+1)*(c+d*x^n)^p/(a*b*n*(m+1)) + 
  1/(a*b*n*(m+1))*
    Int[(a+b*x^n)^(m+1)*(c+d*x^n)^(p-1)*Simp[c*(b*e*n*(m+1)+b*e-a*f)+d*(b*e*n*(m+1)+(b*e-a*f)*(n*p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m,p] && m<-1 && p>0


Int[(a_+b_.*x_^n_)^m_.*(c_+d_.*x_^n_)^p_.*(e_+f_.*x_^n_),x_Symbol] :=
  f*x*(a+b*x^n)^(m+1)*(c+d*x^n)^p/(b*(n*(m+p+1)+1)) + 
  1/(b*(n*(m+p+1)+1))*
    Int[(a+b*x^n)^m*(c+d*x^n)^(p-1)*Simp[c*(b*e-a*f+b*e*n*(m+p+1))+(d*(b*e-a*f)+f*n*p*(b*c-a*d)+b*d*e*n*(m+p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n,m},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[p] && p>0 && NonzeroQ[n*(m+p+1)+1]


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_.*(e_+f_.*x_^n_),x_Symbol] :=
  -(b*e-a*f)*x*(a+b*x^n)^(m+1)*(c+d*x^n)^(p+1)/(a*n*(b*c-a*d)*(m+1)) + 
  1/(a*n*(b*c-a*d)*(m+1))*
    Int[(a+b*x^n)^(m+1)*(c+d*x^n)^p*Simp[c*(b*e-a*f)+e*n*(b*c-a*d)*(m+1)+d*(b*e-a*f)*(n*(m+p+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && 
  RationalQ[m] && m<-1


Int[(a_+b_.*x_^n_)^m_.*(c_+d_.*x_^n_)^p_.*(e_+f_.*x_^n_),x_Symbol] :=
  e*Int[(a+b*x^n)^m*(c+d*x^n)^p,x] + 
  f*Int[x^n*(a+b*x^n)^m*(c+d*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,n,m,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f]


Int[(c_+d_.*x_^n_)^p_.*(e_+f_.*x_^n_)^q_./(a_+b_.*x_^n_),x_Symbol] :=
  d/b*Int[(c+d*x^n)^(p-1)*(e+f*x^n)^q,x] + 
  (b*c-a*d)/b*Int[(c+d*x^n)^(p-1)*(e+f*x^n)^q/(a+b*x^n),x] /;
FreeQ[{a,b,c,d,e,f,n,q},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && RationalQ[p] && p>0


Int[1/((a_+b_.*x_^2)*(c_+d_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  b/(b*c-a*d)*Int[1/((a+b*x^2)*Sqrt[e+f*x^2]),x] - 
  d/(b*c-a*d)*Int[1/((c+d*x^2)*Sqrt[e+f*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f]


Int[1/(x_^2*(c_+d_.*x_^2)*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  1/c*Int[1/(x^2*Sqrt[e+f*x^2]),x] - 
  d/c*Int[1/((c+d*x^2)*Sqrt[e+f*x^2]),x] /;
FreeQ[{c,d,e,f},x] && NonzeroQ[d*e-c*f]


Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  1/(a*Sqrt[c]*Sqrt[e]*Rt[-d/c,2])*EllipticPi[b*c/(a*d), ArcSin[Rt[-d/c,2]*x], c*f/(d*e)] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveQ[c] && PositiveQ[e] &&
  (PosQ[-e*f] && (NegQ[-c*d] || Not[RationalQ[Rt[-c*d,2]]]) || NegQ[-e*f] && NegQ[-c*d] && Not[RationalQ[Rt[c*d,2]]])


Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
  Sqrt[(c+d*x^2)/c]*Sqrt[(e+f*x^2)/e]/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2])*
    Int[1/((a+b*x^2)*Sqrt[1+d/c*x^2]*Sqrt[1+f/e*x^2]),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[PositiveQ[c] && PositiveQ[e]] &&
  (PosQ[-e*f] && (NegQ[-c*d] || Not[RationalQ[Rt[-c*d,2]]]) || NegQ[-e*f] && NegQ[-c*d] &&
  Not[RationalQ[Rt[c*d,2]]]) 


Int[(c_+d_.*x_^n_)^p_*(e_+f_.*x_^n_)^q_./(a_+b_.*x_^n_),x_Symbol] :=
  -d/(b*c-a*d)*Int[(c+d*x^n)^p*(e+f*x^n)^q,x] + 
  b/(b*c-a*d)*Int[(c+d*x^n)^(p+1)*(e+f*x^n)^q/(a+b*x^n),x] /;
FreeQ[{a,b,c,d,e,f,n,q},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && RationalQ[p] && p<-1


Int[(a_+b_.*x_^n_)^m_*(c_+d_.*x_^n_)^p_*(e_+f_.*x_^n_)^q_,x_Symbol] :=
  Module[{u=ExpandIntegrand[(a+b*x^n)^m*(c+d*x^n)^p*(e+f*x^n)^q,x]},
  Int[u,x] /;
 SumQ[u]] /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && PositiveIntegerQ[n]


Int[(a_+b_.*x_^n_)^m_.*(c_+d_.*x_^n_)^p_.*(e_+f_.*x_^n_)^q_.,x_Symbol] :=
  Defer[Int][(a+b*x^n)^m*(c+d*x^n)^p*(e+f*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x]


Int[(a_.+b_.*u_^n_)^m_.*(c_.+d_.*v_^n_)^p_.*(e_.+f_.*w_^n_)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n)^m*(c+d*x^n)^p*(e+f*x^n)^q,x],x,u] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^m_.*v_^p_.*w_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^p*ExpandToSum[w,x]^q,x] /;
FreeQ[{m,p,q},x] && BinomialQ[{u,v,w},x] && ZeroQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && 
  ZeroQ[BinomialDegree[u,x]-BinomialDegree[w,x]] && Not[BinomialMatchQ[{u,v,w},x]]


(* ::Subsection::Closed:: *)
(*2.3.1 (c x)^m (a+b x^n)^p*)


(* Int[x_^m_.*(a_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[(a+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-n+1] *)


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Log[RemoveContent[a+b*x^n,x]]/(b*n) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m-n+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (a+b*x^n)^(p+1)/(b*n*(p+1)) /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m-n+1] && NonzeroQ[p+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[x^(m+n*p)*(b+a*x^(-n))^p,x] /;
FreeQ[{a,b,m,n},x] && IntegerQ[p] && NegQ[n]


Int[1/(x_*(a_+b_.*x_^n_)),x_Symbol] :=
  Log[x]/a - b/a*Int[x^(n-1)/(a+b*x^n),x] /;
FreeQ[{a,b,n},x]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[m+n*p+n+1] && NonzeroQ[m+1]


(* Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^2,x_Symbol] :=
  a^2*Int[(c*x)^m,x] + 2*a*b*Int[x^n*(c*x)^m,x] + b^2*Int[x^(2*n)*(c*x)^m,x] /;
FreeQ[{a,b,c,m,n},x] *)


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^2,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*(a+b*x^n)^2,x],x] /;
FreeQ[{a,b,c,m,n},x]


Int[x_^m_.*(a_.+b_.*x_^n_)^p_,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p,x],x,x^n] /;
FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[(c_*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && IntegerQ[Simplify[(m+1)/n]]


Int[Sqrt[c_.*x_]/Sqrt[a_+b_.*x_^2],x_Symbol] :=
  2*a*Rt[-b/a,2]*Sqrt[c*x]*Sqrt[(a+b*x^2)/a]/(b*Sqrt[a+b*x^2]*Sqrt[-b*x/(a*Rt[-b/a,2])])*
    Subst[Int[Sqrt[1-2*x^2]/Sqrt[1-x^2],x],x,Sqrt[(1-Rt[-b/a,2]*x)/2]] /;
FreeQ[{a,b,c},x]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{g=Gcd[m+1,n]},
  1/(c*g)*Subst[Int[x^((m+1)/g-1)*(a+b*x^(n/g)/c^n)^p,x],x,(c*x)^g] /;
 g!=1] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n] && RationalQ[m,p] && 0<m+1<n && -1<p<0


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,m},x] && PositiveIntegerQ[n,p]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) -
  b*(m+n*p+n+1)/(a*c^n*(m+1))*Int[(c*x)^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,p},x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && NegativeIntegerQ[(m+n*p+n+1)/n]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+1)) - 
  b*n*p/(c^n*(m+1))*Int[(c*x)^(m+n)*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-1 && Not[NegativeIntegerQ[(m+n*p+n+1)/n]] && 
  (IntegerQ[2*p] || IntegerQ[p+(m+1)/n])


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+n*p+1)) +
  a*n*p/(m+n*p+1)*Int[(c*x)^m*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c,m},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && NonzeroQ[m+n*p+1] && (IntegerQ[2*p] || IntegerQ[p+(m+1)/n])


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*n*(p+1)) -
  c^n*(m-n+1)/(b*n*(p+1))*Int[(c*x)^(m-n)*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m+1>n && Not[NegativeIntegerQ[(m+n*p+n+1)/n]] && 
  (IntegerQ[2*p] || IntegerQ[p+(m+1)/n])


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*n*(p+1)) +
  (m+n*p+n+1)/(a*n*(p+1))*Int[(c*x)^m*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,m},x] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && (IntegerQ[2*p] || IntegerQ[p+(m+1)/n])


Int[x_/(a_+b_.*x_^3),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,3]], s=Denominator[Rt[a/b,3]]},
  -r^2/(3*a*s)*Int[1/(r+s*x),x] + 
  r^2/(3*a*s)*Int[(r+s*x)/(r^2-r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b},x] && PosQ[a/b]


Int[x_/(a_+b_.*x_^3),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,3]], s=Denominator[Rt[-a/b,3]]},
  r^2/(3*a*s)*Int[1/(r-s*x),x] - 
  r^2/(3*a*s)*Int[(r-s*x)/(r^2+r*s*x+s^2*x^2),x]] /;
FreeQ[{a,b},x] && NegQ[a/b]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
  u=Int[(r*Cos[(2*k-1)*m*Pi/n]-s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  -(-r)^(m+1)/(a*n*s^m)*Int[1/(r+s*x),x] + Dist[2*r^(m+1)/(a*n*s^m),Sum[u,{k,1,(n-1)/2}],x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[(n-1)/2] && 0<m+1<n && PositiveIntegerQ[m] && Gcd[m+1,n]==1 && PosQ[a/b]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
  u=Int[(r*Cos[(2*k-1)*m*Pi/n]+s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  r^(m+1)/(a*n*s^m)*Int[1/(r-s*x),x] - Dist[(2*(-r)^(m+1))/(a*n*s^m),Sum[u,{k,1,(n-1)/2}],x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,(n-1)/2] && 0<m+1<n && PositiveIntegerQ[m] && Gcd[m+1,n]==1 && NegQ[a/b]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,n]], s=Denominator[Rt[a/b,n]], k, u},
  u=Int[(r*Cos[(2*k-1)*m*Pi/n]-s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x] + 
    Int[(r*Cos[(2*k-1)*m*Pi/n]+s*Cos[(2*k-1)*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[(2*k-1)*Pi/n]*x+s^2*x^2),x];
  2*(-1)^(m/2)*r^(m+2)/(a*n*s^m)*Int[1/(r^2+s^2*x^2),x] + Dist[2*r^(m+1)/(a*n*s^m),Sum[u,{k,1,(n-2)/4}],x]] /;
 FreeQ[{a,b},x] && PositiveIntegerQ[m,(n-2)/4] && 0<m+1<n && PositiveIntegerQ[m] && Gcd[m+1,n]==1 && PosQ[a/b]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]], k, u},
  u=Int[(r*Cos[2*k*m*Pi/n]-s*Cos[2*k*(m+1)*Pi/n]*x)/(r^2-2*r*s*Cos[2*k*Pi/n]*x+s^2*x^2),x] + 
    Int[(r*Cos[2*k*m*Pi/n]+s*Cos[2*k*(m+1)*Pi/n]*x)/(r^2+2*r*s*Cos[2*k*Pi/n]*x+s^2*x^2),x];
  2*r^(m+2)/(a*n*s^m)*Int[1/(r^2-s^2*x^2),x] + Dist[2*r^(m+1)/(a*n*s^m),Sum[u,{k,1,(n-2)/4}],x]] /;
 FreeQ[{a,b},x] && PositiveIntegerQ[m,(n-2)/4] && 0<m+1<n && PositiveIntegerQ[m] && Gcd[m+1,n]==1 && NegQ[a/b]


Int[x_^2/(a_+b_.*x_^4),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,2]], s=Denominator[Rt[a/b,2]]},
  1/(2*s)*Int[(r+s*x^2)/(a+b*x^4),x] - 
  1/(2*s)*Int[(r-s*x^2)/(a+b*x^4),x]] /;
FreeQ[{a,b},x] && (PositiveQ[a/b] || PosQ[a/b] && NonsumQ[a] && NonsumQ[b])


Int[x_^2/(a_+b_.*x_^4),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  s/(2*b)*Int[1/(r+s*x^2),x] -
  s/(2*b)*Int[1/(r-s*x^2),x]] /;
FreeQ[{a,b},x] && Not[PositiveQ[a/b]]


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[a/b,4]], s=Denominator[Rt[a/b,4]]},
  s^3/(2*Sqrt[2]*b*r)*Int[x^(m-n/4)/(r^2-Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x] -
  s^3/(2*Sqrt[2]*b*r)*Int[x^(m-n/4)/(r^2+Sqrt[2]*r*s*x^(n/4)+s^2*x^(n/2)),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,n/4] && 0<m+1<n && PositiveIntegerQ[m] && Gcd[m+1,n]==1 && PositiveQ[a/b]


Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  r/(2*a)*Int[x^m/(r+s*x^(n/2)),x] +
  r/(2*a)*Int[x^m/(r-s*x^(n/2)),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,n/4] && 0<m<n/2 && PositiveIntegerQ[m] && Gcd[m+1,n]==1 && Not[PositiveQ[a/b]]


Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  s/(2*b)*Int[x^(m-n/2)/(r+s*x^(n/2)),x] -
  s/(2*b)*Int[x^(m-n/2)/(r-s*x^(n/2)),x]] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,n/4] && n/2<=m<n && PositiveIntegerQ[m] && Gcd[m+1,n]==1 && Not[PositiveQ[a/b]]


Int[(c_.*x_)^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{g=Gcd[m+1,n]},
  c^(n-1)/g*Subst[Int[x^((m+1)/g-1)/(a*c^n+b*x^(n/g)),x],x,(c*x)^g] /;
 g!=1] /;
FreeQ[{a,b,c},x] && PositiveIntegerQ[n] && RationalQ[m] && 0<m+1<n


Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
  Int[PolynomialDivide[x^m,(a+b*x^n),x],x] /;
FreeQ[{a,b},x] && PositiveIntegerQ[m,n] && 2*n<m+1


Int[(c_.+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  Sqrt[a^(1/3)+b^(1/3)*x]*
       Sqrt[a^(1/3)*Sqrt[-3*b^(2/3)]+a^(1/3)*b^(1/3)-2*b^(2/3)*x]*
       Sqrt[a^(1/3)*Sqrt[-3*b^(2/3)]-a^(1/3)*b^(1/3)+2*b^(2/3)*x]/
    Sqrt[a+b*x^3]*
    Int[(c+d*x)/(Sqrt[a^(1/3)+b^(1/3)*x]*
           Sqrt[a^(1/3)*Sqrt[-3*b^(2/3)]+a^(1/3)*b^(1/3)-2*b^(2/3)*x]*
           Sqrt[a^(1/3)*Sqrt[-3*b^(2/3)]-a^(1/3)*b^(1/3)+2*b^(2/3)*x]),x] /;
FreeQ[{a,b,c,d},x] && PosQ[b]


Int[(c_.+d_.*x_)/Sqrt[a_+b_.*x_^3],x_Symbol] :=
  Sqrt[a^(1/3)-(-b)^(1/3)*x]*
       Sqrt[a^(1/3)*Sqrt[-3*(-b)^(2/3)]-a^(1/3)*(-b)^(1/3)-2*(-b)^(2/3)*x]*
       Sqrt[a^(1/3)*Sqrt[-3*(-b)^(2/3)]+a^(1/3)*(-b)^(1/3)+2*(-b)^(2/3)*x]/
    Sqrt[a+b*x^3]*
    Int[(c+d*x)/(Sqrt[a^(1/3)-(-b)^(1/3)*x]*
           Sqrt[a^(1/3)*Sqrt[-3*(-b)^(2/3)]-a^(1/3)*(-b)^(1/3)-2*(-b)^(2/3)*x]*
           Sqrt[a^(1/3)*Sqrt[-3*(-b)^(2/3)]+a^(1/3)*(-b)^(1/3)+2*(-b)^(2/3)*x]),x] /;
FreeQ[{a,b,c,d},x] && NegQ[b]


Int[(c_.+d_.*x_^2)/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  (Rt[-b,2]*c-Sqrt[a]*d)/Rt[-b,2]*Int[1/(Sqrt[Sqrt[a]+Rt[-b,2]*x^2]*Sqrt[Sqrt[a]-Rt[-b,2]*x^2]),x] + 
  d/Rt[-b,2]*Int[Sqrt[Sqrt[a]+Rt[-b,2]*x^2]/Sqrt[Sqrt[a]-Rt[-b,2]*x^2],x] /;
FreeQ[{a,b,c,d},x] && PositiveQ[a]


Int[(c_.+d_.*x_^2)/Sqrt[a_+b_.*x_^4],x_Symbol] :=
  Sqrt[(a+b*x^4)/a]/Sqrt[a+b*x^4]*Int[(c+d*x^2)/Sqrt[1+b*x^4/a],x] /;
FreeQ[{a,b,c,d},x] && Not[PositiveQ[a]]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*(m+n*p+1)) -
  a*c^n*(m-n+1)/(b*(m+n*p+1))*Int[(c*x)^(m-n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,p},x] && PositiveIntegerQ[n] && RationalQ[m] && m>n-1 && NonzeroQ[m+n*p+1] && (IntegerQ[2*p] || IntegerQ[p+(m+1)/n])


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^(n-1)*(c*x)^(m-n+1)*(a+b*x^n)^(p+1)/(b*(m+n*p+1)) -
  a*c^n*(m-n+1)/(b*(m+n*p+1))*Int[(c*x)^(m-n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && PositiveIntegerQ[n] && SumSimplerQ[m,-n] && NonzeroQ[m+n*p+1] && NegativeIntegerQ[Simplify[p+(m+1)/n]]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) -
  b*(m+n*p+n+1)/(a*c^n*(m+1))*Int[(c*x)^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,p},x] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && (IntegerQ[2*p] || IntegerQ[p+(m+1)/n])


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1)) -
  b*(m+n*p+n+1)/(a*c^n*(m+1))*Int[(c*x)^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && PositiveIntegerQ[n] && SumSimplerQ[m,n] && NegativeIntegerQ[Simplify[p+(m+1)/n]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Denominator[p]},
  q*a^(p+Simplify[(m+1)/n])/n*
	Subst[Int[x^(q*Simplify[(m+1)/n]-1)/(1-b*x^q)^(p+Simplify[(m+1)/n]+1),x],x,x^(n/q)/(a+b*x^n)^(1/q)]] /;
FreeQ[{a,b,m,n},x] && PositiveIntegerQ[n] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && -1<p<0


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,p},x] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{g=Denominator[m]},
  -g/c*Subst[Int[(a+b*c^(-n)*x^(-g*n))^p/x^(g*(m+1)+1),x],x,1/(c*x)^(1/g)]] /;
FreeQ[{a,b,c,p},x] && NegativeIntegerQ[n] && FractionQ[m]


Int[(c_.*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^m*(x^(-1))^m*Subst[Int[(a+b*x^(-n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,m,p},x] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{d=Denominator[n]},
  d*Subst[Int[x^(d*(m+1)-1)*(a+b*x^(d*n))^p,x],x,x^(1/d)]] /;
FreeQ[{a,b,m,p},x] && FractionQ[n]


Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^(m-1/2)*Sqrt[c*x]/Sqrt[x]*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,p},x] && FractionQ[n] && PositiveIntegerQ[m+1/2]


Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  c^(m+1/2)*Sqrt[x]/Sqrt[c*x]*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,p},x] && FractionQ[n] && NegativeIntegerQ[m-1/2]


Int[(c_*x_)^m_*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,p},x] && FractionQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*x^Simplify[n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,m,n,p},x] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(c_*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  x^(m+1)*(a+b*x^n)^p/(m+1) - 
  b*n*p/(m+1)*Int[x^(m+n)*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b,m,n},x] && ZeroQ[p+(m+1)/n] && RationalQ[p] && p>0


Int[(c_*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[p+(m+1)/n] && RationalQ[p] && p>0


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+n*p+1)) +
  a*n*p/(m+n*p+1)*Int[(c*x)^m*(a+b*x^n)^(p-1),x] /;
FreeQ[{a,b,c,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && p>0 && NonzeroQ[m+n*p+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Module[{q=Denominator[p]},
  q*a^(p+Simplify[(m+1)/n])/n*
	Subst[Int[x^(q*Simplify[(m+1)/n]-1)/(1-b*x^q)^(p+Simplify[(m+1)/n]+1),x],x,x^(n/q)/(a+b*x^n)^(1/q)]] /;
FreeQ[{a,b,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && -1<p<0


Int[(c_*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^m/x^m*Int[x^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && -1<p<0


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  -(c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*n*(p+1)) +
  (m+n*p+n+1)/(a*n*(p+1))*Int[(c*x)^m*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,m,n},x] && IntegerQ[p+Simplify[(m+1)/n]] && RationalQ[p] && p<-1


Int[x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
  Module[{mn=Simplify[m-n]},
  x^(mn+1)/(b*(mn+1)) -
  a/b*Int[x^mn/(a+b*x^n),x]] /;
FreeQ[{a,b,m,n},x] && FractionQ[Simplify[(m+1)/n]] && SumSimplerQ[m,-n]


Int[x_^m_/(a_+b_.*x_^n_),x_Symbol] :=
  x^(m+1)/(a*(m+1)) -
  b/a*Int[x^Simplify[m+n]/(a+b*x^n),x] /;
FreeQ[{a,b,m,n},x] && FractionQ[Simplify[(m+1)/n]] && SumSimplerQ[m,n]


Int[(c_*x_)^m_./(a_+b_.*x_^n_),x_Symbol] :=
  (c*x)^m/x^m*Int[x^m/(a+b*x^n),x] /;
FreeQ[{a,b,c,m,n},x] && FractionQ[Simplify[(m+1)/n]] && (SumSimplerQ[m,n] || SumSimplerQ[m,-n])


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(c*x)^m*(a+b*x^n)^p,x],x] /;
FreeQ[{a,b,c,m,n},x] && PositiveIntegerQ[p]


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  a^p*(c*x)^(m+1)/(c*(m+1))*Hypergeometric2F1[-p,(m+1)/n,(m+1)/n+1,-b*x^n/a] /;
FreeQ[{a,b,c,m,n,p},x] && Not[PositiveIntegerQ[p]] && (NegativeIntegerQ[p] || PositiveQ[a])


(* Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
  (c*x)^(m+1)*(a+b*x^n)^(p+1)/(a*c*(m+1))*Hypergeometric2F1[1,(m+1)/n+p+1,(m+1)/n+1,-b*x^n/a] /;
FreeQ[{a,b,c,m,n,p},x] && Not[PositiveIntegerQ[p]] && Not[NegativeIntegerQ[p] || PositiveQ[a]] *)


Int[(c_.*x_)^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
   (c*x)^(m+1)*(a+b*x^n)^p/(c*(m+1)*((a+b*x^n)/a)^p)*Hypergeometric2F1[-p,(m+1)/n,(m+1)/n+1,-b*x^n/a] /;
FreeQ[{a,b,c,m,n,p},x] && Not[PositiveIntegerQ[p]] && Not[NegativeIntegerQ[p] || PositiveQ[a]]


Int[x_^m_.*(a_.+b_.*v_^n_)^p_,x_Symbol] :=
  1/Coefficient[v,x,1]^(m+1)*Subst[Int[SimplifyIntegrand[(x-Coefficient[v,x,0])^m*(a+b*x^n)^p,x],x],x,v] /;
FreeQ[{a,b,n,p},x] && LinearQ[v,x] && IntegerQ[m] && NonzeroQ[v-x]


Int[u_^m_.*(a_+b_.*v_^n_)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n)^p,x],x,v] /;
FreeQ[{a,b,m,n,p},x] && LinearPairQ[u,v,x]


Int[x_^m_.*(a_.+b_.*(d_./x_)^n_)^p_.,x_Symbol] :=
  -d^(m+1)*Subst[Int[(a+b*x^n)^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,d,n,p},x] && IntegerQ[m]


Int[(c_.*x_)^m_.*(a_.+b_.*(d_./x_)^n_)^p_.,x_Symbol] :=
  -d*(c*x)^m*(d/x)^m*Subst[Int[(a+b*x^n)^p/x^(m+2),x],x,d/x] /;
FreeQ[{a,b,c,d,m,n,p},x] && Not[IntegerQ[m]]


Int[(c_.*x_)^m_.*u_^p_.,x_Symbol] :=
  Int[(c*x)^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{c,m,p},x] && BinomialQ[u,x] && Not[BinomialMatchQ[u,x]]


Int[x_^m_.*(a_.+b_.*(c_.*x_^n_)^q_)^p_.,x_Symbol] :=
  x^(m+1)/(c*x^n)^((m+1)/n)*Subst[Int[x^m*(a+b*x^(n*q))^p,x],x,(c*x^n)^(1/n)] /;
FreeQ[{a,b,c,m,n,p,q},x] && IntegerQ[m] && IntegerQ[n*q]


(* ::Subsection::Closed:: *)
(*2.3.2 (e x)^m (a+b x^n)^p (c+d x^n)^q*)


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  1/n*Subst[Int[(a+b*x)^p*(c+d*x)^q,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && NonzeroQ[b*c-a*d] && ZeroQ[m-n+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  Int[x^(m+n*(p+q))*(b+a*x^(-n))^p*(d+c*x^(-n))^q,x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && IntegersQ[p,q] && NegQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p*(c+d*x)^q,x],x,x^n] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && NonzeroQ[b*c-a*d] && IntegerQ[Simplify[(m+1)/n]]


Int[(e_*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.,x_Symbol] :=
  (e*x)^m/x^m*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && NonzeroQ[b*c-a*d] && IntegerQ[Simplify[(m+1)/n]]


Int[(c_+d_.*x_^n_)/(x_*(a_+b_.*x_^n_)),x_Symbol] :=
  c*Log[x]/a - (b*c-a*d)/a*Int[x^(n-1)/(a+b*x^n),x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NonzeroQ[b*c-a*d] && ZeroQ[a*d*(m+1)-b*c*(m+n*(p+1)+1)] && NonzeroQ[m+1]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n),x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a*d*(m+1)-b*c*(m+n*(p+1)+1)] && PositiveIntegerQ[n,p]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*x^(m+1)*(a+b*x^n)^(p+1)/(a*(m+1)) + 
  (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(a*(m+1))*Int[x^(m+n)*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a*d*(m+1)-b*c*(m+n*(p+1)+1)] && 
  RationalQ[m,n] && m<-1 && n>0 && Not[IntegerQ[p] && p<-1]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_),x_Symbol] :=
  -(b*c-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*b*e*n*(p+1)) - 
  (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(a*b*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1),x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a*d*(m+1)-b*c*(m+n*(p+1)+1)] && RationalQ[p] && p<-1


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  d*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(b*e*(m+n*(p+1)+1)) - 
  (a*d*(m+1)-b*c*(m+n*(p+1)+1))/(b*(m+n*(p+1)+1))*Int[(e*x)^m*(a+b*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a*d*(m+1)-b*c*(m+n*(p+1)+1)] && NonzeroQ[m+n(p+1)+1]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n),x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NonzeroQ[b*c-a*d] && NonzeroQ[a*d*(m+1)-b*c*(m+n*(p+1)+1)]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && IntegersQ[p,q] && 
  (p>0 && q>0 || p==-1 && q>0 && (IntegerQ[m] || PositiveIntegerQ[2*(m+1)] || Not[RationalQ[m]]))


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
  c^2*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*e*(m+1)) - 
  1/(a*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p*Simp[b*c^2*n*(p+1)+c*(b*c-2*a*d)*(m+1)-a*(m+1)*d^2*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,n] && m<-1 && n>0


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
  -(b*c-a*d)^2*(e*x)^(m+1)*(a+b*x^n)^(p+1)/(a*b^2*e*n*(p+1)) + 
  1/(a*b^2*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*Simp[(b*c-a*d)^2*(m+1)+b^2*c^2*n*(p+1)+a*b*d^2*n*(p+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^2,x_Symbol] :=
  d^2*(e*x)^(m+n+1)*(a+b*x^n)^(p+1)/(b*e^(n+1)*(m+n*(p+2)+1)) + 
  1/(b*(m+n*(p+2)+1))*Int[(e*x)^m*(a+b*x^n)^p*Simp[b*c^2*(m+n*(p+2)+1)+d*((2*b*c-a*d)*(m+n+1)+2*b*c*n*(p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && NonzeroQ[m+n*(p+2)+1]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*n*(p+1)) - 
  e^n/(b*n*(p+1))*Int[(e*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m-n+1)+d*(m+n*(q-1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p,q] && p<-1 && q>0 && m-n+1>0 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(c*b-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*b*e*n*(p+1)) + 
  1/(a*b*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-2)*
    Simp[c*(c*b*n*(p+1)+(c*b-a*d)*(m+1))+d*(c*b*n*(p+1)+(c*b-a*d)*(m+n*(q-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p,q] && p<-1 && q>1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*n*(p+1)) + 
  1/(a*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m+n*(p+1)+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p,q] && p<-1 && 0<q<1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -a*e^(2*n-1)*(e*x)^(m-2*n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*n*(b*c-a*d)*(p+1)) + 
  e^(2*n)/(b*n*(b*c-a*d)*(p+1))*Int[(e*x)^(m-2*n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
    Simp[a*c*(m-2*n+1)+(a*d*(m-n+n*q+1)+b*c*n*(p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m-n+1>n && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(n*(b*c-a*d)*(p+1)) - 
  e^n/(n*(b*c-a*d)*(p+1))*Int[(e*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*(m-n+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && n>=m-n+1>0 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -b*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*e*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*
    Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*b*(m+1)+n*(b*c-a*d)*(p+1)+d*b*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+1)) - 
  1/(e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[n*(b*c*p+a*d*q)+b*d*n*(p+q)*x^n,x],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p,q] && q>0 && m<-1 && p>0 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  c*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*e*(m+1)) - 
  1/(a*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
    Simp[c*(c*b-a*d)*(m+1)+c*n*(b*c*(p+1)+a*d*(q-1))+d*((c*b-a*d)*(m+1)+c*b*n*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,q] && q>1 && m<-1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*(m+1)) - 
  1/(a*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
    Simp[c*b*(m+1)+n*(b*c*(p+1)+a*d*q)+d*(b*(m+1)+b*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,q] && 0<q<1 && m<-1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+n*(p+q)+1)) + 
  n/(m+n*(p+q)+1)*Int[(e*x)^m*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p,q] && q>0 && p>0 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  d*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(b*e*(m+n*(p+q)+1)) + 
  1/(b*(m+n*(p+q)+1))*Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
    Simp[c*((c*b-a*d)*(m+1)+c*b*n*(p+q))+(d*(c*b-a*d)*(m+1)+d*n*(q-1)*(b*c-a*d)+c*b*d*n*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[q] && q>1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*(m+n*(p+q)+1)) - 
  e^n/(b*(m+n*(p+q)+1))*
    Int[(e*x)^(m-n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*Simp[a*c*(m-n+1)+(a*d*(m-n+1)-n*q*(b*c-a*d))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,q] && q>0 && m-n+1>0 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(2*n-1)*(e*x)^(m-2*n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*d*(m+n*(p+q)+1)) - 
  e^(2*n)/(b*d*(m+n*(p+q)+1))*
    Int[(e*x)^(m-2*n)*(a+b*x^n)^p*(c+d*x^n)^q*Simp[a*c*(m-2*n+1)+(a*d*(m+n*(q-1)+1)+b*c*(m+n*(p-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && m-n+1>n && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*c*e*(m+1)) - 
  1/(a*c*e^n*(m+1))*
    Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q*Simp[(b*c+a*d)*(m+n+1)+n*(b*c*p+a*d*q)+b*d*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,p,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  -a*e^n/(b*c-a*d)*Int[(e*x)^(m-n)/(a+b*x^n),x] + c*e^n/(b*c-a*d)*Int[(e*x)^(m-n)/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && n<=m<=2*n-1


Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  b/(b*c-a*d)*Int[(e*x)^m/(a+b*x^n),x] - d/(b*c-a*d)*Int[(e*x)^m/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,e,m},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n]


Int[(e_.*x_)^m_/((a_+b_.*x_^n_)*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  r/(2*a)*Int[(e*x)^m/((r+s*x^(n/2))*Sqrt[c+d*x^n]),x] +
  r/(2*a)*Int[(e*x)^m/((r-s*x^(n/2))*Sqrt[c+d*x^n]),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[m,n/2] && m<n/2 && CoprimeQ[m+1,n]


Int[(e_.*x_)^m_/((a_+b_.*x_^n_)*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  Module[{r=Numerator[Rt[-a/b,2]], s=Denominator[Rt[-a/b,2]]},
  s*e^(n/2)/(2*b)*Int[(e*x)^(m-n/2)/((r+s*x^(n/2))*Sqrt[c+d*x^n]),x] -
  s*e^(n/2)/(2*b)*Int[(e*x)^(m-n/2)/((r-s*x^(n/2))*Sqrt[c+d*x^n]),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[m,n/2] && n/2<=m<n && CoprimeQ[m+1,n]


Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  e^n/b*Int[(e*x)^(m-n)/Sqrt[c+d*x^n],x] - 
  a*e^n/b*Int[(e*x)^(m-n)/((a+b*x^n)*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[m,n] && 0<m-n+1<n


Int[(e_.*x_)^m_.*Sqrt[c_+d_.*x_^n_]/(a_+b_.*x_^n_),x_Symbol] :=
  d/b*Int[(e*x)^m/Sqrt[c+d*x^n],x] + 
  (b*c-a*d)/b*Int[(e*x)^m/((a+b*x^n)*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && 0<m+1<n


Int[(e_.*x_)^m_./(Sqrt[a_+b_.*x_^n_]*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
  e^n/b*Int[(e*x)^(m-n)*Sqrt[a+b*x^n]/Sqrt[c+d*x^n],x] - 
  a*e^n/b*Int[(e*x)^(m-n)/(Sqrt[a+b*x^n]*Sqrt[c+d*x^n]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n,m] && 0<m-n+1<n && Not[n==2 && SimplerSqrtQ[-b/a,-d/c]]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Module[{g=Gcd[m+1,n]},
  1/(e*g)*Subst[Int[x^((m+1)/g-1)*(a+b*x^(n/g)/e^n)^p*(c+d*x^(n/g)/e^n)^q,x],x,(e*x)^g] /;
 g!=1] /;
FreeQ[{a,b,c,d,e,p,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+1)*(1+(b*x^n)/a)^p*(1+(d*x^n)/c)^q)*
    AppellF1[(m+1)/n,-p,-q,1+(m+1)/n,-b*x^n/a,-d*x^n/c] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && NonzeroQ[m+1] && NonzeroQ[m-n+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,p,q},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Module[{g=Denominator[m]},
  -g/e*Subst[Int[(a+b*e^(-n)*x^(-g*n))^p*(c+d*e^(-n)*x^(-g*n))^q/x^(g*(m+1)+1),x],x,1/(e*x)^(1/g)]] /;
FreeQ[{a,b,c,d,e,p,q},x] && NegativeIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,m,p,q},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Module[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*(a+b*x^(g*n))^p*(c+d*x^(g*n))^q,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,d,m,p,q},x] && NonzeroQ[b*c-a*d] && FractionQ[n]


Int[(e_*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(m-1/2)*Sqrt[e*x]/Sqrt[x]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,p,q},x] && NonzeroQ[b*c-a*d] && FractionQ[n] && PositiveIntegerQ[m+1/2]


Int[(e_*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  e^(m+1/2)*Sqrt[x]/Sqrt[e*x]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,p,q},x] && NonzeroQ[b*c-a*d] && FractionQ[n] && NegativeIntegerQ[m-1/2]


Int[(e_*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^m/x^m*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,m,p,q},x] && NonzeroQ[b*c-a*d] && FractionQ[n]


(* Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -1/(m+1)*Subst[Int[(a+b*x^Simplify[-n/(m+1)])^p*(c+d*x^Simplify[-n/(m+1)])^q/x^2,x],x,x^(-(m+1))] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[m+1] && NegativeIntegerQ[Simplify[n/(m+1)+1]] && 
  RationalQ[p,q] && -1<=p<0 && -1<=q<0 && Not[IntegerQ[n]] *)


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*x^Simplify[n/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && NonzeroQ[b*c-a*d] && IntegerQ[Simplify[n/(m+1)]]


Int[(e_*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^m/x^m*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && NonzeroQ[b*c-a*d] && IntegerQ[Simplify[n/(m+1)]]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(c*b-a*d)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(a*b*e*n*(p+1)) + 
  1/(a*b*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-2)*
    Simp[c*(c*b*n*(p+1)+(c*b-a*d)*(m+1))+d*(c*b*n*(p+1)+(c*b-a*d)*(m+n*(q-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b*c-a*d] && RationalQ[p,q] && p<-1 && q>1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*n*(p+1)) + 
  1/(a*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*Simp[c*(m+n*(p+1)+1)+d*(m+n*(p+q+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b*c-a*d] && RationalQ[p,q] && p<-1 && 0<q<1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  -b*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*e*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*
    Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*Simp[c*b*(m+1)+n*(b*c-a*d)*(p+1)+d*b*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+n*(p+q)+1)) + 
  n/(m+n*(p+q)+1)*Int[(e*x)^m*(a+b*x^n)^(p-1)*(c+d*x^n)^(q-1)*Simp[a*c*(p+q)+(q*(b*c-a*d)+a*d*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b*c-a*d] && RationalQ[p,q] && q>0 && p>0 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  d*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)/(b*e*(m+n*(p+q)+1)) + 
  1/(b*(m+n*(p+q)+1))*Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-2)*
    Simp[c*((c*b-a*d)*(m+1)+c*b*n*(p+q))+(d*(c*b-a*d)*(m+1)+d*n*(q-1)*(b*c-a*d)+c*b*d*n*(p+q))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && NonzeroQ[b*c-a*d] && RationalQ[q] && q>1 && 
  (IntegersQ[2*p,2*q] || PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[x_^m_/((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  -a/(b*c-a*d)*Int[x^(m-n)/(a+b*x^n),x] + c/(b*c-a*d)*Int[x^(m-n)/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && (ZeroQ[m-n] || ZeroQ[m-2*n+1])


Int[(e_.*x_)^m_./((a_+b_.*x_^n_)*(c_+d_.*x_^n_)),x_Symbol] :=
  b/(b*c-a*d)*Int[(e*x)^m/(a+b*x^n),x] - d/(b*c-a*d)*Int[(e*x)^m/(c+d*x^n),x] /;
FreeQ[{a,b,c,d,e,n,m},x] && NonzeroQ[b*c-a*d]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x] /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b*c-a*d] && (PositiveIntegerQ[p,q] || IntegersQ[m,p,q] && p>=-2 && (q>=-2 || q==-3 && OddQ[m]))


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_,x_Symbol] :=
  (e*x)^(m+1)*(a+b*x^n)^p*(c+d*x^n)^q/(e*(m+1)*(1+(b*x^n)/a)^p*(1+(d*x^n)/c)^q)*
    AppellF1[(m+1)/n,-p,-q,1+(m+1)/n,-b*x^n/a,-d*x^n/c] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && NonzeroQ[b*c-a*d] && NonzeroQ[m+1] && NonzeroQ[m-n+1]


Int[x_^m_.*(e_.*(a_+b_.*x_^n_.)^r_.)^p_*(f_.*(c_+d_.*x_^n_.)^s_)^q_,x_Symbol] :=
  (e*(a+b*x^n)^r)^p*(f*(c+d*x^n)^s)^q/((a+b*x^n)^(p*r)*(c+d*x^n)^(q*s))*
    Int[x^m*(a+b*x^n)^(p*r)*(c+d*x^n)^(q*s),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r,s},x]


Int[u_^m_.*(a_.+b_.*v_^n_)^p_.*(c_.+d_.*w_^n_)^q_,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q,x],x,v] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && LinearPairQ[u,v,x] && ZeroQ[v-w]


Int[x_^m_.*u_^p_.*v_^q_.,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q,x] /;
FreeQ[{m,p,q},x] && BinomialQ[{u,v},x] && ZeroQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && Not[BinomialMatchQ[{u,v},x]]


Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^r_.)^q_.,x_Symbol] :=
  Int[(a+b*x^n)^p*(d+c*x^n)^q/x^(n*q),x] /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[n+r] && PosQ[n] && IntegerQ[q]


Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^r_.)^q_,x_Symbol] :=
  -Subst[Int[(b+a*x^n)^p*(c+d*x^n)^q/x^(n*p+2),x],x,1/x] /;
FreeQ[{a,b,c,d,q},x] && ZeroQ[n+r] && PosQ[n] && Not[IntegerQ[q]] && IntegersQ[n,p]


Int[(a_.+b_.*x_^n_.)^p_.*(c_+d_.*x_^r_.)^q_,x_Symbol] :=
  x^(n*q)*(c+d/x^n)^q/(d+c*x^n)^q*Int[(a+b*x^n)^p*(d+c*x^n)^q/x^(n*q),x] /;
FreeQ[{a,b,c,d,n,p,q},x] && ZeroQ[n+r] && PosQ[n] && Not[IntegerQ[q]] && Not[IntegersQ[n,p]]


Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^r_.)^q_.,x_Symbol] :=
  Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && ZeroQ[n+r] && PosQ[n] && IntegerQ[q]


Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^r_.)^q_,x_Symbol] :=
  -Subst[Int[(b+a*x^n)^p*(c+d*x^n)^q/x^(m+n*p+2),x],x,1/x] /;
FreeQ[{a,b,c,d,q},x] && ZeroQ[n+r] && PosQ[n] && Not[IntegerQ[q]] && IntegersQ[m,n,p]


Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^r_.)^q_,x_Symbol] :=
  x^(n*q)*(c+d/x^n)^q/(d+c*x^n)^q*Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q,x] /;
FreeQ[{a,b,c,d,m,n,p,q},x] && ZeroQ[n+r] && PosQ[n] && Not[IntegerQ[q]] && Not[IntegersQ[m,n,p]]


Int[u_.*(e_.*(a_.+b_.*x_^n_.)/(c_.+d_.*x_^n_.))^p_,x_Symbol] :=
  (b*e/d)^p*Int[u,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && ZeroQ[b*c-a*d]


Int[u_.*(e_.*(a_.+b_.*x_^n_.)/(c_.+d_.*x_^n_.))^p_,x_Symbol] :=
  Int[u*(e*(a+b*x^n))^p/(c+d*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && PositiveQ[b*d*e] && PositiveQ[c-a*d/b]


Int[(e_.*(a_.+b_.*x_^n_.)/(c_.+d_.*x_^n_.))^p_,x_Symbol] :=
  Module[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[
    Int[x^(q*(p+1)-1)*(-a*e+c*x^q)^(1/n-1)/(b*e-d*x^q)^(1/n+1),x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && FractionQ[p] && IntegerQ[1/n]


Int[x_^m_.*(e_.*(a_.+b_.*x_^n_.)/(c_.+d_.*x_^n_.))^p_,x_Symbol] :=
  Module[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[
    Int[x^(q*(p+1)-1)*(-a*e+c*x^q)^(Simplify[(m+1)/n]-1)/(b*e-d*x^q)^(Simplify[(m+1)/n]+1),x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e,m,n},x] && FractionQ[p] && IntegerQ[Simplify[(m+1)/n]]


Int[u_^r_.*(e_.*(a_.+b_.*x_^n_.)/(c_.+d_.*x_^n_.))^p_,x_Symbol] :=
  Module[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[Int[SimplifyIntegrand[x^(q*(p+1)-1)*(-a*e+c*x^q)^(1/n-1)/(b*e-d*x^q)^(1/n+1)*
    ReplaceAll[u,x->(-a*e+c*x^q)^(1/n)/(b*e-d*x^q)^(1/n)]^r,x],x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[u,x] && FractionQ[p] && IntegerQ[1/n] && IntegerQ[r]


Int[x_^m_.*u_^r_.*(e_.*(a_.+b_.*x_^n_.)/(c_.+d_.*x_^n_.))^p_,x_Symbol] :=
  Module[{q=Denominator[p]},
  q*e*(b*c-a*d)/n*Subst[Int[SimplifyIntegrand[x^(q*(p+1)-1)*(-a*e+c*x^q)^((m+1)/n-1)/(b*e-d*x^q)^((m+1)/n+1)*
    ReplaceAll[u,x->(-a*e+c*x^q)^(1/n)/(b*e-d*x^q)^(1/n)]^r,x],x],x,(e*(a+b*x^n)/(c+d*x^n))^(1/q)]] /;
FreeQ[{a,b,c,d,e},x] && PolynomialQ[u,x] && FractionQ[p] && IntegerQ[1/n] && IntegersQ[m,r]


(* ::Subsection::Closed:: *)
(*2.3.3 (e x)^m (a+b x^n)^p (c+d x^n)^q (A+B x^n)*)


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  1/n*Subst[Int[(a+b*x)^p*(c+d*x)^q*(e+f*x)^r,x],x,x^n] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && ZeroQ[m-n+1]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  Int[x^(m+n*(p+q+r))*(b+a*x^(-n))^p*(d+c*x^(-n))^q*(f+e*x^(-n))^r,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && IntegersQ[p,q,r] && NegQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x)^p*(c+d*x)^q*(e+f*x)^r,x],x,x^n] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q,r},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && IntegerQ[Simplify[(m+1)/n]]


Int[(g_*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(e_+f_.*x_^n_)^r_.,x_Symbol] :=
  (g*x)^m/x^m*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(e+f*x^n)^r,x] /;
FreeQ[{a,b,c,d,e,f,g,m,n,p,q,r},x] && NonzeroQ[b*c-a*d] && NonzeroQ[b*e-a*f] && NonzeroQ[d*e-c*f] && IntegerQ[Simplify[(m+1)/n]]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(A+B*x^n),x],x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && IntegersQ[p,q] && 
  (p>0 && q>0 || p==-1 && q>0 && (IntegerQ[m] || PositiveIntegerQ[2*(m+1)] || Not[RationalQ[m]]))


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  -(A*b-a*B)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*b*e*n*(p+1)) + 
  1/(a*b*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*
    Simp[c*(A*b*n*(p+1)+(A*b-a*B)*(m+1))+d*(A*b*n*(p+1)+(A*b-a*B)*(m+n*q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,m},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p,q] && p<-1 && q>0


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  e^(n-1)*(A*b-a*B)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*n*(b*c-a*d)*(p+1)) - 
  e^n/(b*n*(b*c-a*d)*(p+1))*Int[(e*x)^(m-n)*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
    Simp[c*(A*b-a*B)*(m-n+1)+(d*(A*b-a*B)*(m+n*q+1)-b*n*(B*c-A*d)*(p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m-n+1>0


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  -(A*b-a*B)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*e*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
    Simp[c*(A*b-a*B)*(m+1)+A*n*(b*c-a*d)*(p+1)+d*(A*b-a*B)*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,m,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[p] && p<-1


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  A*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*e*(m+1)) - 
  1/(a*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
    Simp[c*(A*b-a*B)*(m+1)+A*n*(b*c*(p+1)+a*d*q)+d*((A*b-a*B)*(m+1)+A*b*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m,q] && q>0 && m<-1


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  B*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*e*(m+n*(p+q+1)+1)) + 
  1/(b*(m+n*(p+q+1)+1))*Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
    Simp[c*((A*b-a*B)*(m+1)+A*b*n*(p+q+1))+(d*(A*b-a*B)*(m+1)+B*n*q*(b*c-a*d)+A*b*d*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[q] && q>0


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  B*e^(n-1)*(e*x)^(m-n+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(b*d*(m+n*(p+q+1)+1)) - 
  e^n/(b*d*(m+n*(p+q+1)+1))*Int[(e*x)^(m-n)*(a+b*x^n)^p*(c+d*x^n)^q*
    Simp[a*B*c*(m-n+1)+(a*B*d*(m+n*q+1)-b*(-B*c*(m+n*p+1)+A*d*(m+n*(p+q+1)+1)))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,p,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && m-n+1>0


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  A*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*c*e*(m+1)) + 
  1/(a*c*e^n*(m+1))*Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q*
    Simp[a*B*c*(m+1)-A*(b*c+a*d)*(m+n+1)-A*n*(b*c*p+a*d*q)-A*b*d*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,p,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(A_+B_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(A+B*x^n)/(c+d*x^n),x],x] /;
FreeQ[{a,b,c,d,e,A,B,m,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  Module[{g=Gcd[m+1,n]},
  1/(e*g)*Subst[Int[x^((m+1)/g-1)*(a+b*x^(n/g)/e^n)^p*(c+d*x^(n/g)/e^n)^q*(A+B*x^(n/g)/e^n),x],x,(e*x)^g] /;
 g!=1] /;
FreeQ[{a,b,c,d,e,A,B,p,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n] && RationalQ[m]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  A*Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x] + B/e^n*Int[(e*x)^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,A,B,m,p,q},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  -Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q*(A+B*x^(-n))/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,A,B,p,q},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  Module[{g=Denominator[m]},
  -g/e*Subst[Int[(a+b*e^(-n)*x^(-g*n))^p*(c+d*e^(-n)*x^(-g*n))^q*(A+B*e^(-n)*x^(-g*n))/x^(g*(m+1)+1),x],x,1/(e*x)^(1/g)]] /;
FreeQ[{a,b,c,d,e,A,B,p,q},x] && NegativeIntegerQ[n] && FractionQ[m]


Int[(e_.*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  -(e*x)^m*(x^(-1))^m*Subst[Int[(a+b*x^(-n))^p*(c+d*x^(-n))^q*(A+B*x^(-n))/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,A,B,m,p,q},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  Module[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*(a+b*x^(g*n))^p*(c+d*x^(g*n))^q*(A+B*x^(g*n)),x],x,x^(1/g)]] /;
FreeQ[{a,b,c,d,A,B,m,p,q},x] && NonzeroQ[b*c-a*d] && FractionQ[n]


Int[(e_*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  e^(m-1/2)*Sqrt[e*x]/Sqrt[x]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(A+B*x^n),x] /;
FreeQ[{a,b,c,d,e,A,B,p,q},x] && NonzeroQ[b*c-a*d] && FractionQ[n] && PositiveIntegerQ[m+1/2]


Int[(e_*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  e^(m+1/2)*Sqrt[x]/Sqrt[e*x]*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(A+B*x^n),x] /;
FreeQ[{a,b,c,d,e,A,B,p,q},x] && NonzeroQ[b*c-a*d] && FractionQ[n] && NegativeIntegerQ[m-1/2]


Int[(e_*x_)^m_*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  (e*x)^m/x^m*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(A+B*x^n),x] /;
FreeQ[{a,b,c,d,e,A,B,m,p,q},x] && NonzeroQ[b*c-a*d] && FractionQ[n]


Int[x_^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*x^Simplify[n/(m+1)])^p*(c+d*x^Simplify[n/(m+1)])^q*(A+B*x^Simplify[n/(m+1)]),x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,A,B,m,n,p,q},x] && NonzeroQ[b*c-a*d] && IntegerQ[Simplify[n/(m+1)]]


Int[(e_*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  (e*x)^m/x^m*Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(A+B*x^n),x] /;
FreeQ[{a,b,c,d,e,A,B,m,n,p,q},x] && NonzeroQ[b*c-a*d] && IntegerQ[Simplify[n/(m+1)]]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q*(A+B*x^n),x],x] /;
FreeQ[{a,b,c,d,e,A,B,m,n,p},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[p+2,q]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  -(A*b-a*B)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(a*b*e*n*(p+1)) + 
  1/(a*b*n*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^(q-1)*
    Simp[c*(A*b*n*(p+1)+(A*b-a*B)*(m+1))+d*(A*b*n*(p+1)+(A*b-a*B)*(m+n*q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,m,n},x] && NonzeroQ[b*c-a*d] && RationalQ[p,q] && p<-1 && q>0


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  -(A*b-a*B)*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^(q+1)/(a*e*n*(b*c-a*d)*(p+1)) + 
  1/(a*n*(b*c-a*d)*(p+1))*Int[(e*x)^m*(a+b*x^n)^(p+1)*(c+d*x^n)^q*
    Simp[c*(A*b-a*B)*(m+1)+A*n*(b*c-a*d)*(p+1)+d*(A*b-a*B)*(m+n*(p+q+2)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,m,n,q},x] && NonzeroQ[b*c-a*d] && RationalQ[p] && p<-1


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_.*(c_+d_.*x_^n_)^q_.*(A_+B_.*x_^n_),x_Symbol] :=
  B*(e*x)^(m+1)*(a+b*x^n)^(p+1)*(c+d*x^n)^q/(b*e*(m+n*(p+q+1)+1)) + 
  1/(b*(m+n*(p+q+1)+1))*Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^(q-1)*
    Simp[c*((A*b-a*B)*(m+1)+A*b*n*(p+q+1))+(d*(A*b-a*B)*(m+1)+B*n*q*(b*c-a*d)+A*b*d*n*(p+q+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,A,B,m,n,p},x] && NonzeroQ[b*c-a*d] && RationalQ[q] && q>0


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(A_+B_.*x_^n_)/(c_+d_.*x_^n_),x_Symbol] :=
  Int[ExpandIntegrand[(e*x)^m*(a+b*x^n)^p*(A+B*x^n)/(c+d*x^n),x],x] /;
FreeQ[{a,b,c,d,e,A,B,m,n,p},x] && NonzeroQ[b*c-a*d]


Int[(e_.*x_)^m_.*(a_+b_.*x_^n_)^p_*(c_+d_.*x_^n_)^q_*(A_+B_.*x_^n_),x_Symbol] :=
  A*Int[(e*x)^m*(a+b*x^n)^p*(c+d*x^n)^q,x] + 
  B*(e*x)^m/x^m*Int[x^(m+n)*(a+b*x^n)^p*(c+d*x^n)^q,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n,p,q},x] && NonzeroQ[b*c-a*d]


Int[u_^m_.*(a_.+b_.*w_^n_)^p_.*(c_.+d_.*z_^n_)^q_.*(A_+B_.*v_^n_),x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n)^p*(c+d*x^n)^q*(A+B*x^n),x],x,v] /;
FreeQ[{a,b,c,d,A,B,m,n,p,q},x] && LinearPairQ[u,v,x] && ZeroQ[v-w] && ZeroQ[v-z]


Int[x_^m_.*u_^p_.*v_^q_.*z_,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p*ExpandToSum[v,x]^q*ExpandToSum[z,x],x] /;
FreeQ[{m,p,q},x] && BinomialQ[{u,v,z},x] && ZeroQ[BinomialDegree[u,x]-BinomialDegree[v,x]] && 
  ZeroQ[BinomialDegree[u,x]-BinomialDegree[z,x]] && Not[BinomialMatchQ[{u,v,z},x]]


Int[(a_.+b_.*x_^n_.)^p_*(c_+d_.*x_^r_.)^q_.*(A_+B_.*x_^n_.),x_Symbol] :=
  Int[(a+b*x^n)^p*(d+c*x^n)^q*(A+B*x^n)/x^(n*q),x] /;
FreeQ[{a,b,c,d,A,B,n,p},x] && ZeroQ[n+r] && IntegerQ[q]


Int[(a_.+b_.*x_^n_.)^p_*(c_+d_.*x_^r_.)^q_.*(A_+B_.*x_^n_.),x_Symbol] :=
  x^(n*q)*(c+d/x^n)^q/(d+c*x^n)^q*Int[(a+b*x^n)^p*(d+c*x^n)^q*(A+B*x^n)/x^(n*q),x] /;
FreeQ[{a,b,c,d,A,B,n,p,q},x] && ZeroQ[n+r] && Not[IntegerQ[q]]


Int[x_^m_.*(a_.+b_.*x_^n_.)^p_*(c_+d_.*x_^r_.)^q_.*(A_+B_.*x_^n_.),x_Symbol] :=
  Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q*(A+B*x^n),x] /;
FreeQ[{a,b,c,d,A,B,m,n,p},x] && ZeroQ[n+r] && IntegerQ[q]


Int[x_^m_.*(a_.+b_.*x_^n_.)^p_*(c_+d_.*x_^r_.)^q_.*(A_+B_.*x_^n_.),x_Symbol] :=
  x^(n*q)*(c+d/x^n)^q/(d+c*x^n)^q*Int[x^(m-n*q)*(a+b*x^n)^p*(d+c*x^n)^q*(A+B*x^n),x] /;
FreeQ[{a,b,c,d,A,B,m,n,p,q},x] && ZeroQ[n+r] && Not[IntegerQ[q]]


(* ::Subsection::Closed:: *)
(*2.4.1 (a x^q+b x^n)^p*)


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  Int[((a+b)*x^n)^p,x] /;
FreeQ[{a,b,n,p},x] && ZeroQ[n-q]


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  Int[x^(p*q)*(a+b*x^(n-q))^p,x] /;
FreeQ[{a,b,n,q},x] && IntegerQ[p] && PosQ[n-q]


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^(p+1)/(b*(n-q)(p+1)*x^(n-1)) /;
FreeQ[{a,b,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && ZeroQ[p*q-n+q+1]


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^(p+1)/(b*(n*p+1)*x^(n-1)) - 
  a*(p*q-n+q+1)/(b*(n*p+1))*Int[(a*x^q+b*x^n)^p/x^(n-q),x] /;
FreeQ[{a,b,n,q},x] && Not[IntegerQ[p]] && PosQ[n-q] && RationalQ[p] && p>0 && PositiveIntegerQ[(p*q-n+q+1)/(n-q)]


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^(p+1)/(a*(p*q+1)*x^(q-1)) - 
  b*(n*p+n-q+1)/(a*(p*q+1))*Int[x^(n-q)*(a*x^q+b*x^n)^p,x] /;
FreeQ[{a,b,n,q},x] && Not[IntegerQ[p]] && PosQ[n-q] && RationalQ[p] && p>0 && NonzeroQ[p*q+1] && NegativeIntegerQ[n*p+n-q+1]


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^q+b*x^n)^p/(p*q+1) - 
  b*(n-q)*p/(p*q+1)*Int[x^n*(a*x^q+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[n,p,q] && q<n && p>0 && p*q+1<0


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^q+b*x^n)^p/(n*p+1) + 
  a*(n-q)*p/(n*p+1)*Int[x^q*(a*x^q+b*x^n)^(p-1),x] /;
FreeQ[{a,b,n,q},x] && Not[IntegerQ[p]] && PosQ[n-q] && RationalQ[p] && p>0 && NonzeroQ[n*p+1]


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^(p+1)/(b*(n-q)*(p+1)*x^(n-1)) - 
  (p*q-n+q+1)/(b*(n-q)*(p+1))*Int[(a*x^q+b*x^n)^(p+1)/x^n,x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[n,p,q] && q<n && p<-1 && p*q+1>n-q


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -(a*x^q+b*x^n)^(p+1)/(a*(n-q)*(p+1)*x^(q-1)) + 
  (n*p+n-q+1)/(a*(n-q)*(p+1))*Int[(a*x^q+b*x^n)^(p+1)/x^q,x] /;
FreeQ[{a,b,n,q},x] && Not[IntegerQ[p]] && PosQ[n-q] && RationalQ[p] && p<-1


Int[1/Sqrt[a_.*x_^2+b_.*x_],x_Symbol] :=
  -1/(b*Sqrt[-a/b^2])*ArcSin[1+2*a*x/b] /;
FreeQ[{a,b},x] && PositiveQ[-a/b^2]


Int[1/Sqrt[a_.*x_^2+b_.*x_^n_.],x_Symbol] :=
  2/(2-n)*Subst[Int[1/(1-a*x^2),x],x,x/Sqrt[a*x^2+b*x^n]] /;
FreeQ[{a,b,n},x] && NonzeroQ[n-2]


Int[1/Sqrt[a_.*x_+b_.*x_^n_],x_Symbol] :=
  Sqrt[x]*Sqrt[a+b*x^(n-1)]/Sqrt[a*x+b*x^n]*Int[1/(Sqrt[x]*Sqrt[a+b*x^(n-1)]),x] /;
FreeQ[{a,b,n},x] && (ZeroQ[n-3] || ZeroQ[n-4])


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^(p+1)/(b*(n*p+1)*x^(n-1)) - 
  a*(p*q-n+q+1)/(b*(n*p+1))*Int[(a*x^q+b*x^n)^p/x^(n-q),x] /;
FreeQ[{a,b},x] && RationalQ[n,p,q] && q<n && -1<p<0 && p*q+1>n-q


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^(p+1)/(a*(p*q+1)*x^(q-1)) - 
  b*(n*p+n-q+1)/(a*(p*q+1))*Int[x^(n-q)*(a*x^q+b*x^n)^p,x] /;
FreeQ[{a,b},x] && RationalQ[n,p,q] && q<n && -1<p<0 && p*q+1<0


(* Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^q+b*x^n)^p/(p*(n-q)*((a*x^q+b*x^n)/(b*x^n))^p)*Hypergeometric2F1[-p,-p,1-p,-a/(b*x^(n-q))] /;
FreeQ[{a,b,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && ZeroQ[p*q+1] *)


(* Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x*(a*x^q+b*x^n)^p/((p*q+1)*((a*x^q+b*x^n)/(a*x^q))^p)*
    Hypergeometric2F1[-p,(p*q+1)/(n-q),(p*q+1)/(n-q)+1,-b*x^(n-q)/a] /;
FreeQ[{a,b,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && NonzeroQ[p*q+1] *)


Int[(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^p/(x^(p*q)*(a+b*x^(n-q))^p)*Int[x^(p*q)*(a+b*x^(n-q))^p,x] /;
FreeQ[{a,b,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && PosQ[n-q]


Int[(a_.*u_^q_.+b_.*v_^n_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a*x^q+b*x^n)^p,x],x,u] /;
FreeQ[{a,b,n,p,q},x] && ZeroQ[u-v] && LinearQ[u,x] && NonzeroQ[u-x]


Int[u_^p_,x_Symbol] :=
  Int[ExpandToSum[u,x]^p,x] /;
FreeQ[p,x] && GeneralizedBinomialQ[u,x] && Not[GeneralizedBinomialMatchQ[u,x]]


(* ::Subsection::Closed:: *)
(*2.4.2 x^m (a x^q+b x^n)^p*)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^m*((a+b)*x^n)^p,x] /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[n-q]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^(m+p*q)*(a+b*x^(n-q))^p,x] /;
FreeQ[{a,b,m,n,q},x] && IntegerQ[p] && PosQ[n-q]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m-n+1)*(a*x^q+b*x^n)^(p+1)/(b*(n-q)*(p+1)) /;
FreeQ[{a,b,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && ZeroQ[m+p*q-n+q+1]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m-n+1)*(a*x^q+b*x^n)^(p+1)/(b*(m+n*p+1)) - 
  a*(m+p*q-n+q+1)/(b*(m+n*p+1))*Int[x^(m-n+q)*(a*x^q+b*x^n)^p,x] /;
FreeQ[{a,b,m,n,q},x] && Not[IntegerQ[p]] && PosQ[n-q] && RationalQ[p] && p>0 && PositiveIntegerQ[(m+p*q-n+q+1)/(n-q)]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m-q+1)*(a*x^q+b*x^n)^(p+1)/(a*(m+p*q+1)) - 
  b*(m+n*p+n-q+1)/(a*(m+p*q+1))*Int[x^(m+n-q)*(a*x^q+b*x^n)^p,x] /;
FreeQ[{a,b,m,n,q},x] && Not[IntegerQ[p]] && PosQ[n-q] && RationalQ[p] && p>0 && NonzeroQ[m+p*q+1] && NegativeIntegerQ[m+n*p+n-q+1]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m+1)*(a*x^q+b*x^n)^p/(m+p*q+1) - 
  b*(n-q)*p/(m+p*q+1)*Int[x^(m+n)*(a*x^q+b*x^n)^(p-1),x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[m,n,p,q] && q<n && p>0 && m+p*q+1<0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m+1)*(a*x^q+b*x^n)^p/(m+n*p+1) + 
  a*(n-q)*p/(m+n*p+1)*Int[x^(m+q)*(a*x^q+b*x^n)^(p-1),x] /;
FreeQ[{a,b,m,n,q},x] && Not[IntegerQ[p]] && PosQ[n-q] && RationalQ[p] && p>0 && NonzeroQ[m+n*p+1]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m-n+1)*(a*x^q+b*x^n)^(p+1)/(b*(n-q)*(p+1)) - 
  (m+p*q-n+q+1)/(b*(n-q)*(p+1))*Int[x^(m-n)*(a*x^q+b*x^n)^(p+1),x] /;
FreeQ[{a,b},x] && Not[IntegerQ[p]] && RationalQ[m,n,p,q] && q<n && p<-1 && m+p*q+1>n-q && 
  Not[NegativeIntegerQ[(m+n*p+n-q+1)/(n-q)]]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  -x^(m-q+1)*(a*x^q+b*x^n)^(p+1)/(a*(n-q)*(p+1)) + 
  (m+n*p+n-q+1)/(a*(n-q)*(p+1))*Int[x^(m-q)*(a*x^q+b*x^n)^(p+1),x] /;
FreeQ[{a,b,m,n,q},x] && Not[IntegerQ[p]] && PosQ[n-q] && RationalQ[p] && p<-1


Int[x_^m_./Sqrt[a_.*x_^n_+b_.*x_^j_.],x_Symbol] :=
  1/n*Subst[Int[1/Sqrt[a*x+b*x^2],x],x,x^n] /;
FreeQ[{a,b,n},x] && ZeroQ[j-2*n] && ZeroQ[m-n+1]


Int[x_^m_./Sqrt[a_.*x_^q_.+b_.*x_^n_.],x_Symbol] :=
  -2/(n-q)*Subst[Int[1/(1-a*x^2),x],x,x^(q/2)/Sqrt[a*x^q+b*x^n]] /;
FreeQ[{a,b,n,q},x] && ZeroQ[m-q/2+1] && NonzeroQ[n-q]


Int[x_^m_./Sqrt[a_.*x_^q_.+b_.*x_^n_.],x_Symbol] :=
  x^(q/2)*Sqrt[a+b*x^(n-q)]/Sqrt[a*x^q+b*x^n]*Int[x^(m-q/2)/Sqrt[a+b*x^(n-q)],x] /;
FreeQ[{a,b,m,n,q},x] && PosQ[n-q] && 
	RationalQ[m,n,q] && (m==1 && q==1 && n==3 || m==2 && q==1 && n==4 || (m==1/2 || m==3/2) && q==2 && n==4 || (m==1 || m==2 || m==1/2 || m==5/2) && q==2 && n==5)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m-n+1)*(a*x^q+b*x^n)^(p+1)/(b*(m+n*p+1)) - 
  a*(m+p*q-n+q+1)/(b*(m+n*p+1))*Int[x^(m-n+q)*(a*x^q+b*x^n)^p,x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p,q] && q<n && -1<p<0 && m+p*q+1>n-q


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m-q+1)*(a*x^q+b*x^n)^(p+1)/(a*(m+p*q+1)) - 
  b*(m+n*p+n-q+1)/(a*(m+p*q+1))*Int[x^(m+n-q)*(a*x^q+b*x^n)^p,x] /;
FreeQ[{a,b},x] && RationalQ[m,n,p,q] && q<n && -1<p<0 && m+p*q+1<0


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  Module[{mn=Simplify[m-n+q]},
  x^(mn-q+1)*(a*x^q+b*x^n)^(p+1)/(b*(m+n*p+1)) - 
  a*(mn+p*q+1)/(b*(m+n*p+1))*Int[x^mn*(a*x^q+b*x^n)^p,x]] /;
FreeQ[{a,b,m,n,p,q},x] && Not[RationalQ[p]] && NonzeroQ[n-q] && NonzeroQ[m+n*p+1] && SumSimplerQ[m,-(n-q)]


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  Module[{mn=Simplify[m+n-q]},
  x^(m-q+1)*(a*x^q+b*x^n)^(p+1)/(a*(m+p*q+1)) - 
  b*(mn+n*p+1)/(a*(m+p*q+1))*Int[x^mn*(a*x^q+b*x^n)^p,x]] /;
FreeQ[{a,b,m,n,p,q},x] && Not[RationalQ[p]] && NonzeroQ[n-q] && NonzeroQ[m+p*q+1] && SumSimplerQ[m,n-q]


(* Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m+1)*(a*x^q+b*x^n)^p/(p*(n-q)*((a*x^q+b*x^n)/(b*x^n))^p)*Hypergeometric2F1[-p,-p,1-p,-a/(b*x^(n-q))] /;
FreeQ[{a,b,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && ZeroQ[m+p*q+1] *)


(* Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^(p+1)/(b*(p-1)*(n-q)*x^(2*n+q*(p-1)))*Hypergeometric2F1[1,2,2-p,-a/(b*x^(n-q))] /;
FreeQ[{a,b,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && ZeroQ[m+n+(p-1)*q+1] *)


(* Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  x^(m+1)*(a*x^q+b*x^n)^p/((m+p*q+1)*((a*x^q+b*x^n)/(a*x^q))^p)*
    Hypergeometric2F1[-p,(m+p*q+1)/(n-q),(m+p*q+1)/(n-q)+1,-b*x^(n-q)/a] /;
FreeQ[{a,b,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && NonzeroQ[m+p*q+1] && NonzeroQ[m+n+(p-1)*q+1] *)


Int[x_^m_.*(a_.*x_^q_.+b_.*x_^n_.)^p_,x_Symbol] :=
  (a*x^q+b*x^n)^p/(x^(p*q)*(a+b*x^(n-q))^p)*Int[x^(m+p*q)*(a+b*x^(n-q))^p,x] /;
FreeQ[{a,b,m,n,p,q},x] && Not[IntegerQ[p]] && NonzeroQ[n-q] && PosQ[n-q]


Int[u_^m_.*(a_.*v_^q_.+b_.*w_^n_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[x^m*(a*x^q+b*x^n)^p,x],x,u] /;
FreeQ[{a,b,m,n,p,q},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]


Int[x_^m_.*u_^p_.,x_Symbol] :=
  Int[x^m*ExpandToSum[u,x]^p,x] /;
FreeQ[{m,p},x] && GeneralizedBinomialQ[u,x] && Not[GeneralizedBinomialMatchQ[u,x]]
