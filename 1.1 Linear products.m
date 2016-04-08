(* ::Package:: *)

(* ::Section:: *)
(*Linear Product Rules*)


(* ::Subsection::Closed:: *)
(*1.1 (a+b x)^m*)


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





(* ::Subsection::Closed:: *)
(*1.2 (a+b x)^m (c+d x)^n*)


Int[1/((a_+b_.*x_)*(c_+d_.*x_)),x_Symbol] :=
  Int[1/(a*c+b*d*x^2),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c+a*d]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*x),x] - d/(b*c-a*d)*Int[1/(c+d*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


Int[(a_.+b_.*x_)^m_.*(c_+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && ZeroQ[m+n+2] && NonzeroQ[m+1]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
  x*(a+b*x)^m*(c+d*x)^m/(2*m+1) + 2*a*c*m/(2*m+1)*Int[(a+b*x)^(m-1)*(c+d*x)^(m-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c+a*d] && PositiveIntegerQ[m+1/2]


Int[1/((a_+b_.*x_)^(3/2)*(c_+d_.*x_)^(3/2)),x_Symbol] :=
  x/(a*c*Sqrt[a+b*x]*Sqrt[c+d*x]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c+a*d]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
  -x*(a+b*x)^(m+1)*(c+d*x)^(m+1)/(2*a*c*(m+1)) + 
  (2*m+3)/(2*a*c*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(m+1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c+a*d] && NegativeIntegerQ[m+3/2]


Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^m_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[b*c+a*d] && (IntegerQ[m] || PositiveQ[a] && PositiveQ[c])


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  ArcCosh[b*x/a]/b /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c+a*d] && PositiveQ[a] && ZeroQ[a+c]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2*Subst[Int[1/(b-d*x^2),x],x,Sqrt[a+b*x]/Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c+a*d]


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^m_,x_Symbol] :=
  (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m]*Int[(a*c+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[b*c+a*d] && Not[IntegerQ[2*m]]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) + 
  2*c*n/(m+n+1)*Int[(a+b*x)^m*(c+d*x)^(n-1),x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c+a*d] && IntegerQ[m+1/2] && IntegerQ[n+1/2] && 0<m<n


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  -(a+b*x)^(m+1)*(c+d*x)^(n+1)/(2*a*d*(m+1)) + 
  (m+n+2)/(2*a*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b*c+a*d] && IntegerQ[m+1/2] && IntegerQ[n+1/2] && m<n<0


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && PositiveIntegerQ[m] && 
  (Not[IntegerQ[n]] || ZeroQ[c] && 7*m+4*n<=0 || 9*m+5*(n+1)<0 || m+n+2>0)


Int[(a_+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[m] && IntegerQ[n] && Not[PositiveIntegerQ[n] && m+n+2<0]


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  (c+d*x)^n/(b*n) + 
  (b*c-a*d)/b*Int[(c+d*x)^(n-1)/(a+b*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[n] && n>0


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
  With[{p=Denominator[n]},
  p*Subst[Int[x^(p*(n+1)-1)/(a*d-b*c+b*x^p),x],x,(c+d*x)^(1/p)]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[n] && -1<n<0


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  -(c+d*x)^(n+1)/((n+1)*(b*c-a*d)) + 
  b*(n+1)/((n+1)*(b*c-a*d))*Int[(c+d*x)^(n+1)/(a+b*x),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[n] && n<-1


Int[(c_+d_.*x_)^n_/x_,x_Symbol] :=
  -(c+d*x)^(n+1)/(c*(n+1))*Hypergeometric2F1[1,n+1,n+2,1+d*x/c] /;
FreeQ[{c,d,n},x] && Not[IntegerQ[n]]


Int[(c_.+d_.*x_)^n_/(a_+b_.*x_),x_Symbol] :=
  -(c+d*x)^(n+1)/((n+1)*(b*c-a*d))*Hypergeometric2F1[1,n+1,n+2,TogetherSimplify[b*(c+d*x)/(b*c-a*d)]] /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && Not[IntegerQ[n]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+1)) - 
  d*n/(b*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && m<-1 && n>0 && Not[IntegerQ[n] && Not[IntegerQ[m]]] && 
  Not[IntegerQ[m+n] && m+n+2<=0 && (FractionQ[m] || 2*n+m+1>=0)] && 
  (IntegerQ[m] || IntegerQ[n] || IntegersQ[2*m,2*n] || IntegerQ[m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) - 
  d*(m+n+2)/((b*c-a*d)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && m<-1 && 
  Not[n<-1 && (ZeroQ[a] || NonzeroQ[c] && m<n && IntegerQ[n])] && 
  (IntegerQ[m] || IntegerQ[n] || IntegersQ[2*m,2*n] || IntegerQ[m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) + 
  n*(b*c-a*d)/(b*(m+n+1))*Int[(a+b*x)^m*(c+d*x)^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && n>0 && m+n+1!=0 && 
  Not[PositiveIntegerQ[m] && (Not[IntegerQ[n]] || 0<m<n)] && 
  Not[IntegerQ[m+n] && m+n+2<0] && 
  (IntegerQ[m] || IntegerQ[n] || IntegersQ[2*m,2*n] || IntegerQ[m+n])


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  Int[1/Sqrt[a*c-b*(a-c)*x-b^2*x^2],x] /;
FreeQ[{a,b,c,d},x] && ZeroQ[b+d] && PositiveQ[a+c]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  2/Sqrt[b]*Subst[Int[1/Sqrt[b*c-a*d+d*x^2],x],x,Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d},x] && PositiveQ[b*c-a*d] && PositiveQ[b]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2/b*Subst[Int[1/Sqrt[c-a+x^2],x],x,Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && ZeroQ[b-d]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  2*Subst[Int[1/(b-d*x^2),x],x,Sqrt[a+b*x]/Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d]


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
  With[{p=Denominator[m]},
  p*Subst[Int[x^(p*(m+1)-1)/(b-d*x^p),x],x,(a+b*x)^(1/p)/(c+d*x)^(1/p)]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && -1<m<0 && m+n+1==0


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  With[{p=Denominator[m]},
  p/b*Subst[Int[x^(p*(m+1)-1)*(c-a*d/b+d*x^p/b)^n,x],x,(a+b*x)^(1/p)]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[b*c-a*d] && RationalQ[m,n] && -1<m<0 && -1<n<0 && Denominator[n]<=Denominator[m] && 
  (IntegerQ[m] || IntegerQ[n] || IntegersQ[2*m,2*n] || IntegerQ[m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) - 
  d*Simplify[m+n+2]/((b*c-a*d)*(m+1))*Int[(a+b*x)^Simplify[m+1]*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && NegativeIntegerQ[Simplify[m+n+2]] && NonzeroQ[m+1] && 
  (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  c^n*(b*x)^(m+1)/(b*(m+1))*Hypergeometric2F1[-n,m+1,m+2,-d*x/c] /;
FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && (IntegerQ[n] || PositiveQ[c] && 
  Not[ZeroQ[n+1/2] && ZeroQ[c^2-d^2] && PositiveQ[-d/(b*c)]])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (c+d*x)^(n+1)/(d*(n+1)*(-d/(b*c))^m)*Hypergeometric2F1[-m,n+1,n+2,1+d*x/c] /;
FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && PositiveQ[-d/(b*c)]


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  c^IntPart[n]*(c+d*x)^FracPart[n]/((c+d*x)/c)^FracPart[n]*Int[(b*x)^m*(1+d*x/c)^n,x] /;
FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[PositiveQ[c]] && Not[PositiveQ[-d/(b*c)]] && 
  (RationalQ[m] && Not[ZeroQ[n+1/2] && ZeroQ[c^2-d^2]] || Not[RationalQ[n]])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (-b*c/d)^IntPart[m]*(b*x)^FracPart[m]/(-d*x/c)^FracPart[m]*Int[(-d*x/c)^m*(c+d*x)^n,x] /;
FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[PositiveQ[c]] && Not[PositiveQ[-d/(b*c)]]


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (b*c-a*d)^n*(a+b*x)^(m+1)/(b^(n+1)*(m+1))*Hypergeometric2F1[-n,m+1,m+2,-d*(a+b*x)/(b*c-a*d)] /;
FreeQ[{a,b,c,d,m},x] && NonzeroQ[b*c-a*d] && Not[IntegerQ[m]] && IntegerQ[n]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)/(b*(m+1)*(b/(b*c-a*d))^n)*Hypergeometric2F1[m+1,-n,m+2,-d*(a+b*x)/(b*c-a*d)] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && PositiveQ[b/(b*c-a*d)] && 
  (RationalQ[m] || Not[RationalQ[n] && PositiveQ[-d/(b*c-a*d)]])


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (c+d*x)^FracPart[n]/((b/(b*c-a*d))^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n])*
    Int[(a+b*x)^m*(b*c/(b*c-a*d)+b*d*x/(b*c-a*d))^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && NonzeroQ[b*c-a*d] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && (RationalQ[m] || Not[SimplerQ[n+1,m+1]])


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*v_)^n_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n,x],x,u] /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[u-v] && LinearQ[u,x] && NonzeroQ[Coefficient[u,x,0]]





(* ::Subsection::Closed:: *)
(*1.3 (a+b x)^m (c+d x)^n (e+f x)^p*)


Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[b*c+a*d] && ZeroQ[m-n] && 
  (IntegerQ[m] || ZeroQ[e] && PositiveQ[a] && PositiveQ[c] && Not[RationalQ[m]])


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+2)) /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[n+p+2] && ZeroQ[a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1))]


Int[(a_+b_.*x_)*(d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)*(d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && PositiveIntegerQ[p] && ZeroQ[b*e+a*f] && Not[NegativeIntegerQ[n+p+2] && n+2*p>0]


Int[(a_+b_.*x_)*(d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)*(d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && PositiveIntegerQ[p] && (NonzeroQ[n+1] || p==1) && NonzeroQ[b*e+a*f] &&
  (Not[IntegerQ[n]] || 9*p+5*n<0 || n+p+1>=0 || n+p+2>=0 && RationalQ[a,b,d,e,f])


Int[(a_.+b_.*x_)*(c_+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[b*c-a*d] && 
  (NegativeIntegerQ[n,p] || ZeroQ[p-1] || 
    PositiveIntegerQ[p] && (Not[IntegerQ[n]] || 9*p+5*(n+2)<=0 || n+p+1>=0 || n+p+2>=0 && RationalQ[a,b,c,d,e,f]))


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) + 
  b/f*Int[(c+d*x)^n*(e+f*x)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[n+p+2] && NonzeroQ[p+1] && Not[SumSimplerQ[n,1] && Not[SumSimplerQ[p,1]]]


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) - 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(f*(p+1)*(c*f-d*e))*Int[(c+d*x)^n*(e+f*x)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NonzeroQ[n+p+2] && RationalQ[p] && p<-1 && 
  (Not[RationalQ[n] && n<-1] || IntegerQ[p] || Not[IntegerQ[n] || Not[ZeroQ[e] || Not[ZeroQ[c] || p<n]]])


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) - 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(f*(p+1)*(c*f-d*e))*Int[(c+d*x)^n*(e+f*x)^Simplify[p+1],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[n+p+2] && Not[RationalQ[p]] && SumSimplerQ[p,1]


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+2)) + 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(d*f*(n+p+2))*Int[(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[n+p+2]


Int[(e_.+f_.*x_)^p_./((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^p/((a+b*x)*(c+d*x)),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IntegerQ[p]


Int[(e_.+f_.*x_)^p_./((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)/(a+b*x),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[p] && 0<p<1


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  f*(e+f*x)^(p-1)/(b*d*(p-1)) + 
 1/(b*d)*Int[(b*d*e^2-a*c*f^2+f*(2*b*d*e-b*c*f-a*d*f)*x)*(e+f*x)^(p-2)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[p] && p>1


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  f*(e+f*x)^(p+1)/((p+1)*(b*e-a*f)*(d*e-c*f)) + 
  1/((b*e-a*f)*(d*e-c*f))*Int[(b*d*e-b*c*f-a*d*f-b*d*f*x)*(e+f*x)^(p+1)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[p] && p<-1


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  b/(b*c-a*d)*Int[(e+f*x)^p/(a+b*x),x] - 
  d/(b*c-a*d)*Int[(e+f*x)^p/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && Not[IntegerQ[p]]


Int[(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_/(a_.+b_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^FractionalPart[p],(c+d*x)^n*(e+f*x)^IntegerPart[p]/(a+b*x),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveIntegerQ[n] && FractionQ[p] && p<-1


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && IntegersQ[m,n] && (IntegerQ[p] || m>0 && n>=-1)


Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (b*c-a*d)^2*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d^2*(d*e-c*f)*(n+1)) - 
  1/(d^2*(d*e-c*f)*(n+1))*Int[(c+d*x)^(n+1)*(e+f*x)^p*
    Simp[a^2*d^2*f*(n+p+2)+b^2*c*(d*e*(n+1)+c*f*(p+1))-2*a*b*d*(d*e*(n+1)+c*f*(p+1))-b^2*d*(d*e-c*f)*(n+1)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && (RationalQ[n] && n<-1 || ZeroQ[n+p+3] && NonzeroQ[n+1] && (SumSimplerQ[n,1] || Not[SumSimplerQ[p,1]]))


Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+3)) + 
  1/(d*f*(n+p+3))*Int[(c+d*x)^n*(e+f*x)^p*
    Simp[a^2*d*f*(n+p+3)-b*(b*c*e+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(n+p+4)-b*(d*e*(n+2)+c*f*(p+2)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NonzeroQ[n+p+3]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(2/3)),x_Symbol] :=
  -Log[a+b*x]/(2*Rt[b*c-a*d,3]*Rt[b*e-a*f,3]^2) + 
  Sqrt[3]/(Rt[b*c-a*d,3]*Rt[b*e-a*f,3]^2)*ArcTan[1/Sqrt[3]*(1+2*Rt[b*e-a*f,3]*(c+d*x)^(1/3)/(Rt[b*c-a*d,3]*(e+f*x)^(1/3)))] + 
  3/(2*Rt[b*c-a*d,3]*Rt[b*e-a*f,3]^2)*Log[Rt[b*e-a*f,3]*(c+d*x)^(1/3)-Rt[b*c-a*d,3]*(e+f*x)^(1/3)] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[b*c-a*d] && PosQ[b*e-a*f]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(2/3)),x_Symbol] :=
  -Log[a+b*x]/(2*Rt[b*c-a*d,3]*Rt[-(b*e-a*f),3]^2) + 
  Sqrt[3]/(Rt[b*c-a*d,3]*Rt[-(b*e-a*f),3]^2)*ArcTan[1/Sqrt[3]*(1-2*Rt[-(b*e-a*f),3]*(c+d*x)^(1/3)/(Rt[b*c-a*d,3]*(e+f*x)^(1/3)))] + 
  3/(2*Rt[b*c-a*d,3]*Rt[-(b*e-a*f),3]^2)*Log[Rt[-(b*e-a*f),3]*(c+d*x)^(1/3)+Rt[b*c-a*d,3]*(e+f*x)^(1/3)] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[b*c-a*d] && NegQ[b*e-a*f]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(2/3)),x_Symbol] :=
  Log[a+b*x]/(2*Rt[-(b*c-a*d),3]*Rt[b*e-a*f,3]^2) - 
  Sqrt[3]/(Rt[-(b*c-a*d),3]*Rt[b*e-a*f,3]^2)*ArcTan[1/Sqrt[3]*(1-2*Rt[b*e-a*f,3]*(c+d*x)^(1/3)/(Rt[-(b*c-a*d),3]*(e+f*x)^(1/3)))] - 
  3/(2*Rt[-(b*c-a*d),3]*Rt[b*e-a*f,3]^2)*Log[Rt[b*e-a*f,3]*(c+d*x)^(1/3)+Rt[-(b*c-a*d),3]*(e+f*x)^(1/3)] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[b*c-a*d] && PosQ[b*e-a*f]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(2/3)),x_Symbol] :=
  Log[a+b*x]/(2*Rt[-(b*c-a*d),3]*Rt[-(b*e-a*f),3]^2) - 
  Sqrt[3]/(Rt[-(b*c-a*d),3]*Rt[-(b*e-a*f),3]^2)*
    ArcTan[1/Sqrt[3]*(1+2*Rt[-(b*e-a*f),3]*(c+d*x)^(1/3)/((-(b*c-a*d))^(1/3)*(e+f*x)^(1/3)))] - 
  3/(2*Rt[-(b*c-a*d),3]*Rt[-(b*e-a*f),3]^2)*Log[Rt[-(b*e-a*f),3]*(c+d*x)^(1/3)-(-(b*c-a*d))^(1/3)*(e+f*x)^(1/3)] /;
FreeQ[{a,b,c,d,e,f},x] && NegQ[b*c-a*d] && NegQ[b*e-a*f]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)),x_Symbol] :=
  b*f*Subst[Int[1/(d*(b*e-a*f)^2+b*f^2*x^2),x],x,Sqrt[a+b*x]*Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[2*b*d*e-f*(b*c+a*d)]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_),x_Symbol] :=
  With[{q=Denominator[m]},
  q*Subst[Int[x^(q*(m+1)-1)/(b*e-a*f-(d*e-c*f)*x^q),x],x,(a+b*x)^(1/q)/(c+d*x)^(1/q)]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[m+n+1] && RationalQ[m,n] && -1<m<0 && SimplerQ[a+b*x,c+d*x]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((m+1)*(b*e-a*f)) - 
  n*(d*e-c*f)/((m+1)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && ZeroQ[m+n+p+2] && RationalQ[n] && n>0 && Not[SumSimplerQ[p,1] && Not[SumSimplerQ[m,1]]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_,x_Symbol] :=
  (b*c-a*d)^n*(a+b*x)^(m+1)/((m+1)*(b*e-a*f)^(n+1)*(e+f*x)^(m+1))*
    Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && ZeroQ[m+n+p+2] && NegativeIntegerQ[n]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((b*e-a*f)*(m+1))*((b*e-a*f)*(c+d*x)/((b*c-a*d)*(e+f*x)))^(-n)*
    Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[m+n+p+2] && Not[IntegerQ[n]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((b*e-a*f)*(m+1))*((b*e-a*f)*(c+d*x)/((b*c-a*d)*(e+f*x)))^(-n)*
    Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[m+n+p+2] && Not[IntegerQ[n]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[Simplify[m+n+p+3]] && ZeroQ[a*d*f*(m+1)+b*c*f*(n+1)+b*d*e*(p+1)] && NonzeroQ[m+1]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  (a*d*f*(m+1)+b*c*f*(n+1)+b*d*e*(p+1))/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[Simplify[m+n+p+3]] && (RationalQ[m] && m<-1 || SumSimplerQ[m,1])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p/(b*(m+1)) - 
  1/(b*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^(p-1)*Simp[d*e*n+c*f*p+d*f*(n+p)*x,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[m,n,p] && m<-1 && n>0 && p>0 && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (b*c-a*d)*(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) + 
  1/(b*(b*e-a*f)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-2)*(e+f*x)^p*
    Simp[a*d*(d*e*(n-1)+c*f*(p+1))+b*c*(d*e*(m-n+2)-c*f*(m+p+2))+d*(a*d*f*(n+p)+b*(d*e*(m+1)-c*f*(m+n+p+1)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && RationalQ[m,n,p] && m<-1 && n>1 && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((m+1)*(b*e-a*f)) - 
  1/((m+1)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[d*e*n+c*f*(m+p+2)+d*f*(m+n+p+2)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && RationalQ[m,n,p] && m<-1 && n>0 && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^n*(e+f*x)^(p+1)/(f*(m+n+p+1)) - 
  1/(f*(m+n+p+1))*Int[(a+b*x)^(m-1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[c*m*(b*e-a*f)+a*n*(d*e-c*f)+(d*m*(b*e-a*f)+b*n*(d*e-c*f))*x,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[m,n,p] && m>0 && n>0 && NonzeroQ[m+n+p+1] && (IntegersQ[2*m,2*n,2*p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+1)) + 
  1/(d*f*(m+n+p+1))*Int[(a+b*x)^(m-2)*(c+d*x)^n*(e+f*x)^p*
    Simp[a^2*d*f*(m+n+p+1)-b*(b*c*e*(m-1)+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(2*m+n+p)-b*(d*e*(m+n)+c*f*(m+p)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && RationalQ[m] && m>1 && NonzeroQ[m+n+p+1] && IntegerQ[m]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+1)) + 
  1/(d*f*(m+n+p+1))*Int[(a+b*x)^(m-2)*(c+d*x)^n*(e+f*x)^p*
    Simp[a^2*d*f*(m+n+p+1)-b*(b*c*e*(m-1)+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(2*m+n+p)-b*(d*e*(m+n)+c*f*(m+p)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && RationalQ[m] && m>1 && NonzeroQ[m+n+p+1] && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && RationalQ[m] && m<-1 && IntegerQ[m] && (IntegerQ[n] || IntegerQ[n+p])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && RationalQ[m] && m<-1 && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_),x_Symbol] :=
  b/f*Int[(a+b*x)^(m-1)*(c+d*x)^n,x] - (b*e-a*f)/f*Int[(a+b*x)^(m-1)*(c+d*x)^n/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && PositiveIntegerQ[Simplify[m+n+1]] && 
  (RationalQ[m] && m>0 || Not[RationalQ[m]] && (SumSimplerQ[m,-1] || Not[SumSimplerQ[n,-1]]))


(* Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  b/f*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^(p+1),x] - (b*e-a*f)/f*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NegativeIntegerQ[p] && PositiveIntegerQ[m+n+p+2] && Not[SimplerQ[c+d*x,a+b*x]] *)


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(1/4)),x_Symbol] :=
  2*Rt[(d*e-c*f)/d,4]^3*Sqrt[-f*(c+d*x)/(d*e-c*f)]/((b*e-a*f)*Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2]*Sqrt[c+d*x])*
   (EllipticPi[Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2],-ArcSin[(e+f*x)^(1/4)/Rt[(d*e-c*f)/d,4]],-1] - 
    EllipticPi[-Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2],-ArcSin[(e+f*x)^(1/4)/Rt[(d*e-c*f)/d,4]],-1]) /;
FreeQ[{a,b,c,d,e,f},x]


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(3/4)),x_Symbol] :=
  2*Rt[(d*e-c*f)/d,4]*Sqrt[-f*(c+d*x)/(d*e-c*f)]/((b*e-a*f)*Sqrt[c+d*x])*
    (EllipticPi[-Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2],-ArcSin[(e+f*x)^(1/4)/Rt[(d*e-c*f)/d,4]],-1] + 
     EllipticPi[Rt[b*(d*e-c*f)/(d*(b*e-a*f)),2],-ArcSin[(e+f*x)^(1/4)/Rt[(d*e-c*f)/d,4]],-1]) /;
FreeQ[{a,b,c,d,e,f},x]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2*Sqrt[e]/b*Rt[-b/d,2]*EllipticE[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && PositiveQ[c] && PositiveQ[e] && Not[NegativeQ[-b/d]]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[-b*x]/Sqrt[b*x]*Int[Sqrt[e+f*x]/(Sqrt[-b*x]*Sqrt[c+d*x]),x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && PositiveQ[c] && PositiveQ[e] && NegativeQ[-b/d]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[e+f*x]*Sqrt[(c+d*x)/c]/(Sqrt[c+d*x]*Sqrt[(e+f*x)/e])*Int[Sqrt[1+f*x/e]/(Sqrt[b*x]*Sqrt[1+d*x/c]),x] /;
FreeQ[{b,c,d,e,f},x] && NonzeroQ[d*e-c*f] && Not[PositiveQ[c] && PositiveQ[e]]


(* Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  f/b*Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]),x] - 
  f/b*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[b*e-f*(a-1)] *)


(* Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2/b*Rt[-(b*c-a*d)/d,2]*Sqrt[(b*e-a*f)/(b*c-a*d)]*
    EllipticE[ArcSin[Sqrt[a+b*x]/Rt[-(b*c-a*d)/d,2]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)] && Not[NegativeQ[-(b*c-a*d)/d]] && 
  Not[SimplerQ[c+d*x,a+b*x] && PositiveQ[-d/(b*c-a*d)] && PositiveQ[d/(d*e-c*f)] && Not[NegativeQ[(b*c-a*d)/b]]] *)


Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2/b*Rt[-(b*e-a*f)/d,2]*EllipticE[ArcSin[Sqrt[a+b*x]/Rt[-(b*c-a*d)/d,2]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)] && Not[NegativeQ[-(b*c-a*d)/d]] && 
  Not[SimplerQ[c+d*x,a+b*x] && PositiveQ[-d/(b*c-a*d)] && PositiveQ[d/(d*e-c*f)] && Not[NegativeQ[(b*c-a*d)/b]]]


Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[e+f*x]*Sqrt[b*(c+d*x)/(b*c-a*d)]/(Sqrt[c+d*x]*Sqrt[b*(e+f*x)/(b*e-a*f)])*
    Int[Sqrt[Simp[b*e/(b*e-a*f)+b*f*x/(b*e-a*f),x]]/(Sqrt[a+b*x]*Sqrt[Simp[b*c/(b*c-a*d)+b*d*x/(b*c-a*d),x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)]] && Not[NegativeQ[-(b*c-a*d)/d]]


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
FreeQ[{a,b,c,d,e,f},x] && PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)] && Not[NegativeQ[-(b*c-a*d)/d]] && 
  SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  Sqrt[-a-b*x]/Sqrt[a+b*x]*Int[1/(Sqrt[-a-b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)] && NegativeQ[-(b*c-a*d)/d] && 
  SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  Sqrt[b*(c+d*x)/(b*c-a*d)]*Sqrt[b*(e+f*x)/(b*e-a*f)]/(Sqrt[c+d*x]*Sqrt[e+f*x])*
    Int[1/(Sqrt[a+b*x]*Sqrt[Simp[b*c/(b*c-a*d)+b*d*x/(b*c-a*d),x]]*Sqrt[Simp[b*e/(b*e-a*f)+b*f*x/(b*e-a*f),x]]),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[PositiveQ[b/(b*c-a*d)] && PositiveQ[b/(b*e-a*f)]] && 
  SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m*(f*x)^p,x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && ZeroQ[b*c+a*d] && ZeroQ[m-n] && PositiveQ[a] && PositiveQ[c]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m]*Int[(a*c+b*d*x^2)^m*(f*x)^p,x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && ZeroQ[b*c+a*d] && ZeroQ[m-n]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
   Int[ExpandIntegrand[(a+b*x)^n*(c+d*x)^n*(f*x)^p,(a+b*x)^(m-n),x],x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && ZeroQ[b*c+a*d] && PositiveIntegerQ[m-n]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && (PositiveIntegerQ[m] || NegativeIntegerQ[m,n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && NegativeIntegerQ[m+n+p+2] && NonzeroQ[m+1] && 
  (SumSimplerQ[m,1] || Not[NonzeroQ[n+1] && SumSimplerQ[n,1]] && Not[NonzeroQ[p+1] && SumSimplerQ[p,1]])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_Symbol] :=
  c^n*e^p*(b*x)^(m+1)/(b*(m+1))*AppellF1[m+1,-n,-p,m+2,-d*x/c,-f*x/e] /;
FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && PositiveQ[c] && (IntegerQ[p] || PositiveQ[e])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_Symbol] :=
  (c+d*x)^(n+1)/(d*(n+1)*(-d/(b*c))^m*(d/(d*e-c*f))^p)*AppellF1[n+1,-m,-p,n+2,1+d*x/c,-f*(c+d*x)/(d*e-c*f)] /;
FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && PositiveQ[-d/(b*c)] && (IntegerQ[p] || PositiveQ[d/(d*e-c*f)])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_Symbol] :=
  c^IntPart[n]*(c+d*x)^FracPart[n]/((c+d*x)/c)^FracPart[n]*Int[(b*x)^m*(1+d*x/c)^n*(e+f*x)^p,x] /;
FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[PositiveQ[c]]


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (b*e-a*f)^p*(a+b*x)^(m+1)/(b^(p+1)*(m+1)*(b/(b*c-a*d))^n)*
    AppellF1[m+1,-n,-p,m+2,-d*(a+b*x)/(b*c-a*d),-f*(a+b*x)/(b*e-a*f)] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && IntegerQ[p] && PositiveQ[b/(b*c-a*d)] && 
  (RationalQ[m] || Not[RationalQ[n] && PositiveQ[-d/(b*c-a*d)]])


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (c+d*x)^FracPart[n]/((b/(b*c-a*d))^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n])*
    Int[(a+b*x)^m*(b*c/(b*c-a*d)+b*d*x/(b*c-a*d))^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && IntegerQ[p] && Not[PositiveQ[b/(b*c-a*d)]] && 
  (RationalQ[m] || Not[RationalQ[n]])


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (a+b*x)^(m+1)/(b*(m+1)*(b/(b*c-a*d))^n*(b/(b*e-a*f))^p)*AppellF1[m+1,-n,-p,m+2,-d*(a+b*x)/(b*c-a*d),-f*(a+b*x)/(b*e-a*f)] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && PositiveQ[b/(b*c-a*d)] && 
  PositiveQ[b/(b*e-a*f)] && (RationalQ[m] || 
    Not[RationalQ[n] && PositiveQ[-d/(b*c-a*d)] && PositiveQ[d/(d*e-c*f)] || 
      RationalQ[p] && PositiveQ[-f/(d*e-c*f)] && PositiveQ[-f/(b*e-a*f)]])


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (e+f*x)^FracPart[p]/((b/(b*e-a*f))^IntPart[p]*(b*(e+f*x)/(b*e-a*f))^FracPart[p])*
    Int[(a+b*x)^m*(c+d*x)^n*(b*e/(b*e-a*f)+b*f*x/(b*e-a*f))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && PositiveQ[b/(b*c-a*d)] && 
  Not[PositiveQ[b/(b*e-a*f)]] && (RationalQ[m] || 
    Not[RationalQ[n] && PositiveQ[-d/(b*c-a*d)] && Not[PositiveQ[d/(d*e-c*f)]] || 
      RationalQ[p] && PositiveQ[-f/(d*e-c*f)] && Not[PositiveQ[-f/(b*e-a*f)]]])


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (c+d*x)^FracPart[n]/((b/(b*c-a*d))^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n])*
    Int[(a+b*x)^m*(b*c/(b*c-a*d)+b*d*x/(b*c-a*d))^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && Not[PositiveQ[b/(b*c-a*d)]] && 
  (RationalQ[m] || Not[RationalQ[n] || RationalQ[p]])


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*v_)^n_.*(e_+f_.*w_)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ZeroQ[u-v] && ZeroQ[u-w] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q*)


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)*(g+h*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && (PositiveIntegerQ[m] || IntegersQ[m,n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  (b^2*d*e*g-a^2*d*f*h*m-a*b*(d*(f*g+e*h)-c*f*h*(m+1))+b*f*h*(b*c-a*d)*(m+1)*x)*(a+b*x)^(m+1)*(c+d*x)^(n+1)/
    (b^2*d*(b*c-a*d)*(m+1)) + 
  (a*d*f*h*m+b*(d*(f*g+e*h)-c*f*h*(m+2)))/(b^2*d)*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && ZeroQ[m+n+2] && NonzeroQ[m+1] && Not[SumSimplerQ[n,1] && Not[SumSimplerQ[m,1]]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  (b^2*c*d*e*g*(n+1)+a^2*c*d*f*h*(n+1)+a*b*(d^2*e*g*(m+1)+c^2*f*h*(m+1)-c*d*(f*g+e*h)*(m+n+2))+
      (a^2*d^2*f*h*(n+1)-a*b*d^2*(f*g+e*h)*(n+1)+b^2*(c^2*f*h*(m+1)-c*d*(f*g+e*h)*(m+1)+d^2*e*g*(m+n+2)))*x)/
    (b*d*(b*c-a*d)^2*(m+1)*(n+1))*(a+b*x)^(m+1)*(c+d*x)^(n+1) - 
  (a^2*d^2*f*h*(2+3*n+n^2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
      b^2*(c^2*f*h*(2+3*m+m^2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(6+m^2+5*n+n^2+m*(2*n+5))))/
    (b*d*(b*c-a*d)^2*(m+1)*(n+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && RationalQ[m,n] && m<-1 && n<-1


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  (b^3*c*e*g*(m+2)-a^3*d*f*h*(n+2)-a^2*b*(c*f*h*m-d*(f*g+e*h)*(m+n+3))-a*b^2*(c*(f*g+e*h)+d*e*g*(2*m+n+4))+
      b*(a^2*d*f*h*(m-n)-a*b*(2*c*f*h*(m+1)-d*(f*g+e*h)*(n+1))+b^2*(c*(f*g+e*h)*(m+1)-d*e*g*(m+n+2)))*x)/
    (b^2*(b*c-a*d)^2*(m+1)*(m+2))*(a+b*x)^(m+1)*(c+d*x)^(n+1) + 
  (f*h/b^2-(d*(m+n+3)*(a^2*d*f*h*(m-n)-a*b*(2*c*f*h*(m+1)-d*(f*g+e*h)*(n+1))+b^2*(c*(f*g+e*h)*(m+1)-d*e*g*(m+n+2))))/
      (b^2*(b*c-a*d)^2*(m+1)*(m+2)))*
    Int[(a+b*x)^(m+2)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && (RationalQ[m] && m<-2 || ZeroQ[m+n+3] && Not[RationalQ[n] && n<-2])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  (a^2*d*f*h*(n+2)+b^2*d*e*g*(m+n+3)+a*b*(c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+b*f*h*(b*c-a*d)*(m+1)*x)/
    (b^2*d*(b*c-a*d)*(m+1)*(m+n+3))*(a+b*x)^(m+1)*(c+d*x)^(n+1) - 
  (a^2*d^2*f*h*(n+1)*(n+2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
      b^2*(c^2*f*h*(m+1)*(m+2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(m+n+2)*(m+n+3)))/
    (b^2*d*(b*c-a*d)*(m+1)*(m+n+3))*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && (RationalQ[m] && -2<=m<-1 || SumSimplerQ[m,1]) && NonzeroQ[m+1] && NonzeroQ[m+n+3]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  -(a*d*f*h*(n+2)+b*c*f*h*(m+2)-b*d*(f*g+e*h)*(m+n+3)-b*d*f*h*(m+n+2)*x)*(a+b*x)^(m+1)*(c+d*x)^(n+1)/
    (b^2*d^2*(m+n+2)*(m+n+3)) + 
  (a^2*d^2*f*h*(n+1)*(n+2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
      b^2*(c^2*f*h*(m+1)*(m+2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(m+n+2)*(m+n+3)))/
    (b^2*d^2*(m+n+2)*(m+n+3))*Int[(a+b*x)^m*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && NonzeroQ[m+n+2] && NonzeroQ[m+n+3]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && (IntegersQ[m,n,p] || PositiveIntegerQ[n,p])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) - 
  1/(b*(b*e-a*f)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[b*c*(f*g-e*h)*(m+1)+(b*g-a*h)*(d*e*n+c*f*(p+1))+d*(b*(f*g-e*h)*(m+1)+f*(b*g-a*h)*(n+p+1))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p},x] && RationalQ[m,n] && m<-1 && n>0 && IntegerQ[m]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) - 
  1/(b*(b*e-a*f)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[b*c*(f*g-e*h)*(m+1)+(b*g-a*h)*(d*e*n+c*f*(p+1))+d*(b*(f*g-e*h)*(m+1)+f*(b*g-a*h)*(n+p+1))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p},x] && RationalQ[m,n] && m<-1 && n>0 && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && RationalQ[m] && m<-1 && IntegerQ[m]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && RationalQ[m] && m<-1 && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  h*(a+b*x)^m*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+2)) + 
  1/(d*f*(m+n+p+2))*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*g*(m+n+p+2)-h*(b*c*e*m+a*(d*e*(n+1)+c*f*(p+1)))+(b*d*f*g*(m+n+p+2)+h*(a*d*f*m-b*(d*e*(m+n+1)+c*f*(m+p+1))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && RationalQ[m] && m>0 && NonzeroQ[m+n+p+2] && IntegerQ[m]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  h*(a+b*x)^m*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+2)) + 
  1/(d*f*(m+n+p+2))*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*g*(m+n+p+2)-h*(b*c*e*m+a*(d*e*(n+1)+c*f*(p+1)))+(b*d*f*g*(m+n+p+2)+h*(a*d*f*m-b*(d*e*(m+n+1)+c*f*(m+p+1))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && RationalQ[m] && m>0 && NonzeroQ[m+n+p+2] && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && NegativeIntegerQ[m+n+p+2] && NonzeroQ[m+1] && 
  (SumSimplerQ[m,1] || Not[NonzeroQ[n+1] && SumSimplerQ[n,1]] && Not[NonzeroQ[p+1] && SumSimplerQ[p,1]])


Int[(e_.+f_.*x_)^p_*(g_.+h_.*x_)/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  (b*g-a*h)/(b*c-a*d)*Int[(e+f*x)^p/(a+b*x),x] - 
  (d*g-c*h)/(b*c-a*d)*Int[(e+f*x)^p/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)/(a_.+b_.*x_),x_Symbol] :=
  h/b*Int[(c+d*x)^n*(e+f*x)^p,x] + (b*g-a*h)/b*Int[(c+d*x)^n*(e+f*x)^p/(a+b*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x]


Int[(g_.+h_.*x_)/(Sqrt[a_.+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  h/f*Int[Sqrt[e+f*x]/(Sqrt[a+b*x]*Sqrt[c+d*x]),x] + (f*g-e*h)/f*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && SimplerQ[a+b*x,e+f*x] && SimplerQ[c+d*x,e+f*x]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  h/b*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] + (b*g-a*h)/b*Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]] && Not[SumSimplerQ[p,1]])


Int[(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)*(g+h*x)^q/(a+b*x),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)*(g+h*x)^q/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,q},x] && RationalQ[p] && 0<p<1


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*Sqrt[d*(e+f*x)/(d*e-c*f)]*Sqrt[d*(g+h*x)/(d*g-c*h)]/((b*c-a*d)*Sqrt[-f/(d*e-c*f)]*Sqrt[e+f*x]*Sqrt[g+h*x])*
    EllipticPi[-b*(d*e-c*f)/(f*(b*c-a*d)),ArcSin[Sqrt[-f/(d*e-c*f)]*Sqrt[c+d*x]],h*(d*e-c*f)/(f*(d*g-c*h))] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[(c_.+d_.*x_)^n_/((a_.+b_.*x_)*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  Int[ExpandIntegrand[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),(c+d*x)^(n+1/2)/(a+b*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && IntegerQ[n+1/2]


Int[Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  (b*e-a*f)*(b*g-a*h)/b^2*Int[1/((a+b*x)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] + 
  1/b^2*Int[(b*f*g+b*e*h-a*f*h+b*f*h*x)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[Sqrt[a_.+b_.*x_]/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  2*(a+b*x)*Sqrt[(b*g-a*h)*(c+d*x)/((d*g-c*h)*(a+b*x))]*Sqrt[(b*g-a*h)*(e+f*x)/((f*g-e*h)*(a+b*x))]/
    (h*Sqrt[-((b*e-a*f)/(f*g-e*h))]*Sqrt[c+d*x]*Sqrt[e+f*x])*
    EllipticPi[-b*(f*g-e*h)/(h*(b*e-a*f)),ArcSin[Sqrt[-(b*e-a*f)/(f*g-e*h)]*(Sqrt[g+h*x]/Sqrt[a+b*x])],
      (b*c-a*d)*(f*g-e*h)/((b*e-a*f)*(d*g-c*h))] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[Sqrt[i_.*(a_.+b_.*x_)/((c_.+d_.*x_)*(e_+f_.*x_)*(g_.+h_.*x_))],x_Symbol] :=
  Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/Sqrt[a+b*x]*Sqrt[i*(a+b*x)/((c+d*x)*(e+f*x)*(g+h*x))]*
    Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i},x]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*(a+b*x)*Sqrt[(b*g-a*h)*(c+d*x)/((d*g-c*h)*(a+b*x))]*Sqrt[(b*g-a*h)*(e+f*x)/((f*g-e*h)*(a+b*x))]/
    ((b*g-a*h)*Sqrt[-(b*e-a*f)/(f*g-e*h)]*Sqrt[c+d*x]*Sqrt[e+f*x])*
    EllipticF[ArcSin[Sqrt[-(b*e-a*f)/(f*g-e*h)]*(Sqrt[g+h*x]/Sqrt[a+b*x])],(b*c-a*d)*(f*g-e*h)/((b*e-a*f)*(d*g-c*h))] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[Sqrt[i_./((a_.+b_.*x_)*(c_.+d_.*x_)*(e_+f_.*x_)*(g_.+h_.*x_))],x_Symbol] :=
  Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]*Sqrt[i/((a+b*x)*(c+d*x)*(e+f*x)*(g+h*x))]*
    Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i},x]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && IntegersQ[p,q]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_,x_Symbol] :=
  h/b*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^(q-1),x] + 
  (b*g-a*h)/b*Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^(q-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && PositiveIntegerQ[q] && 
  (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]] && Not[SumSimplerQ[p,1]])


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
  Defer[Int][(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x]


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*v_)^n_.*(e_.+f_.*w_)^p_.*(g_.+h_.*z_)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x,u] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && LinearQ[u,x] && NonzeroQ[u-x] && ZeroQ[u-v] && ZeroQ[u-w] && ZeroQ[u-z]



