(* ::Package:: *)

(* ::Section:: *)
(*1.1.1 Linear binomial products integration rules*)


(* ::Subsection::Closed:: *)
(*1.1.1.1 (a+b x)^m*)


Int[1/x_,x_Symbol] :=
  Log[x]


Int[x_^m_.,x_Symbol] :=
  x^(m+1)/(m+1) /;
FreeQ[m,x] && NeQ[m,-1]


Int[1/(a_+b_.*x_),x_Symbol] :=
  Log[RemoveContent[a+b*x,x]]/b /;
FreeQ[{a,b},x]


Int[(a_.+b_.*x_)^m_,x_Symbol] :=
  (a+b*x)^(m+1)/(b*(m+1)) /;
FreeQ[{a,b,m},x] && NeQ[m,-1]


Int[(a_.+b_.*u_)^m_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m,x],x,u] /;
FreeQ[{a,b,m},x] && LinearQ[u,x] && NeQ[u,x]





(* ::Subsection::Closed:: *)
(*1.1.1.2 (a+b x)^m (c+d x)^n*)


Int[1/((a_+b_.*x_)*(c_+d_.*x_)),x_Symbol] :=
  Int[1/(a*c+b*d*x^2),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  b/(b*c-a*d)*Int[1/(a+b*x),x] - d/(b*c-a*d)*Int[1/(c+d*x),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d,0] && EqQ[m+n+2,0] && NeQ[m,-1]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
  x*(a+b*x)^m*(c+d*x)^m/(2*m+1) + 2*a*c*m/(2*m+1)*Int[(a+b*x)^(m-1)*(c+d*x)^(m-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && IGtQ[m+1/2,0]


Int[1/((a_+b_.*x_)^(3/2)*(c_+d_.*x_)^(3/2)),x_Symbol] :=
  x/(a*c*Sqrt[a+b*x]*Sqrt[c+d*x]) /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
  -x*(a+b*x)^(m+1)*(c+d*x)^(m+1)/(2*a*c*(m+1)) + 
  (2*m+3)/(2*a*c*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(m+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && ILtQ[m+3/2,0]


Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^m_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[b*c+a*d,0] && (IntegerQ[m] || GtQ[a,0] && GtQ[c,0])


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  ArcCosh[b*x/a]/b /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && GtQ[a,0] && EqQ[a+c,0]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2*Subst[Int[1/(b-d*x^2),x],x,Sqrt[a+b*x]/Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
  (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m]*Int[(a*c+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[b*c+a*d,0] && Not[IntegerQ[2*m]]


Int[1/((a_+b_.*x_)^(5/4)*(c_+d_.*x_)^(1/4)),x_Symbol] :=
  -2/(b*(a+b*x)^(1/4)*(c+d*x)^(1/4)) + c*Int[1/((a+b*x)^(5/4)*(c+d*x)^(5/4)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && NegQ[a^2*b^2]


Int[1/((a_+b_.*x_)^(9/4)*(c_+d_.*x_)^(1/4)),x_Symbol] :=
  -4/(5*b*(a+b*x)^(5/4)*(c+d*x)^(1/4)) - d/(5*b)*Int[1/((a+b*x)^(5/4)*(c+d*x)^(5/4)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && NegQ[a^2*b^2]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) + 
  2*c*n/(m+n+1)*Int[(a+b*x)^m*(c+d*x)^(n-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && IGtQ[m+1/2,0] && IGtQ[n+1/2,0] && LtQ[m,n]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  -(a+b*x)^(m+1)*(c+d*x)^(n+1)/(2*a*d*(m+1)) + 
  (m+n+2)/(2*a*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d},x] && EqQ[b*c+a*d,0] && ILtQ[m-1/2,0] && ILtQ[n-1/2,0] && LtQ[m,n]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && IGtQ[m,0] && 
  (Not[IntegerQ[n]] || EqQ[c,0] && LeQ[7*m+4*n+4,0] || LtQ[9*m+5*(n+1),0] || GtQ[m+n+2,0])


Int[(a_+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n,x],x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && ILtQ[m,0] && IntegerQ[n] && Not[IGtQ[n,0] && LtQ[m+n+2,0]]


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  (c+d*x)^n/(b*n) + 
  (b*c-a*d)/b*Int[(c+d*x)^(n-1)/(a+b*x),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && GtQ[n,0]


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  -(c+d*x)^(n+1)/((n+1)*(b*c-a*d)) + 
  b*(n+1)/((n+1)*(b*c-a*d))*Int[(c+d*x)^(n+1)/(a+b*x),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[n,-1]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)),x_Symbol] :=
  With[{q=Rt[(b*c-a*d)/b,3]},
  -Log[RemoveContent[a+b*x,x]]/(2*b*q) - 
  3/(2*b*q)*Subst[Int[1/(q-x),x],x,(c+d*x)^(1/3)] + 
  3/(2*b)*Subst[Int[1/(q^2+q*x+x^2),x],x,(c+d*x)^(1/3)]] /;
FreeQ[{a,b,c,d},x] && PosQ[(b*c-a*d)/b]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)),x_Symbol] :=
  With[{q=Rt[-(b*c-a*d)/b,3]},
  Log[RemoveContent[a+b*x,x]]/(2*b*q) - 
  3/(2*b*q)*Subst[Int[1/(q+x),x],x,(c+d*x)^(1/3)] + 
  3/(2*b)*Subst[Int[1/(q^2-q*x+x^2),x],x,(c+d*x)^(1/3)]] /;
FreeQ[{a,b,c,d},x] && NegQ[(b*c-a*d)/b]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  With[{q=Rt[(b*c-a*d)/b,3]},
  -Log[RemoveContent[a+b*x,x]]/(2*b*q^2) - 
  3/(2*b*q^2)*Subst[Int[1/(q-x),x],x,(c+d*x)^(1/3)] - 
  3/(2*b*q)*Subst[Int[1/(q^2+q*x+x^2),x],x,(c+d*x)^(1/3)]] /;
FreeQ[{a,b,c,d},x] && PosQ[(b*c-a*d)/b]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  With[{q=Rt[-(b*c-a*d)/b,3]},
  -Log[RemoveContent[a+b*x,x]]/(2*b*q^2) + 
  3/(2*b*q^2)*Subst[Int[1/(q+x),x],x,(c+d*x)^(1/3)] + 
  3/(2*b*q)*Subst[Int[1/(q^2-q*x+x^2),x],x,(c+d*x)^(1/3)]] /;
FreeQ[{a,b,c,d},x] && NegQ[(b*c-a*d)/b]


Int[(c_.+d_.*x_)^n_/(a_.+b_.*x_),x_Symbol] :=
  With[{p=Denominator[n]},
  p*Subst[Int[x^(p*(n+1)-1)/(a*d-b*c+b*x^p),x],x,(c+d*x)^(1/p)]] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && GtQ[n,-1] && LtQ[n,0]


Int[(c_+d_.*x_)^n_/x_,x_Symbol] :=
  -(c+d*x)^(n+1)/(c*(n+1))*Hypergeometric2F1[1,n+1,n+2,1+d*x/c] /;
FreeQ[{c,d,n},x] && Not[IntegerQ[n]]


Int[(c_.+d_.*x_)^n_/(a_+b_.*x_),x_Symbol] :=
  -(c+d*x)^(n+1)/((n+1)*(b*c-a*d))*Hypergeometric2F1[1,n+1,n+2,TogetherSimplify[b*(c+d*x)/(b*c-a*d)]] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[n]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+1)) - 
  d*n/(b*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[m,-1] && GtQ[n,0] && Not[IntegerQ[n] && Not[IntegerQ[m]]] && 
  Not[ILeQ[m+n+2,0] && (FractionQ[m] || GeQ[2*n+m+1,0])] && IntLinearQ[a,b,c,d,m,n,x]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) - 
  d*(m+n+2)/((b*c-a*d)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && LtQ[m,-1] && 
  Not[LtQ[n,-1] && (EqQ[a,0] || NeQ[c,0] && LtQ[m-n,0] && IntegerQ[n])] && IntLinearQ[a,b,c,d,m,n,x]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) + 
  n*(b*c-a*d)/(b*(m+n+1))*Int[(a+b*x)^m*(c+d*x)^(n-1),x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && GtQ[n,0] && NeQ[m+n+1,0] && 
  Not[IGtQ[m,0] && (Not[IntegerQ[n]] || GtQ[m,0] && LtQ[m-n,0])] && 
  Not[ILtQ[m+n+2,0]] && IntLinearQ[a,b,c,d,m,n,x]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  Int[1/Sqrt[a*c-b*(a-c)*x-b^2*x^2],x] /;
FreeQ[{a,b,c,d},x] && EqQ[b+d,0] && GtQ[a+c,0]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  2/Sqrt[b]*Subst[Int[1/Sqrt[b*c-a*d+d*x^2],x],x,Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d},x] && GtQ[b*c-a*d,0] && GtQ[b,0]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2/b*Subst[Int[1/Sqrt[c-a+x^2],x],x,Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && EqQ[b-d,0]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  2*Subst[Int[1/(b-d*x^2),x],x,Sqrt[a+b*x]/Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0]


Int[(a_.+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^m/(a*c+(b*c+a*d)*x+b*d*x^2)^m*Int[(a*c+(b*c+a*d)*x+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[-1,m,0] && LeQ[3,Denominator[m],4] && AtomQ[b*c+a*d]


Int[(a_.+b_.*x_)^m_*(c_+d_.*x_)^m_,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^m/((a+b*x)*(c+d*x))^m*Int[(a*c+(b*c+a*d)*x+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[-1,m,0] && LeQ[3,Denominator[m],4]


Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  With[{q=Rt[d/b,3]},
  -Sqrt[3]*q/d*ArcTan[2*q*(a+b*x)^(1/3)/(Sqrt[3]*(c+d*x)^(1/3))+1/Sqrt[3]] - 
  q/(2*d)*Log[c+d*x] - 
  3*q/(2*d)*Log[q*(a+b*x)^(1/3)/(c+d*x)^(1/3)-1]] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && PosQ[d/b]


Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)),x_Symbol] :=
  With[{q=Rt[-d/b,3]},
  Sqrt[3]*q/d*ArcTan[1/Sqrt[3]-2*q*(a+b*x)^(1/3)/(Sqrt[3]*(c+d*x)^(1/3))] + 
  q/(2*d)*Log[c+d*x] + 
  3*q/(2*d)*Log[q*(a+b*x)^(1/3)/(c+d*x)^(1/3)+1]] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && NegQ[d/b]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  With[{p=Denominator[m]},
  p*Subst[Int[x^(p*(m+1)-1)/(b-d*x^p),x],x,(a+b*x)^(1/p)/(c+d*x)^(1/p)]] /;
FreeQ[{a,b,c,d,n},x] && NeQ[b*c-a*d,0] && LtQ[-1,m,0] && EqQ[m+n+1,0]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  With[{p=Denominator[m]},
  p/b*Subst[Int[x^(p*(m+1)-1)*(c-a*d/b+d*x^p/b)^n,x],x,(a+b*x)^(1/p)]] /;
FreeQ[{a,b,c,d},x] && NeQ[b*c-a*d,0] && LtQ[-1,m,0] && LtQ[-1,n,0] && LeQ[Denominator[n],Denominator[m]] && 
  IntLinearQ[a,b,c,d,m,n,x]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^(n+1)/((b*c-a*d)*(m+1)) - 
  d*Simplify[m+n+2]/((b*c-a*d)*(m+1))*Int[(a+b*x)^Simplify[m+1]*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d,0] && ILtQ[Simplify[m+n+2],0] && NeQ[m,-1] && 
  (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  c^n*(b*x)^(m+1)/(b*(m+1))*Hypergeometric2F1[-n,m+1,m+2,-d*x/c] /;
FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && (IntegerQ[n] || GtQ[c,0] && Not[EqQ[n,-1/2] && EqQ[c^2-d^2,0] && GtQ[-d/(b*c),0]])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (c+d*x)^(n+1)/(d*(n+1)*(-d/(b*c))^m)*Hypergeometric2F1[-m,n+1,n+2,1+d*x/c] /;
FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[n]] && (IntegerQ[m] || GtQ[-d/(b*c),0])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  c^IntPart[n]*(c+d*x)^FracPart[n]/(1+d*x/c)^FracPart[n]*Int[(b*x)^m*(1+d*x/c)^n,x] /;
FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[GtQ[c,0]] && Not[GtQ[-d/(b*c),0]] && 
  (RationalQ[m] && Not[EqQ[n,-1/2] && EqQ[c^2-d^2,0]] || Not[RationalQ[n]])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (-b*c/d)^IntPart[m]*(b*x)^FracPart[m]/(-d*x/c)^FracPart[m]*Int[(-d*x/c)^m*(c+d*x)^n,x] /;
FreeQ[{b,c,d,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[GtQ[c,0]] && Not[GtQ[-d/(b*c),0]]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (b*c-a*d)^n*(a+b*x)^(m+1)/(b^(n+1)*(m+1))*Hypergeometric2F1[-n,m+1,m+2,-d*(a+b*x)/(b*c-a*d)] /;
FreeQ[{a,b,c,d,m},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[m]] && IntegerQ[n]


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^(m+1)/(b*(m+1)*(b/(b*c-a*d))^n)*Hypergeometric2F1[-n,m+1,m+2,-d*(a+b*x)/(b*c-a*d)] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[b/(b*c-a*d),0] && 
  (RationalQ[m] || Not[RationalQ[n] && GtQ[-d/(b*c-a*d),0]])


Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  (c+d*x)^FracPart[n]/((b/(b*c-a*d))^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n])*
    Int[(a+b*x)^m*Simp[b*c/(b*c-a*d)+b*d*x/(b*c-a*d),x]^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && NeQ[b*c-a*d,0] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && (RationalQ[m] || Not[SimplerQ[n+1,m+1]])


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*u_)^n_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n,x],x,u] /;
FreeQ[{a,b,c,d,m,n},x] && LinearQ[u,x] && NeQ[Coefficient[u,x,0],0]


(* IntLinearQ[a,b,c,d,m,n,x] returns True iff (a+b*x)^m*(c+d*x)^n is integrable wrt x in terms of non-hypergeometric functions. *)
IntLinearQ[a_,b_,c_,d_,m_,n_,x_] :=
  IGtQ[m,0] || IGtQ[n,0] || IntegersQ[3*m,3*n] || IntegersQ[4*m,4*n] || IntegersQ[2*m,6*n] || IntegersQ[6*m,2*n] || ILtQ[m+n,-1] || IntegerQ[m+n] && RationalQ[m]


(* ::Subsection::Closed:: *)
(*1.1.1.3 (a+b x)^m (c+d x)^n (e+f x)^p*)


Int[(e_.+f_.*x_)^p_./((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^p/((a+b*x)*(c+d*x)),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IntegerQ[p]


Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[m-n,0] && IntegerQ[m]


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+2)) /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NeQ[n+p+2,0] && EqQ[a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)),0]


Int[(a_+b_.*x_)*(d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)*(d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && IGtQ[p,0] && EqQ[b*e+a*f,0] && Not[ILtQ[n+p+2,0] && GtQ[n+2*p,0]]


Int[(a_+b_.*x_)*(d_.*x_)^n_.*(e_+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)*(d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,d,e,f,n},x] && IGtQ[p,0] && (NeQ[n,-1] || EqQ[p,1]) && NeQ[b*e+a*f,0] &&
  (Not[IntegerQ[n]] || LtQ[9*p+5*n,0] || GeQ[n+p+1,0] || GeQ[n+p+2,0] && RationalQ[a,b,d,e,f]) && (NeQ[n+p+3,0] || EqQ[p,1])


Int[(a_.+b_.*x_)*(c_+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,n},x] && NeQ[b*c-a*d,0] && 
  (ILtQ[n,0] && ILtQ[p,0] || EqQ[p,1] || 
    IGtQ[p,0] && (Not[IntegerQ[n]] || LeQ[9*p+5*(n+2),0] || GeQ[n+p+1,0] || GeQ[n+p+2,0] && RationalQ[a,b,c,d,e,f]))


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) - 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(f*(p+1)*(c*f-d*e))*Int[(c+d*x)^n*(e+f*x)^(p+1),x] /;
FreeQ[{a,b,c,d,e,f,n},x] && LtQ[p,-1] && 
  (Not[LtQ[n,-1]] || IntegerQ[p] || Not[IntegerQ[n] || Not[EqQ[e,0] || Not[EqQ[c,0] || LtQ[p,n]]]])


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  -(b*e-a*f)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(f*(p+1)*(c*f-d*e)) - 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(f*(p+1)*(c*f-d*e))*Int[(c+d*x)^n*(e+f*x)^Simplify[p+1],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && Not[RationalQ[p]] && SumSimplerQ[p,1]


Int[(a_.+b_.*x_)*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+2)) + 
  (a*d*f*(n+p+2)-b*(d*e*(n+1)+c*f*(p+1)))/(d*f*(n+p+2))*Int[(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NeQ[n+p+2,0]


Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(c+d*x)^(n+1)*(e+f*x)^(p+1)*(2*a*d*f*(n+p+3)-b*(d*e*(n+2)+c*f*(p+2))+b*d*f*(n+p+2)*x)/(d^2*f^2*(n+p+2)*(n+p+3)) /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NeQ[n+p+2,0] && NeQ[n+p+3,0] && 
  EqQ[d*f*(n+p+2)*(a^2*d*f*(n+p+3)-b*(b*c*e+a*(d*e*(n+1)+c*f*(p+1))))-b*(d*e*(n+1)+c*f*(p+1))*(a*d*f*(n+p+4)-b*(d*e*(n+2)+c*f*(p+2))),0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
   a*Int[(a+b*x)^n*(c+d*x)^n*(f*x)^p,x] + b/f*Int[(a+b*x)^n*(c+d*x)^n*(f*x)^(p+1),x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[m-n-1,0] && Not[RationalQ[p]] && Not[IGtQ[m,0]] && NeQ[m+n+p+2,0]


Int[(e_.+f_.*x_)^p_./((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)/(a+b*x),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f},x] && LtQ[0,p,1]


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  f*(e+f*x)^(p-1)/(b*d*(p-1)) + 
 1/(b*d)*Int[(b*d*e^2-a*c*f^2+f*(2*b*d*e-b*c*f-a*d*f)*x)*(e+f*x)^(p-2)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[p,1]


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  f*(e+f*x)^(p+1)/((p+1)*(b*e-a*f)*(d*e-c*f)) + 
  1/((b*e-a*f)*(d*e-c*f))*Int[(b*d*e-b*c*f-a*d*f-b*d*f*x)*(e+f*x)^(p+1)/((a+b*x)*(c+d*x)),x] /;
FreeQ[{a,b,c,d,e,f},x] && LtQ[p,-1]


Int[(e_.+f_.*x_)^p_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  b/(b*c-a*d)*Int[(e+f*x)^p/(a+b*x),x] - 
  d/(b*c-a*d)*Int[(e+f*x)^p/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,p},x] && Not[IntegerQ[p]]


Int[(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_/(a_.+b_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(e+f*x)^FractionalPart[p],(c+d*x)^n*(e+f*x)^IntegerPart[p]/(a+b*x),x],x] /;
FreeQ[{a,b,c,d,e,f},x] && IGtQ[n,0] && LtQ[p,-1] && FractionQ[p]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && IntegersQ[m,n] && (IntegerQ[p] || GtQ[m,0] && GeQ[n,-1])


Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (b*c-a*d)^2*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d^2*(d*e-c*f)*(n+1)) - 
  1/(d^2*(d*e-c*f)*(n+1))*Int[(c+d*x)^(n+1)*(e+f*x)^p*
    Simp[a^2*d^2*f*(n+p+2)+b^2*c*(d*e*(n+1)+c*f*(p+1))-2*a*b*d*(d*e*(n+1)+c*f*(p+1))-b^2*d*(d*e-c*f)*(n+1)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && (LtQ[n,-1] || EqQ[n+p+3,0] && NeQ[n,-1] && (SumSimplerQ[n,1] || Not[SumSimplerQ[p,1]]))


Int[(a_.+b_.*x_)^2*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(n+p+3)) + 
  1/(d*f*(n+p+3))*Int[(c+d*x)^n*(e+f*x)^p*
    Simp[a^2*d*f*(n+p+3)-b*(b*c*e+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(n+p+4)-b*(d*e*(n+2)+c*f*(p+2)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && NeQ[n+p+3,0]


Int[1/((a_.+b_.*x_)^(1/3)*(c_.+d_.*x_)^(2/3)*(e_.+f_.*x_)),x_Symbol] :=
  With[{q=Rt[(d*e-c*f)/(b*e-a*f),3]},
  -Sqrt[3]*q*ArcTan[1/Sqrt[3]+2*q*(a+b*x)^(1/3)/(Sqrt[3]*(c+d*x)^(1/3))]/(d*e-c*f) + 
  q*Log[e+f*x]/(2*(d*e-c*f)) - 
  3*q*Log[q*(a+b*x)^(1/3)-(c+d*x)^(1/3)]/(2*(d*e-c*f))] /;
FreeQ[{a,b,c,d,e,f},x]


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)),x_Symbol] :=
  b*f*Subst[Int[1/(d*(b*e-a*f)^2+b*f^2*x^2),x],x,Sqrt[a+b*x]*Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[2*b*d*e-f*(b*c+a*d),0]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_),x_Symbol] :=
  With[{q=Denominator[m]},
  q*Subst[Int[x^(q*(m+1)-1)/(b*e-a*f-(d*e-c*f)*x^q),x],x,(a+b*x)^(1/q)/(c+d*x)^(1/q)]] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[m+n+1,0] && RationalQ[n] && LtQ[-1,m,0] && SimplerQ[a+b*x,c+d*x]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((m+1)*(b*e-a*f)) - 
  n*(d*e-c*f)/((m+1)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[m+n+p+2,0] && GtQ[n,0] && Not[SumSimplerQ[p,1] && Not[SumSimplerQ[m,1]]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[Simplify[m+n+p+3],0] && EqQ[a*d*f*(m+1)+b*c*f*(n+1)+b*d*e*(p+1),0] && NeQ[m,-1]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  (a*d*f*(m+1)+b*c*f*(n+1)+b*d*e*(p+1))/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[Simplify[m+n+p+3],0] && (LtQ[m,-1] || SumSimplerQ[m,1])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p/(b*(m+1)) - 
  1/(b*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^(p-1)*Simp[d*e*n+c*f*p+d*f*(n+p)*x,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && LtQ[m,-1] && GtQ[n,0] && GtQ[p,0] && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (b*c-a*d)*(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) + 
  1/(b*(b*e-a*f)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-2)*(e+f*x)^p*
    Simp[a*d*(d*e*(n-1)+c*f*(p+1))+b*c*(d*e*(m-n+2)-c*f*(m+p+2))+d*(a*d*f*(n+p)+b*(d*e*(m+1)-c*f*(m+n+p+1)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && LtQ[m,-1] && GtQ[n,1] && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((m+1)*(b*e-a*f)) - 
  1/((m+1)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[d*e*n+c*f*(m+p+2)+d*f*(m+n+p+2)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && LtQ[m,-1] && GtQ[n,0] && (IntegersQ[2*m,2*n,2*p] || IntegersQ[m,n+p] || IntegersQ[p,m+n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+1)) + 
  1/(d*f*(m+n+p+1))*Int[(a+b*x)^(m-2)*(c+d*x)^n*(e+f*x)^p*
    Simp[a^2*d*f*(m+n+p+1)-b*(b*c*e*(m-1)+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(2*m+n+p)-b*(d*e*(m+n)+c*f*(m+p)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && GtQ[m,1] && NeQ[m+n+p+1,0] && IntegerQ[m]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^m*(c+d*x)^n*(e+f*x)^(p+1)/(f*(m+n+p+1)) - 
  1/(f*(m+n+p+1))*Int[(a+b*x)^(m-1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[c*m*(b*e-a*f)+a*n*(d*e-c*f)+(d*m*(b*e-a*f)+b*n*(d*e-c*f))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && GtQ[m,0] && GtQ[n,0] && NeQ[m+n+p+1,0] && (IntegersQ[2*m,2*n,2*p] || (IntegersQ[m,n+p] || IntegersQ[p,m+n]))


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+1)) + 
  1/(d*f*(m+n+p+1))*Int[(a+b*x)^(m-2)*(c+d*x)^n*(e+f*x)^p*
    Simp[a^2*d*f*(m+n+p+1)-b*(b*c*e*(m-1)+a*(d*e*(n+1)+c*f*(p+1)))+b*(a*d*f*(2*m+n+p)-b*(d*e*(m+n)+c*f*(m+p)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && GtQ[m,1] && NeQ[m+n+p+1,0] && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && LtQ[m,-1] && IntegerQ[m] && (IntegerQ[n] || IntegersQ[2*n,2*p])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && LtQ[m,-1] && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_/(e_.+f_.*x_),x_Symbol] :=
  b/f*Int[(a+b*x)^(m-1)*(c+d*x)^n,x] - (b*e-a*f)/f*Int[(a+b*x)^(m-1)*(c+d*x)^n/(e+f*x),x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && IGtQ[Simplify[m+n+1],0] && 
  (GtQ[m,0] || Not[RationalQ[m]] && (SumSimplerQ[m,-1] || Not[SumSimplerQ[n,-1]]))


(* Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  b/f*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^(p+1),x] - (b*e-a*f)/f*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ILtQ[p,0] && IGtQ[m+n+p+2,0] && Not[SimplerQ[c+d*x,a+b*x]] *)


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(1/4)),x_Symbol] :=
  -4*Subst[Int[x^2/((b*e-a*f-b*x^4)*Sqrt[c-d*e/f+d*x^4/f]),x],x,(e+f*x)^(1/4)] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[-f/(d*e-c*f),0]


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(1/4)),x_Symbol] :=
  Sqrt[-f*(c+d*x)/(d*e-c*f)]/Sqrt[c+d*x]*Int[1/((a+b*x)*Sqrt[-c*f/(d*e-c*f)-d*f*x/(d*e-c*f)]*(e+f*x)^(1/4)),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[-f/(d*e-c*f),0]]


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(3/4)),x_Symbol] :=
  -4*Subst[Int[1/((b*e-a*f-b*x^4)*Sqrt[c-d*e/f+d*x^4/f]),x],x,(e+f*x)^(1/4)] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[-f/(d*e-c*f),0]


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*(e_.+f_.*x_)^(3/4)),x_Symbol] :=
  Sqrt[-f*(c+d*x)/(d*e-c*f)]/Sqrt[c+d*x]*Int[1/((a+b*x)*Sqrt[-c*f/(d*e-c*f)-d*f*x/(d*e-c*f)]*(e+f*x)^(3/4)),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[-f/(d*e-c*f),0]]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2*Sqrt[e]/b*Rt[-b/d,2]*EllipticE[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
FreeQ[{b,c,d,e,f},x] && NeQ[d*e-c*f,0] && GtQ[c,0] && GtQ[e,0] && Not[LtQ[-b/d,0]]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[-b*x]/Sqrt[b*x]*Int[Sqrt[e+f*x]/(Sqrt[-b*x]*Sqrt[c+d*x]),x] /;
FreeQ[{b,c,d,e,f},x] && NeQ[d*e-c*f,0] && GtQ[c,0] && GtQ[e,0] && LtQ[-b/d,0]


Int[Sqrt[e_+f_.*x_]/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[e+f*x]*Sqrt[1+d*x/c]/(Sqrt[c+d*x]*Sqrt[1+f*x/e])*Int[Sqrt[1+f*x/e]/(Sqrt[b*x]*Sqrt[1+d*x/c]),x] /;
FreeQ[{b,c,d,e,f},x] && NeQ[d*e-c*f,0] && Not[GtQ[c,0] && GtQ[e,0]]


(* Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  f/b*Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]),x] - 
  f/b*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[b*e-f*(a-1),0] *)


(* Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2/b*Rt[-(b*c-a*d)/d,2]*Sqrt[(b*e-a*f)/(b*c-a*d)]*
    EllipticE[ArcSin[Sqrt[a+b*x]/Rt[-(b*c-a*d)/d,2]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[b/(b*c-a*d),0] && GtQ[b/(b*e-a*f),0] && Not[LtQ[-(b*c-a*d)/d,0]] && 
  Not[SimplerQ[c+d*x,a+b*x] && GtQ[-d/(b*c-a*d),0] && GtQ[d/(d*e-c*f),0] && Not[LtQ[(b*c-a*d)/b,0]]] *)


Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  2/b*Rt[-(b*e-a*f)/d,2]*EllipticE[ArcSin[Sqrt[a+b*x]/Rt[-(b*c-a*d)/d,2]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[b/(b*c-a*d),0] && GtQ[b/(b*e-a*f),0] && Not[LtQ[-(b*c-a*d)/d,0]] && 
  Not[SimplerQ[c+d*x,a+b*x] && GtQ[-d/(b*c-a*d),0] && GtQ[d/(d*e-c*f),0] && Not[LtQ[(b*c-a*d)/b,0]]]


Int[Sqrt[e_.+f_.*x_]/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]),x_Symbol] :=
  Sqrt[e+f*x]*Sqrt[b*(c+d*x)/(b*c-a*d)]/(Sqrt[c+d*x]*Sqrt[b*(e+f*x)/(b*e-a*f)])*
    Int[Sqrt[b*e/(b*e-a*f)+b*f*x/(b*e-a*f)]/(Sqrt[a+b*x]*Sqrt[b*c/(b*c-a*d)+b*d*x/(b*c-a*d)]),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[b/(b*c-a*d),0] && GtQ[b/(b*e-a*f),0]] && Not[LtQ[-(b*c-a*d)/d,0]]


Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  2/(b*Sqrt[e])*Rt[-b/d,2]*EllipticF[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
FreeQ[{b,c,d,e,f},x] && GtQ[c,0] && GtQ[e,0] && (GtQ[-b/d,0] || LtQ[-b/f,0])


Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  2/(b*Sqrt[e])*Rt[-b/d,2]*EllipticF[ArcSin[Sqrt[b*x]/(Sqrt[c]*Rt[-b/d,2])],c*f/(d*e)] /;
FreeQ[{b,c,d,e,f},x] && GtQ[c,0] && GtQ[e,0] && (PosQ[-b/d] || NegQ[-b/f])


Int[1/(Sqrt[b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  Sqrt[1+d*x/c]*Sqrt[1+f*x/e]/(Sqrt[c+d*x]*Sqrt[e+f*x])*Int[1/(Sqrt[b*x]*Sqrt[1+d*x/c]*Sqrt[1+f*x/e]),x] /;
FreeQ[{b,c,d,e,f},x] && Not[GtQ[c,0] && GtQ[e,0]]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  -2*Sqrt[d/f]/(d*Rt[-(b*e-a*f)/f,2])*EllipticF[ArcSin[Rt[-(b*e-a*f)/f,2]/Sqrt[a+b*x]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[d/b,0] && GtQ[f/b,0] && LeQ[c,a*d/b] && LeQ[e,a*f/b]


(* Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  -2*Sqrt[c+d*x]*Sqrt[b*(e+f*x)/(f*(a+b*x))]/(d*Rt[-(b*e-a*f)/f,2]*Sqrt[e+f*x]*Sqrt[b*(c+d*x)/(d*(a+b*x))])*
    EllipticF[ArcSin[Rt[-(b*e-a*f)/f,2]/Sqrt[a+b*x]],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && PosQ[-(b*e-a*f)/f] && (* (LtQ[-a/b,-c/d,-e/f] || GtQ[-a/b,-c/d,-e/f]) *)
  Not[SimplerQ[c+d*x,a+b*x] && (PosQ[(-d*e+c*f)/f] || PosQ[(b*e-a*f)/b])] && 
  Not[SimplerQ[e+f*x,a+b*x] && (PosQ[(b*e-a*f)/b] || PosQ[(b*c-a*d)/b])] *)


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  2*Rt[-b/d,2]/(b*Sqrt[(b*e-a*f)/b])*EllipticF[ArcSin[Sqrt[a+b*x]/(Rt[-b/d,2]*Sqrt[(b*c-a*d)/b])],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[(b*c-a*d)/b,0] && GtQ[(b*e-a*f)/b,0] && PosQ[-b/d] && 
  Not[SimplerQ[c+d*x,a+b*x] && GtQ[(d*e-c*f)/d,0] && GtQ[-d/b,0]] && 
  Not[SimplerQ[c+d*x,a+b*x] && GtQ[(-b*e+a*f)/f,0] && GtQ[-f/b,0]] && 
  Not[SimplerQ[e+f*x,a+b*x] && GtQ[(-d*e+c*f)/f,0] && GtQ[(-b*e+a*f)/f,0] && (PosQ[-f/d] || PosQ[-f/b])]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  2*Rt[-b/d,2]/(b*Sqrt[(b*e-a*f)/b])*EllipticF[ArcSin[Sqrt[a+b*x]/(Rt[-b/d,2]*Sqrt[(b*c-a*d)/b])],f*(b*c-a*d)/(d*(b*e-a*f))] /;
FreeQ[{a,b,c,d,e,f},x] && GtQ[b/(b*c-a*d),0] && GtQ[b/(b*e-a*f),0] && SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x] && 
  (PosQ[-(b*c-a*d)/d] || NegQ[-(b*e-a*f)/f]) (* && PosQ[-b/d] *)


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  Sqrt[b*(c+d*x)/(b*c-a*d)]/Sqrt[c+d*x]*Int[1/(Sqrt[a+b*x]*Sqrt[b*c/(b*c-a*d)+b*d*x/(b*c-a*d)]*Sqrt[e+f*x]),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[(b*c-a*d)/b,0]] && SimplerQ[a+b*x,c+d*x] && SimplerQ[a+b*x,e+f*x]


Int[1/(Sqrt[a_+b_.*x_]*Sqrt[c_+d_.*x_]*Sqrt[e_+f_.*x_]),x_Symbol] :=
  Sqrt[b*(e+f*x)/(b*e-a*f)]/Sqrt[e+f*x]*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[b*e/(b*e-a*f)+b*f*x/(b*e-a*f)]),x] /;
FreeQ[{a,b,c,d,e,f},x] && Not[GtQ[(b*e-a*f)/b,0]]


Int[1/((a_.+b_.*x_)*(c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(1/3)),x_Symbol] :=
  With[{q=Rt[b*(b*e-a*f)/(b*c-a*d)^2,3]},
  -Log[a+b*x]/(2*q*(b*c-a*d)) - 
  Sqrt[3]*ArcTan[1/Sqrt[3]+2*q*(c+d*x)^(2/3)/(Sqrt[3]*(e+f*x)^(1/3))]/(2*q*(b*c-a*d)) + 
  3*Log[q*(c+d*x)^(2/3)-(e+f*x)^(1/3)]/(4*q*(b*c-a*d))] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[2*b*d*e-b*c*f-a*d*f,0]


Int[(a_.+b_.*x_)^m_/((c_.+d_.*x_)^(1/3)*(e_.+f_.*x_)^(1/3)),x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(2/3)*(e+f*x)^(2/3)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  f/(6*(m+1)*(b*c-a*d)*(b*e-a*f))*
    Int[(a+b*x)^(m+1)*(a*d*(3*m+1)-3*b*c*(3*m+5)-2*b*d*(3*m+7)*x)/((c+d*x)^(1/3)*(e+f*x)^(1/3)),x] /;
FreeQ[{a,b,c,d,e,f},x] && EqQ[2*b*d*e-b*c*f-a*d*f,0] && ILtQ[m,-1]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
  Int[(a*c+b*d*x^2)^m*(f*x)^p,x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[m-n,0] && GtQ[a,0] && GtQ[c,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m]*Int[(a*c+b*d*x^2)^m*(f*x)^p,x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && EqQ[b*c+a*d,0] && EqQ[m-n,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(f_.*x_)^p_.,x_Symbol] :=
   Int[ExpandIntegrand[(a+b*x)^n*(c+d*x)^n*(f*x)^p,(a+b*x)^(m-n),x],x] /;
FreeQ[{a,b,c,d,f,m,n,p},x] && EqQ[b*c+a*d,0] && IGtQ[m-n,0] && NeQ[m+n+p+2,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && (IGtQ[m,0] || ILtQ[m,0] && ILtQ[n,0])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  b*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*(m+1)-b*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && ILtQ[m+n+p+2,0] && NeQ[m,-1] && 
  (SumSimplerQ[m,1] || Not[NeQ[n,-1] && SumSimplerQ[n,1]] && Not[NeQ[p,-1] && SumSimplerQ[p,1]])


Int[(e_.*x_)^p_*(a_+b_.*x_)^m_*(c_+d_.*x_)^n_,x_Symbol] :=
  With[{k=Denominator[p]},
  k/e*Subst[Int[x^(k*(p+1)-1)*(a+b*x^k/e)^m*(c+d*x^k/e)^n,x],x,(e*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,m,n},x] && NeQ[b*c-a*d,0] && FractionQ[p] && IntegerQ[m]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_,x_Symbol] :=
  (b*c-a*d)^n*(a+b*x)^(m+1)/((m+1)*(b*e-a*f)^(n+1)*(e+f*x)^(m+1))*
    Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
FreeQ[{a,b,c,d,e,f,m,p},x] && EqQ[m+n+p+2,0] && ILtQ[n,0]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/((b*e-a*f)*(m+1))*((b*e-a*f)*(c+d*x)/((b*c-a*d)*(e+f*x)))^(-n)*
    Hypergeometric2F1[m+1,-n,m+2,-(d*e-c*f)*(a+b*x)/((b*c-a*d)*(e+f*x))] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && EqQ[m+n+p+2,0] && Not[IntegerQ[n]]


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_Symbol] :=
  c^n*e^p*(b*x)^(m+1)/(b*(m+1))*AppellF1[m+1,-n,-p,m+2,-d*x/c,-f*x/e] /;
FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[c,0] && (IntegerQ[p] || GtQ[e,0])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_Symbol] :=
  (c+d*x)^(n+1)/(d*(n+1)*(-d/(b*c))^m*(d/(d*e-c*f))^p)*AppellF1[n+1,-m,-p,n+2,1+d*x/c,-f*(c+d*x)/(d*e-c*f)] /;
FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && GtQ[-d/(b*c),0] && (IntegerQ[p] || GtQ[d/(d*e-c*f),0])


Int[(b_.*x_)^m_*(c_+d_.*x_)^n_*(e_+f_.*x_)^p_,x_Symbol] :=
  c^IntPart[n]*(c+d*x)^FracPart[n]/(1+d*x/c)^FracPart[n]*Int[(b*x)^m*(1+d*x/c)^n*(e+f*x)^p,x] /;
FreeQ[{b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[GtQ[c,0]]


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (b*e-a*f)^p*(a+b*x)^(m+1)/(b^(p+1)*(m+1)*(b/(b*c-a*d))^n)*
    AppellF1[m+1,-n,-p,m+2,-d*(a+b*x)/(b*c-a*d),-f*(a+b*x)/(b*e-a*f)] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && IntegerQ[p] && GtQ[b/(b*c-a*d),0] && 
  Not[GtQ[d/(d*a-c*b),0] && SimplerQ[c+d*x,a+b*x]]


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (c+d*x)^FracPart[n]/((b/(b*c-a*d))^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n])*
    Int[(a+b*x)^m*(b*c/(b*c-a*d)+b*d*x/(b*c-a*d))^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && IntegerQ[p] && Not[GtQ[b/(b*c-a*d),0]] && 
  Not[SimplerQ[c+d*x,a+b*x]]


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (a+b*x)^(m+1)/(b*(m+1)*(b/(b*c-a*d))^n*(b/(b*e-a*f))^p)*AppellF1[m+1,-n,-p,m+2,-d*(a+b*x)/(b*c-a*d),-f*(a+b*x)/(b*e-a*f)] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && 
  GtQ[b/(b*c-a*d),0] && GtQ[b/(b*e-a*f),0] && 
  Not[GtQ[d/(d*a-c*b),0] && GtQ[d/(d*e-c*f),0] && SimplerQ[c+d*x,a+b*x]] && 
  Not[GtQ[f/(f*a-e*b),0] && GtQ[f/(f*c-e*d),0] && SimplerQ[e+f*x,a+b*x]]


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (e+f*x)^FracPart[p]/((b/(b*e-a*f))^IntPart[p]*(b*(e+f*x)/(b*e-a*f))^FracPart[p])*
    Int[(a+b*x)^m*(c+d*x)^n*(b*e/(b*e-a*f)+b*f*x/(b*e-a*f))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && 
  GtQ[b/(b*c-a*d),0] && Not[GtQ[b/(b*e-a*f),0]]


Int[(a_+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_,x_Symbol] :=
  (c+d*x)^FracPart[n]/((b/(b*c-a*d))^IntPart[n]*(b*(c+d*x)/(b*c-a*d))^FracPart[n])*
    Int[(a+b*x)^m*(b*c/(b*c-a*d)+b*d*x/(b*c-a*d))^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && Not[IntegerQ[m]] && Not[IntegerQ[n]] && Not[IntegerQ[p]] && Not[GtQ[b/(b*c-a*d),0]] && 
  Not[SimplerQ[c+d*x,a+b*x]] && Not[SimplerQ[e+f*x,a+b*x]]


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*u_)^n_.*(e_+f_.*u_)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x,u] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && LinearQ[u,x] && NeQ[u,x]





(* ::Subsection::Closed:: *)
(*1.1.1.4 (a+b x)^m (c+d x)^n (e+f x)^p (g+h x)^q*)


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)*(g+h*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && (IGtQ[m,0] || IntegersQ[m,n])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  (b^2*d*e*g-a^2*d*f*h*m-a*b*(d*(f*g+e*h)-c*f*h*(m+1))+b*f*h*(b*c-a*d)*(m+1)*x)*(a+b*x)^(m+1)*(c+d*x)^(n+1)/
    (b^2*d*(b*c-a*d)*(m+1)) + 
  (a*d*f*h*m+b*(d*(f*g+e*h)-c*f*h*(m+2)))/(b^2*d)*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && EqQ[m+n+2,0] && NeQ[m,-1] && Not[SumSimplerQ[n,1] && Not[SumSimplerQ[m,1]]]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  (b^2*c*d*e*g*(n+1)+a^2*c*d*f*h*(n+1)+a*b*(d^2*e*g*(m+1)+c^2*f*h*(m+1)-c*d*(f*g+e*h)*(m+n+2))+
      (a^2*d^2*f*h*(n+1)-a*b*d^2*(f*g+e*h)*(n+1)+b^2*(c^2*f*h*(m+1)-c*d*(f*g+e*h)*(m+1)+d^2*e*g*(m+n+2)))*x)/
    (b*d*(b*c-a*d)^2*(m+1)*(n+1))*(a+b*x)^(m+1)*(c+d*x)^(n+1) - 
  (a^2*d^2*f*h*(2+3*n+n^2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
      b^2*(c^2*f*h*(2+3*m+m^2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(6+m^2+5*n+n^2+m*(2*n+5))))/
    (b*d*(b*c-a*d)^2*(m+1)*(n+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n+1),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && LtQ[m,-1] && LtQ[n,-1]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  (b^3*c*e*g*(m+2)-a^3*d*f*h*(n+2)-a^2*b*(c*f*h*m-d*(f*g+e*h)*(m+n+3))-a*b^2*(c*(f*g+e*h)+d*e*g*(2*m+n+4))+
      b*(a^2*d*f*h*(m-n)-a*b*(2*c*f*h*(m+1)-d*(f*g+e*h)*(n+1))+b^2*(c*(f*g+e*h)*(m+1)-d*e*g*(m+n+2)))*x)/
    (b^2*(b*c-a*d)^2*(m+1)*(m+2))*(a+b*x)^(m+1)*(c+d*x)^(n+1) + 
  (f*h/b^2-(d*(m+n+3)*(a^2*d*f*h*(m-n)-a*b*(2*c*f*h*(m+1)-d*(f*g+e*h)*(n+1))+b^2*(c*(f*g+e*h)*(m+1)-d*e*g*(m+n+2))))/
      (b^2*(b*c-a*d)^2*(m+1)*(m+2)))*
    Int[(a+b*x)^(m+2)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && (LtQ[m,-2] || EqQ[m+n+3,0] && Not[LtQ[n,-2]])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  (a^2*d*f*h*(n+2)+b^2*d*e*g*(m+n+3)+a*b*(c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+b*f*h*(b*c-a*d)*(m+1)*x)/
    (b^2*d*(b*c-a*d)*(m+1)*(m+n+3))*(a+b*x)^(m+1)*(c+d*x)^(n+1) - 
  (a^2*d^2*f*h*(n+1)*(n+2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
      b^2*(c^2*f*h*(m+1)*(m+2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(m+n+2)*(m+n+3)))/
    (b^2*d*(b*c-a*d)*(m+1)*(m+n+3))*Int[(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && (GeQ[m,-2] && LtQ[m,-1] || SumSimplerQ[m,1]) && NeQ[m,-1] && NeQ[m+n+3,0]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_+f_.*x_)*(g_.+h_.*x_),x_Symbol] :=
  -(a*d*f*h*(n+2)+b*c*f*h*(m+2)-b*d*(f*g+e*h)*(m+n+3)-b*d*f*h*(m+n+2)*x)*(a+b*x)^(m+1)*(c+d*x)^(n+1)/
    (b^2*d^2*(m+n+2)*(m+n+3)) + 
  (a^2*d^2*f*h*(n+1)*(n+2)+a*b*d*(n+1)*(2*c*f*h*(m+1)-d*(f*g+e*h)*(m+n+3))+
      b^2*(c^2*f*h*(m+1)*(m+2)-c*d*(f*g+e*h)*(m+1)*(m+n+3)+d^2*e*g*(m+n+2)*(m+n+3)))/
    (b^2*d^2*(m+n+2)*(m+n+3))*Int[(a+b*x)^m*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && NeQ[m+n+2,0] && NeQ[m+n+3,0]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && (IntegersQ[m,n,p] || IGtQ[n,0] && IGtQ[p,0])


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) - 
  1/(b*(b*e-a*f)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[b*c*(f*g-e*h)*(m+1)+(b*g-a*h)*(d*e*n+c*f*(p+1))+d*(b*(f*g-e*h)*(m+1)+f*(b*g-a*h)*(n+p+1))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p},x] && LtQ[m,-1] && GtQ[n,0] && IntegerQ[m]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^(p+1)/(b*(b*e-a*f)*(m+1)) - 
  1/(b*(b*e-a*f)*(m+1))*Int[(a+b*x)^(m+1)*(c+d*x)^(n-1)*(e+f*x)^p*
    Simp[b*c*(f*g-e*h)*(m+1)+(b*g-a*h)*(d*e*n+c*f*(p+1))+d*(b*(f*g-e*h)*(m+1)+f*(b*g-a*h)*(n+p+1))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,p},x] && LtQ[m,-1] && GtQ[n,0] && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && LtQ[m,-1] && IntegerQ[m]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && LtQ[m,-1] && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  h*(a+b*x)^m*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+2)) + 
  1/(d*f*(m+n+p+2))*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*g*(m+n+p+2)-h*(b*c*e*m+a*(d*e*(n+1)+c*f*(p+1)))+(b*d*f*g*(m+n+p+2)+h*(a*d*f*m-b*(d*e*(m+n+1)+c*f*(m+p+1))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && GtQ[m,0] && NeQ[m+n+p+2,0] && IntegerQ[m]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  h*(a+b*x)^m*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*(m+n+p+2)) + 
  1/(d*f*(m+n+p+2))*Int[(a+b*x)^(m-1)*(c+d*x)^n*(e+f*x)^p*
    Simp[a*d*f*g*(m+n+p+2)-h*(b*c*e*m+a*(d*e*(n+1)+c*f*(p+1)))+(b*d*f*g*(m+n+p+2)+h*(a*d*f*m-b*(d*e*(m+n+1)+c*f*(m+p+1))))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && GtQ[m,0] && NeQ[m+n+p+2,0] && IntegersQ[2*m,2*n,2*p]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_),x_Symbol] :=
  (b*g-a*h)*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    Simp[(a*d*f*g-b*(d*e+c*f)*g+b*c*e*h)*(m+1)-(b*g-a*h)*(d*e*(n+1)+c*f*(p+1))-d*f*(b*g-a*h)*(m+n+p+3)*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,n,p},x] && ILtQ[m+n+p+2,0] && NeQ[m,-1] && 
  (SumSimplerQ[m,1] || Not[NeQ[n,-1] && SumSimplerQ[n,1]] && Not[NeQ[p,-1] && SumSimplerQ[p,1]])


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


Int[(a_.+b_.*x_)^m_*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_],x_Symbol] :=
  (a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(b*(m+1)) - 
  1/(2*b*(m+1))*Int[(a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
    Simp[d*e*g+c*f*g+c*e*h+2*(d*f*g+d*e*h+c*f*h)*x+3*d*f*h*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && LtQ[m,-1]


Int[(a_.+b_.*x_)^m_*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_],x_Symbol] :=
  2*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(b*(2*m+5)) + 
  1/(b*(2*m+5))*Int[((a+b*x)^m)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
    Simp[3*b*c*e*g-a*(d*e*g+c*f*g+c*e*h)+2*(b*(d*e*g+c*f*g+c*e*h)-a*(d*f*g+d*e*h+c*f*h))*x-(3*a*d*f*h-b*(d*f*g+d*e*h+c*f*h))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && Not[LtQ[m,-1]]


Int[(a_.+b_.*x_)^m_*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  2*(a+b*x)^m*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*(2*m+3)) - 
  1/(d*(2*m+3))*Int[((a+b*x)^(m-1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
    Simp[2*b*c*e*g*m+a*(c*(f*g+e*h)-2*d*e*g*(m+1)) - 
      (b*(2*d*e*g-c*(f*g+e*h)*(2*m+1))-a*(2*c*f*h-d*(2*m+1)*(f*g+e*h)))*x - 
      (2*a*d*f*h*m+b*(d*(f*g+e*h)-2*c*f*h*(m+1)))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && GtQ[m,0]


Int[Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]),x_Symbol] :=
  (b*e-a*f)*(b*g-a*h)/b^2*Int[1/((a+b*x)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] + 
  1/b^2*Int[Simp[b*f*g+b*e*h-a*f*h+b*f*h*x,x]/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[(a_.+b_.*x_)^m_*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]/Sqrt[c_.+d_.*x_],x_Symbol] :=
  (a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*c-a*d)) - 
  1/(2*(m+1)*(b*c-a*d))*Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
    Simp[c*(f*g+e*h)+d*e*g*(2*m+3)+2*(c*f*h+d*(m+2)*(f*g+e*h))*x+d*f*h*(2*m+5)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && LtQ[m,-1]


Int[Sqrt[a_.+b_.*x_]/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  2*(a+b*x)*Sqrt[(b*g-a*h)*(c+d*x)/((d*g-c*h)*(a+b*x))]*Sqrt[(b*g-a*h)*(e+f*x)/((f*g-e*h)*(a+b*x))]/(Sqrt[c+d*x]*Sqrt[e+f*x])*
    Subst[Int[1/((h-b*x^2)*Sqrt[1+(b*c-a*d)*x^2/(d*g-c*h)]*Sqrt[1+(b*e-a*f)*x^2/(f*g-e*h)]),x],x,Sqrt[g+h*x]/Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[(a_.+b_.*x_)^(3/2)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  b/d*Int[Sqrt[a+b*x]*Sqrt[c+d*x]/(Sqrt[e+f*x]*Sqrt[g+h*x]),x] - 
  (b*c-a*d)/d*Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[(a_.+b_.*x_)^m_/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  2*b^2*(a+b*x)^(m-2)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*f*h*(2*m-1)) - 
  1/(d*f*h*(2*m-1))*Int[((a+b*x)^(m-3)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
    Simp[a*b^2*(d*e*g+c*f*g+c*e*h)+2*b^3*c*e*g*(m-2)-a^3*d*f*h*(2*m-1) + 
      b*(2*a*b*(d*f*g+d*e*h+c*f*h)+b^2*(2*m-3)*(d*e*g+c*f*g+c*e*h)-3*a^2*d*f*h*(2*m-1))*x - 
      2*b^2*(m-1)*(3*a*d*f*h-b*(d*f*g+d*e*h+c*f*h))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && IntegerQ[2*m] && GeQ[m,2]


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*Subst[Int[1/(Simp[b*c-a*d-b*x^2,x]*Sqrt[Simp[(d*e-c*f)/d+f*x^2/d,x]]*Sqrt[Simp[(d*g-c*h)/d+h*x^2/d,x]]),x],x,Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && GtQ[(d*e-c*f)/d,0]


Int[1/((a_.+b_.*x_)*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*Subst[Int[1/(Simp[b*c-a*d-b*x^2,x]*Sqrt[Simp[(d*e-c*f)/d+f*x^2/d,x]]*Sqrt[Simp[(d*g-c*h)/d+h*x^2/d,x]]),x],x,Sqrt[c+d*x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && Not[SimplerQ[e+f*x,c+d*x]] && Not[SimplerQ[g+h*x,c+d*x]]


(* Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*(a+b*x)*Sqrt[(b*g-a*h)*(c+d*x)/((d*g-c*h)*(a+b*x))]*Sqrt[(b*g-a*h)*(e+f*x)/((f*g-e*h)*(a+b*x))]/
    ((b*g-a*h)*Sqrt[c+d*x]*Sqrt[e+f*x])*
    Subst[Int[1/(Sqrt[1+(b*c-a*d)*x^2/(d*g-c*h)]*Sqrt[1+(b*e-a*f)*x^2/(f*g-e*h)]),x],x,Sqrt[g+h*x]/Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] *)


Int[1/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  2*Sqrt[g+h*x]*Sqrt[(b*e-a*f)*(c+d*x)/((d*e-c*f)*(a+b*x))]/
    ((f*g-e*h)*Sqrt[c+d*x]*Sqrt[-(b*e-a*f)*(g+h*x)/((f*g-e*h)*(a+b*x))])*
    Subst[Int[1/(Sqrt[1+(b*c-a*d)*x^2/(d*e-c*f)]*Sqrt[1-(b*g-a*h)*x^2/(f*g-e*h)]),x],x,Sqrt[e+f*x]/Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[1/((a_.+b_.*x_)^(3/2)*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -d/(b*c-a*d)*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] + 
  b/(b*c-a*d)*Int[Sqrt[c+d*x]/((a+b*x)^(3/2)*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[(a_.+b_.*x_)^m_/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  b^2*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) - 
  1/(2*(m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h))*Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
    Simp[2*a^2*d*f*h*(m+1)-2*a*b*(m+1)*(d*f*g+d*e*h+c*f*h)+b^2*(2*m+3)*(d*e*g+c*f*g+c*e*h) - 
      2*b*(a*d*f*h*(m+1)-b*(m+2)*(d*f*g+d*e*h+c*f*h))*x + d*f*h*(2*m+5)*b^2*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && IntegerQ[2*m] && LeQ[m,-2]


Int[Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]/(Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[g+h*x]/(h*Sqrt[e+f*x]) + 
  (d*e-c*f)*(b*f*g+b*e*h-2*a*f*h)/(2*f^2*h)*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] + 
  (a*d*f*h-b*(d*f*g+d*e*h-c*f*h))/(2*f^2*h)*Int[Sqrt[e+f*x]/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[g+h*x]),x] - 
  (d*e-c*f)*(f*g-e*h)/(2*f*h)*Int[Sqrt[a+b*x]/(Sqrt[c+d*x]*(e+f*x)^(3/2)*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[(a_.+b_.*x_)^m_*Sqrt[c_.+d_.*x_]/(Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  2*b*(a+b*x)^(m-1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(f*h*(2*m+1)) - 
  1/(f*h*(2*m+1))*Int[((a+b*x)^(m-2)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
    Simp[a*b*(d*e*g+c*(f*g+e*h))+2*b^2*c*e*g*(m-1)-a^2*c*f*h*(2*m+1) + 
    (b^2*(2*m-1)*(d*e*g+c*(f*g+e*h))-a^2*d*f*h*(2*m+1)+2*a*b*(d*f*g+d*e*h-2*c*f*h*m))*x - 
    b*(a*d*f*h*(4*m-1)+b*(c*f*h-2*d*(f*g+e*h)*m))*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && GtQ[m,1]


Int[Sqrt[c_.+d_.*x_]/((a_.+b_.*x_)*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  d/b*Int[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] + 
  (b*c-a*d)/b*Int[1/((a+b*x)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),x] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


(* Int[Sqrt[c_.+d_.*x_]/((a_.+b_.*x_)^(3/2)*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*Sqrt[c+d*x]*Sqrt[(b*g-a*h)*(e+f*x)/((f*g-e*h)*(a+b*x))]/
    ((b*g-a*h)*Sqrt[e+f*x]*Sqrt[(b*g-a*h)*(c+d*x)/((d*g-c*h)*(a+b*x))])*
    Subst[Int[Sqrt[1+(b*c-a*d)*x^2/(d*g-c*h)]/Sqrt[1+(b*e-a*f)*x^2/(f*g-e*h)],x],x,Sqrt[g+h*x]/Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] *)


Int[Sqrt[c_.+d_.*x_]/((a_.+b_.*x_)^(3/2)*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  -2*Sqrt[c+d*x]*Sqrt[-(b*e-a*f)*(g+h*x)/((f*g-e*h)*(a+b*x))]/
    ((b*e-a*f)*Sqrt[g+h*x]*Sqrt[(b*e-a*f)*(c+d*x)/((d*e-c*f)*(a+b*x))])*
    Subst[Int[Sqrt[1+(b*c-a*d)*x^2/(d*e-c*f)]/Sqrt[1-(b*g-a*h)*x^2/(f*g-e*h)],x],x,Sqrt[e+f*x]/Sqrt[a+b*x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x]


Int[(a_.+b_.*x_)^m_*Sqrt[c_.+d_.*x_]/(Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  b*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*e-a*f)*(b*g-a*h)) + 
  1/(2*(m+1)*(b*e-a*f)*(b*g-a*h))*Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
    Simp[2*a*c*f*h*(m+1)-b*(d*e*g+c*(2*m+3)*(f*g+e*h))+2*(a*d*f*h*(m+1)-b*(m+2)*(d*f*g+d*e*h+c*f*h))*x-b*d*f*h*(2*m+5)*x^2,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m},x] && IntegerQ[2*m] && LeQ[m,-2]


Int[(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_/((a_.+b_.*x_)*(c_.+d_.*x_)),x_Symbol] :=
  (b*e-a*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)*(g+h*x)^q/(a+b*x),x] - 
  (d*e-c*f)/(b*c-a*d)*Int[(e+f*x)^(p-1)*(g+h*x)^q/(c+d*x),x] /;
FreeQ[{a,b,c,d,e,f,g,h,q},x] && LtQ[0,p,1]


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_/(Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  Int[ExpandIntegrand[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]),(a+b*x)^m*(c+d*x)^(n+1/2),x],x] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && IntegerQ[m] && IntegerQ[n+1/2]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && IntegersQ[p,q]


Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_,x_Symbol] :=
  h/b*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^(q-1),x] + 
  (b*g-a*h)/b*Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^(q-1),x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p},x] && IGtQ[q,0] && (SumSimplerQ[m,1] || Not[SumSimplerQ[n,1]] && Not[SumSimplerQ[p,1]])


Int[(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
  CannotIntegrate[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x]


Int[(a_.+b_.*u_)^m_.*(c_.+d_.*u_)^n_.*(e_.+f_.*u_)^p_.*(g_.+h_.*u_)^q_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x,u] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && LinearQ[u,x] && NeQ[u,x]


Int[(i_.*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_*(g_.+h_.*x_)^q_)^r_,x_Symbol] :=
  (i*(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q)^r/((a+b*x)^(m*r)*(c+d*x)^(n*r)*(e+f*x)^(p*r)*(g+h*x)^(q*r))*
    Int[(a+b*x)^(m*r)*(c+d*x)^(n*r)*(e+f*x)^(p*r)*(g+h*x)^(q*r),x] /;
FreeQ[{a,b,c,d,e,f,g,h,i,m,n,p,q,r},x]


Int[u_^m_,x_Symbol] :=
  Int[ExpandToSum[u,x]^m,x] /;
FreeQ[m,x] && LinearQ[u,x] && Not[LinearMatchQ[u,x]]


Int[u_^m_.*v_^n_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n,x] /;
FreeQ[{m,n},x] && LinearQ[{u,v},x] && Not[LinearMatchQ[{u,v},x]]


Int[u_^m_.*v_^n_.*w_^p_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p,x] /;
FreeQ[{m,n,p},x] && LinearQ[{u,v,w},x] && Not[LinearMatchQ[{u,v,w},x]]


Int[u_^m_.*v_^n_.*w_^p_.*z_^q_.,x_Symbol] :=
  Int[ExpandToSum[u,x]^m*ExpandToSum[v,x]^n*ExpandToSum[w,x]^p*ExpandToSum[z,x]^q,x] /;
FreeQ[{m,n,p,q},x] && LinearQ[{u,v,w,z},x] && Not[LinearMatchQ[{u,v,w,z},x]]





(* ::Subsection::Closed:: *)
(*1.1.1.5 P(x) (a+b x)^m (c+d x)^n...*)


Int[(A_.+B_.*x_+C_.*x_^2)/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  C*Sqrt[a+b*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(b*f*h*Sqrt[c+d*x]) + 
  C*(d*e-c*f)*(d*g-c*h)/(2*b*d*f*h)*Int[Sqrt[a+b*x]/((c+d*x)^(3/2)*Sqrt[e+f*x]*Sqrt[g+h*x]),x] + 
  1/(2*b*d*f*h)*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
    Simp[2*A*b*d*f*h-C*(b*d*e*g+a*c*f*h)+(2*b*B*d*f*h-C*(a*d*f*h+b*(d*f*g+d*e*h+c*f*h)))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,A,B,C},x]


Int[(A_.+C_.*x_^2)/(Sqrt[a_.+b_.*x_]*Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  C*Sqrt[a+b*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(b*f*h*Sqrt[c+d*x]) + 
  C*(d*e-c*f)*(d*g-c*h)/(2*b*d*f*h)*Int[Sqrt[a+b*x]/((c+d*x)^(3/2)*Sqrt[e+f*x]*Sqrt[g+h*x]),x] + 
  1/(2*b*d*f*h)*Int[1/(Sqrt[a+b*x]*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
    Simp[2*A*b*d*f*h-C*(b*d*e*g+a*c*f*h)-C*(a*d*f*h+b*(d*f*g+d*e*h+c*f*h))*x,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,A,C},x]


Int[Px_*(a_.+b_.*x_)^m_./(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
  2*C*(a+b*x)^m*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(d*f*h*(2*m+3)) + 
  1/(d*f*h*(2*m+3))*Int[((a+b*x)^(m-1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
    Simp[a*A*d*f*h*(2*m+3)-C*(a*(d*e*g+c*f*g+c*e*h)+2*b*c*e*g*m) + 
      ((A*b+a*B)*d*f*h*(2*m+3)-C*(2*a*(d*f*g+d*e*h+c*f*h)+b*(2*m+1)*(d*e*g+c*f*g+c*e*h)))*x + 
      (b*B*d*f*h*(2*m+3)+2*C*(a*d*f*h*m-b*(m+1)*(d*f*g+d*e*h+c*f*h)))*x^2,x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && PolyQ[Px,x] && LeQ[1,Expon[Px,x],2] && IntegerQ[2*m] && GtQ[m,0]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
  Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x,x],0] && EqQ[m,-1]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
  Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x,x],0]


Int[Px_*(a_.+b_.*x_)^m_/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  With[{A=Coeff[Px,x,0],B=Coeff[Px,x,1],C=Coeff[Px,x,2]},
  (A*b^2-a*b*B+a^2*C)*(a+b*x)^(m+1)*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/((m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h)) - 
  1/(2*(m+1)*(b*c-a*d)*(b*e-a*f)*(b*g-a*h))*Int[((a+b*x)^(m+1)/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]))*
    Simp[A*(2*a^2*d*f*h*(m+1)-2*a*b*(m+1)*(d*f*g+d*e*h+c*f*h)+b^2*(2*m+3)*(d*e*g+c*f*g+c*e*h)) - 
      (b*B-a*C)*(a*(d*e*g+c*f*g+c*e*h)+2*b*c*e*g*(m+1)) - 
      2*((A*b-a*B)*(a*d*f*h*(m+1)-b*(m+2)*(d*f*g+d*e*h+c*f*h))-C*(a^2*(d*f*g+d*e*h+c*f*h)-b^2*c*e*g*(m+1)+a*b*(m+1)*(d*e*g+c*f*g+c*e*h)))*x + 
      d*f*h*(2*m+5)*(A*b^2-a*b*B+a^2*C)*x^2,x],x]] /;
FreeQ[{a,b,c,d,e,f,g,h},x] && PolyQ[Px,x] && LeQ[1,Expon[Px,x],2] && IntegerQ[2*m] && LtQ[m,-1]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && PolyQ[Px,x] && IntegersQ[m,n]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
  PolynomialRemainder[Px,a+b*x,x]*Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] + 
  Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && PolyQ[Px,x] && EqQ[m,-1]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.*(g_.+h_.*x_)^q_.,x_Symbol] :=
  PolynomialRemainder[Px,a+b*x,x]*Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] + 
  Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*(g+h*x)^q,x] /;
FreeQ[{a,b,c,d,e,f,g,h,m,n,p,q},x] && PolyQ[Px,x]


Int[(A_.+B_.*x_+C_.*x_^2)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  2*C*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(3*d*f*h) + 
  1/(3*d*f*h)*Int[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
    Simp[3*A*d*f*h-C*(d*e*g+c*f*g+c*e*h)+(3*B*d*f*h-2*C*(d*f*g+d*e*h+c*f*h))*x,x],x] /;
FreeQ[{c,d,e,f,g,h,A,B,C},x]


Int[(A_.+C_.*x_^2)/(Sqrt[c_.+d_.*x_]*Sqrt[e_.+f_.*x_]*Sqrt[g_.+h_.*x_]),x_Symbol] :=
  2*C*Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x]/(3*d*f*h) + 
  1/(3*d*f*h)*Int[1/(Sqrt[c+d*x]*Sqrt[e+f*x]*Sqrt[g+h*x])*
    Simp[3*A*d*f*h-C*(d*e*g+c*f*g+c*e*h)-2*C*(d*f*g+d*e*h+c*f*h)*x,x],x] /;
FreeQ[{c,d,e,f,g,h,A,C},x]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[Px*(a*c+b*d*x^2)^m*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && EqQ[b*c+a*d,0] && EqQ[m,n] && (IntegerQ[m] || GtQ[a,0] && GtQ[c,0])


Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*e*(m+1)) /;
FreeQ[{a1,b1,a2,b2,c,d,e,m,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && EqQ[a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1),0] && NeQ[m,-1]


Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*e*(m+1)) + 
  (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(a1*a2*e^n*(m+1))*Int[(e*x)^(m+n)*(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,d,e,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && (IntegerQ[n] || GtQ[e,0]) && 
  (GtQ[n,0] && LtQ[m,-1] || LtQ[n,0] && GtQ[m+n,-1]) && Not[ILtQ[p,-1]]


Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  -(b1*b2*c-a1*a2*d)*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*b1*b2*e*n*(p+1)) - 
  (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(a1*a2*b1*b2*n*(p+1))*Int[(e*x)^m*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1),x] /;
FreeQ[{a1,b1,a2,b2,c,d,e,m,n},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && LtQ[p,-1] && 
  (Not[IntegerQ[p+1/2]] && NeQ[p,-5/4] || Not[RationalQ[m]] || IGtQ[n,0] && ILtQ[p+1/2,0] && LeQ[-1,m,-n*(p+1)])


Int[(e_.*x_)^m_.*(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  d*(e*x)^(m+1)*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(b1*b2*e*(m+n*(p+1)+1)) - 
  (a1*a2*d*(m+1)-b1*b2*c*(m+n*(p+1)+1))/(b1*b2*(m+n*(p+1)+1))*Int[(e*x)^m*(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,d,e,m,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && NeQ[m+n*(p+1)+1,0]


Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_*(e_.+f_.*x_)^p_.,x_Symbol] :=
  (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m]*Int[Px*(a*c+b*d*x^2)^m*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && EqQ[b*c+a*d,0] && EqQ[m,n] && Not[IntegerQ[m]]


Int[Px_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_./(a_.+b_.*x_),x_Symbol] :=
  Int[PolynomialQuotient[Px,a+b*x,x]*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x,x],0]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x,x],0]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*x)^m*(c+d*x)^n*(e+f*x)^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && IntegersQ[m,n]


Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  With[{Qx=PolynomialQuotient[Px,a+b*x,x], R=PolynomialRemainder[Px,a+b*x,x]},
  b*R*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    ExpandToSum[(m+1)*(b*c-a*d)*(b*e-a*f)*Qx+a*d*f*R*(m+1)-b*R*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*R*(m+n+p+3)*x,x],x]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && PolyQ[Px,x] && ILtQ[m,-1] && IntegersQ[2*m,2*n,2*p]


Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  With[{Qx=PolynomialQuotient[Px,a+b*x,x], R=PolynomialRemainder[Px,a+b*x,x]},
  b*R*(a+b*x)^(m+1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/((m+1)*(b*c-a*d)*(b*e-a*f)) + 
  1/((m+1)*(b*c-a*d)*(b*e-a*f))*Int[(a+b*x)^(m+1)*(c+d*x)^n*(e+f*x)^p*
    ExpandToSum[(m+1)*(b*c-a*d)*(b*e-a*f)*Qx+a*d*f*R*(m+1)-b*R*(d*e*(m+n+2)+c*f*(m+p+2))-b*d*f*R*(m+n+p+3)*x,x],x]] /;
FreeQ[{a,b,c,d,e,f,n,p},x] && PolyQ[Px,x] && LtQ[m,-1] && IntegersQ[2*m,2*n,2*p]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.*(e_.+f_.*x_)^p_.,x_Symbol] :=
  With[{q=Expon[Px,x],k=Coeff[Px,x,Expon[Px,x]]},
  k*(a+b*x)^(m+q-1)*(c+d*x)^(n+1)*(e+f*x)^(p+1)/(d*f*b^(q-1)*(m+q+n+p+1)) + 
  1/(d*f*b^q*(m+q+n+p+1))*Int[(a+b*x)^m*(c+d*x)^n*(e+f*x)^p*
    ExpandToSum[d*f*b^q*(m+q+n+p+1)*Px-d*f*k*(m+q+n+p+1)*(a+b*x)^q + 
      k*(a+b*x)^(q-2)*(a^2*d*f*(m+q+n+p+1)-b*(b*c*e*(m+q-1)+a*(d*e*(n+1)+c*f*(p+1)))+
        b*(a*d*f*(2*(m+q)+n+p)-b*(d*e*(m+q+n)+c*f*(m+q+p)))*x),x],x] /;
  NeQ[m+q+n+p+1,0]] /;
FreeQ[{a,b,c,d,e,f,m,n,p},x] && PolyQ[Px,x] && IntegersQ[2*m,2*n,2*p]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[Px*(a*c+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && EqQ[b*c+a*d,0] && EqQ[m,n] && (IntegerQ[m] || GtQ[a,0] && GtQ[c,0])


Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  c*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2) /;
FreeQ[{a1,b1,a2,b2,c,d,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && EqQ[a1*a2*d-b1*b2*c*(n*(p+1)+1),0]


Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  -(b1*b2*c-a1*a2*d)*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(a1*a2*b1*b2*n*(p+1)) - 
  (a1*a2*d-b1*b2*c*(n*(p+1)+1))/(a1*a2*b1*b2*n*(p+1))*Int[(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1),x] /;
FreeQ[{a1,b1,a2,b2,c,d,n},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && (LtQ[p,-1] || ILtQ[1/n+p,0])


Int[(a1_+b1_.*x_^non2_.)^p_.*(a2_+b2_.*x_^non2_.)^p_.*(c_+d_.*x_^n_),x_Symbol] :=
  d*x*(a1+b1*x^(n/2))^(p+1)*(a2+b2*x^(n/2))^(p+1)/(b1*b2*(n*(p+1)+1)) - 
  (a1*a2*d-b1*b2*c*(n*(p+1)+1))/(b1*b2*(n*(p+1)+1))*Int[(a1+b1*x^(n/2))^p*(a2+b2*x^(n/2))^p,x] /;
FreeQ[{a1,b1,a2,b2,c,d,n,p},x] && EqQ[non2,n/2] && EqQ[a2*b1+a1*b2,0] && NeQ[n*(p+1)+1,0]


Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_,x_Symbol] :=
  (a+b*x)^FracPart[m]*(c+d*x)^FracPart[m]/(a*c+b*d*x^2)^FracPart[m]*Int[Px*(a*c+b*d*x^2)^m,x] /;
FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && EqQ[b*c+a*d,0] && EqQ[m,n] && Not[IntegerQ[m]]


Int[Px_*(c_.+d_.*x_)^n_./(a_.+b_.*x_),x_Symbol] :=
  Int[PolynomialQuotient[Px,a+b*x,x]*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,n},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x,x],0]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[PolynomialQuotient[Px,a+b*x,x]*(a+b*x)^(m+1)*(c+d*x)^n,x] /;
FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && EqQ[PolynomialRemainder[Px,a+b*x,x],0]


Int[Px_*(c_.+d_.*x_)^n_./(a_.+b_.*x_),x_Symbol] :=
  Int[ExpandIntegrand[1/Sqrt[c+d*x],Px*(c+d*x)^(n+1/2)/(a+b*x),x],x] /;
FreeQ[{a,b,c,d,n},x] && PolyQ[Px,x] && ILtQ[n+1/2,0] && GtQ[Expon[Px,x],2]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  Int[ExpandIntegrand[Px*(a+b*x)^m*(c+d*x)^n,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && (IntegersQ[m,n] || IGtQ[m,-2]) && GtQ[Expon[Px,x],2]


Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.,x_Symbol] :=
  With[{Qx=PolynomialQuotient[Px,a+b*x,x], R=PolynomialRemainder[Px,a+b*x,x]},
  R*(a+b*x)^(m+1)*(c+d*x)^(n+1)/((m+1)*(b*c-a*d)) + 
  1/((m+1)*(b*c-a*d))*Int[(a+b*x)^(m+1)*(c+d*x)^n*ExpandToSum[(m+1)*(b*c-a*d)*Qx-d*R*(m+n+2),x],x]] /;
FreeQ[{a,b,c,d,n},x] && PolyQ[Px,x] && ILtQ[m,-1] && GtQ[Expon[Px,x],2]


Int[Px_*(a_.+b_.*x_)^m_*(c_.+d_.*x_)^n_.,x_Symbol] :=
  With[{Qx=PolynomialQuotient[Px,a+b*x,x], R=PolynomialRemainder[Px,a+b*x,x]},
  R*(a+b*x)^(m+1)*(c+d*x)^(n+1)/((m+1)*(b*c-a*d)) + 
  1/((m+1)*(b*c-a*d))*Int[(a+b*x)^(m+1)*(c+d*x)^n*ExpandToSum[(m+1)*(b*c-a*d)*Qx-d*R*(m+n+2),x],x]] /;
FreeQ[{a,b,c,d,n},x] && PolyQ[Px,x] && LtQ[m,-1] && GtQ[Expon[Px,x],2]


Int[Px_*(a_.+b_.*x_)^m_.*(c_.+d_.*x_)^n_.,x_Symbol] :=
  With[{q=Expon[Px,x],k=Coeff[Px,x,Expon[Px,x]]},
  k*(a+b*x)^(m+q)*(c+d*x)^(n+1)/(d*b^q*(m+q+n+1)) + 
  1/(d*b^q*(m+q+n+1))*Int[(a+b*x)^m*(c+d*x)^n*
    ExpandToSum[d*b^q*(m+q+n+1)*Px-d*k*(m+q+n+1)*(a+b*x)^q-k*(b*c-a*d)*(m+q)*(a+b*x)^(q-1),x],x] /;
  NeQ[m+q+n+1,0]] /;
FreeQ[{a,b,c,d,m,n},x] && PolyQ[Px,x] && GtQ[Expon[Px,x],2]



