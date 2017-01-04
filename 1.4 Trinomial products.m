(* ::Package:: *)

(* ::Section:: *)
(*Trinomial Product Rules*)


(* ::Subsection::Closed:: *)
(*4.1 (a+b x^n+c x^(2 n))^p*)


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(2*n*p)*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c},x] && ZeroQ[n2-2*n] && RationalQ[n] && n<0 && IntegerQ[p]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k-1)*(a+b*x^(k*n)+c*x^(2*k*n))^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,p},x] && ZeroQ[n2-2*n] && FractionQ[n]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  x*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[n*(2*p+1)+1]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -x*(a+b*x^n+c*x^(2*n))^(p+1)/(a*(2*p+1)) + 
  x*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*(n+1)) /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && ZeroQ[2*n*(p+1)+1] && NonzeroQ[n+1]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  Sqrt[a+b*x^n+c*x^(2*n)]/(b+2*c*x^n)*Int[(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p-1/2),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && (ZeroQ[2*n*p+1] || ZeroQ[n*(2*p-1)+1]) && 
  RationalQ[p] && p>0 && IntegerQ[p+1/2]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p]))*Int[(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && (ZeroQ[2*n*p+1] || ZeroQ[n*(2*p-1)+1]) && 
  RationalQ[p] && p>0 && Not[IntegerQ[2*p]]


Int[Sqrt[a_+b_.*x_^n_+c_.*x_^n2_],x_Symbol] :=
  x*Sqrt[a+b*x^n+c*x^(2*n)]/(n+1) + 
  b*n*x*Sqrt[a+b*x^n+c*x^(2*n)]/((n+1)*(b+2*c*x^n)) /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && NonzeroQ[n+1] && NonzeroQ[2*n+1] && NonzeroQ[3*n+1]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  x*(a+b*x^n+c*x^(2*n))^p/(2*n*p+1) + 
  n*p*x*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/((2*n*p+1)*(n*(2*p-1)+1)) + 
  2*a*n^2*p*(2*p-1)/((2*n*p+1)*(n*(2*p-1)+1))*Int[(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && 
  NonzeroQ[2*n*p+1] && NonzeroQ[n*(2*p-1)+1] && RationalQ[p] && p>1


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -(n*(2*p+1)+1)*x*(a+b*x^n+c*x^(2*n))^(p+1)/(2*a*n^2*(p+1)*(2*p+1)) - 
  x*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*n*(2*p+1)) + 
  (n*(2*p+1)+1)*(2*n*(p+1)+1)/(2*a*n^2*(p+1)*(2*p+1))*Int[(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && 
  NonzeroQ[n*(2*p+1)+1] && NonzeroQ[2*n*(p+1)+1] && RationalQ[n,p] && p<-1


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/(c^IntPart[p]*(b/2+c*x^n)^(2*FracPart[p]))*Int[(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,p},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[n]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  x*(a+b*x^n+c*x^(2*n))^p/(2*n*p+1) + 
  n*p/(2*n*p+1)*Int[(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p>0 && NonzeroQ[2*n*p+1] && IntegerQ[2*p] && 
  (IntegerQ[p] || ZeroQ[n-2])


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -x*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) +
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[(b^2-2*a*c+n*(p+1)*(b^2-4*a*c)+b*c*(n*(2*p+3)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p<-1 && IntegerQ[2*p] && 
  (IntegerQ[p] || ZeroQ[n-2])


Int[1/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q-b*c,2]},
  q/(2*a*r)*Int[(r-c*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + q/(2*a*r)*Int[(r+c*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]]] /;
FreeQ[{a,b,c},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n/2] && PosQ[a*c] && 
  (RationalQ[a*c] || PerfectSquareQ[a*c] || NegativeQ[b^2-4*a*c] || ZeroQ[b^2-a*c]) && Not[PositiveQ[b^2-4*a*c]]


Int[1/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[1/(b/2-q/2+c*x^n),x] - c/q*Int[1/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*Sqrt[-c]*Int[1/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c] && NegativeQ[c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  (1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(2*q*Sqrt[a+b*x^2+c*x^4])*EllipticF[2*ArcTan[q*x],1/2-b*q^2/(4*c)]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c] && PositiveQ[c/a] && NegativeQ[b/a]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[-2*a-(b-q)*x^2]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*Sqrt[-a]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)] /;
  IntegerQ[q]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c] && NegativeQ[a] && PositiveQ[c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*Sqrt[a+b*x^2+c*x^4]*Sqrt[a/(2*a+(b+q)*x^2)])*
    EllipticF[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c] && NegativeQ[a] && PositiveQ[c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*a+(b+q)*x^2)*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]/(2*a*Rt[(b+q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcTan[Rt[(b+q)/(2*a),2]*x],2*q/(b+q)] /;
 PosQ[(b+q)/a] && Not[PosQ[(b-q)/a] && SimplerSqrtQ[(b-q)/(2*a),(b+q)/(2*a)]]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*a+(b-q)*x^2)*Sqrt[(2*a+(b+q)*x^2)/(2*a+(b-q)*x^2)]/(2*a*Rt[(b-q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcTan[Rt[(b-q)/(2*a),2]*x],-2*q/(b-q)] /;
 PosQ[(b-q)/a]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+(b+q)*x^2/(2*a)]*Sqrt[1+(b-q)*x^2/(2*a)]/(Rt[-(b+q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcSin[Rt[-(b+q)/(2*a),2]*x],(b-q)/(b+q)] /;
 NegQ[(b+q)/a] && Not[NegQ[(b-q)/a] && SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+(b-q)*x^2/(2*a)]*Sqrt[1+(b+q)*x^2/(2*a)]/(Rt[-(b-q)/(2*a),2]*Sqrt[a+b*x^2+c*x^4])*
    EllipticF[ArcSin[Rt[-(b-q)/(2*a),2]*x],(b+q)/(b-q)] /;
 NegQ[(b-q)/a]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  (1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(2*q*Sqrt[a+b*x^2+c*x^4])*EllipticF[2*ArcTan[q*x],1/2-b*q^2/(4*c)]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PosQ[c/a]


Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[1/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && NegQ[c/a]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^n+c*x^(2*n))^FracPart[p]/
    ((1+2*c*x^n/(b+Rt[b^2-4*a*c,2]))^FracPart[p]*(1+2*c*x^n/(b-Rt[b^2-4*a*c,2]))^FracPart[p])*
    Int[(1+2*c*x^n/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^n/(b-Sqrt[b^2-4*a*c]))^p,x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n]


Int[(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[(b+a*x^n+c*x^(2*n))^p/x^(n*p),x] /;
FreeQ[{a,b,c,n},x] && EqQ[mn,-n] && IntegerQ[p] && PosQ[n]


Int[(a_+b_.*x_^mn_+c_.*x_^n_.)^p_,x_Symbol] :=
  x^(n*FracPart[p])*(a+b*x^(-n)+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p]*Int[(b+a*x^n+c*x^(2*n))^p/x^(n*p),x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[mn,-n] && Not[IntegerQ[p]] && PosQ[n]


Int[(a_+b_.*u_^n_+c_.*u_^n2_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a+b*x^n+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,b,c,n,p},x] && ZeroQ[n2-2*n] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*4.2 (d x)^m (a+b x^n+c x^(2 n))^p*)


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && ZeroQ[Simplify[m-n+1]]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(d*x)^m*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && PositiveIntegerQ[p] && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  Int[x^(m+2*n*p)*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,m,n},x] && EqQ[n2,2*n] && NegativeIntegerQ[p] && NegQ[n]


Int[Sqrt[a_+b_.*x_^n_+c_.*x_^n2_.]/x_,x_Symbol] :=
  Sqrt[a+b*x^n+c*x^(2*n)]/n + 
  b*Sqrt[a+b*x^n+c*x^(2*n)]*Log[x]/(b+2*c*x^n) /;
FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c]


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_/x_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^p/(2*n*p) + (2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/(2*n*(2*p-1)) + 
  a*Int[(a+b*x^n+c*x^(2*n))^(p-1)/x,x] /;
FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && RationalQ[p] && p>1


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_/x_,x_Symbol] :=
  -(a+b*x^n+c*x^(2*n))^(p+1)/(2*a*n*(p+1)) - (2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*n*(2*p+1)) + 
  1/a*Int[(a+b*x^n+c*x^(2*n))^(p+1)/x,x] /;
FreeQ[{a,b,c,n},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && RationalQ[p] && p<-1


Int[(a_+b_.*x_^n_+c_.*x_^n2_.)^p_/x_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/(c^IntPart[p]*(b/2+c*x^n)^(2*FracPart[p]))*Int[(b/2+c*x^n)^(2*p)/x,x] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(b*d*(m+1)) /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && ZeroQ[m+n*(2*p+1)+1]


Int[(d_.*x_)^m_.*Sqrt[a_+b_.*x_^n_+c_.*x_^n2_.],x_Symbol] :=
  Sqrt[a+b*x^n+c*x^(2*n)]/(b+2*c*x^n)*Int[(d*x)^m*(b+2*c*x^n),x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && ZeroQ[m+n+1]


Int[(d_.*x_)^m_.*Sqrt[a_+b_.*x_^n_+c_.*x_^n2_.],x_Symbol] :=
  (d*x)^(m+1)*Sqrt[a+b*x^n+c*x^(2*n)]/(d*(m+n+1)) + 
  b*n*(d*x)^(m+1)*Sqrt[a+b*x^n+c*x^(2*n)]/(d*(m+1)*(m+n+1)*(b+2*c*x^n)) /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && NonzeroQ[m+n+1]


Int[x_^m_./Sqrt[a_+b_.*x_^n_+c_.*x_^n2_.],x_Symbol] :=
  -x^(m+1)*Sqrt[a+b*x^n+c*x^(2*n)]/(a*n) - 
  b/(2*a)*Int[1/(x*Sqrt[a+b*x^n+c*x^(2*n)]),x] /;
FreeQ[{a,b,c,m,n},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && ZeroQ[m+n+1]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(2*a*d*n*(p+1)*(2*p+1)) - 
  (d*x)^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*d*n*(2*p+1)) /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && ZeroQ[m+2*n(p+1)+1] && NonzeroQ[2*p+1]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^(p+1)/(2*c*n*(p+1)) - 
  b/(2*c)*Int[x^(n-1)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && ZeroQ[m-2*n+1] && NonzeroQ[p+3/2]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+2*n*p+1)) + 
  n*p*(d*x)^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d*(m+1)*(m+2*n*p+1)) - 
  b*p*n^2*(2*p-1)/(d^n*(m+1)*(m+2*n*p+1))*Int[(d*x)^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>1 && -1<=m+n<0 && 
  IntegerQ[2*p] && IntegerQ[m]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (m-n*(2*p-1)+1)*(d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+1)*(m+n+1)) + 
  n*p*(d*x)^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d*(m+1)*(m+n+1)) + 
  2*c*p*n^2*(2*p-1)/(d^(2*n)*(m+1)*(m+n+1))*Int[(d*x)^(m+2*n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>1 && m+n<-1 && 
  Not[NegativeIntegerQ[(m+2*n(p+1)+1)/n] && (m+2*n(p+1)+1)/n+p>0] && IntegerQ[2*p] && IntegerQ[m]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+2*n*p+1)) + 
  n*p*(d*x)^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d*(m+2*n*p+1)*(m+n*(2*p-1)+1)) + 
  2*a*n^2*p*(2*p-1)/((m+2*n*p+1)*(m+n*(2*p-1)+1))*Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p>1 && 
  NonzeroQ[m+2*n*p+1] && NonzeroQ[m+n*(2*p-1)+1] && 
  Not[NegativeIntegerQ[(m+2*n*(p+1)+1)/n] && (m+2*n(p+1)+1)/n+p>0] && 
  Not[PositiveIntegerQ[m] && IntegerQ[(m+1)/n] && (m+1)/n-1<2*p] && IntegerQ[2*p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(n-1)*(m+n*(2*p+1)+1)*(d*x)^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(b*n^2*(p+1)*(2*p+1)) - 
  (d*x)^(m+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(b*d*n*(2*p+1)) - 
  d^n*(m-n+1)*(m+n*(2*p+1)+1)/(b*n^2*(p+1)*(2*p+1))*Int[(d*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && n-1<m<=2*n-1 && 
  IntegerQ[2*p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -d^(2*n-1)*(m-3*n-2*n*p+1)*(d*x)^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(2*c*n^2*(p+1)*(2*p+1)) - 
  d^(2*n-1)*(d*x)^(m-2*n+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*c*n*(2*p+1)) + 
  d^(2*n)*(m-n+1)*(m-2*n+1)/(2*c*n^2*(p+1)*(2*p+1))*Int[(d*x)^(m-2*n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>2*n-1 && 
  IntegerQ[2*p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -(m+n*(2*p+1)+1)*(d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(2*a*d*n^2*(p+1)*(2*p+1)) - 
  (d*x)^(m+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*a*d*n*(2*p+1)) + 
  (m+n*(2*p+1)+1)*(m+2*n*(p+1)+1)/(2*a*n^2*(p+1)*(2*p+1))*Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && IntegerQ[2*p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(n-1)*(d*x)^(m-n+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(2*c*(m+2*n*p+1)) - 
  b*d^n*(m-n+1)/(2*c*(m+2*n*p+1))*Int[(d*x)^(m-n)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>n-1 && 
  NonzeroQ[m+2*n*p+1] && (IntegerQ[2*p] || PositiveIntegerQ[(m+1)/n])


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^p/(b*d*(m+1)) - 
  2*c*(m+n*(2*p+1)+1)/(b*d^n*(m+1))*Int[(d*x)^(m+n)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && 
  (IntegerQ[2*p] || PositiveIntegerQ[(m+1)/n])


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/d*Subst[Int[(a+b*d^(-n)*x^(-k*n)+c*d^(-2*n)*x^(-2*k*n))^p/x^(k*(m+1)+1),x],x,1/(d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && FractionQ[m]


Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -d^IntPart[m]*(d*x)^FracPart[m]*(x^(-1))^FracPart[m]*Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/(c^IntPart[p]*(b/2+c*x^n)^(2*FracPart[p]))*Int[(d*x)^m*(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[(d_*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(a+b*x^(n/k)+c*x^(2*n/k))^p,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/d*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)/d^n+c*x^(2*k*n)/d^(2*n))^p,x],x,(d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && FractionQ[m] && IntegerQ[p]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(n-1)*(d*x)^(m-n+1)*(b*n*p+c*(m+n*(2*p-1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/(c*(m+2*n*p+1)*(m+n*(2*p-1)+1)) - 
  n*p*d^n/(c*(m+2*n*p+1)*(m+n*(2*p-1)+1))*
    Int[(d*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p-1)*Simp[a*b*(m-n+1)-(2*a*c*(m+n*(2*p-1)+1)-b^2*(m+n*(p-1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m>n-1 && 
  m+2*n*p+1!=0 && m+n*(2*p-1)+1!=0 && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+1)) - 
  n*p/(d^n*(m+1))*Int[(d*x)^(m+n)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p/(d*(m+2*n*p+1)) + 
  n*p/(m+2*n*p+1)*Int[(d*x)^m*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p>0 && NonzeroQ[m+2*n*p+1] && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(n-1)*(d*x)^(m-n+1)*(b+2*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) - 
  d^n/(n*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^(m-n)*(b*(m-n+1)+2*c*(m+2*n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && n-1<m<=2*n-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -d^(2*n-1)*(d*x)^(m-2*n+1)*(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(n*(p+1)*(b^2-4*a*c)) + 
  d^(2*n)/(n*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^(m-2*n)*(2*a*(m-2*n+1)+b*(m+n*(2*p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>2*n-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -(d*x)^(m+1)*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*Simp[b^2*(n*(p+1)+m+1)-2*a*c*(m+2*n*(p+1)+1)+b*c*(2*n*p+3*n+m+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^(2*n-1)*(d*x)^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+2*n*p+1)) - 
  d^(2*n)/(c*(m+2*n*p+1))*
    Int[(d*x)^(m-2*n)*Simp[a*(m-2*n+1)+b*(m+n*(p-1)+1)*x^n,x]*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>2*n-1 && 
  NonzeroQ[m+2*n*p+1] && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (d*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*(m+1)) - 
  1/(a*d^n*(m+1))*Int[(d*x)^(m+n)*(b*(m+n*(p+1)+1)+c*(m+2*n*(p+1)+1)*x^n)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  (d*x)^(m+1)/(a*d*(m+1)) -
  1/(a*d^n)*Int[(d*x)^(m+n)*(b+c*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m<-1


Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[PolynomialDivide[x^m,(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m] && m>3*n-1


Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  d^(2*n-1)*(d*x)^(m-2*n+1)/(c*(m-2*n+1)) -
  d^(2*n)/c*Int[(d*x)^(m-2*n)*(a+b*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>2*n-1


Int[x_^2/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  With[{q=Rt[a/c,2]},
  1/2*Int[(q+x^2)/(a+b*x^2+c*x^4),x] -
  1/2*Int[(q-x^2)/(a+b*x^2+c*x^4),x]] /;
FreeQ[{a,b,c},x] && NegativeQ[b^2-4*a*c] && PosQ[a*c]


Int[(d_.*x_)^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q-b*c,2]},
  c*d^(n/2)/(2*r)*Int[(d*x)^(m-n/2)/(q-r*x^(n/2)+c*x^n),x] - 
  c*d^(n/2)/(2*r)*Int[(d*x)^(m-n/2)/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NegativeQ[b^2-4*a*c] && PositiveIntegerQ[n/2,m] && n/2<=m<2*n && PosQ[a*c]


Int[(d_.*x_)^m_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  d^n/2*(b/q+1)*Int[(d*x)^(m-n)/(b/2+q/2+c*x^n),x] - 
  d^n/2*(b/q-1)*Int[(d*x)^(m-n)/(b/2-q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>=n


Int[(d_.*x_)^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  c/q*Int[(d*x)^m/(b/2-q/2+c*x^n),x] - c/q*Int[(d*x)^m/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d,m},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*Sqrt[-c]*Int[x^2/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c] && NegativeQ[c]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  1/q*Int[1/Sqrt[a+b*x^2+c*x^4],x] - 1/q*Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c] && PositiveQ[c/a] && NegativeQ[b/a]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(b-q)/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c] && NegativeQ[a] && PositiveQ[c]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  x*(b+q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) - 
  Rt[(b+q)/(2*a),2]*(2*a+(b+q)*x^2)*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]/(2*c*Sqrt[a+b*x^2+c*x^4])*
    EllipticE[ArcTan[Rt[(b+q)/(2*a),2]*x],2*q/(b+q)] /;
 PosQ[(b+q)/a] && Not[PosQ[(b-q)/a] && SimplerSqrtQ[(b-q)/(2*a),(b+q)/(2*a)]]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  x*(b-q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) - 
  Rt[(b-q)/(2*a),2]*(2*a+(b-q)*x^2)*Sqrt[(2*a+(b+q)*x^2)/(2*a+(b-q)*x^2)]/(2*c*Sqrt[a+b*x^2+c*x^4])*
    EllipticE[ArcTan[Rt[(b-q)/(2*a),2]*x],-2*q/(b-q)] /;
 PosQ[(b-q)/a]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(b+q)/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c)*Int[(b+q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NegQ[(b+q)/a] && Not[NegQ[(b-q)/a] && SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(b-q)/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + 1/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NegQ[(b-q)/a]] /;
FreeQ[{a,b,c},x] && PositiveQ[b^2-4*a*c]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  1/q*Int[1/Sqrt[a+b*x^2+c*x^4],x] - 1/q*Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PosQ[c/a]


Int[x_^2/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[x^2/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && NegQ[c/a]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  -k/d*Subst[Int[(a+b*d^(-n)*x^(-k*n)+c*d^(-2*n)*x^(-2*k*n))^p/x^(k*(m+1)+1),x],x,1/(d*x)^(1/k)]] /;
FreeQ[{a,b,c,d,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && FractionQ[m]


Int[(d_.*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -d^IntPart[m]*(d*x)^FracPart[m]*(x^(-1))^FracPart[m]*Subst[Int[(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[n]},
  k*Subst[Int[x^(k*(m+1)-1)*(a+b*x^(k*n)+c*x^(2*k*n))^p,x],x,x^(1/k)]] /;
FreeQ[{a,b,c,m,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && FractionQ[n]


Int[(d_*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && FractionQ[n]


Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(d_*x_)^m_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(d_.*x_)^m_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/q*Int[(d*x)^m/(b-q+2*c*x^n),x] -
  2*c/q*Int[(d*x)^m/(b+q+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -(d*x)^(m+1)*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*d*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[(d*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*Simp[b^2*(n*(p+1)+m+1)-2*a*c*(m+2*n*(p+1)+1)+b*c*(2*n*p+3*n+m+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,m,n},x] && EqQ[n2,2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(d_.*x_)^m_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  a^IntPart[p]*(a+b*x^n+c*x^(2*n))^FracPart[p]/
    ((1+2*c*x^n/(b+Rt[b^2-4*a*c,2]))^FracPart[p]*(1+2*c*x^n/(b-Rt[b^2-4*a*c,2]))^FracPart[p])*
    Int[(d*x)^m*(1+2*c*x^n/(b+Sqrt[b^2-4*a*c]))^p*(1+2*c*x^n/(b-Sqrt[b^2-4*a*c]))^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[n2,2*n]


Int[x_^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^(m-n*p)*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,m,n},x] && EqQ[mn,-n] && IntegerQ[p] && PosQ[n]


Int[x_^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p]*Int[x^(m-n*p)*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[mn,-n] && Not[IntegerQ[p]] && PosQ[n]


Int[(d_*x_)^m_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  d^IntPart[m]*(d*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(a+b*x^(-n)+c*x^n)^p,x] /;
FreeQ[{a,b,c,d,m,n,p},x] && EqQ[mn,-n]


Int[x_^m_.*(a_.+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  1/Coefficient[v,x,1]^(m+1)*Subst[Int[SimplifyIntegrand[(x-Coefficient[v,x,0])^m*(a+b*x^n+c*x^(2*n))^p,x],x],x,v] /;
FreeQ[{a,b,c,n,p},x] && EqQ[n2,2*n] && LinearQ[v,x] && IntegerQ[m] && NonzeroQ[v-x]


Int[u_^m_.*(a_.+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,m,n,p},x] && EqQ[n2,2*n] && LinearPairQ[u,v,x]





(* ::Subsection::Closed:: *)
(*4.3 (d+e x^n)^m (a+b x^n+c x^(2 n))^p*)


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(n*(2*p+q))*(e+d*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && IntegersQ[p,q] && NegQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(n*(2*p+q))*(e+d*x^(-n))^q*(c+a*x^(-2*n))^p,x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n] && IntegersQ[p,q] && NegQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^2,x],x,1/x] /;
FreeQ[{a,b,c,d,e,p,q},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^2,x],x,1/x] /;
FreeQ[{a,c,d,e,p,q},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*(d+e*x^(g*n))^q*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,d,e,p,q},x] && ZeroQ[n2-2*n] && FractionQ[n]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g-1)*(d+e*x^(g*n))^q*(a+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,c,d,e,p,q},x] && ZeroQ[n2-2*n] && FractionQ[n]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (b*e-d*c)*(b*x^n+c*x^(2*n))^(p+1)/(b*c*n*(p+1)*x^(2*n*(p+1))) + 
  e/c*Int[x^(-n)*(b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{b,c,d,e,n,p},x] && ZeroQ[n2-2*n] && Not[IntegerQ[p]] && ZeroQ[n*(2*p+1)+1]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  e*x^(-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(n*(2*p+1)+1)) /;
FreeQ[{b,c,d,e,n,p},x] && ZeroQ[n2-2*n] && Not[IntegerQ[p]] && NonzeroQ[n*(2*p+1)+1] && ZeroQ[b*e*(n*p+1)-c*d*(n*(2*p+1)+1)]


Int[(d_+e_.*x_^n_)*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  e*x^(-n+1)*(b*x^n+c*x^(2*n))^(p+1)/(c*(n*(2*p+1)+1)) - 
  (b*e*(n*p+1)-c*d*(n*(2*p+1)+1))/(c*(n*(2*p+1)+1))*Int[(b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{b,c,d,e,n,p},x] && ZeroQ[n2-2*n] && Not[IntegerQ[p]] && NonzeroQ[n*(2*p+1)+1] && NonzeroQ[b*e*(n*p+1)-c*d*(n*(2*p+1)+1)]


Int[(d_+e_.*x_^n_)^q_.*(b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (b*x^n+c*x^(2*n))^FracPart[p]/(x^(n*FracPart[p])*(b+c*x^n)^FracPart[p])*Int[x^(n*p)*(d+e*x^n)^q*(b+c*x^n)^p,x] /;
FreeQ[{b,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p]))*Int[(d+e*x^n)^q*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,n,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,n,q},x] && ZeroQ[n2-2*n] && ZeroQ[c*d^2+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*Int[(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*Int[(d+e*x^n)^(p+q)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[q]


Int[(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q*(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[q]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  -(c*d^2-b*d*e+a*e^2)*x*(d+e*x^n)^(q+1)/(d*e^2*n*(q+1)) + 
  1/(n*(q+1)*d*e^2)*Int[(d+e*x^n)^(q+1)*Simp[c*d^2-b*d*e+a*e^2*(n*(q+1)+1)+c*d*e*n*(q+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && RationalQ[q] && q<-1


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_),x_Symbol] :=
  -(c*d^2+a*e^2)*x*(d+e*x^n)^(q+1)/(d*e^2*n*(q+1)) + 
  1/(n*(q+1)*d*e^2)*Int[(d+e*x^n)^(q+1)*Simp[c*d^2+a*e^2*(n*(q+1)+1)+c*d*e*n*(q+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && RationalQ[q] && q<-1


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  c*x^(n+1)*(d+e*x^n)^(q+1)/(e*(n*(q+2)+1)) + 
  1/(e*(n*(q+2)+1))*Int[(d+e*x^n)^q*(a*e*(n*(q+2)+1)-(c*d*(n+1)-b*e*(n*(q+2)+1))*x^n),x] /;
FreeQ[{a,b,c,d,e,n,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_),x_Symbol] :=
  c*x^(n+1)*(d+e*x^n)^(q+1)/(e*(n*(q+2)+1)) + 
  1/(e*(n*(q+2)+1))*Int[(d+e*x^n)^q*(a*e*(n*(q+2)+1)-c*d*(n+1)*x^n),x] /;
FreeQ[{a,c,d,e,n,q},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2]


(* Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  e^2/c*Subst[Int[1/(1+2*d*e*x^2),x],x,x/(d-e*x^2)] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2-a*e^2] *)


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  e^2/(2*c)*Int[1/(d-Rt[2*d*e,2]*x+e*x^2),x] + 
  e^2/(2*c)*Int[1/(d+Rt[2*d*e,2]*x+e*x^2),x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2-a*e^2] && PosQ[d*e]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[-2*d*e,2]},
  e^2/(2*c*q)*Int[(q+2*e*x)/(d-q*x-e*x^2),x] + 
  e^2/(2*c*q)*Int[(q-2*e*x)/(d+q*x-e*x^2),x]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2-a*e^2] && NegQ[d*e]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  (d*q+a*e)/(2*a*c)*Int[(q+c*x^2)/(a+c*x^4),x] +
  (d*q-a*e)/(2*a*c)*Int[(q-c*x^2)/(a+c*x^4),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NonzeroQ[c*d^2-a*e^2] && PosQ[a*c]


Int[(d_+e_.*x_^2)/(a_+c_.*x_^4),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (c*d+e*q)/(2*c)*Int[1/(a+q*x^2),x] + (c*d-e*q)/(2*c)*Int[1/(a-q*x^2),x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NonzeroQ[c*d^2-a*e^2] && NegQ[a*c]


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q-b*c,2]},
  e/2*Int[1/(q-r*x^(n/2)+c*x^n),x] + e/2*Int[1/(q+r*x^(n/2)+c*x^n),x]] /;
 ZeroQ[c*d-e*q] && Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[n/2] && 
  PosQ[a*c] && (RationalQ[a*c] || PerfectSquareQ[a*c] || NegativeQ[b^2-4*a*c] || ZeroQ[b^2-a*c])


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q,2]},
  e/2*Int[1/(q-r*x^(n/2)+c*x^n),x] + e/2*Int[1/(q+r*x^(n/2)+c*x^n),x]] /;
 ZeroQ[c*d-e*q] && Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[n/2] && PositiveQ[a*c]


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q-b*c,2]},
  c/(2*q*r)*Int[(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[n/2] && 
  PosQ[a*c] && (RationalQ[a*c] || PerfectSquareQ[a*c] || NegativeQ[b^2-4*a*c] || ZeroQ[b^2-a*c]) && Not[PositiveQ[b^2-4*a*c]]


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q,2]},
  c/(2*q*r)*Int[(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[n/2] && NegativeQ[-a*c] && Not[PositiveQ[-a*c]]


Int[(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (e/2+(2*c*d-b*e)/(2*q))*Int[1/(b/2-q/2+c*x^n),x] + (e/2-(2*c*d-b*e)/(2*q))*Int[1/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  -(e/2+c*d/(2*q))*Int[1/(q-c*x^n),x] + (e/2-c*d/(2*q))*Int[1/(q+c*x^n),x]] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2]


Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[q]


Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[q]


Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  e^2/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x^n)^q,x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(d+e*x^n)^(q+1)*(c*d-b*e-c*e*x^n)/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[q]] && 
  RationalQ[q] && q<-1


Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
  e^2/(c*d^2+a*e^2)*Int[(d+e*x^n)^q,x] + 
  c/(c*d^2+a*e^2)*Int[(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[q]] && RationalQ[q] && q<-1


Int[(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  2*c/r*Int[(d+e*x^n)^q/(b-r+2*c*x^n),x] - 2*c/r*Int[(d+e*x^n)^q/(b+r+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,e,n,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[q]]


Int[(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{r=Rt[-a*c,2]},
  -c/(2*r)*Int[(d+e*x^n)^q/(r-c*x^n),x] - c/(2*r)*Int[(d+e*x^n)^q/(r+c*x^n),x]] /;
FreeQ[{a,c,d,e,n,q},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && Not[IntegerQ[q]]


Int[(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  x*(b*e*n*p+c*d*(2*n*p+n+1)+c*e*(2*n*p+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/(c*(2*n*p+1)*(2*n*p+n+1)) + 
  n*p/(c*(2*n*p+1)*(2*n*p+n+1))*
    Int[Simp[2*a*c*d*(2*n*p+n+1)-a*b*e+(2*a*c*e*(2*n*p+1)+b*d*c*(2*n*p+n+1)-b^2*e*(n*p+1))*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && FractionQ[p] && p>0 && NonzeroQ[2*n*p+1] && NonzeroQ[2*n*p+n+1] && 
  IntegerQ[2*p] && (IntegerQ[p] || ZeroQ[n-2])


Int[(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  x*(d*(2*n*p+n+1)+e*(2*n*p+1)*x^n)*(a+c*x^(2*n))^p/((2*n*p+1)*(2*n*p+n+1)) + 
  2*a*n*p/((2*n*p+1)*(2*n*p+n+1))*Int[(d*(2*n*p+n+1)+e*(2*n*p+1)*x^n)*(a+c*x^(2*n))^(p-1),x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n] && FractionQ[p] && p>0 && NonzeroQ[2*n*p+1] && NonzeroQ[2*n*p+n+1] && 
  IntegerQ[2*p] && (IntegerQ[p] || ZeroQ[n-2])


Int[(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(d*b^2-a*b*e-2*a*c*d+(b*d-2*a*e)*c*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*
    Int[Simp[(n*p+n+1)*d*b^2-a*b*e-2*a*c*d*(2*n*p+2*n+1)+(2*n*p+3*n+1)*(d*b-2*a*e)*c*x^n,x]*
      (a+b*x^n+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && RationalQ[p] && p<-1 && IntegerQ[2*p] && 
  (IntegerQ[p] || ZeroQ[n-2])


Int[(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -x*(d+e*x^n)*(a+c*x^(2*n))^(p+1)/(2*a*n*(p+1)) + 
  1/(2*a*n*(p+1))*Int[(d*(2*n*p+2*n+1)+e*(2*n*p+3*n+1)*x^n)*(a+c*x^(2*n))^(p+1),x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n] && RationalQ[p] && p<-1 && IntegerQ[2*p] && (IntegerQ[p] || ZeroQ[n-2])


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*Sqrt[-c]*Int[(d+e*x^2)/(Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c] && NegativeQ[c]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  Sqrt[-c]*Int[(d+e*x^2)/(Sqrt[q+c*x^2]*Sqrt[q-c*x^2]),x]] /;
FreeQ[{a,c,d,e},x] && PositiveQ[a] && NegativeQ[c]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  -d*x*Sqrt[a+b*x^2+c*x^4]/(a*(1+q^2*x^2)) + 
  d*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+b*x^2+c*x^4])*EllipticE[2*ArcTan[q*x],1/2-b*q^2/(4*c)] /;
 ZeroQ[e+d*q^2]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c] && PositiveQ[c/a] && NegativeQ[b/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  (e+d*q)/q*Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/q*Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NonzeroQ[e+d*q]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c] && PositiveQ[c/a] && NegativeQ[b/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  e*x*(b+q+2*c*x^2)/(2*c*Sqrt[a+b*x^2+c*x^4]) - 
  e*q*Sqrt[(2*a+(b-q)*x^2)/(2*a+(b+q)*x^2)]*Sqrt[(2*a+(b+q)*x^2)/q]/(2*c*Sqrt[a+b*x^2+c*x^4]*Sqrt[a/(2*a+(b+q)*x^2)])*
    EllipticE[ArcSin[x/Sqrt[(2*a+(b+q)*x^2)/(2*q)]],(b+q)/(2*q)] /;
 ZeroQ[2*c*d-e*(b-q)]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c] && NegativeQ[a] && PositiveQ[c]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  e*x*(q+c*x^2)/(c*Sqrt[a+c*x^4]) - 
  Sqrt[2]*e*q*Sqrt[-a+q*x^2]*Sqrt[(a+q*x^2)/q]/(Sqrt[-a]*c*Sqrt[a+c*x^4])*
    EllipticE[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2] /;
 ZeroQ[c*d+e*q] && IntegerQ[q]] /;
FreeQ[{a,c,d,e},x] && NegativeQ[a] && PositiveQ[c]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  e*x*(q+c*x^2)/(c*Sqrt[a+c*x^4]) - 
  Sqrt[2]*e*q*Sqrt[(a-q*x^2)/(a+q*x^2)]*Sqrt[(a+q*x^2)/q]/(c*Sqrt[a+c*x^4]*Sqrt[a/(a+q*x^2)])*
    EllipticE[ArcSin[x/Sqrt[(a+q*x^2)/(2*q)]],1/2] /;
 ZeroQ[c*d+e*q]] /;
FreeQ[{a,c,d,e},x] && NegativeQ[a] && PositiveQ[c]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-e*(b-q))/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NonzeroQ[2*c*d-e*(b-q)]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c] && NegativeQ[a] && PositiveQ[c]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (c*d+e*q)/c*Int[1/Sqrt[a+c*x^4],x] - e/c*Int[(q-c*x^2)/Sqrt[a+c*x^4],x] /;
 NonzeroQ[c*d+e*q]] /;
FreeQ[{a,c,d,e},x] && NegativeQ[a] && PositiveQ[c]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  d*Int[1/Sqrt[a+b*x^2+c*x^4],x] + e*Int[x^2/Sqrt[a+b*x^2+c*x^4],x] /;
 PosQ[(b+q)/a] || PosQ[(b-q)/a]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  d*Int[1/Sqrt[a+c*x^4],x] + e*Int[x^2/Sqrt[a+c*x^4],x] /;
FreeQ[{a,c,d,e},x] && PositiveQ[-a*c]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -a*e*Rt[-(b+q)/(2*a),2]*Sqrt[1+(b+q)*x^2/(2*a)]*Sqrt[1+(b-q)*x^2/(2*a)]/(c*Sqrt[a+b*x^2+c*x^4])*
    EllipticE[ArcSin[Rt[-(b+q)/(2*a),2]*x],(b-q)/(b+q)] /;
 NegQ[(b+q)/a] && ZeroQ[2*c*d-e*(b+q)] && Not[SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-e*(b+q))/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c)*Int[(b+q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NegQ[(b+q)/a] && NonzeroQ[2*c*d-e*(b+q)] && Not[SimplerSqrtQ[-(b-q)/(2*a),-(b+q)/(2*a)]]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -a*e*Rt[-(b-q)/(2*a),2]*Sqrt[1+(b-q)*x^2/(2*a)]*Sqrt[1+(b+q)*x^2/(2*a)]/(c*Sqrt[a+b*x^2+c*x^4])*
    EllipticE[ArcSin[Rt[-(b-q)/(2*a),2]*x],(b+q)/(b-q)] /;
 NegQ[(b-q)/a] && ZeroQ[2*c*d-e*(b-q)]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*d-e*(b-q))/(2*c)*Int[1/Sqrt[a+b*x^2+c*x^4],x] + e/(2*c)*Int[(b-q+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NegQ[(b-q)/a] && NonzeroQ[2*c*d-e*(b-q)]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  -d*x*Sqrt[a+b*x^2+c*x^4]/(a*(1+q^2*x^2)) + 
  d*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+b*x^2+c*x^4])*EllipticE[2*ArcTan[q*x],1/2-b*q^2/(4*c)] /;
 ZeroQ[e+d*q^2]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && PosQ[c/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,4]},
  -d*x*Sqrt[a+c*x^4]/(a*(1+q^2*x^2)) + 
  d*(1+q^2*x^2)*Sqrt[(a+c*x^4)/(a*(1+q^2*x^2)^2)]/(q*Sqrt[a+c*x^4])*EllipticE[2*ArcTan[q*x],1/2] /;
 ZeroQ[e+d*q^2]] /;
FreeQ[{a,c,d,e},x] && PosQ[c/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  (e+d*q)/q*Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/q*Int[(1-q*x^2)/Sqrt[a+b*x^2+c*x^4],x] /;
 NonzeroQ[e+d*q]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && PosQ[c/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[c/a,2]},
  (e+d*q)/q*Int[1/Sqrt[a+c*x^4],x] - e/q*Int[(1-q*x^2)/Sqrt[a+c*x^4],x] /;
 NonzeroQ[e+d*q]] /;
FreeQ[{a,c,d,e},x] && PosQ[c/a]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  d/Sqrt[a]*Int[Sqrt[1+e*x^2/d]/Sqrt[1-e*x^2/d],x] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && ZeroQ[c*d^2+a*e^2] && PositiveQ[a]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  Sqrt[1+c*x^4/a]/Sqrt[a+c*x^4]*Int[(d+e*x^2)/Sqrt[1+c*x^4/a],x] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && ZeroQ[c*d^2+a*e^2] && Not[PositiveQ[a]]


Int[(d_+e_.*x_^2)/Sqrt[a_+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[-c/a,2]},
  (d*q-e)/q*Int[1/Sqrt[a+c*x^4],x] + e/q*Int[(1+q*x^2)/Sqrt[a+c*x^4],x]] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && NonzeroQ[c*d^2+a*e^2]


Int[(d_+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[(d+e*x^2)/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NegQ[c/a]


Int[(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[n2-2*n]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  c^p*x^(2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*(2*n*p+n*q+1)) + 
  Int[(d+e*x^n)^q*ExpandToSum[(a+b*x^n+c*x^(2*n))^p-c^p*x^(2*n*p)-d*c^p*(2*n*p-n+1)*x^(2*n*p-n)/(e*(2*n*p+n*q+1)),x],x] /;
FreeQ[{a,b,c,d,e,n,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[p] && 
  NonzeroQ[2*n*p+n*q+1] && PositiveIntegerQ[n] && Not[PositiveIntegerQ[q]]


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  c^p*x^(2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*(2*n*p+n*q+1)) + 
  Int[(d+e*x^n)^q*ExpandToSum[(a+c*x^(2*n))^p-c^p*x^(2*n*p)-d*c^p*(2*n*p-n+1)*x^(2*n*p-n)/(e*(2*n*p+n*q+1)),x],x] /;
FreeQ[{a,c,d,e,n,q},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[p] && 
  NonzeroQ[2*n*p+n*q+1] && PositiveIntegerQ[n] && Not[PositiveIntegerQ[q]]


Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
  -1/e^2*Int[(c*d-b*e-c*e*x^2)/Sqrt[a+b*x^2+c*x^4],x] + 
  (c*d^2-b*d*e+a*e^2)/e^2*Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[Sqrt[a_+c_.*x_^4]/(d_+e_.*x_^2),x_Symbol] :=
  -c/e^2*Int[(d-e*x^2)/Sqrt[a+c*x^4],x] + 
  (c*d^2+a*e^2)/e^2*Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[(a_+b_.*x_^2+c_.*x_^4)^(3/2)/(d_+e_.*x_^2),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  -(c*d^2-b*d*e+a*e^2)^2/(e^3*(2*c*d-e*(b+q)))*
    Int[(b+q+2*c*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] - 
  1/e^4*Int[1/Sqrt[a+b*x^2+c*x^4]*
    Simp[(c*d-b*e)*(c*d^2-b*d*e+2*a*e^2)-2*c*(c*d^2-b*d*e+a*e^2)^2/(2*c*d-e*(b+q))-
      e*(c^2*d^2+b^2*e^2-2*c*e*(b*d-a*e))*x^2+c*e^2*(c*d-2*b*e)*x^4-c^2*e^3*x^6,x],x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveQ[b^2-4*a*c]


Int[(a_+c_.*x_^4)^(3/2)/(d_+e_.*x_^2),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  -(c*d^2+a*e^2)^2/(e^3*(c*d-e*q))*
    Int[(q+c*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] - 
  c/e^4*Int[1/Sqrt[a+c*x^4]*
    Simp[d*(c*d^2+2*a*e^2)-(c*d^2+a*e^2)^2/(c*d-e*q)-e*(c*d^2+2*a*e^2)*x^2+c*d*e^2*x^4-c*e^3*x^6,x],x]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && PositiveQ[-a*c]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
  a*Int[(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] + 
  b*Int[x^2*(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] + 
  c*Int[x^4*(a+b*x^2+c*x^4)^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PositiveIntegerQ[p-1/2]


Int[(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
  a*Int[(a+c*x^4)^(p-1)/(d+e*x^2),x] + 
  c*Int[x^4*(a+c*x^4)^(p-1)/(d+e*x^2),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && PositiveIntegerQ[p-1/2]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*Sqrt[-c]*Int[1/((d+e*x^2)*Sqrt[b+q+2*c*x^2]*Sqrt[-b+q-2*c*x^2]),x]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c] && NegativeQ[c]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  Sqrt[-c]*Int[1/((d+e*x^2)*Sqrt[q+c*x^2]*Sqrt[q-c*x^2]),x]] /;
FreeQ[{a,c,d,e},x] && PositiveQ[a] && NegativeQ[c]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  2*c/(2*c*d-e*(b-q))*Int[1/Sqrt[a+b*x^2+c*x^4],x] - e/(2*c*d-e*(b-q))*Int[(b-q+2*c*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x]] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[b^2-4*a*c] && Not[NegativeQ[c]]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  c/(c*d+e*q)*Int[1/Sqrt[a+c*x^4],x] + e/(c*d+e*q)*Int[(q-c*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x]] /;
FreeQ[{a,c,d,e},x] && PositiveQ[-a*c] && Not[NegativeQ[c]]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[c/a,4]},
  ArcTan[Sqrt[(c*d^2-b*d*e+a*e^2)/(d*e)]*x/Sqrt[a+b*x^2+c*x^4]]/(2*d*Sqrt[(c*d^2-b*d*e+a*e^2)/(d*e)]) + 
  (e+d*q^2)*(1+q^2*x^2)*Sqrt[(a+b*x^2+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*d*q*(e-d*q^2)*Sqrt[a+b*x^2+c*x^4])*
    EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2-b*q^2/(4*c)] - 
  q^2/(e-d*q^2)*Int[1/Sqrt[a+b*x^2+c*x^4],x] /;
 NonzeroQ[e-d*q^2]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && PosQ[c/a]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[c/a,4]},
  ArcTan[Sqrt[(c*d^2+a*e^2)/(d*e)]*x/Sqrt[a+c*x^4]]/(2*d*Sqrt[(c*d^2+a*e^2)/(d*e)]) + 
  (e+d*q^2)*(1+q^2*x^2)*Sqrt[(a+c*x^4)/(a*(1+q^2*x^2)^2)]/(4*d*q*(e-d*q^2)*Sqrt[a+c*x^4])*
    EllipticPi[-(e-d*q^2)^2/(4*d*e*q^2),2*ArcTan[q*x],1/2] - 
  q^2/(e-d*q^2)*Int[1/Sqrt[a+c*x^4],x] /;
 NonzeroQ[e-d*q^2]] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && PosQ[c/a]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[-c/a,4]},
  1/(d*Sqrt[a]*q)*EllipticPi[-e/(d*q^2),ArcSin[q*x],-1]] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && PositiveQ[a]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  Sqrt[1+c*x^4/a]/Sqrt[a+c*x^4]*Int[1/((d+e*x^2)*Sqrt[1+c*x^4/a]),x] /;
FreeQ[{a,c,d,e},x] && NegQ[c/a] && Not[PositiveQ[a]]


Int[1/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
    Int[1/((d+e*x^2)*Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NegQ[c/a]


Int[(a_+b_.*x_^2+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
  -x*(b^2*c*d-b^3*e-2*a*c^2*d+3*a*b*c*e+c*(b*c*d-b^2*e+2*a*c*e)*x^2)*(a+b*x^2+c*x^4)^(p+1)/
    (2*a*(p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2)) - 
  1/(2*a*(p+1)*(b^2-4*a*c)*(c*d^2-b*d*e+a*e^2))*Int[((a+b*x^2+c*x^4)^(p+1)/(d+e*x^2))*
    Simp[b^3*d*e*(3+2*p)-a*b*c*d*e*(11+8*p)-b^2*(2*a*e^2*(p+1)+c*d^2*(3+2*p))+
      2*a*c*(4*a*e^2*(p+1)+c*d^2*(5+4*p))-
      (4*a*c^2*d*e-2*b^2*c*d*e*(2+p)-b^3*e^2*(3+2*p)+b*c*(c*d^2*(7+4*p)+a*e^2*(11+8*p)))*x^2-
      c*e*(b*c*d-b^2*e+2*a*c*e)*(7+4*p)*x^4,x],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && NegativeIntegerQ[p+1/2]


Int[(a_+c_.*x_^4)^p_/(d_+e_.*x_^2),x_Symbol] :=
  -x*(-2*a*c^2*d+c*(2*a*c*e)*x^2)*(a+c*x^4)^(p+1)/(2*a*(p+1)*(-4*a*c)*(c*d^2+a*e^2)) - 
  1/(2*a*(p+1)*(-4*a*c)*(c*d^2+a*e^2))*Int[((a+c*x^4)^(p+1)/(d+e*x^2))*
    Simp[2*a*c*(4*a*e^2*(p+1)+c*d^2*(5+4*p))-(4*a*c^2*d*e)*x^2-c*e*(2*a*c*e)*(7+4*p)*x^4,x],x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2] && NegativeIntegerQ[p+1/2]


Int[1/((d_+e_.*x_^2)^2*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  e^2*x*Sqrt[a+b*x^2+c*x^4]/(2*d*(c*d^2-b*d*e+a*e^2)*(d+e*x^2)) - 
  c/(2*d*(c*d^2-b*d*e+a*e^2))*Int[(d+e*x^2)/Sqrt[a+b*x^2+c*x^4],x] + 
  (3*c*d^2-2*b*d*e+a*e^2)/(2*d*(c*d^2-b*d*e+a*e^2))*Int[1/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2]


Int[1/((d_+e_.*x_^2)^2*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  e^2*x*Sqrt[a+c*x^4]/(2*d*(c*d^2+a*e^2)*(d+e*x^2)) - 
  c/(2*d*(c*d^2+a*e^2))*Int[(d+e*x^2)/Sqrt[a+c*x^4],x] + 
  (3*c*d^2+a*e^2)/(2*d*(c*d^2+a*e^2))*Int[1/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
FreeQ[{a,c,d,e},x] && NonzeroQ[c*d^2+a*e^2]


Int[(d_+e_.*x_^2)^q_*(a_+b_.*x_^2+c_.*x_^4)^p_,x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  a^IntPart[p]*(a+b*x^2+c*x^4)^FracPart[p]/((1+2*c*x^2/(b-r))^FracPart[p]*(1+2*c*x^2/(b+r))^FracPart[p])*
    Int[(d+e*x^2)^q*(1+2*c*x^2/(b-r))^p*(1+2*c*x^2/(b+r))^p,x]] /;
FreeQ[{a,b,c,d,e,q},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p-1/2] && NegativeIntegerQ[q]


Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  With[{r=Rt[-a*c,2]},
  a^IntPart[p]*(a+c*x^4)^FracPart[p]/((1-c*x^2/r)^FracPart[p]*(1+c*x^2/r)^FracPart[p])*
    Int[(d+e*x^2)^q*(1-c*x^2/r)^p*(1+c*x^2/r)^p,x]] /;
FreeQ[{a,c,d,e,q},x] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[p-1/2] && NegativeIntegerQ[q]


(* Int[(d_+e_.*x_^2)^q_*(a_+c_.*x_^4)^p_,x_Symbol] :=
  With[{r=Rt[-a*c,2]},
  a^IntPart[p]*(a+c*x^4)^FracPart[p]/(1-c*x^4/r^2)^FracPart[p]*Int[(d+e*x^2)^q*(1-c*x^4/r^2)^p,x]] /;
FreeQ[{a,c,d,e,q},x] && NonzeroQ[c*d^2+a*e^2] && IntegerQ[p-1/2] && NegativeIntegerQ[q] *)


Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  1/(2*Sqrt[a]*Sqrt[d]*Rt[-e/d,2])*EllipticF[2*ArcSin[Rt[-e/d,2]*x],b*d/(4*a*e)] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c*d-b*e] && PositiveQ[a] && PositiveQ[d]


Int[1/(Sqrt[d_+e_.*x_^2]*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  Sqrt[(d+e*x^2)/d]*Sqrt[(a+b*x^2+c*x^4)/a]/(Sqrt[d+e*x^2]*Sqrt[a+b*x^2+c*x^4])*
    Int[1/(Sqrt[1+e/d*x^2]*Sqrt[1+b/a*x^2+c/a*x^4]),x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c*d-b*e] && Not[PositiveQ[a] && PositiveQ[d]]


Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[a]/(2*Sqrt[d]*Rt[-e/d,2])*EllipticE[2*ArcSin[Rt[-e/d,2]*x],b*d/(4*a*e)] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c*d-b*e] && PositiveQ[a] && PositiveQ[d]


Int[Sqrt[a_+b_.*x_^2+c_.*x_^4]/Sqrt[d_+e_.*x_^2],x_Symbol] :=
  Sqrt[a+b*x^2+c*x^4]*Sqrt[(d+e*x^2)/d]/(Sqrt[d+e*x^2]*Sqrt[(a+b*x^2+c*x^4)/a])*
    Int[Sqrt[1+b/a*x^2+c/a*x^4]/Sqrt[1+e/d*x^2],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c*d-b*e] && Not[PositiveQ[a] && PositiveQ[d]]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && 
  (IntegersQ[p,q] && Not[IntegerQ[n]] || PositiveIntegerQ[p] || PositiveIntegerQ[q] && Not[IntegerQ[n]])


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && 
  (IntegersQ[p,q] && Not[IntegerQ[n]] || PositiveIntegerQ[p] || PositiveIntegerQ[q] && Not[IntegerQ[n]])


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^(2*n))^p,(d/(d^2-e^2*x^(2*n))-e*x^n/(d^2-e^2*x^(2*n)))^(-q),x],x] /;
FreeQ[{a,c,d,e,n,p},x] && ZeroQ[n2-2*n] && NonzeroQ[c*d^2+a*e^2] && NegativeIntegerQ[q] && Not[IntegersQ[n,2*p]]


Int[(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  Defer[Int][(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && Not[IntegersQ[n,q]]


Int[(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  Defer[Int][(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && Not[IntegersQ[n,q]]


Int[(d_+e_.*u_^n_)^q_.*(a_+b_.*u_^n_+c_.*u_^n2_)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(d_+e_.*u_^n_)^q_.*(a_+c_.*u_^n2_)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x,u] /;
FreeQ[{a,c,d,e,n,p,q},x] && ZeroQ[n2-2*n] && LinearQ[u,x] && NonzeroQ[u-x]


Int[(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,p},x] && EqQ[n2,2*n] && EqQ[mn,-n] && IntegerQ[q]


Int[(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
FreeQ[{a,c,d,e,mn,p},x] && EqQ[n2,-2*mn] && IntegerQ[q]


Int[(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(2*n*p)*(d+e*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && IntegerQ[p]


Int[(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(-2*mn*p)*(d+e*x^mn)^q*(c+a*x^(2*mn))^p,x] /;
FreeQ[{a,c,d,e,mn,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && IntegerQ[p]


Int[(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  x^(n*FracPart[q])*(d+e*x^(-n))^FracPart[q]/(e+d*x^n)^FracPart[q]*Int[x^(-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]] && PosQ[n]


Int[(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  x^(-mn*FracPart[q])*(d+e*x^mn)^FracPart[q]/(e+d*x^(-mn))^FracPart[q]*Int[x^(mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
FreeQ[{a,c,d,e,mn,p,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && Not[IntegerQ[p]] && PosQ[n2]


Int[(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/(x^(2*n*FracPart[p])*(c+b*x^(-n)+a*x^(-2*n))^FracPart[p])*
    Int[x^(2*n*p)*(d+e*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]] && NegQ[n]


Int[(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+c*x^n2)^FracPart[p]/(x^(n2*FracPart[p])*(c+a*x^(2*mn))^FracPart[p])*
    Int[x^(n2*p)*(d+e*x^mn)^q*(c+a*x^(2*mn))^p,x] /;
FreeQ[{a,c,d,e,mn,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && Not[IntegerQ[p]] && NegQ[n2]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^(-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,q},x] && EqQ[mn,-n] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p]*
    Int[x^(-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((4*c)^IntPart[p]*(b+2*c*x^n)^(2*FracPart[p]))*
    Int[(d+e*x^n)^q*(f+g*x^n)^r*(b+2*c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,q,r},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,f,g,n,q,r},x] && ZeroQ[n2-2*n] && ZeroQ[c*d^2+a*e^2] && IntegerQ[p]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*
    Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,g,n,p,q,r},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(d_+e_.*x_^n_)^q_.*(f_+g_.*x_^n_)^r_.*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*
    Int[(d+e*x^n)^(p+q)*(f+g*x^n)^r*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,f,g,n,p,q,r},x] && ZeroQ[n2-2*n] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[(f_.+g_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+b_.*x_^2+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (2*c*f-g*(b-q))/(2*c*d-e*(b-q))*Int[1/Sqrt[a+b*x^2+c*x^4],x] - 
  (e*f-d*g)/(2*c*d-e*(b-q))*Int[(b-q+2*c*x^2)/((d+e*x^2)*Sqrt[a+b*x^2+c*x^4]),x] /;
 NonzeroQ[2*c*f-g*(b-q)]] /;
FreeQ[{a,b,c,d,e,f,g},x] && PositiveQ[b^2-4*a*c] && NonzeroQ[c*d^2-b*d*e+a*e^2] && Not[NegativeQ[c]]


Int[(f_+g_.*x_^2)/((d_+e_.*x_^2)*Sqrt[a_+c_.*x_^4]),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  (c*f+g*q)/(c*d+e*q)*Int[1/Sqrt[a+c*x^4],x] + (e*f-d*g)/(c*d+e*q)*Int[(q-c*x^2)/((d+e*x^2)*Sqrt[a+c*x^4]),x] /;
 NonzeroQ[c*f+g*q]] /;
FreeQ[{a,c,d,e,f,g},x] && PositiveQ[-a*c] && NonzeroQ[c*d^2+a*e^2] && Not[NegativeQ[c]]


Int[(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[non2-n/2] && ZeroQ[d2*e1+d1*e2] && 
  (IntegerQ[q] || PositiveQ[d1] && PositiveQ[d2])


Int[(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (d1+e1*x^(n/2))^FracPart[q]*(d2+e2*x^(n/2))^FracPart[q]/(d1*d2+e1*e2*x^n)^FracPart[q]*
    Int[(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[non2-n/2] && ZeroQ[d2*e1+d1*e2]


Int[(A_+B_.*x_^m_.)*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  A*Int[(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] + B*Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,A,B,m,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[m-n+1]


Int[(A_+B_.*x_^m_.)*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  A*Int[(d+e*x^n)^q*(a+c*x^(2*n))^p,x] + B*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,A,B,m,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[m-n+1]





(* ::Subsection::Closed:: *)
(*4.4 (f x)^m (d+e x^n)^q (a+b x^n+c x^(2 n))^p*)
(**)


Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^m/(n*e^((m+1)/n-1))*Subst[Int[(e*x)^(q+(m+1)/n-1)*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && (IntegerQ[m] || PositiveQ[f]) && IntegerQ[Simplify[(m+1)/n]]


Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^m/(n*e^((m+1)/n-1))*Subst[Int[(e*x)^(q+(m+1)/n-1)*(a+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,c,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && (IntegerQ[m] || PositiveQ[f]) && IntegerQ[Simplify[(m+1)/n]]


Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^m*e^IntPart[q]*(e*x^n)^FracPart[q]/x^(n*FracPart[q])*Int[x^(m+n*q)*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && (IntegerQ[m] || PositiveQ[f]) && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[(f_.*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^m*e^IntPart[q]*(e*x^n)^FracPart[q]/x^(n*FracPart[q])*Int[x^(m+n*q)*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && (IntegerQ[m] || PositiveQ[f]) && Not[IntegerQ[Simplify[(m+1)/n]]]


Int[(f_*x_)^m_.*(e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && Not[IntegerQ[m]]


Int[(f_*x_)^m_.*(e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && Not[IntegerQ[m]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[Simplify[m-n+1]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[(d+e*x)^q*(a+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,c,d,e,m,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[Simplify[m-n+1]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m+n*(2*p+q))*(e+d*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n},x] && ZeroQ[n2-2*n] && IntegersQ[p,q] && NegQ[n]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m+n*(2*p+q))*(e+d*x^(-n))^q*(c+a*x^(-2*n))^p,x] /;
FreeQ[{a,c,d,e,m,n},x] && ZeroQ[n2-2*n] && IntegersQ[p,q] && NegQ[n]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/n*Subst[Int[x^((m+1)/n-1)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]] && PositiveIntegerQ[m,n,(m+1)/n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/(c^IntPart[p]*(b/2+c*x^n)^(2*FracPart[p]))*
    Int[(f*x)^m*(d+e*x^n)^q*(b/2+c*x^n)^(2*p),x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[b^2-4*a*c] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x)^q*(a+b*x+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && ZeroQ[n2-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  1/n*Subst[Int[x^(Simplify[(m+1)/n]-1)*(d+e*x)^q*(a+c*x^2)^p,x],x,x^n] /;
FreeQ[{a,c,d,e,m,n,p,q},x] && ZeroQ[n2-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && IntegerQ[Simplify[(m+1)/n]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(f*x)^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(f*x)^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,f,q,m,n,q},x] && ZeroQ[n2-2*n] && ZeroQ[c*d^2+a*e^2] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+b*x^n+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*
    Int[(f*x)^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-b*d*e+a*e^2] && Not[IntegerQ[p]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  (a+c*x^(2*n))^FracPart[p]/((d+e*x^n)^FracPart[p]*(a/d+(c*x^n)/e)^FracPart[p])*Int[(f*x)^m*(d+e*x^n)^(q+p)*(a/d+c/e*x^n)^p,x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[c*d^2+a*e^2] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) + 
  1/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1))*Int[x^Mod[m,n]*(d+e*x^n)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^n)*(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)*x^(m-Mod[m,n])*(a+b*x^n+c*x^(2*n))^p-
      (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n,p] && IntegersQ[m,q] && q<-1 && m>0


Int[x_^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) + 
  1/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1))*Int[x^Mod[m,n]*(d+e*x^n)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^n)*(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)*x^(m-Mod[m,n])*(a+c*x^(2*n))^p-
      (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n,p] && IntegersQ[m,q] && q<-1 && m>0


Int[x_^m_*(d_+e_.*x_^n_)^q_*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  (-d)^((m-Mod[m,n])/n-1)*(c*d^2-b*d*e+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) + 
  (-d)^((m-Mod[m,n])/n-1)/(n*e^(2*p)*(q+1))*Int[x^m*(d+e*x^n)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^n)*(n*(-d)^(-(m-Mod[m,n])/n+1)*e^(2*p)*(q+1)*(a+b*x^n+c*x^(2*n))^p - 
  (e^(-(m-Mod[m,n])/n)*(c*d^2-b*d*e+a*e^2)^p*x^(-(m-Mod[m,n])))*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n,p] && IntegersQ[m,q] && q<-1 && m<0


Int[x_^m_*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  (-d)^((m-Mod[m,n])/n-1)*(c*d^2+a*e^2)^p*x^(Mod[m,n]+1)*(d+e*x^n)^(q+1)/(n*e^(2*p+(m-Mod[m,n])/n)*(q+1)) + 
  (-d)^((m-Mod[m,n])/n-1)/(n*e^(2*p)*(q+1))*Int[x^m*(d+e*x^n)^(q+1)*
    ExpandToSum[Together[1/(d+e*x^n)*(n*(-d)^(-(m-Mod[m,n])/n+1)*e^(2*p)*(q+1)*(a+c*x^(2*n))^p - 
  (e^(-(m-Mod[m,n])/n)*(c*d^2+a*e^2)^p*x^(-(m-Mod[m,n])))*(d*(Mod[m,n]+1)+e*(Mod[m,n]+n*(q+1)+1)*x^n))],x],x] /;
FreeQ[{a,c,d,e},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n,p] && IntegersQ[m,q] && q<-1 && m<0


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  c^p*(f*x)^(m+2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*f^(2*n*p-n+1)*(m+2*n*p+n*q+1)) + 
  1/(e*(m+2*n*p+n*q+1))*Int[(f*x)^m*(d+e*x^n)^q*
    ExpandToSum[e*(m+2*n*p+n*q+1)*((a+b*x^n+c*x^(2*n))^p-c^p*x^(2*n*p))-d*c^p*(m+2*n*p-n+1)*x^(2*n*p-n),x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n,p] && 2*n*p>n-1 && 
  Not[IntegerQ[q]] && NonzeroQ[m+2*n*p+n*q+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  c^p*(f*x)^(m+2*n*p-n+1)*(d+e*x^n)^(q+1)/(e*f^(2*n*p-n+1)*(m+2*n*p+n*q+1)) + 
  1/(e*(m+2*n*p+n*q+1))*Int[(f*x)^m*(d+e*x^n)^q*
    ExpandToSum[e*(m+2*n*p+n*q+1)*((a+c*x^(2*n))^p-c^p*x^(2*n*p))-d*c^p*(m+2*n*p-n+1)*x^(2*n*p-n),x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n,p] && 2*n*p>n-1 && 
  Not[IntegerQ[q]] && NonzeroQ[m+2*n*p+n*q+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n,p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && ZeroQ[n2-2*n] && ZeroQ[n2-2*n] && PositiveIntegerQ[n,p]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(d+e*x^(n/k))^q*(a+b*x^(n/k)+c*x^(2*n/k))^p,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,b,c,d,e,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=GCD[m+1,n]},
  1/k*Subst[Int[x^((m+1)/k-1)*(d+e*x^(n/k))^q*(a+c*x^(2*n/k))^p,x],x,x^k] /;
 k!=1] /;
FreeQ[{a,c,d,e,p,q},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && IntegerQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/f*Subst[Int[x^(k*(m+1)-1)*(d+e*x^(k*n)/f^n)^q*(a+b*x^(k*n)/f^n+c*x^(2*k*n)/f^(2*n))^p,x],x,(f*x)^(1/k)]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && FractionQ[m] && IntegerQ[p]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{k=Denominator[m]},
  k/f*Subst[Int[x^(k*(m+1)-1)*(d+e*x^(k*n)/f)^q*(a+c*x^(2*k*n)/f)^p,x],x,(f*x)^(1/k)]] /;
FreeQ[{a,c,d,e,f,p,q},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && FractionQ[m] && IntegerQ[p]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p*(d*(m+n*(2*p+1)+1)+e*(m+1)*x^n)/(f*(m+1)*(m+n*(2*p+1)+1)) + 
  n*p/(f^n*(m+1)*(m+n*(2*p+1)+1))*Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1)*
      Simp[2*a*e*(m+1)-b*d*(m+n*(2*p+1)+1)+(b*e*(m+1)-2*c*d*(m+n*(2*p+1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-1 && 
  m+n*(2*p+1)+1!=0 && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+c*x^(2*n))^p*(d*(m+n*(2*p+1)+1)+e*(m+1)*x^n)/(f*(m+1)*(m+n*(2*p+1)+1)) + 
  2*n*p/(f^n*(m+1)*(m+n*(2*p+1)+1))*Int[(f*x)^(m+n)*(a+c*x^(2*n))^(p-1)*(a*e*(m+1)-c*d*(m+n*(2*p+1)+1)*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-1 && 
  m+n*(2*p+1)+1!=0 && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^p*(b*e*n*p+c*d*(m+n*(2*p+1)+1)+c*e*(2*n*p+m+1)*x^n)/
    (c*f*(2*n*p+m+1)*(m+n*(2*p+1)+1)) + 
  n*p/(c*(2*n*p+m+1)*(m+n*(2*p+1)+1))*Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p-1)*
    Simp[2*a*c*d*(m+n*(2*p+1)+1)-a*b*e*(m+1)+(2*a*c*e*(2*n*p+m+1)+b*c*d*(m+n*(2*p+1)+1)-b^2*e*(m+n*p+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p>0 && 
  NonzeroQ[2*n*p+m+1] && NonzeroQ[m+n*(2*p+1)+1] && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (f*x)^(m+1)*(a+c*x^(2*n))^p*(c*d*(m+n*(2*p+1)+1)+c*e*(2*n*p+m+1)*x^n)/(c*f*(2*n*p+m+1)*(m+n*(2*p+1)+1)) + 
  2*a*n*p/((2*n*p+m+1)*(m+n*(2*p+1)+1))*Int[(f*x)^m*(a+c*x^(2*n))^(p-1)*Simp[d*(m+n*(2*p+1)+1)+e*(2*n*p+m+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[p] && p>0 && 
  NonzeroQ[2*n*p+m+1] && NonzeroQ[m+n*(2*p+1)+1] && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  f^(n-1)*(f*x)^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(b*d-2*a*e-(b*e-2*c*d)*x^n)/(n*(p+1)*(b^2-4*a*c)) + 
  f^n/(n*(p+1)*(b^2-4*a*c))*Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1)*
      Simp[(n-m-1)*(b*d-2*a*e)+(2*n*p+2*n+m+1)*(b*e-2*c*d)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m>n-1 && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_.,x_Symbol] :=
  f^(n-1)*(f*x)^(m-n+1)*(a+c*x^(2*n))^(p+1)*(a*e-c*d*x^n)/(2*a*c*n*(p+1)) + 
  f^n/(2*a*c*n*(p+1))*Int[(f*x)^(m-n)*(a+c*x^(2*n))^(p+1)*(a*e*(n-m-1)+c*d*(2*n*p+2*n+m+1)*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && 
  RationalQ[m,p] && p<-1 && m>n-1 && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(d*(b^2-2*a*c)-a*b*e+(b*d-2*a*e)*c*x^n)/(a*f*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*
      Simp[d*(b^2*(m+n*(p+1)+1)-2*a*c*(m+2*n*(p+1)+1))-a*b*e*(m+1)+c*(m+n*(2*p+3)+1)*(b*d-2*a*e)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)*(d+e*x^n)/(2*a*f*n*(p+1)) + 
  1/(2*a*n*(p+1))*Int[(f*x)^m*(a+c*x^(2*n))^(p+1)*Simp[d*(m+2*n*(p+1)+1)+e*(m+n*(2*p+3)+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,f,m},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[p] && p<-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  e*f^(n-1)*(f*x)^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+n(2*p+1)+1)) - 
  f^n/(c*(m+n(2*p+1)+1))*
    Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^p*Simp[a*e*(m-n+1)+(b*e*(m+n*p+1)-c*d*(m+n(2*p+1)+1))*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m>n-1 && 
  NonzeroQ[m+n(2*p+1)+1] && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  e*f^(n-1)*(f*x)^(m-n+1)*(a+c*x^(2*n))^(p+1)/(c*(m+n(2*p+1)+1)) - 
  f^n/(c*(m+n(2*p+1)+1))*Int[(f*x)^(m-n)*(a+c*x^(2*n))^p*(a*e*(m-n+1)-c*d*(m+n(2*p+1)+1)*x^n),x] /;
FreeQ[{a,c,d,e,f,p},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m] && m>n-1 && 
  NonzeroQ[m+n(2*p+1)+1] && (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  d*(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*f*(m+1)) + 
  1/(a*f^n*(m+1))*Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^p*Simp[a*e*(m+1)-b*d*(m+n*(p+1)+1)-c*d*(m+2*n(p+1)+1)*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,p},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  d*(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)/(a*f*(m+1)) + 
  1/(a*f^n*(m+1))*Int[(f*x)^(m+n)*(a+c*x^(2*n))^p*(a*e*(m+1)-c*d*(m+2*n(p+1)+1)*x^n),x] /;
FreeQ[{a,c,d,e,f,p},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m] && m<-1 && 
  (IntegerQ[p] || IntegerQ[2*p] && IntegerQ[m] && n==2)


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q-b*c,2]},
  c/(2*q*r)*Int[(f*x)^m*Simp[d*r-(c*d-e*q)*x^(n/2),x]/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(f*x)^m*Simp[d*r+(c*d-e*q)*x^(n/2),x]/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NegativeQ[b^2-4*a*c] && IntegersQ[m,n/2] && 0<m<n && PosQ[a*c]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q,2]},
  c/(2*q*r)*Int[(f*x)^m*Simp[d*r-(c*d-e*q)*x^(n/2),x]/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(f*x)^m*Simp[d*r+(c*d-e*q)*x^(n/2),x]/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveQ[a*c] && IntegersQ[m,n/2] && 0<m<n


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
  With[{r=Rt[c/e*(2*c*d-b*e),2]},
  e/2*Int[(f*x)^m/(c*d/e-r*x+c*x^2),x] + 
  e/2*Int[(f*x)^m/(c*d/e+r*x+c*x^2),x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-a*e^2] && PositiveQ[d/e] && PosQ[c/e*(2*c*d-b*e)]


Int[(f_.*x_)^m_.*(d_+e_.*x_^2)/(a_+c_.*x_^4), x_Symbol] :=
  With[{r=Rt[2*c^2*d/e,2]},
  e/2*Int[(f*x)^m/(c*d/e-r*x+c*x^2),x] + 
  e/2*Int[(f*x)^m/(c*d/e+r*x+c*x^2),x]] /;
FreeQ[{a,c,d,e,f,m},x] && ZeroQ[c*d^2-a*e^2] && PositiveQ[d/e]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q-b*c,2]},
  c/(2*q*r)*Int[(f*x)^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(f*x)^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q-b*c]]] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[n2-2*n] && NegativeQ[b^2-4*a*c] && IntegerQ[n/2] && n>2 && PosQ[a*c]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[a*c,2]},
  With[{r=Rt[2*c*q,2]},
  c/(2*q*r)*Int[(f*x)^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x] + 
  c/(2*q*r)*Int[(f*x)^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]] /;
 Not[NegativeQ[2*c*q]]] /;
FreeQ[{a,c,d,e,f,m},x] && ZeroQ[n2-2*n] && IntegerQ[n/2] && n>2 && PositiveQ[a*c]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[b^2-4*a*c,2]},
  (e/2+(2*c*d-b*e)/(2*q))*Int[(f*x)^m/(b/2-q/2+c*x^n),x] + (e/2-(2*c*d-b*e)/(2*q))*Int[(f*x)^m/(b/2+q/2+c*x^n),x]] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)/(a_+c_.*x_^n2_),x_Symbol] :=
  With[{q=Rt[-a*c,2]},
  -(e/2+c*d/(2*q))*Int[(f*x)^m/(q-c*x^n),x] + (e/2-c*d/(2*q))*Int[(f*x)^m/(q+c*x^n),x]] /;
FreeQ[{a,c,d,e,f,m},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[q] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,f,m},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && IntegerQ[q] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m,(d+e*x^n)^q/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && IntegerQ[q] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_./(a_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m,(d+e*x^n)^q/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,f,m},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && IntegerQ[q] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  f^(2*n)/c^2*Int[(f*x)^(m-2*n)*(c*d-b*e+c*e*x^n)*(d+e*x^n)^(q-1),x] - 
  f^(2*n)/c^2*Int[(f*x)^(m-2*n)*(d+e*x^n)^(q-1)*Simp[a*(c*d-b*e)+(b*c*d-b^2*e+a*c*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q>0 && m>2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  f^(2*n)/c*Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] - 
  a*f^(2*n)/c*Int[(f*x)^(m-2*n)*(d+e*x^n)^q/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f,q},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m] && m>2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  e*f^n/c*Int[(f*x)^(m-n)*(d+e*x^n)^(q-1),x] - 
  f^n/c*Int[(f*x)^(m-n)*(d+e*x^n)^(q-1)*Simp[a*e-(c*d-b*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q>0 && n-1<m<=2n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  e*f^n/c*Int[(f*x)^(m-n)*(d+e*x^n)^(q-1),x] - 
  f^n/c*Int[(f*x)^(m-n)*(d+e*x^n)^(q-1)*Simp[a*e-c*d*x^n,x]/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m,q] && q>0 && n-1<m<=2n-1


Int[(f_.*x_)^m_*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  d/a*Int[(f*x)^m*(d+e*x^n)^(q-1),x] - 
  1/(a*f^n)*Int[(f*x)^(m+n)*(d+e*x^n)^(q-1)*Simp[b*d-a*e+c*d*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q>0 && m<0


Int[(f_.*x_)^m_*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  d/a*Int[(f*x)^m*(d+e*x^n)^(q-1),x] + 
  1/(a*f^n)*Int[(f*x)^(m+n)*(d+e*x^n)^(q-1)*Simp[a*e-c*d*x^n,x]/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m,q] && q>0 && m<0


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  d^2*f^(2*n)/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] - 
  f^(2*n)/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2*n)*(d+e*x^n)^(q+1)*Simp[a*d+(b*d-a*e)*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q<-1 && m>2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  d^2*f^(2*n)/(c*d^2+a*e^2)*Int[(f*x)^(m-2*n)*(d+e*x^n)^q,x] - 
  a*f^(2*n)/(c*d^2+a*e^2)*Int[(f*x)^(m-2*n)*(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m,q] && q<-1 && m>2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  -d*e*f^n/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-n)*(d+e*x^n)^q,x] + 
  f^n/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-n)*(d+e*x^n)^(q+1)*Simp[a*e+c*d*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[m,q] && q<-1 && n-1<m<=2*n-1


Int[(f_.*x_)^m_.*(d_.+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  -d*e*f^n/(c*d^2+a*e^2)*Int[(f*x)^(m-n)*(d+e*x^n)^q,x] + 
  f^n/(c*d^2+a*e^2)*Int[(f*x)^(m-n)*(d+e*x^n)^(q+1)*Simp[a*e+c*d*x^n,x]/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[m,q] && q<-1 && n-1<m<=2*n-1


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_),x_Symbol] :=
  e^2/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^m*(d+e*x^n)^q,x] + 
  1/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^m*(d+e*x^n)^(q+1)*Simp[c*d-b*e-c*e*x^n,x]/(a+b*x^n+c*x^(2*n)),x] /;
FreeQ[{a,b,c,d,e,f,m},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  RationalQ[q] && q<-1


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_),x_Symbol] :=
  e^2/(c*d^2+a*e^2)*Int[(f*x)^m*(d+e*x^n)^q,x] + 
  c/(c*d^2+a*e^2)*Int[(f*x)^m*(d+e*x^n)^(q+1)*(d-e*x^n)/(a+c*x^(2*n)),x] /;
FreeQ[{a,c,d,e,f,m},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && RationalQ[q] && q<-1


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q,(f*x)^m/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,f,q,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(d+e*x^n)^q,(f*x)^m/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,f,q,n},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q,1/(a+b*x^n+c*x^(2*n)),x],x] /;
FreeQ[{a,b,c,d,e,f,m,q,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && 
  Not[IntegerQ[m]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q,1/(a+c*x^(2*n)),x],x] /;
FreeQ[{a,c,d,e,f,m,q,n},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && Not[IntegerQ[q]] && Not[IntegerQ[m]]


Int[(f_.*x_)^m_*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  1/d^2*Int[(f*x)^m*(a*d+(b*d-a*e)*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] + 
  (c*d^2-b*d*e+a*e^2)/(d^2*f^(2*n))*Int[(f*x)^(m+2*n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-n


Int[(f_.*x_)^m_*(a_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  a/d^2*Int[(f*x)^m*(d-e*x^n)*(a+c*x^(2*n))^(p-1),x] + 
  (c*d^2+a*e^2)/(d^2*f^(2*n))*Int[(f*x)^(m+2*n)*(a+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<-n


Int[(f_.*x_)^m_*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  1/(d*e)*Int[(f*x)^m*(a*e+c*d*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x] - 
  (c*d^2-b*d*e+a*e^2)/(d*e*f^n)*Int[(f*x)^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<0


Int[(f_.*x_)^m_*(a_+c_.*x_^n2_.)^p_./(d_.+e_.*x_^n_),x_Symbol] :=
  1/(d*e)*Int[(f*x)^m*(a*e+c*d*x^n)*(a+c*x^(2*n))^(p-1),x] - 
  (c*d^2+a*e^2)/(d*e*f^n)*Int[(f*x)^(m+n)*(a+c*x^(2*n))^(p-1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p>0 && m<0


Int[(f_.*x_)^m_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  -f^(2*n)/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2*n)*(a*d+(b*d-a*e)*x^n)*(a+b*x^n+c*x^(2*n))^p,x] + 
  d^2*f^(2*n)/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-2*n)*(a+b*x^n+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>n


Int[(f_.*x_)^m_.*(a_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  -a*f^(2*n)/(c*d^2+a*e^2)*Int[(f*x)^(m-2*n)*(d-e*x^n)*(a+c*x^(2*n))^p,x] + 
  d^2*f^(2*n)/(c*d^2+a*e^2)*Int[(f*x)^(m-2*n)*(a+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>n


Int[(f_.*x_)^m_.*(a_.+b_.*x_^n_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  f^n/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-n)*(a*e+c*d*x^n)*(a+b*x^n+c*x^(2*n))^p,x] - 
  d*e*f^n/(c*d^2-b*d*e+a*e^2)*Int[(f*x)^(m-n)*(a+b*x^n+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,b,c,d,e,f},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>0


Int[(f_.*x_)^m_.*(a_+c_.*x_^n2_.)^p_/(d_.+e_.*x_^n_),x_Symbol] :=
  f^n/(c*d^2+a*e^2)*Int[(f*x)^(m-n)*(a*e+c*d*x^n)*(a+c*x^(2*n))^p,x] - 
  d*e*f^n/(c*d^2+a*e^2)*Int[(f*x)^(m-n)*(a+c*x^(2*n))^(p+1)/(d+e*x^n),x] /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && RationalQ[m,p] && p<-1 && m>0


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+b*x^n+c*x^(2*n))^p,(f*x)^m(d+e*x^n)^q,x],x] /;
FreeQ[{a,b,c,d,e,f,m,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && PositiveIntegerQ[n] && (PositiveIntegerQ[q] || IntegersQ[m,q])


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(a+c*x^(2*n))^p,(f*x)^m(d+e*x^n)^q,x],x] /;
FreeQ[{a,c,d,e,f,m,q},x] && ZeroQ[n2-2*n] && PositiveIntegerQ[n] && (PositiveIntegerQ[q] || IntegersQ[m,q])


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && IntegerQ[m]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,e,p,q},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[n] && IntegerQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[m]},
  -g/f*Subst[Int[(d+e*f^(-n)*x^(-g*n))^q*(a+b*f^(-n)*x^(-g*n)+c*f^(-2*n)*x^(-2*g*n))^p/x^(g*(m+1)+1),x],x,1/(f*x)^(1/g)]] /;
FreeQ[{a,b,c,d,e,f,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && FractionQ[m]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[m]},
  -g/f*Subst[Int[(d+e*f^(-n)*x^(-g*n))^q*(a+c*f^(-2*n)*x^(-2*g*n))^p/x^(g*(m+1)+1),x],x,1/(f*x)^(1/g)]] /;
FreeQ[{a,c,d,e,f,p,q},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[n] && FractionQ[m]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -f^IntPart[m]*(f*x)^FracPart[m]*(x^(-1))^FracPart[m]*Subst[Int[(d+e*x^(-n))^q*(a+b*x^(-n)+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  -f^IntPart[m]*(f*x)^FracPart[m]*(x^(-1))^FracPart[m]*Subst[Int[(d+e*x^(-n))^q*(a+c*x^(-2*n))^p/x^(m+2),x],x,1/x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[n] && Not[RationalQ[m]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*(d+e*x^(g*n))^q*(a+b*x^(g*n)+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,b,c,d,e,m,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && FractionQ[n]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  With[{g=Denominator[n]},
  g*Subst[Int[x^(g*(m+1)-1)*(d+e*x^(g*n))^q*(a+c*x^(2*g*n))^p,x],x,x^(1/g)]] /;
FreeQ[{a,c,d,e,m,p,q},x] && ZeroQ[n2-2*n] && FractionQ[n]


Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && FractionQ[n]


Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && ZeroQ[n2-2*n] && FractionQ[n]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(d+e*x^Simplify[n/(m+1)])^q*(a+b*x^Simplify[n/(m+1)]+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  1/(m+1)*Subst[Int[(d+e*x^Simplify[n/(m+1)])^q*(a+c*x^Simplify[2*n/(m+1)])^p,x],x,x^(m+1)] /;
FreeQ[{a,c,d,e,m,n,p,q},x] && ZeroQ[n2-2*n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(f_*x_)^m_*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,p,q},x] && ZeroQ[n2-2*n] && IntegerQ[Simplify[n/(m+1)]] && Not[IntegerQ[n]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+b_.*x_^n_+c_.*x_^n2_.),x_Symbol] :=
  With[{r=Rt[b^2-4*a*c,2]},
  2*c/r*Int[(f*x)^m*(d+e*x^n)^q/(b-r+2*c*x^n),x] - 2*c/r*Int[(f*x)^m*(d+e*x^n)^q/(b+r+2*c*x^n),x]] /;
FreeQ[{a,b,c,d,e,f,m,n,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_/(a_+c_.*x_^n2_.),x_Symbol] :=
  With[{r=Rt[-a*c,2]},
  -c/(2*r)*Int[(f*x)^m*(d+e*x^n)^q/(r-c*x^n),x] - c/(2*r)*Int[(f*x)^m*(d+e*x^n)^q/(r+c*x^n),x]] /;
FreeQ[{a,c,d,e,f,m,n,q},x] && ZeroQ[n2-2*n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^n2_)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)*(d*(b^2-2*a*c)-a*b*e+(b*d-2*a*e)*c*x^n)/(a*f*n*(p+1)*(b^2-4*a*c)) + 
  1/(a*n*(p+1)*(b^2-4*a*c))*Int[(f*x)^m*(a+b*x^n+c*x^(2*n))^(p+1)*
      Simp[d*(b^2*(m+n*(p+1)+1)-2*a*c*(m+2*n*(p+1)+1))-a*b*e*(m+1)+(m+n*(2*p+3)+1)*(b*d-2*a*e)*c*x^n,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && NegativeIntegerQ[p+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  -(f*x)^(m+1)*(a+c*x^(2*n))^(p+1)*(d+e*x^n)/(2*a*f*n*(p+1)) + 
  1/(2*a*n*(p+1))*Int[(f*x)^m*(a+c*x^(2*n))^(p+1)*Simp[d*(m+2*n*(p+1)+1)+e*(m+n*(2*p+3)+1)*x^n,x],x] /;
FreeQ[{a,c,d,e,f,m,n},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[p+1]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && NonzeroQ[b^2-4*a*c] && (PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[ExpandIntegrand[(f*x)^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && (PositiveIntegerQ[p] || PositiveIntegerQ[q])


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  f^m*Int[ExpandIntegrand[x^m*(a+c*x^(2*n))^p,(d/(d^2-e^2*x^(2*n))-e*x^n/(d^2-e^2*x^(2*n)))^(-q),x],x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[q] && (IntegerQ[m] || PositiveQ[f])


Int[(f_.*x_)^m_*(d_+e_.*x_^n_)^q_*(a_+c_.*x_^n2_)^p_,x_Symbol] :=
  (f*x)^m/x^m*Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n] && NegativeIntegerQ[q] && Not[IntegerQ[m] || PositiveQ[f]]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^n_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Defer[Int][(f*x)^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n]


Int[(f_.*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Defer[Int][(f*x)^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,n,p,q},x] && ZeroQ[n2-2*n]


Int[u_^m_.*(d_+e_.*v_^n_)^q_.*(a_+b_.*v_^n_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(d+e*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && ZeroQ[n2-2*n] && LinearPairQ[u,v,x]


Int[u_^m_.*(d_+e_.*v_^n_)^q_.*(a_+c_.*v_^n2_.)^p_.,x_Symbol] :=
  u^m/(Coefficient[v,x,1]*v^m)*Subst[Int[x^m*(d+e*x^n)^q*(a+c*x^(2*n))^p,x],x,v] /;
FreeQ[{a,c,d,e,m,n,p},x] && ZeroQ[n2-2*n] && LinearPairQ[u,v,x]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p},x] && EqQ[n2,2*n] && EqQ[mn,-n] && IntegerQ[q]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m+mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
FreeQ[{a,c,d,e,m,mn,p},x] && EqQ[n2,-2*mn] && IntegerQ[q]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m+2*n*p)*(d+e*x^(-n))^q*(c+b*x^(-n)+a*x^(-2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_.,x_Symbol] :=
  Int[x^(m-2*mn*p)*(d+e*x^mn)^q*(c+a*x^(2*mn))^p,x] /;
FreeQ[{a,c,d,e,m,mn,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_,x_Symbol] :=
  x^(n*FracPart[q])*(d+e*x^(-n))^FracPart[q]/(e+d*x^n)^FracPart[q]*Int[x^(m-n*q)*(e+d*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n] && Not[IntegerQ[q]] && Not[IntegerQ[p]]


Int[x_^m_.*(d_+e_.*x_^mn_.)^q_*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  x^(-mn*FracPart[q])*(d+e*x^mn)^FracPart[q]/(e+d*x^(-mn))^FracPart[q]*Int[x^(m+mn*q)*(e+d*x^(-mn))^q*(a+c*x^n2)^p,x] /;
FreeQ[{a,c,d,e,m,mn,p,q},x] && EqQ[n2,-2*mn] && Not[IntegerQ[q]] && Not[IntegerQ[p]]


Int[(f_*x_)^m_*(d_+e_.*x_^mn_.)^q_.*(a_.+b_.*x_^n_.+c_.*x_^n2_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^mn)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[n2,2*n] && EqQ[mn,-n]


Int[(f_*x_)^m_*(d_+e_.*x_^mn_.)^q_.*(a_+c_.*x_^n2_.)^p_,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^mn)^q*(a+c*x^(2*n))^p,x] /;
FreeQ[{a,c,d,e,f,m,mn,p,q},x] && EqQ[n2,-2*mn]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  Int[x^(m-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,q},x] && EqQ[mn,-n] && IntegerQ[p]


Int[x_^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  x^(n*FracPart[p])*(a+b/x^n+c*x^n)^FracPart[p]/(b+a*x^n+c*x^(2*n))^FracPart[p]*
    Int[x^(m-n*p)*(d+e*x^n)^q*(b+a*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d,e,m,n,p,q},x] && EqQ[mn,-n] && Not[IntegerQ[p]]


Int[(f_*x_)^m_.*(d_+e_.*x_^n_)^q_.*(a_+b_.*x_^mn_+c_.*x_^n_.)^p_.,x_Symbol] :=
  f^IntPart[m]*(f*x)^FracPart[m]/x^FracPart[m]*Int[x^m*(d+e*x^n)^q*(a+b*x^(-n)+c*x^n)^p,x] /;
FreeQ[{a,b,c,d,e,f,m,n,p,q},x] && EqQ[mn,-n]


Int[(f_.*x_)^m_.*(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  Int[(f*x)^m*(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[non2-n/2] && ZeroQ[d2*e1+d1*e2] && 
  (IntegerQ[q] || PositiveQ[d1] && PositiveQ[d2])


Int[(f_.*x_)^m_.*(d1_+e1_.*x_^non2_.)^q_.*(d2_+e2_.*x_^non2_.)^q_.*(a_.+b_.*x_^n_+c_.*x_^n2_)^p_.,x_Symbol] :=
  (d1+e1*x^(n/2))^FracPart[q]*(d2+e2*x^(n/2))^FracPart[q]/(d1*d2+e1*e2*x^n)^FracPart[q]*
    Int[(f*x)^m*(d1*d2+e1*e2*x^n)^q*(a+b*x^n+c*x^(2*n))^p,x] /;
FreeQ[{a,b,c,d1,e1,d2,e2,f,n,p,q},x] && ZeroQ[n2-2*n] && ZeroQ[non2-n/2] && ZeroQ[d2*e1+d1*e2]





(* ::Subsection::Closed:: *)
(*4.6 (a x^q+b x^n+c x^(2 n-q))^p*)


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


Int[(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,n,p,q},x] && ZeroQ[r-(2*n-q)] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*4.7 (d x)^m (a x^q+b x^n+c x^(2 n-q))^p*)


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


Int[u_^m_.*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[x^m*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,m,n,p,q},x] && ZeroQ[r-(2*n-q)] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*4.8 (d+e x^(n-q)) (a x^q+b x^n+c x^(2 n-q))^p*)


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
  With[{n=q+r},
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
  With[{n=q+r},
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


Int[(A_+B_.*u_^j_.)*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,A,B,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && LinearQ[u,x] && NonzeroQ[u-x]





(* ::Subsection::Closed:: *)
(*4.9 (f x)^m (d+e x^(n-q)) (a x^q+b x^n+c x^(2 n-q))^p*)


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
  With[{n=q+r},
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
  With[{n=q+r},
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
  With[{n=q+r},
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
  With[{n=q+r},
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
  With[{n=q+r},
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
  With[{n=q+r},
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


Int[u_^m_.*(A_+B_.*u_^j_.)*(a_.*u_^q_.+b_.*u_^n_.+c_.*u_^r_.)^p_.,x_Symbol] :=
  1/Coefficient[u,x,1]*Subst[Int[x^m*(A+B*x^(n-q))*(a*x^q+b*x^n+c*x^(2*n-q))^p,x],x,u] /;
FreeQ[{a,b,c,A,B,m,n,p,q},x] && ZeroQ[j-(n-q)] && ZeroQ[r-(2*n-q)] && LinearQ[u,x] && NonzeroQ[u-x]



